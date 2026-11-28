"""Z3 counterexample search (interop-spec §4).

The search looks for a classical many-sorted model in which every premise holds
and the goal fails. It is advisory: the result never changes a verification
status and is never recorded in a certificate. Z3 is an optional dependency
(`smt` extra) imported on first use.

A model found by Z3 is re-checked, when its domains are finite, by evaluating
the AxiomWeave propositions directly in Python with the model's symbol tables
(interop-spec §4.5).
"""

import importlib
import itertools
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any, Literal

from axiomweave.core.expressions import Prop, Sort, Term, Var, VarKey, _fresh_name
from axiomweave.errors import AxwTypeError, BackendUnavailableError

Status = Literal["found", "none", "unknown"]

_NAT = "arith.Nat"
# Standard arithmetic symbols: canonical name -> (argument sorts, result sort).
_ARITH: dict[str, tuple[tuple[str, ...], str]] = {
    "arith.zero": ((), _NAT),
    "arith.succ": ((_NAT,), _NAT),
    "arith.add": ((_NAT, _NAT), _NAT),
    "arith.mul": ((_NAT, _NAT), _NAT),
}


@dataclass(frozen=True)
class Model:
    """A displayable counterexample model (interop-spec §4.4)."""

    domains: tuple[tuple[str, tuple[str, ...]], ...]  # uninterpreted sort -> elements
    values: tuple[tuple[str, str], ...]  # symbol or application -> value

    def __str__(self) -> str:
        lines = [f"  {sort} = {{{', '.join(elements)}}}" for sort, elements in self.domains]
        lines += [f"  {name} = {value}" for name, value in self.values]
        return "\n".join(lines)


@dataclass(frozen=True)
class Counterexample:
    """The result of a counterexample search (interop-spec §4.1–4.2)."""

    status: Status
    model: Model | None
    reason: str
    checked: bool  # the model was confirmed by the independent evaluator
    premises: str  # which premises were considered
    solver: str

    @property
    def found(self) -> bool:
        return self.status == "found"

    def __str__(self) -> str:
        head = {
            "found": "counterexample found",
            "none": "no counterexample",
            "unknown": "unknown",
        }[self.status]
        note = "" if self.status != "found" or self.checked else ", not re-checked"
        lines = [f"{head} ({self.solver}; premises: {self.premises}{note})"]
        if self.reason:
            lines.append(f"  reason: {self.reason}")
        if self.model is not None:
            lines.append(str(self.model))
        return "\n".join(lines)


def _z3() -> Any:
    try:
        return importlib.import_module("z3")
    except ImportError as exc:
        raise BackendUnavailableError(
            "counterexample search needs Z3; install it with `uv sync --extra smt`"
        ) from exc


def counterexample(
    goal: object,
    using: Sequence[object] = (),
    timeout_ms: int = 5000,
) -> Counterexample:
    """Search a model of the premises in which the goal is false.

    `goal` is a `Prop` or a `GoalView` (whose hypotheses become premises);
    `using` adds premises given as `Prop` or `Fact` objects.
    """
    z3 = _z3()
    if isinstance(goal, Prop):
        context: list[Prop] = []
        target = goal
    else:
        view_target = getattr(goal, "target", None)
        if not isinstance(view_target, Prop):
            raise AxwTypeError(f"counterexample expects a Prop or a goal, got {goal!r}")
        target = view_target
        context = [prop for _, prop in getattr(goal, "context", ())]
    extra = [_premise(item) for item in using]
    if type(timeout_ms) is not int or timeout_ms <= 0:
        raise AxwTypeError(f"timeout_ms must be a positive int, got {timeout_ms!r}")

    assumptions = [*context, *extra]
    target = _open_universals(target, assumptions)
    premises = "context" + (f" + {len(extra)} using" if extra else "")
    solver_name = f"Z3 {z3.get_version_string()}"
    encoder = _Encoder(z3)
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    solver.set("random_seed", 0)
    for prop in assumptions:
        solver.add(encoder.prop(prop, {}))
    solver.add(z3.Not(encoder.prop(target, {})))

    try:
        answer = solver.check()
    except z3.Z3Exception as exc:  # pragma: no cover - defensive
        return Counterexample("unknown", None, str(exc), False, premises, solver_name)
    if answer == z3.unsat:
        return Counterexample("none", None, "", False, premises, solver_name)
    if answer != z3.sat:
        reason = solver.reason_unknown()
        return Counterexample("unknown", None, reason, False, premises, solver_name)

    model = solver.model()
    reader = _Reader(z3, encoder, model)
    checked = False
    try:
        holds = all(reader.holds(p) for p in assumptions) and not reader.holds(target)
    except _NotEvaluable:
        holds = None
    if holds is False:
        reason = "the independent evaluator does not confirm the Z3 model"
        return Counterexample("unknown", None, reason, False, premises, solver_name)
    checked = holds is True
    return Counterexample("found", reader.display(), "", checked, premises, solver_name)


def _open_universals(target: Prop, premises: Sequence[Prop]) -> Prop:
    """Replace the leading ∀ binders of the target by fresh free variables, as `intro`
    would. The search is unchanged (¬∀x.A is satisfiable iff ¬A[c/x] is, for a new
    constant c), but the witness becomes a displayed constant of the model."""
    taken = {name for p in (target, *premises) for name, _ in p.free_vars()}
    while target.tag == "forall":
        var = target.var
        name = var.name if var.name not in taken else _fresh_name(var.name, taken)
        taken.add(name)
        target = target.open(Var(name, var.sort))
    return target


def _premise(item: object) -> Prop:
    prop = item if isinstance(item, Prop) else getattr(item, "prop", None)
    if not isinstance(prop, Prop):
        raise AxwTypeError(f"using expects Prop or Fact objects, got {item!r}")
    return prop


def _standard(const: Any) -> bool:
    """Whether a constant is a standard arithmetic symbol (interop-spec §4.3)."""
    signature = _ARITH.get(const.name)
    if signature is None or const.result is None:
        return False
    return (tuple(s.name for s in const.args), const.result.name) == signature


# --- encoding (interop-spec §4.3) ---------------------------------------------------


@dataclass
class _Symbol:
    decl: Any
    display: str
    args: tuple[Sort, ...]
    result: Sort | None  # None for propositions


class _Encoder:
    def __init__(self, z3: Any) -> None:
        self.z3 = z3
        self.sorts: dict[str, tuple[Sort, Any]] = {}
        self.symbols: dict[tuple[str, ...], _Symbol] = {}
        self._bound = 0

    def sort(self, sort: Sort) -> Any:
        found = self.sorts.get(sort.name)
        if found is None:
            z = self.z3.IntSort() if sort.name == _NAT else self.z3.DeclareSort(sort.name)
            found = self.sorts[sort.name] = (sort, z)
        return found[1]

    def _nat_guard(self, sort: Sort, value: Any) -> Any | None:
        return value >= 0 if sort.name == _NAT else None

    def symbol(
        self, key: tuple[str, ...], display: str, args: tuple[Sort, ...], result: Sort | None
    ) -> Any:
        """A function applying the symbol `key` to Z3 arguments."""
        if key not in self.symbols:
            z3 = self.z3
            codomain = z3.BoolSort() if result is None else self.sort(result)
            decl = z3.Function(":".join(key), *(self.sort(s) for s in args), codomain)
            self.symbols[key] = _Symbol(decl, display, args, result)
        symbol = self.symbols[key]
        return lambda *values: self.call(symbol, values)

    def call(self, symbol: _Symbol, values: Sequence[Any]) -> Any:
        """Apply a symbol. A Nat-valued symbol is the absolute value of an Int-valued
        one: every function into ℕ has this form, and no range axiom is needed."""
        value = symbol.decl(*values)
        if symbol.result is not None and symbol.result.name == _NAT:
            return self.z3.If(value >= 0, value, -value)
        return value

    def term(self, term: Term, bound: dict[VarKey, Any]) -> Any:
        node = term._node
        if node[0] == "var":
            if term.key in bound:
                return bound[term.key]
            return self.symbol(("v", term.name, term.sort.name), term.name, (), term.sort)()
        const = node[1]
        args = [self.term(a, bound) for a in node[2]]
        if _standard(const):
            if const.name == "arith.zero":
                return self.z3.IntVal(0)
            if const.name == "arith.succ":
                return args[0] + 1
            return args[0] + args[1] if const.name == "arith.add" else args[0] * args[1]
        return self.symbol(("c", const.name), const.short, const.args, const.result)(*args)

    def prop(self, prop: Prop, bound: dict[VarKey, Any]) -> Any:
        z3 = self.z3
        tag = prop.tag
        if tag == "false":
            return z3.BoolVal(False)
        if tag == "atom":
            return self.symbol(("p", prop.name), prop.name, (), None)()
        if tag == "pvar":
            sorts = tuple(a.sort for a in prop.args)
            key = ("p", prop.name, *(s.name for s in sorts))
            args = [self.term(a, bound) for a in prop.args]
            return self.symbol(key, prop.name, sorts, None)(*args)
        if tag == "pred":
            const = prop._node[1]
            args = [self.term(a, bound) for a in prop.args]
            return self.symbol(("c", const.name), const.short, const.args, None)(*args)
        if tag == "eq":
            left, right = prop.sides
            return self.term(left, bound) == self.term(right, bound)
        if tag in ("and", "or", "imp"):
            left = self.prop(prop.left, bound)
            right = self.prop(prop.right, bound)
            return {"and": z3.And, "or": z3.Or, "imp": z3.Implies}[tag](left, right)
        var = prop.var
        self._bound += 1
        x = z3.Const(f"b{self._bound}:{var.name}", self.sort(var.sort))
        body = self.prop(prop.body, {**bound, var.key: x})
        guard = self._nat_guard(var.sort, x)
        if tag == "forall":
            return z3.ForAll([x], body if guard is None else z3.Implies(guard, body))
        return z3.Exists([x], body if guard is None else z3.And(guard, body))


# --- model reading and re-checking (interop-spec §4.4–4.5) ---------------------------


class _NotEvaluable(Exception):
    """The model cannot be evaluated independently (an infinite or unknown domain)."""


class _Reader:
    """Reads a Z3 model into Python values: element indices for uninterpreted
    sorts, ints for Nat and bools for propositions."""

    def __init__(self, z3: Any, encoder: _Encoder, model: Any) -> None:
        self.z3 = z3
        self.encoder = encoder
        self.model = model
        self.universes: dict[str, list[Any]] = {}
        for name, (_, z) in encoder.sorts.items():
            if name != _NAT:
                universe = model.get_universe(z)
                self.universes[name] = list(universe) if universe is not None else []

    # values

    def _to_python(self, value: Any, sort: Sort | None) -> Any:
        if sort is None:
            return self.z3.is_true(value)
        if sort.name == _NAT:
            return value.as_long()
        for i, element in enumerate(self.universes.get(sort.name, [])):
            if element.eq(value):
                return i
        raise _NotEvaluable(f"value {value} is outside the domain of {sort.name}")

    def _to_z3(self, value: Any, sort: Sort) -> Any:
        if sort.name == _NAT:
            return self.z3.IntVal(value)
        return self.universes[sort.name][value]

    def apply(self, key: tuple[str, ...], args: Sequence[Any]) -> Any:
        symbol = self.encoder.symbols[key]
        z_args = [self._to_z3(a, s) for a, s in zip(args, symbol.args, strict=True)]
        value = self.model.eval(self.encoder.call(symbol, z_args), model_completion=True)
        return self._to_python(value, symbol.result)

    def domain(self, sort: Sort) -> range:
        elements = self.universes.get(sort.name)
        if not elements:
            raise _NotEvaluable(f"no finite domain for {sort.name}")
        return range(len(elements))

    # independent evaluation of AxiomWeave propositions

    def holds(self, prop: Prop, env: dict[VarKey, Any] | None = None) -> bool:
        env = env or {}
        tag = prop.tag
        if tag == "false":
            return False
        if tag == "atom":
            return bool(self.apply(("p", prop.name), ()))
        if tag == "pvar":
            key = ("p", prop.name, *(a.sort.name for a in prop.args))
            return bool(self.apply(key, [self.value(a, env) for a in prop.args]))
        if tag == "pred":
            key = ("c", prop._node[1].name)
            return bool(self.apply(key, [self.value(a, env) for a in prop.args]))
        if tag == "eq":
            left, right = prop.sides
            return bool(self.value(left, env) == self.value(right, env))
        if tag == "and":
            return self.holds(prop.left, env) and self.holds(prop.right, env)
        if tag == "or":
            return self.holds(prop.left, env) or self.holds(prop.right, env)
        if tag == "imp":
            return not self.holds(prop.left, env) or self.holds(prop.right, env)
        var = prop.var
        if var.sort.name == _NAT:
            raise _NotEvaluable("quantifier over Nat")
        values = (self.holds(prop.body, {**env, var.key: v}) for v in self.domain(var.sort))
        return all(values) if tag == "forall" else any(values)

    def value(self, term: Term, env: dict[VarKey, Any]) -> Any:
        node = term._node
        if node[0] == "var":
            if term.key in env:
                return env[term.key]
            return self.apply(("v", term.name, term.sort.name), ())
        const = node[1]
        args = [self.value(a, env) for a in node[2]]
        if _standard(const):
            if const.name == "arith.zero":
                return 0
            if const.name == "arith.succ":
                return args[0] + 1
            return args[0] + args[1] if const.name == "arith.add" else args[0] * args[1]
        return self.apply(("c", const.name), args)

    # display

    def _label(self, value: Any, sort: Sort | None) -> str:
        if sort is None:
            return "true" if value else "false"
        if sort.name == _NAT:
            return str(value)
        return f"{sort.short}#{value}"

    def display(self) -> Model:
        domains = tuple(
            (sort.short, tuple(self._label(i, sort) for i in range(len(self.universes[name]))))
            for name, (sort, _) in self.encoder.sorts.items()
            if name != _NAT
        )
        values: list[tuple[str, str]] = []
        for key, symbol in self.encoder.symbols.items():
            if not symbol.args:
                values.append((symbol.display, self._label(self.apply(key, ()), symbol.result)))
            elif all(s.name != _NAT for s in symbol.args):
                ranges = [range(len(self.universes[s.name])) for s in symbol.args]
                for args in itertools.product(*ranges):
                    shown = ", ".join(
                        self._label(a, s) for a, s in zip(args, symbol.args, strict=True)
                    )
                    value = self._label(self.apply(key, args), symbol.result)
                    values.append((f"{symbol.display}({shown})", value))
            else:
                values.extend(self._entries(key, symbol))
        return Model(domains, tuple(values))

    def _entries(self, key: tuple[str, ...], symbol: _Symbol) -> list[tuple[str, str]]:
        """Values of a function with a Nat argument at the Nat values of the model's
        constants and at the points listed in Z3's interpretation; the function's
        other values are left out."""
        constants = sorted(
            {
                self.apply(k, ())
                for k, s in self.encoder.symbols.items()
                if not s.args and s.result is not None and s.result.name == _NAT
            }
        )
        choices = [
            constants if s.name == _NAT else range(len(self.universes[s.name])) for s in symbol.args
        ]
        points: list[tuple[Any, ...]] = list(itertools.islice(itertools.product(*choices), 64))
        interpretation = self.model[symbol.decl]
        if interpretation is not None and hasattr(interpretation, "as_list"):
            for entry in interpretation.as_list()[:-1]:
                try:
                    point = tuple(
                        self._to_python(a, s) for a, s in zip(entry[:-1], symbol.args, strict=True)
                    )
                except (_NotEvaluable, AttributeError):
                    continue
                if all(v >= 0 for v, s in zip(point, symbol.args, strict=True) if s.name == _NAT):
                    points.append(point)
        result: list[tuple[str, str]] = []
        for point in dict.fromkeys(points):
            shown = ", ".join(self._label(v, s) for v, s in zip(point, symbol.args, strict=True))
            value = self._label(self.apply(key, point), symbol.result)
            result.append((f"{symbol.display}({shown})", value))
        return result
