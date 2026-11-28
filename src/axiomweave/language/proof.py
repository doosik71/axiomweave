"""Proof context: goal tactics, forward rules and derivation building (language-spec §6–7, §12.5–12.6).

Tactics build a kernel derivation tree (kernel-spec §5, §13.5) whose open
positions are `_Goal` objects. Propositions and terms stay named while the
proof runs; `finish()` replaces each goal by its solution and encodes them with
de Bruijn indices relative to the variables in scope at each node.
"""

from collections.abc import Callable, Iterator, Mapping, Sequence
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any

from axiomweave.core.expressions import (
    Falsehood,
    PredicateSymbol,
    Prop,
    SchemaValue,
    Term,
    Var,
    VarKey,
    _fresh_name,
    is_local_name,
)
from axiomweave.errors import AxwTypeError, ScopeError, TacticError

Context = tuple[tuple[str, Prop], ...]
Variables = tuple[Term, ...]
Scope = frozenset[str]  # "h:<hypothesis>" and "v:<variable>" entries


@dataclass(frozen=True)
class DeclRef:
    """What a proof may know about an earlier declaration."""

    kind: str  # "axiom" or "theorem"
    name: str
    hash: str
    statement: Prop


Resolver = Callable[[object], DeclRef]


@dataclass(frozen=True)
class GoalView:
    """Read-only view of an open goal."""

    context: Context
    target: Prop
    variables: Variables = ()

    def __str__(self) -> str:
        lines = [f"  {v.name} : {v.sort}" for v in self.variables]
        lines += [f"  {name} : {prop}" for name, prop in self.context]
        lines.append(f"  ⊢ {self.target}")
        return "\n".join(lines)


@dataclass(frozen=True)
class Fact:
    """A proposition derived in a context; `prop` is what it proves."""

    prop: Prop
    _derivation: Any = field(repr=False, compare=False)
    _scope: Scope = field(repr=False, compare=False)


class _Goal:
    __slots__ = ("context", "solution", "target", "variables")

    def __init__(self, context: Context, target: Prop, variables: Variables = ()) -> None:
        self.context = context
        self.target = target
        self.variables = variables
        self.solution: Any = None

    @property
    def names(self) -> Scope:
        return frozenset(f"h:{name}" for name, _ in self.context) | frozenset(
            f"v:{v.name}" for v in self.variables
        )

    def with_target(self, target: Prop) -> "_Goal":
        return _Goal(self.context, target, self.variables)

    def extended(self, name: str, prop: Prop, target: Prop) -> "_Goal":
        return _Goal((*self.context, (name, prop)), target, self.variables)

    def with_var(self, var: Term, target: Prop) -> "_Goal":
        return _Goal(self.context, target, (*self.variables, var))


class _Binder:
    """A proposition under one extra bound variable (the `prop` of `ex_i`)."""

    __slots__ = ("prop", "var")

    def __init__(self, var: Term, prop: Prop) -> None:
        self.var = var
        self.prop = prop


class _Subst:
    """A schematic substitution, encoded relative to the scope where it is used."""

    __slots__ = ("values",)

    def __init__(self, values: dict[str, SchemaValue]) -> None:
        self.values = values


def _realize(node: Any, scope: Variables) -> Any:
    if isinstance(node, _Goal):
        return _realize(node.solution, scope)
    if isinstance(node, Prop | Term):
        return node.to_json(scope)
    if isinstance(node, _Binder):
        return node.prop.to_json((*scope, node.var))
    if isinstance(node, _Subst):
        encoded: dict[str, Any] = {}
        for name in sorted(node.values):
            params, body = node.values[name]
            if params:
                encoded[name] = {
                    "params": [p.sort.name for p in params],
                    "body": body.to_json((*scope, *params)),
                }
            else:
                encoded[name] = body.to_json(scope)
        return encoded
    if isinstance(node, dict):
        inner = (*scope, node["_var"]) if "_var" in node else scope
        result: dict[str, Any] = {}
        for key, value in node.items():
            if key == "_var":
                continue
            result[key] = _realize(value, inner if key == "body" else scope)
        return result
    return node


def _hyp(name: str) -> dict[str, Any]:
    return {"rule": "hyp", "name": name}


class ProofContext:
    """The `ctx` argument of a proof function."""

    def __init__(self, statement: Prop, resolve: Resolver) -> None:
        self._root = _Goal((), statement)
        self._stack: list[list[_Goal]] = [[self._root]]
        self._resolve = resolve
        self._used_names: set[str] = set()
        self._used_vars: set[str] = set()
        # variable name -> (sort name, scope where it was introduced)
        self._var_scopes: dict[str, tuple[str, Scope]] = {}
        self._counter = 0

    # --- state ------------------------------------------------------------------

    @property
    def goals(self) -> tuple[GoalView, ...]:
        """Open goals, the current goal first."""
        return tuple(
            GoalView(goal.context, goal.target, goal.variables)
            for goals in reversed(self._stack)
            for goal in goals
        )

    def __str__(self) -> str:
        goals = self.goals
        if not goals:
            return "no goals"
        return "\n".join(f"goal {i}/{len(goals)}\n{goal}" for i, goal in enumerate(goals, start=1))

    def finish(self) -> dict[str, Any] | None:
        """The derivation JSON if every goal is closed, otherwise None."""
        if any(self._stack):
            return None
        result: dict[str, Any] = _realize(self._root, ())
        return result

    # --- helpers ----------------------------------------------------------------

    def _current(self) -> _Goal:
        goals = self._stack[-1]
        if not goals:
            raise TacticError("no goals left")
        return goals[0]

    def _replace(self, new_goals: list[_Goal]) -> None:
        self._stack[-1][0:1] = new_goals

    def _fresh(self, name: str | None) -> str:
        if name is None:
            while True:
                self._counter += 1
                name = f"h{self._counter}"
                if name not in self._used_names:
                    break
        elif not is_local_name(name):
            raise TacticError(f"invalid hypothesis name {name!r}")
        elif name in self._used_names:
            raise TacticError(f"hypothesis name {name!r} is already used in this proof")
        self._used_names.add(name)
        return name

    def _fresh_var(self, name: str | None, default: Term, target: Prop, goal: _Goal) -> str:
        """A new variable name: `name`, or the binder name made unique (language-spec §12.5).

        Besides names already used in this proof, the default avoids names that the
        goal uses with a different sort, since one name may not have two sorts."""
        if name is not None:
            if not is_local_name(name):
                raise TacticError(f"invalid variable name {name!r}")
            if name in self._used_vars:
                raise TacticError(f"variable name {name!r} is already used in this proof")
            chosen = name
        else:
            taken = set(self._used_vars)
            for prop in (target, *(p for _, p in goal.context)):
                taken |= {n for n, s in prop.var_sorts().items() if s != default.sort}
            base = default.name
            chosen = base if base not in taken else _fresh_name(base, taken)
        self._used_vars.add(chosen)
        return chosen

    @staticmethod
    def _fact(value: object) -> Fact:
        if not isinstance(value, Fact):
            raise AxwTypeError(f"expected a Fact, got {type(value).__name__}")
        return value

    @staticmethod
    def _prop(value: object) -> Prop:
        if not isinstance(value, Prop):
            raise AxwTypeError(f"expected a Prop, got {type(value).__name__}")
        return value

    @staticmethod
    def _term(value: object) -> Term:
        if not isinstance(value, Term):
            raise AxwTypeError(f"expected a Term, got {type(value).__name__}")
        return value

    @staticmethod
    def _expect(prop: Prop, tag: str, what: str) -> tuple[Prop, Prop]:
        if prop.tag != tag:
            symbol = {"and": "∧", "or": "∨", "imp": "→"}[tag]
            raise TacticError(f"{what} needs a '{symbol}' proposition, got {prop}")
        return prop.left, prop.right

    @staticmethod
    def _expect_quantifier(prop: Prop, tag: str, what: str) -> None:
        if prop.tag != tag:
            symbol = "∀" if tag == "forall" else "∃"
            raise TacticError(f"{what} needs a '{symbol}' proposition, got {prop}")

    def _in_scope(self, fact: Fact, goal: _Goal) -> None:
        if not fact._scope <= goal.names:
            missing = ", ".join(sorted(n[2:] for n in fact._scope - goal.names))
            raise ScopeError(f"fact {fact.prop} depends on names not in this goal: {missing}")

    def _scope_of(self, free: frozenset[VarKey]) -> Scope:
        """The scope a proposition or term with these free variables depends on."""
        scope: Scope = frozenset()
        for name, sort in sorted(free):
            introduced = self._var_scopes.get(name)
            if introduced is None or introduced[0] != sort:
                raise ScopeError(f"variable {name} was not introduced in this proof")
            scope = self._join_scopes(scope, introduced[1])
        return scope

    def _check_free(self, free: frozenset[VarKey], goal: _Goal, what: str) -> None:
        available = {v.key for v in goal.variables}
        missing = sorted(name for name, sort in free if (name, sort) not in available)
        if missing:
            raise ScopeError(f"{what} uses variables not in this goal: {', '.join(missing)}")

    @staticmethod
    def _join_scopes(*scopes: Scope) -> Scope:
        result: Scope = frozenset()
        for scope in scopes:
            if scope <= result:
                continue
            if result <= scope:
                result = scope
                continue
            raise ScopeError("facts come from unrelated goals and cannot be combined")
        return result

    def _join(self, *facts: Fact) -> Scope:
        return self._join_scopes(*(f._scope for f in facts))

    # --- goal tactics (language-spec §6.3, §12.5) -------------------------------

    def intro(self, name: str | None = None) -> Any:
        """Introduce the premise of `A → B` (returns a Fact) or the variable of `∀x. A`
        (returns its Term)."""
        goal = self._current()
        if goal.target.tag == "forall":
            target = goal.target
            var = Var(self._fresh_var(name, target.var, target, goal), target.var.sort)
            sub = goal.with_var(var, target.open(var))
            goal.solution = {"rule": "all_i", "sort": var.sort.name, "_var": var, "body": sub}
            self._var_scopes[var.name] = (var.sort.name, sub.names)
            self._replace([sub])
            return var
        a, b = self._expect(goal.target, "imp", "intro")
        h = self._fresh(name)
        sub = goal.extended(h, a, b)
        goal.solution = {"rule": "imp_i", "name": h, "hyp": a, "body": sub}
        self._replace([sub])
        return Fact(a, _hyp(h), sub.names)

    def split(self) -> None:
        goal = self._current()
        a, b = self._expect(goal.target, "and", "split")
        left, right = goal.with_target(a), goal.with_target(b)
        goal.solution = {"rule": "and_i", "left": left, "right": right}
        self._replace([left, right])

    def left(self) -> None:
        goal = self._current()
        a, b = self._expect(goal.target, "or", "left")
        sub = goal.with_target(a)
        goal.solution = {"rule": "or_i1", "of": sub, "right": b}
        self._replace([sub])

    def right(self) -> None:
        goal = self._current()
        a, b = self._expect(goal.target, "or", "right")
        sub = goal.with_target(b)
        goal.solution = {"rule": "or_i2", "left": a, "of": sub}
        self._replace([sub])

    def cases(
        self, fact: Fact, names: tuple[str | None, str | None] | None = None
    ) -> tuple[Fact, Fact]:
        goal = self._current()
        fact = self._fact(fact)
        self._in_scope(fact, goal)
        a, b = self._expect(fact.prop, "or", "cases")
        first, second = names if names is not None else (None, None)
        h1, h2 = self._fresh(first), self._fresh(second)
        left = goal.extended(h1, a, goal.target)
        right = goal.extended(h2, b, goal.target)
        goal.solution = {
            "rule": "or_e",
            "of": fact._derivation,
            "left_name": h1,
            "left": left,
            "right_name": h2,
            "right": right,
        }
        self._replace([left, right])
        return Fact(a, _hyp(h1), left.names), Fact(b, _hyp(h2), right.names)

    def exfalso(self) -> None:
        goal = self._current()
        sub = goal.with_target(Falsehood)
        goal.solution = {"rule": "false_e", "of": sub, "goal": goal.target}
        self._replace([sub])

    def apply(self, fact: Fact) -> None:
        goal = self._current()
        fact = self._fact(fact)
        self._in_scope(fact, goal)
        premises: list[Prop] = []
        prop = fact.prop
        while prop.tag == "imp":
            premises.append(prop.left)
            prop = prop.right
            if prop == goal.target:
                break
        else:
            raise TacticError(f"apply: {fact.prop} does not conclude {goal.target}")
        subgoals = [goal.with_target(premise) for premise in premises]
        derivation: Any = fact._derivation
        for sub in subgoals:
            derivation = {"rule": "imp_e", "fn": derivation, "arg": sub}
        goal.solution = derivation
        self._replace(subgoals)

    def exact(self, fact: Fact) -> None:
        goal = self._current()
        fact = self._fact(fact)
        self._in_scope(fact, goal)
        if fact.prop != goal.target:
            raise TacticError(f"exact: fact proves {fact.prop}, goal is {goal.target}")
        goal.solution = fact._derivation
        self._replace([])

    def assumption(self) -> None:
        goal = self._current()
        for name, prop in reversed(goal.context):
            if prop == goal.target:
                goal.solution = _hyp(name)
                self._replace([])
                return
        raise TacticError(f"assumption: no hypothesis proves {goal.target}")

    def have(self, prop: Prop, name: str | None = None) -> Fact:
        goal = self._current()
        a = self._prop(prop)
        self._check_free(a.free_vars(), goal, "have")
        h = self._fresh(name)
        lemma = goal.with_target(a)
        rest = goal.extended(h, a, goal.target)
        goal.solution = {
            "rule": "imp_e",
            "fn": {"rule": "imp_i", "name": h, "hyp": a, "body": rest},
            "arg": lemma,
        }
        self._replace([lemma, rest])
        return Fact(a, _hyp(h), rest.names)

    def exists(self, term: Term) -> None:
        """Prove `∃x:S. A` by giving a witness: the goal becomes A[term/x]."""
        goal = self._current()
        target = goal.target
        self._expect_quantifier(target, "exists", "exists")
        t = self._term(term)
        if t.sort != target.var.sort:
            raise TacticError(f"exists: witness {t} has sort {t.sort}, expected {target.var.sort}")
        self._check_free(t.free_vars(), goal, "exists")
        sub = goal.with_target(target.body.subst_var(target.var, t))
        goal.solution = {
            "rule": "ex_i",
            "prop": _Binder(target.var, target.body),
            "witness": t,
            "of": sub,
        }
        self._replace([sub])

    def obtain(
        self, fact: Fact, names: tuple[str | None, str | None] | None = None
    ) -> tuple[Term, Fact]:
        """Use `∃x:S. A`: add a variable y and hypothesis A[y/x] to the current goal."""
        goal = self._current()
        fact = self._fact(fact)
        self._in_scope(fact, goal)
        prop = fact.prop
        self._expect_quantifier(prop, "exists", "obtain")
        var_name, hyp_name = names if names is not None else (None, None)
        var = Var(self._fresh_var(var_name, prop.var, prop, goal), prop.var.sort)
        h = self._fresh(hyp_name)
        opened = prop.open(var)
        sub = goal.with_var(var, goal.target).extended(h, opened, goal.target)
        goal.solution = {
            "rule": "ex_e",
            "of": fact._derivation,
            "name": h,
            "_var": var,
            "body": sub,
        }
        self._var_scopes[var.name] = (var.sort.name, sub.names - {f"h:{h}"})
        self._replace([sub])
        return var, Fact(opened, _hyp(h), sub.names)

    @contextmanager
    def focus(self) -> Iterator[None]:
        """Work on the current goal only; it must be closed when the block ends."""
        goal = self._current()
        self._stack[-1].pop(0)
        self._stack.append([goal])
        yield
        if self._stack.pop():
            raise TacticError("focused goal is not closed at the end of the block")

    # --- forward rules (language-spec §6.4, §12.5) -------------------------------

    def mp(self, f: Fact, g: Fact) -> Fact:
        f, g = self._fact(f), self._fact(g)
        a, b = self._expect(f.prop, "imp", "mp")
        if g.prop != a:
            raise TacticError(f"mp: argument proves {g.prop}, expected {a}")
        derivation = {"rule": "imp_e", "fn": f._derivation, "arg": g._derivation}
        return Fact(b, derivation, self._join(f, g))

    def and_intro(self, f: Fact, g: Fact) -> Fact:
        f, g = self._fact(f), self._fact(g)
        derivation = {"rule": "and_i", "left": f._derivation, "right": g._derivation}
        return Fact(f.prop & g.prop, derivation, self._join(f, g))

    def and_left(self, f: Fact) -> Fact:
        f = self._fact(f)
        a, _ = self._expect(f.prop, "and", "and_left")
        return Fact(a, {"rule": "and_e1", "of": f._derivation}, f._scope)

    def and_right(self, f: Fact) -> Fact:
        f = self._fact(f)
        _, b = self._expect(f.prop, "and", "and_right")
        return Fact(b, {"rule": "and_e2", "of": f._derivation}, f._scope)

    def or_inl(self, f: Fact, right: Prop) -> Fact:
        f, b = self._fact(f), self._prop(right)
        scope = self._join_scopes(f._scope, self._scope_of(b.free_vars()))
        return Fact(f.prop | b, {"rule": "or_i1", "of": f._derivation, "right": b}, scope)

    def or_inr(self, left: Prop, f: Fact) -> Fact:
        a, f = self._prop(left), self._fact(f)
        scope = self._join_scopes(f._scope, self._scope_of(a.free_vars()))
        return Fact(a | f.prop, {"rule": "or_i2", "left": a, "of": f._derivation}, scope)

    def absurd(self, f: Fact, goal: Prop) -> Fact:
        f, a = self._fact(f), self._prop(goal)
        if f.prop != Falsehood:
            raise TacticError(f"absurd needs a proof of ⊥, got {f.prop}")
        scope = self._join_scopes(f._scope, self._scope_of(a.free_vars()))
        return Fact(a, {"rule": "false_e", "of": f._derivation, "goal": a}, scope)

    def spec(self, f: Fact, *terms: Term) -> Fact:
        """From `∀x₁ … xₙ. A` derive A[t₁/x₁, …, tₙ/xₙ]."""
        f = self._fact(f)
        if not terms:
            raise TacticError("spec needs at least one term")
        prop, derivation, scope = f.prop, f._derivation, f._scope
        for term in terms:
            t = self._term(term)
            self._expect_quantifier(prop, "forall", "spec")
            if t.sort != prop.var.sort:
                raise TacticError(f"spec: {t} has sort {t.sort}, expected {prop.var.sort}")
            scope = self._join_scopes(scope, self._scope_of(t.free_vars()))
            prop = prop.body.subst_var(prop.var, t)
            derivation = {"rule": "all_e", "of": derivation, "term": t}
        return Fact(prop, derivation, scope)

    def thm(self, decl: object, subst: Mapping[object, object] | None = None) -> Fact:
        ref = self._resolve(decl)
        signature = ref.statement.signature()
        values: dict[str, SchemaValue] = {}
        scope: Scope = frozenset()
        for key, value in (subst or {}).items():
            name, sorts = self._subst_key(key)
            if name not in signature:
                raise TacticError(f"{name} does not occur in {ref.name}")
            if signature[name] != sorts:
                raise TacticError(f"{name} has a different arity in {ref.name}")
            params, body = self._subst_value(name, sorts, value)
            param_keys = {p.key for p in params}
            free = frozenset(k for k in body.free_vars() if k not in param_keys)
            scope = self._join_scopes(scope, self._scope_of(free))
            values[name] = (params, body)
        derivation = {
            "rule": "thm" if ref.kind == "theorem" else "ax",
            "name": ref.name,
            "hash": ref.hash,
            "subst": _Subst(values),
        }
        return Fact(ref.statement.instantiate(values), derivation, scope)

    @staticmethod
    def _subst_key(key: object) -> tuple[str, tuple[Any, ...]]:
        if isinstance(key, Prop) and key.is_atom:
            return key.name, ()
        if isinstance(key, PredicateSymbol):
            return key.name, key.sorts
        raise TacticError(f"substitution keys must be atoms or predicate symbols, got {key!r}")

    def _subst_value(self, name: str, sorts: tuple[Any, ...], value: object) -> SchemaValue:
        if not sorts:
            return (), self._prop(value)
        if not (isinstance(value, tuple) and len(value) == 2):
            raise TacticError(f"the value for {name} must be a (variables, Prop) pair")
        params_obj, body = value
        params = tuple(params_obj) if isinstance(params_obj, Sequence) else (params_obj,)
        if len(params) != len(sorts) or any(
            not (isinstance(p, Term) and p.is_var) or p.sort != s
            for p, s in zip(params, sorts, strict=False)
        ):
            raise TacticError(f"the variables for {name} must have sorts {list(map(str, sorts))}")
        if len({p.name for p in params}) != len(params):
            raise TacticError(f"the variables for {name} must have distinct names")
        return params, self._prop(body)
