"""Proof context: goal tactics, forward rules and derivation building (language-spec §6–7).

Tactics build a kernel derivation tree (kernel-spec §5) whose open positions
are `_Goal` objects. When every goal is closed, `finish()` replaces each goal
by its solution and returns plain JSON for the kernel.
"""

from collections.abc import Callable, Iterator, Mapping
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any

from axiomweave.core.expressions import Falsehood, Prop, is_local_name
from axiomweave.errors import AxwTypeError, ScopeError, TacticError

Context = tuple[tuple[str, Prop], ...]


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

    def __str__(self) -> str:
        lines = [f"  {name} : {prop}" for name, prop in self.context]
        lines.append(f"  ⊢ {self.target}")
        return "\n".join(lines)


@dataclass(frozen=True)
class Fact:
    """A proposition derived in a context; `prop` is what it proves."""

    prop: Prop
    _derivation: Any = field(repr=False, compare=False)
    _scope: frozenset[str] = field(repr=False, compare=False)


class _Goal:
    __slots__ = ("context", "solution", "target")

    def __init__(self, context: Context, target: Prop) -> None:
        self.context = context
        self.target = target
        self.solution: Any = None

    @property
    def names(self) -> frozenset[str]:
        return frozenset(name for name, _ in self.context)

    def extended(self, name: str, prop: Prop, target: Prop) -> "_Goal":
        return _Goal((*self.context, (name, prop)), target)


def _realize(node: Any) -> Any:
    if isinstance(node, _Goal):
        return _realize(node.solution)
    if isinstance(node, Prop):
        return node.to_json()
    if isinstance(node, dict):
        return {key: _realize(value) for key, value in node.items()}
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
        self._counter = 0

    # --- state ------------------------------------------------------------------

    @property
    def goals(self) -> tuple[GoalView, ...]:
        """Open goals, the current goal first."""
        return tuple(
            GoalView(goal.context, goal.target) for goals in reversed(self._stack) for goal in goals
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
        result: dict[str, Any] = _realize(self._root)
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
    def _expect(prop: Prop, tag: str, what: str) -> tuple[Prop, Prop]:
        if prop.tag != tag:
            symbol = {"and": "∧", "or": "∨", "imp": "→"}[tag]
            raise TacticError(f"{what} needs a '{symbol}' proposition, got {prop}")
        return prop.left, prop.right

    def _in_scope(self, fact: Fact, goal: _Goal) -> None:
        if not fact._scope <= goal.names:
            missing = ", ".join(sorted(fact._scope - goal.names))
            raise ScopeError(f"fact {fact.prop} depends on hypotheses not in this goal: {missing}")

    @staticmethod
    def _join(*facts: Fact) -> frozenset[str]:
        scope: frozenset[str] = frozenset()
        for fact in facts:
            if fact._scope <= scope:
                continue
            if scope <= fact._scope:
                scope = fact._scope
                continue
            raise ScopeError("facts come from unrelated goals and cannot be combined")
        return scope

    # --- goal tactics (language-spec §6.3) --------------------------------------

    def intro(self, name: str | None = None) -> Fact:
        goal = self._current()
        a, b = self._expect(goal.target, "imp", "intro")
        h = self._fresh(name)
        sub = goal.extended(h, a, b)
        goal.solution = {"rule": "imp_i", "name": h, "hyp": a, "body": sub}
        self._replace([sub])
        return Fact(a, _hyp(h), sub.names)

    def split(self) -> None:
        goal = self._current()
        a, b = self._expect(goal.target, "and", "split")
        left, right = _Goal(goal.context, a), _Goal(goal.context, b)
        goal.solution = {"rule": "and_i", "left": left, "right": right}
        self._replace([left, right])

    def left(self) -> None:
        goal = self._current()
        a, b = self._expect(goal.target, "or", "left")
        sub = _Goal(goal.context, a)
        goal.solution = {"rule": "or_i1", "of": sub, "right": b}
        self._replace([sub])

    def right(self) -> None:
        goal = self._current()
        a, b = self._expect(goal.target, "or", "right")
        sub = _Goal(goal.context, b)
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
        sub = _Goal(goal.context, Falsehood)
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
        subgoals = [_Goal(goal.context, premise) for premise in premises]
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
        h = self._fresh(name)
        lemma = _Goal(goal.context, a)
        rest = goal.extended(h, a, goal.target)
        goal.solution = {
            "rule": "imp_e",
            "fn": {"rule": "imp_i", "name": h, "hyp": a, "body": rest},
            "arg": lemma,
        }
        self._replace([lemma, rest])
        return Fact(a, _hyp(h), rest.names)

    @contextmanager
    def focus(self) -> Iterator[None]:
        """Work on the current goal only; it must be closed when the block ends."""
        goal = self._current()
        self._stack[-1].pop(0)
        self._stack.append([goal])
        yield
        if self._stack.pop():
            raise TacticError("focused goal is not closed at the end of the block")

    # --- forward rules (language-spec §6.4) -------------------------------------

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
        return Fact(f.prop | b, {"rule": "or_i1", "of": f._derivation, "right": b}, f._scope)

    def or_inr(self, left: Prop, f: Fact) -> Fact:
        a, f = self._prop(left), self._fact(f)
        return Fact(a | f.prop, {"rule": "or_i2", "left": a, "of": f._derivation}, f._scope)

    def absurd(self, f: Fact, goal: Prop) -> Fact:
        f, a = self._fact(f), self._prop(goal)
        if f.prop != Falsehood:
            raise TacticError(f"absurd needs a proof of ⊥, got {f.prop}")
        return Fact(a, {"rule": "false_e", "of": f._derivation, "goal": a}, f._scope)

    def thm(self, decl: object, subst: Mapping[Prop, Prop] | None = None) -> Fact:
        ref = self._resolve(decl)
        atoms = ref.statement.atoms()
        mapping: dict[str, Prop] = {}
        for key, value in (subst or {}).items():
            if not isinstance(key, Prop) or not key.is_atom:
                raise TacticError(f"substitution keys must be atoms, got {key!r}")
            if key.name not in atoms:
                raise TacticError(f"atom {key.name} does not occur in {ref.name}")
            mapping[key.name] = self._prop(value)
        derivation = {
            "rule": "thm" if ref.kind == "theorem" else "ax",
            "name": ref.name,
            "hash": ref.hash,
            "subst": {name: mapping[name] for name in sorted(mapping)},
        }
        return Fact(ref.statement.substitute(mapping), derivation, frozenset())
