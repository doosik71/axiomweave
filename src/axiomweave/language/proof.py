"""Proof context: goal tactics, forward rules and derivation building
(language-spec §6–7, §12.5–12.6, §13.3–13.4, §14.4).

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
    Eq,
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
# Declarations a proof may refer to, in environment order, with their axioms.
Candidates = Callable[[], Sequence[tuple[object, frozenset[str]]]]


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

    def __init__(
        self, statement: Prop, resolve: Resolver, candidates: Candidates | None = None
    ) -> None:
        self._root = _Goal((), statement)
        self._stack: list[list[_Goal]] = [[self._root]]
        self._resolve = resolve
        self._candidates = candidates
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

    # --- equality (language-spec §13.3–13.4) --------------------------------------

    @staticmethod
    def _sides(prop: Prop, what: str) -> tuple[Term, Term]:
        if prop.tag != "eq":
            raise TacticError(f"{what} needs an equality, got {prop}")
        return prop.sides

    def _motive_var(self, sort: Any, *things: Prop | Term) -> Term:
        """A variable for an `eq_e` motive whose name occurs in none of `things`."""
        taken = set(self._used_vars)
        for thing in things:
            taken |= thing.var_names() if isinstance(thing, Prop) else set(thing._names or ())
        return Var(_fresh_name("z", taken), sort)

    def _symm_derivation(self, derivation: Any, t: Term, u: Term) -> dict[str, Any]:
        """u = t from a derivation of t = u (logic-spec §13.5)."""
        z = self._motive_var(t.sort, t, u)
        return {
            "rule": "eq_e",
            "eq": derivation,
            "motive": _Binder(z, Eq(z, t)),
            "of": {"rule": "eq_refl", "term": t},
        }

    def rfl(self) -> None:
        """Close a goal `t = t`."""
        goal = self._current()
        t, u = self._sides(goal.target, "rfl")
        if t != u:
            raise TacticError(f"rfl: {t} and {u} are different terms")
        goal.solution = {"rule": "eq_refl", "term": t}
        self._replace([])

    def rewrite(self, fact: Fact, reverse: bool = False) -> None:
        """With `fact : t = u`, replace the free occurrences of t in the goal by u
        (or of u by t when `reverse` is true)."""
        goal = self._current()
        fact = self._fact(fact)
        self._in_scope(fact, goal)
        t, u = self._sides(fact.prop, "rewrite")
        source, target_term = (u, t) if reverse else (t, u)
        if not goal.target.contains(source):
            raise TacticError(f"rewrite: {source} does not occur in {goal.target}")
        z = self._motive_var(t.sort, goal.target, t, u)
        motive = goal.target.abstract(source, z)
        sub = goal.with_target(motive.subst_var(z, target_term))
        equation = fact._derivation if reverse else self._symm_derivation(fact._derivation, t, u)
        goal.solution = {"rule": "eq_e", "eq": equation, "motive": _Binder(z, motive), "of": sub}
        self._replace([sub])

    def refl(self, term: Term) -> Fact:
        """t = t."""
        t = self._term(term)
        return Fact(Eq(t, t), {"rule": "eq_refl", "term": t}, self._scope_of(t.free_vars()))

    def symm(self, f: Fact) -> Fact:
        """From t = u derive u = t."""
        f = self._fact(f)
        t, u = self._sides(f.prop, "symm")
        return Fact(Eq(u, t), self._symm_derivation(f._derivation, t, u), f._scope)

    def trans(self, f: Fact, g: Fact) -> Fact:
        """From t = u and u = v derive t = v."""
        f, g = self._fact(f), self._fact(g)
        t, u = self._sides(f.prop, "trans")
        u2, v = self._sides(g.prop, "trans")
        if u != u2:
            raise TacticError(f"trans: {f.prop} and {g.prop} do not share the middle term")
        z = self._motive_var(t.sort, t, v)
        derivation = {
            "rule": "eq_e",
            "eq": g._derivation,
            "motive": _Binder(z, Eq(t, z)),
            "of": f._derivation,
        }
        return Fact(Eq(t, v), derivation, self._join(f, g))

    def congr(self, f: Fact, context: tuple[Term, Term]) -> Fact:
        """From t = u and (x, s) derive s[t/x] = s[u/x]."""
        f = self._fact(f)
        t, u = self._sides(f.prop, "congr")
        if not (isinstance(context, tuple) and len(context) == 2):
            raise TacticError("congr expects an (x, s) pair of a variable and a term")
        x, s = context
        if not (isinstance(x, Term) and x.is_var) or not isinstance(s, Term):
            raise TacticError("congr expects an (x, s) pair of a variable and a term")
        if x.sort != t.sort:
            raise TacticError(f"congr: {x} has sort {x.sort}, the equation has sort {t.sort}")
        left = s._replace({x.key: t})
        z = self._motive_var(t.sort, s, t, u, left)
        derivation = {
            "rule": "eq_e",
            "eq": f._derivation,
            "motive": _Binder(z, Eq(left, s._replace({x.key: z}))),
            "of": {"rule": "eq_refl", "term": left},
        }
        free = frozenset(k for k in s.free_vars() if k != x.key)
        scope = self._join_scopes(f._scope, self._scope_of(free))
        return Fact(Eq(left, s._replace({x.key: u})), derivation, scope)

    def subst(self, f: Fact, g: Fact, motive: tuple[Term, Prop] | None = None) -> Fact:
        """From t = u and g, replace t by u: in every free occurrence, or where the
        variable of `motive = (x, A)` stands (then g must prove A[t/x])."""
        f, g = self._fact(f), self._fact(g)
        t, u = self._sides(f.prop, "subst")
        if motive is None:
            if not g.prop.contains(t):
                raise TacticError(f"subst: {t} does not occur in {g.prop}")
            var = self._motive_var(t.sort, g.prop, t, u)
            body = g.prop.abstract(t, var)
        else:
            if not (isinstance(motive, tuple) and len(motive) == 2):
                raise TacticError("subst motive must be an (x, A) pair")
            var, body = motive
            if not (isinstance(var, Term) and var.is_var) or not isinstance(body, Prop):
                raise TacticError("subst motive must be an (x, A) pair")
            if var.sort != t.sort:
                raise TacticError(f"subst: {var} has sort {var.sort}, expected {t.sort}")
            if g.prop != body.subst_var(var, t):
                raise TacticError(f"subst: {g.prop} is not the motive at {t}")
        derivation = {
            "rule": "eq_e",
            "eq": f._derivation,
            "motive": _Binder(var, body),
            "of": g._derivation,
        }
        free = frozenset(k for k in body.free_vars() if k != var.key)
        scope = self._join_scopes(self._join(f, g), self._scope_of(free))
        return Fact(body.subst_var(var, u), derivation, scope)

    # --- natural numbers (language-spec §14.4) ----------------------------------------

    def induction(self) -> None:
        """Split `∀n:Nat. A` into `A[0/n]` and `∀n:Nat. A → A[S(n)/n]` using the
        `arith.induction` axiom schema (no new kernel rule)."""
        goal = self._current()
        target = goal.target
        self._expect_quantifier(target, "forall", "induction")
        sort = target.var.sort
        if sort.name != "arith.Nat":
            raise TacticError(f"induction needs a goal ∀n:Nat, got {target}")
        # Look the axiom up by its canonical name, so that any loaded copy of the
        # `arith` library in this theory's environment is used.
        motive = Prop.symbol("P", sort)
        schema = self._instance(
            self._resolve("arith.induction"), {motive: ((target.var,), target.body)}
        )
        self.apply(schema)

    # --- propositional automation (ai-spec §3.2) -----------------------------------------

    def auto(self, using: Sequence[Fact] = (), limit: int | None = None) -> None:
        """Close the current goal by intuitionistic propositional reasoning from the
        context hypotheses and `using`; other formulas are treated as atoms."""
        from axiomweave.ai.propositional import DEFAULT_LIMIT, auto

        if limit is None:
            limit = DEFAULT_LIMIT
        if type(limit) is not int or limit <= 0:
            raise AxwTypeError(f"auto: limit must be a positive int, got {limit!r}")
        goal = self._current()
        facts: dict[Prop, Fact] = {}
        for name, prop in goal.context:
            facts.setdefault(prop, Fact(prop, _hyp(name), goal.names))
        for item in using:
            fact = self._fact(item)
            self._in_scope(fact, goal)
            facts.setdefault(fact.prop, fact)
        auto(self, facts, limit)

    # --- theorem search (ai-spec §4.4) -------------------------------------------------

    def search(self, limit: int | None = None) -> tuple[Any, ...]:
        """Theorems and axioms of the environment whose conclusion fits the current goal,
        best first. The proof state is not changed."""
        from axiomweave.ai.search import DEFAULT_LIMIT, search

        if limit is None:
            limit = DEFAULT_LIMIT
        if type(limit) is not int or limit <= 0:
            raise AxwTypeError(f"search: limit must be a positive int, got {limit!r}")
        self._current()
        candidates = self._candidates() if self._candidates is not None else ()
        return search(self, candidates, limit)

    # --- semiring identities (interop-spec §5.3) ----------------------------------------

    def ring(self) -> None:
        """Close a goal `t = u` over Nat that is a polynomial identity."""
        goal = self._current()
        t, u = self._sides(goal.target, "ring")
        self.exact(self._ring(t, u))

    def ring_eq(self, t: Term, u: Term) -> Fact:
        """t = u for a polynomial identity over Nat."""
        t, u = self._term(t), self._term(u)
        self._check_free(t.free_vars() | u.free_vars(), self._current(), "ring_eq")
        return self._ring(t, u)

    def _ring(self, t: Term, u: Term) -> Fact:
        from axiomweave.backends.symbolic import check_identity
        from axiomweave.language.ring import NAT, prove_equal

        for side in (t, u):
            if side.sort.name != NAT:
                raise TacticError(f"ring works on terms of sort Nat, got {side} : {side.sort}")
        check = check_identity(t, u)
        if not check.identity:
            raise TacticError(f"ring: not a polynomial identity: lhs - rhs = {check.difference}")
        return prove_equal(self, t, u)

    # --- counterexample search (interop-spec §4.2) -------------------------------------

    def counterexample(self, using: Sequence[object] = (), timeout_ms: int = 5000) -> Any:
        """Search a classical model where the current goal's hypotheses and `using`
        hold and its target fails. Advisory only: goals and derivations are unchanged."""
        from axiomweave.backends.smt import counterexample

        goal = self._current()
        premises: list[Prop] = []
        for item in using:
            if isinstance(item, Fact):
                self._in_scope(item, goal)
                premises.append(item.prop)
            else:
                prop = self._prop(item)
                self._check_free(prop.free_vars(), goal, "counterexample premise")
                premises.append(prop)
        view = GoalView(goal.context, goal.target, goal.variables)
        return counterexample(view, premises, timeout_ms)

    def thm(self, decl: object, subst: Mapping[object, object] | None = None) -> Fact:
        if isinstance(decl, str):
            raise AxwTypeError(f"thm expects a Theorem or Axiom handle, got {decl!r}")
        return self._instance(self._resolve(decl), subst)

    def _instance(self, ref: DeclRef, subst: Mapping[object, object] | None) -> Fact:
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
