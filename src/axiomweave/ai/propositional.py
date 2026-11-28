"""Proof search for `ctx.auto()` (ai-spec §3, §6).

The search runs Dyckhoff's contraction-free sequent calculus G4ip. With
`first_order=False` it works on the propositional skeleton of the goal: ⊥, ∧, ∨
and → are connectives, every other proposition is an opaque atom, and the
search is a complete decision procedure (ai-spec §3). With `first_order=True`
it also uses quantifier rules over the terms of the sequent and an equality
closure (ai-spec §6); that search is bounded and incomplete.

A found proof tree is replayed with the public tactics of the proof context,
so the kernel checks an ordinary derivation.
"""

import itertools
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any

from axiomweave.core.expressions import Falsehood, Prop, Term, Var, VarKey, _fresh_name
from axiomweave.errors import TacticError

if TYPE_CHECKING:
    from axiomweave.language.proof import Fact, ProofContext

DEFAULT_LIMIT = 100_000
DEFAULT_DEPTH = 3
MAX_HINT_ATOMS = 16

_CONNECTIVES = ("false", "and", "or", "imp")
_QUANTIFIERS = ("forall", "exists")


def _is_atom(prop: Prop) -> bool:
    return prop.tag not in _CONNECTIVES


# --- proof trees ----------------------------------------------------------------------


@dataclass(frozen=True)
class Step:
    """A rule application. `principal` is the premise or goal it works on; `extra`
    is a further formula (the antecedent of L→atom) or term (an instance or
    witness); `var` is a new eigenvariable; `eq` is an equality proof."""

    rule: str
    principal: Prop
    subs: tuple["Step", ...] = ()
    extra: Any = None
    var: Term | None = None
    eq: "EqProof | None" = None


@dataclass(frozen=True)
class EqProof:
    """A proof of t = u: "refl", "hyp" (an equation of Γ, possibly flipped),
    "trans" of `parts`, or "congr" of argument proofs `parts`."""

    kind: str
    left: Term
    right: Term
    parts: tuple["EqProof", ...] = ()
    hyp: Prop | None = None
    flipped: bool = False


class _LimitReached(Exception):
    pass


# --- equality closure (ai-spec §6.4) --------------------------------------------------


def _prove_eq(left: Term, right: Term, equations: Sequence[Prop]) -> EqProof | None:
    if left == right:
        return EqProof("refl", left, right)
    path = _eq_path(left, right, equations)
    if path is not None:
        return path
    ln, rn = left._node, right._node
    if ln[0] == "app" and rn[0] == "app" and ln[1].name == rn[1].name and len(ln[2]) == len(rn[2]):
        parts = []
        for a, b in zip(ln[2], rn[2], strict=True):
            part = _prove_eq(a, b, equations)
            if part is None:
                return None
            parts.append(part)
        return EqProof("congr", left, right, tuple(parts))
    return None


def _eq_path(left: Term, right: Term, equations: Sequence[Prop]) -> EqProof | None:
    """A chain of hypothesis equations from left to right (breadth-first)."""
    previous: dict[Term, tuple[Term, EqProof] | None] = {left: None}
    frontier = [left]
    while frontier:
        following: list[Term] = []
        for node in frontier:
            for eq in equations:
                a, b = eq.sides
                for start, end, flipped in ((a, b, False), (b, a, True)):
                    if start == node and end not in previous:
                        previous[end] = (node, EqProof("hyp", start, end, hyp=eq, flipped=flipped))
                        following.append(end)
        if right in previous:
            steps: list[EqProof] = []
            current = right
            while previous[current] is not None:
                node, step = previous[current]  # type: ignore[misc]
                steps.append(step)
                current = node
            steps.reverse()
            if len(steps) == 1:
                return steps[0]
            return EqProof("trans", left, right, tuple(steps))
        frontier = following
    return None


# --- terms of a sequent ----------------------------------------------------------------


def _terms(props: Iterable[Prop]) -> list[Term]:
    """Terms occurring in the props whose variables are all free, first occurrence first."""
    found: list[Term] = []

    def add_term(t: Term, bound: frozenset[VarKey]) -> None:
        for arg in t._node[2] if t._node[0] == "app" else ():
            add_term(arg, bound)
        if not (t.free_vars() & bound) and t not in found:
            found.append(t)

    def go(p: Prop, bound: frozenset[VarKey]) -> None:
        tag = p.tag
        if tag in ("pvar", "pred"):
            for arg in p.args:
                add_term(arg, bound)
        elif tag == "eq":
            for side in p.sides:
                add_term(side, bound)
        elif tag in _QUANTIFIERS:
            go(p.body, bound | {p.var.key})
        elif tag in ("and", "or", "imp"):
            go(p.left, bound)
            go(p.right, bound)

    for p in props:
        go(p, frozenset())
    return found


def _has_first_order(prop: Prop) -> bool:
    tag = prop.tag
    if tag in (*_QUANTIFIERS, "eq"):
        return True
    if tag in ("and", "or", "imp"):
        return _has_first_order(prop.left) or _has_first_order(prop.right)
    return False


# --- search (ai-spec §3.3, §6.3) -----------------------------------------------------


Gamma = tuple[Prop, ...]


def _add(gamma: Gamma, *props: Prop) -> Gamma:
    result = list(gamma)
    for p in props:
        if p not in result:
            result.append(p)
    return tuple(result)


def _without(gamma: Gamma, prop: Prop) -> Gamma:
    return tuple(p for p in gamma if p != prop)


class Search:
    def __init__(
        self, limit: int, first_order: bool = False, taken_names: Iterable[str] = ()
    ) -> None:
        self.limit = limit
        self.first_order = first_order
        self.steps = 0
        self.taken = set(taken_names)
        self._failed: set[tuple[frozenset[Prop], Prop, int]] = set()

    def _tick(self) -> None:
        self.steps += 1
        if self.steps > self.limit:
            raise _LimitReached

    def _fresh(self, var: Term) -> Term:
        name = var.name if var.name not in self.taken else _fresh_name(var.name, self.taken)
        self.taken.add(name)
        return Var(name, var.sort)

    def prove(self, gamma: Gamma, goal: Prop, budget: int = 0) -> Step | None:
        key = (frozenset(gamma), goal, budget)
        if key in self._failed:
            return None
        result = self._prove(gamma, goal, budget)
        if result is None:
            self._failed.add(key)
        return result

    def _prove(self, gamma: Gamma, goal: Prop, budget: int) -> Step | None:
        self._tick()
        fo = self.first_order
        # Invertible rules, in the order of ai-spec §3.3 and §6.3.
        if goal in gamma:
            return Step("ax", goal)
        if Falsehood in gamma:
            return Step("bot", Falsehood)
        if fo and goal.tag == "eq":
            proof = _prove_eq(*goal.sides, [p for p in gamma if p.tag == "eq"])
            if proof is not None:
                return Step("eq", goal, eq=proof)
        if goal.tag == "imp":
            sub = self.prove(_add(gamma, goal.left), goal.right, budget)
            return None if sub is None else Step("imp_r", goal, (sub,))
        if goal.tag == "and":
            left = self.prove(gamma, goal.left, budget)
            if left is None:
                return None
            right = self.prove(gamma, goal.right, budget)
            return None if right is None else Step("and_r", goal, (left, right))
        for p in gamma:
            if p.tag == "and":
                sub = self.prove(_add(_without(gamma, p), p.left, p.right), goal, budget)
                return None if sub is None else Step("and_l", p, (sub,))
        for p in gamma:
            if p.tag == "or":
                rest = _without(gamma, p)
                left = self.prove(_add(rest, p.left), goal, budget)
                if left is None:
                    return None
                right = self.prove(_add(rest, p.right), goal, budget)
                return None if right is None else Step("or_l", p, (left, right))
        for p in gamma:
            if p.tag == "imp" and p.left in gamma:
                sub = self.prove(_add(_without(gamma, p), p.right), goal, budget)
                return None if sub is None else Step("imp_atom", p, (sub,), extra=p.left)
        for p in gamma:
            if p.tag != "imp":
                continue
            a, d = p.left, p.right
            rest = _without(gamma, p)
            if a.tag == "and":
                sub = self.prove(_add(rest, a.left >> (a.right >> d)), goal, budget)
                return None if sub is None else Step("imp_and", p, (sub,))
            if a.tag == "or":
                sub = self.prove(_add(rest, a.left >> d, a.right >> d), goal, budget)
                return None if sub is None else Step("imp_or", p, (sub,))
            if a.tag == "false":
                sub = self.prove(rest, goal, budget)
                return None if sub is None else Step("imp_bot", p, (sub,))
        if fo and goal.tag == "forall":
            c = self._fresh(goal.var)
            sub = self.prove(gamma, goal.open(c), budget)
            return None if sub is None else Step("forall_r", goal, (sub,), var=c)
        if fo:
            for p in gamma:
                if p.tag == "exists":
                    c = self._fresh(p.var)
                    sub = self.prove(_add(_without(gamma, p), p.open(c)), goal, budget)
                    return None if sub is None else Step("exists_l", p, (sub,), var=c)
        # Non-invertible rules, tried in order with backtracking.
        if goal.tag == "or":
            for rule, side in (("or_r1", goal.left), ("or_r2", goal.right)):
                sub = self.prove(gamma, side, budget)
                if sub is not None:
                    return Step(rule, goal, (sub,))
        for p in gamma:
            if p.tag == "imp" and p.left.tag == "imp":
                a, b, d = p.left.left, p.left.right, p.right
                rest = _without(gamma, p)
                left = self.prove(_add(rest, b >> d), a >> b, budget)
                if left is None:
                    continue
                right = self.prove(_add(rest, d), goal, budget)
                if right is not None:
                    return Step("imp_imp", p, (left, right))
        if not fo:
            return None
        for p in gamma:
            if p.tag == "imp" and p.left.tag in _QUANTIFIERS:
                rest = _without(gamma, p)
                left = self.prove(rest, p.left, budget)
                if left is None:
                    continue
                right = self.prove(_add(rest, p.right), goal, budget)
                if right is not None:
                    return Step("imp_q", p, (left, right))
        if budget <= 0:
            return None
        terms = _terms((*gamma, goal))
        if goal.tag == "exists":
            for t in terms:
                if t.sort == goal.var.sort:
                    sub = self.prove(gamma, goal.body.subst_var(goal.var, t), budget - 1)
                    if sub is not None:
                        return Step("exists_r", goal, (sub,), extra=t)
        for p in gamma:
            if p.tag != "forall":
                continue
            for t in terms:
                if t.sort != p.var.sort:
                    continue
                instance = p.body.subst_var(p.var, t)
                if instance in gamma:
                    continue
                sub = self.prove(_add(gamma, instance), goal, budget - 1)
                if sub is not None:
                    return Step("forall_l", p, (sub,), extra=t)
        return None


# --- replay (ai-spec §3.4, §6.5) -----------------------------------------------------


class Replay:
    """Replays a proof tree on the current goal of a proof context."""

    def __init__(self, ctx: "ProofContext") -> None:
        self.ctx = ctx

    def run(self, step: Step, facts: dict[Prop, "Fact"]) -> None:
        ctx = self.ctx
        rule, p = step.rule, step.principal
        if rule == "ax":
            ctx.exact(facts[p])
        elif rule == "bot":
            ctx.exact(ctx.absurd(facts[p], ctx.goals[0].target))
        elif rule == "eq":
            assert step.eq is not None
            ctx.exact(self._eq(step.eq, facts))
        elif rule == "imp_r":
            h = ctx.intro()
            self.run(step.subs[0], {**facts, p.left: h})
        elif rule == "and_r":
            ctx.split()
            for sub in step.subs:
                with ctx.focus():
                    self.run(sub, facts)
        elif rule == "and_l":
            f = facts[p]
            extra = {p.left: ctx.and_left(f), p.right: ctx.and_right(f)}
            self.run(step.subs[0], {**extra, **facts})
        elif rule == "or_l":
            left, right = ctx.cases(facts[p])
            for sub, side, fact in zip(step.subs, (p.left, p.right), (left, right), strict=True):
                with ctx.focus():
                    self.run(sub, {**facts, side: fact})
        elif rule in ("or_r1", "or_r2"):
            ctx.left() if rule == "or_r1" else ctx.right()
            self.run(step.subs[0], facts)
        elif rule == "imp_atom":
            b = ctx.mp(facts[p], facts[step.extra])
            self.run(step.subs[0], {**facts, p.right: b})
        elif rule == "imp_and":
            self.run(step.subs[0], {**facts, **self._curry(p, facts[p])})
        elif rule == "imp_or":
            self.run(step.subs[0], {**facts, **self._split_or(p, facts[p])})
        elif rule == "imp_bot":
            self.run(step.subs[0], facts)
        elif rule == "imp_imp":
            self._imp_imp(step, facts)
        elif rule == "forall_r":
            assert step.var is not None
            ctx.intro(step.var.name)
            self.run(step.subs[0], facts)
        elif rule == "exists_l":
            assert step.var is not None
            _, h = ctx.obtain(facts[p], (step.var.name, None))
            self.run(step.subs[0], {**facts, h.prop: h})
        elif rule == "exists_r":
            ctx.exists(step.extra)
            self.run(step.subs[0], facts)
        elif rule == "forall_l":
            g = ctx.spec(facts[p], step.extra)
            self.run(step.subs[0], {**facts, g.prop: g})
        elif rule == "imp_q":
            k = ctx.have(p.left)
            with ctx.focus():
                self.run(step.subs[0], facts)
            self.run(step.subs[1], {**facts, p.right: ctx.mp(facts[p], k)})
        else:  # pragma: no cover - the search produces only the rules above
            raise AssertionError(rule)

    def _eq(self, proof: EqProof, facts: dict[Prop, "Fact"]) -> "Fact":
        ctx = self.ctx
        if proof.kind == "refl":
            return ctx.refl(proof.left)
        if proof.kind == "hyp":
            assert proof.hyp is not None
            fact = facts[proof.hyp]
            return ctx.symm(fact) if proof.flipped else fact
        if proof.kind == "trans":
            result = self._eq(proof.parts[0], facts)
            for part in proof.parts[1:]:
                result = ctx.trans(result, self._eq(part, facts))
            return result
        # congr: rewrite one argument at a time, left to right
        const = proof.left._node[1]
        args = list(proof.left._node[2])
        result = ctx.refl(proof.left)
        for i, part in enumerate(proof.parts):
            if part.left == part.right:
                continue
            z = _fresh_var(part.left.sort, [proof.left, proof.right])
            context = const(*args[:i], z, *args[i + 1 :])
            result = ctx.trans(result, ctx.congr(self._eq(part, facts), (z, context)))
            args[i] = part.right
        return result

    def _curry(self, p: Prop, f: "Fact") -> dict[Prop, "Fact"]:
        """From (A ∧ B) → D, a fact A → (B → D)."""
        ctx = self.ctx
        a, b, d = p.left.left, p.left.right, p.right
        g = ctx.have(a >> (b >> d))
        with ctx.focus():
            ha = ctx.intro()
            hb = ctx.intro()
            ctx.exact(ctx.mp(f, ctx.and_intro(ha, hb)))
        return {a >> (b >> d): g}

    def _split_or(self, p: Prop, f: "Fact") -> dict[Prop, "Fact"]:
        """From (A ∨ B) → D, facts A → D and B → D."""
        ctx = self.ctx
        a, b, d = p.left.left, p.left.right, p.right
        g1 = ctx.have(a >> d)
        with ctx.focus():
            ctx.exact(ctx.mp(f, ctx.or_inl(ctx.intro(), b)))
        g2 = ctx.have(b >> d)
        with ctx.focus():
            ctx.exact(ctx.mp(f, ctx.or_inr(a, ctx.intro())))
        return {a >> d: g1, b >> d: g2}

    def _imp_imp(self, step: Step, facts: dict[Prop, "Fact"]) -> None:
        """(A → B) → D: prove A → B with B → D available, then use D."""
        ctx = self.ctx
        p = step.principal
        f = facts[p]
        a, b, d = p.left.left, p.left.right, p.right
        g = ctx.have(b >> d)  # B → D, since B gives A → B
        with ctx.focus():
            hb = ctx.intro()
            k0 = ctx.have(a >> b)
            with ctx.focus():
                ctx.intro()
                ctx.exact(hb)
            ctx.exact(ctx.mp(f, k0))
        k = ctx.have(a >> b)
        with ctx.focus():
            self.run(step.subs[0], {**facts, b >> d: g})
        self.run(step.subs[1], {**facts, d: ctx.mp(f, k)})


def _fresh_var(sort: Any, terms: Sequence[Term]) -> Term:
    taken = {name for t in terms for name, _ in t.free_vars()}
    name = "_eq" if "_eq" not in taken else _fresh_name("_eq", taken)
    return Var(name, sort)


# --- failure hint (ai-spec §3.2) ----------------------------------------------------


def _atoms(props: Sequence[Prop]) -> list[Prop]:
    found: list[Prop] = []

    def go(p: Prop) -> None:
        if p.tag == "false":
            return
        if _is_atom(p):
            if p not in found:
                found.append(p)
            return
        go(p.left)
        go(p.right)

    for p in props:
        go(p)
    return found


def _value(p: Prop, valuation: dict[Prop, bool]) -> bool:
    if p.tag == "false":
        return False
    if _is_atom(p):
        return valuation[p]
    left, right = _value(p.left, valuation), _value(p.right, valuation)
    if p.tag == "and":
        return left and right
    if p.tag == "or":
        return left or right
    return (not left) or right


def classical_hint(premises: Sequence[Prop], goal: Prop) -> str:
    """A falsifying valuation, a note that the goal is classically valid, or ''."""
    atoms = _atoms([*premises, goal])
    if len(atoms) > MAX_HINT_ATOMS:
        return ""
    for values in itertools.product((True, False), repeat=len(atoms)):
        valuation = dict(zip(atoms, values, strict=True))
        if all(_value(p, valuation) for p in premises) and not _value(goal, valuation):
            shown = ", ".join(f"{a} = {'true' if v else 'false'}" for a, v in valuation.items())
            return f"false under {shown}"
    return "classically valid; it may need classical.em"


# --- entry point ----------------------------------------------------------------------


def auto(
    ctx: "ProofContext",
    facts: dict[Prop, "Fact"],
    limit: int,
    depth: int = DEFAULT_DEPTH,
    first_order: bool = True,
) -> None:
    """Close the current goal from `facts`, or raise TacticError."""
    goal = ctx.goals[0].target
    premises = tuple(facts)
    first_order = first_order and any(_has_first_order(p) for p in (*premises, goal))
    taken = set(ctx._used_vars)
    for p in (*premises, goal):
        taken |= p.var_names()
    search = Search(limit, first_order, taken)
    proof = None
    try:
        # Iterative deepening on the number of instantiations (ai-spec §6.3).
        for budget in range(depth + 1) if first_order else (0,):
            proof = search.prove(premises, goal, budget)
            if proof is not None:
                break
    except _LimitReached:
        raise TacticError(f"auto: search limit reached ({limit} steps)") from None
    if proof is None:
        if first_order:
            raise TacticError(
                f"auto: no proof found within depth {depth} (first-order search is incomplete)"
            )
        message = "auto: not provable in intuitionistic propositional logic from the premises"
        hint = classical_hint(premises, goal)
        raise TacticError(f"{message} ({hint})" if hint else message)
    try:
        Replay(ctx).run(proof, facts)
    except TacticError as exc:  # pragma: no cover - a defect of the search or replay
        raise TacticError(f"auto: replay failed (possible defect): {exc}") from exc
