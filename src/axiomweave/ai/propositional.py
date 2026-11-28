"""Decision procedure for intuitionistic propositional logic (ai-spec §3).

The search runs Dyckhoff's contraction-free sequent calculus G4ip on the
propositional skeleton of the goal: ⊥, ∧, ∨ and → are connectives, every other
proposition (atoms, predicates, equations, quantified formulas) is an opaque
atom. A found proof tree is then replayed with the public tactics of the proof
context, so the kernel checks an ordinary derivation.
"""

import itertools
from collections.abc import Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from axiomweave.core.expressions import Falsehood, Prop
from axiomweave.errors import TacticError

if TYPE_CHECKING:
    from axiomweave.language.proof import Fact, ProofContext

DEFAULT_LIMIT = 100_000
MAX_HINT_ATOMS = 16

_CONNECTIVES = ("false", "and", "or", "imp")


def _is_atom(prop: Prop) -> bool:
    return prop.tag not in _CONNECTIVES


# --- proof trees ----------------------------------------------------------------------


@dataclass(frozen=True)
class Step:
    """A G4ip rule application. `principal` is the premise or goal it works on;
    `extra` is a further formula (the atom of L→atom); `subs` are sub-proofs."""

    rule: str
    principal: Prop
    subs: tuple["Step", ...] = ()
    extra: Prop | None = None


class _LimitReached(Exception):
    pass


# --- search (ai-spec §3.3) ----------------------------------------------------------


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
    def __init__(self, limit: int) -> None:
        self.limit = limit
        self.steps = 0
        self._failed: set[tuple[frozenset[Prop], Prop]] = set()

    def _tick(self) -> None:
        self.steps += 1
        if self.steps > self.limit:
            raise _LimitReached

    def prove(self, gamma: Gamma, goal: Prop) -> Step | None:
        key = (frozenset(gamma), goal)
        if key in self._failed:
            return None
        result = self._prove(gamma, goal)
        if result is None:
            self._failed.add(key)
        return result

    def _prove(self, gamma: Gamma, goal: Prop) -> Step | None:
        self._tick()
        # Invertible rules, in the order of ai-spec §3.3.
        if goal in gamma:
            return Step("ax", goal)
        if Falsehood in gamma:
            return Step("bot", Falsehood)
        if goal.tag == "imp":
            sub = self.prove(_add(gamma, goal.left), goal.right)
            return None if sub is None else Step("imp_r", goal, (sub,))
        if goal.tag == "and":
            left = self.prove(gamma, goal.left)
            if left is None:
                return None
            right = self.prove(gamma, goal.right)
            return None if right is None else Step("and_r", goal, (left, right))
        for p in gamma:
            if p.tag == "and":
                sub = self.prove(_add(_without(gamma, p), p.left, p.right), goal)
                return None if sub is None else Step("and_l", p, (sub,))
        for p in gamma:
            if p.tag == "or":
                rest = _without(gamma, p)
                left = self.prove(_add(rest, p.left), goal)
                if left is None:
                    return None
                right = self.prove(_add(rest, p.right), goal)
                return None if right is None else Step("or_l", p, (left, right))
        for p in gamma:
            if p.tag == "imp" and _is_atom(p.left) and p.left in gamma:
                sub = self.prove(_add(_without(gamma, p), p.right), goal)
                return None if sub is None else Step("imp_atom", p, (sub,), extra=p.left)
        for p in gamma:
            if p.tag != "imp":
                continue
            a, d = p.left, p.right
            rest = _without(gamma, p)
            if a.tag == "and":
                sub = self.prove(_add(rest, a.left >> (a.right >> d)), goal)
                return None if sub is None else Step("imp_and", p, (sub,))
            if a.tag == "or":
                sub = self.prove(_add(rest, a.left >> d, a.right >> d), goal)
                return None if sub is None else Step("imp_or", p, (sub,))
            if a.tag == "false":
                sub = self.prove(rest, goal)
                return None if sub is None else Step("imp_bot", p, (sub,))
        # Non-invertible rules, tried in order with backtracking.
        if goal.tag == "or":
            for rule, side in (("or_r1", goal.left), ("or_r2", goal.right)):
                sub = self.prove(gamma, side)
                if sub is not None:
                    return Step(rule, goal, (sub,))
        for p in gamma:
            if p.tag == "imp" and p.left.tag == "imp":
                a, b, d = p.left.left, p.left.right, p.right
                rest = _without(gamma, p)
                left = self.prove(_add(rest, b >> d), a >> b)
                if left is None:
                    continue
                right = self.prove(_add(rest, d), goal)
                if right is not None:
                    return Step("imp_imp", p, (left, right))
        return None


# --- replay (ai-spec §3.4) ----------------------------------------------------------


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
            assert step.extra is not None
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
        else:  # pragma: no cover - the search produces only the rules above
            raise AssertionError(rule)

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


def auto(ctx: "ProofContext", facts: dict[Prop, "Fact"], limit: int) -> None:
    """Close the current goal from `facts`, or raise TacticError."""
    goal = ctx.goals[0].target
    premises = tuple(facts)
    search = Search(limit)
    try:
        proof = search.prove(premises, goal)
    except _LimitReached:
        raise TacticError(f"auto: search limit reached ({limit} steps)") from None
    if proof is None:
        message = "auto: not provable in intuitionistic propositional logic from the premises"
        hint = classical_hint(premises, goal)
        raise TacticError(f"{message} ({hint})" if hint else message)
    try:
        Replay(ctx).run(proof, facts)
    except TacticError as exc:  # pragma: no cover - a defect of the search or replay
        raise TacticError(f"auto: replay failed (possible defect): {exc}") from exc
