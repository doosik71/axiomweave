"""Propositional logic examples (language-spec §11).

Run with:  uv run axw check examples/logic/implication.py
"""

from axiomweave import Implies, Prop, Theory
from axiomweave.language.proof import ProofContext

P, Q, R = (Prop.symbol(name) for name in ("P", "Q", "R"))
thy = Theory("examples.implication")


@thy.theorem
def imp_trans() -> Prop:
    return Implies(P >> Q, Q >> R, P >> R)


@thy.proof(imp_trans)
def _prove_imp_trans(ctx: ProofContext) -> None:
    hpq = ctx.intro()
    hqr = ctx.intro()
    hp = ctx.intro()
    hq = ctx.mp(hpq, hp)
    ctx.exact(ctx.mp(hqr, hq))


@thy.theorem
def and_comm() -> Prop:
    return (P & Q) >> (Q & P)


@thy.proof(and_comm)
def _prove_and_comm(ctx: ProofContext) -> None:
    h = ctx.intro()
    ctx.split()
    with ctx.focus():
        ctx.exact(ctx.and_right(h))
    with ctx.focus():
        ctx.exact(ctx.and_left(h))


@thy.theorem
def or_comm() -> Prop:
    return (P | Q) >> (Q | P)


@thy.proof(or_comm)
def _prove_or_comm(ctx: ProofContext) -> None:
    h = ctx.intro()
    hp, hq = ctx.cases(h)
    with ctx.focus():
        ctx.right()
        ctx.exact(hp)
    with ctx.focus():
        ctx.left()
        ctx.exact(hq)


@thy.theorem
def curry() -> Prop:
    return ((P & Q) >> R) >> Implies(P, Q, R)


@thy.proof(curry)
def _prove_curry(ctx: ProofContext) -> None:
    h = ctx.intro()
    hp = ctx.intro()
    hq = ctx.intro()
    ctx.apply(h)  # goal: P ∧ Q
    ctx.exact(ctx.and_intro(hp, hq))
