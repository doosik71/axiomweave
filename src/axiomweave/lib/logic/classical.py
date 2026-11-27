"""Standard classical principles (language-spec §10, logic-spec §9).

`em` is the only axiom; `dne` and `peirce` are proved from it. The statement of
`em` must match the kernel's standard allow list (kernel-spec §9.2).
"""

from axiomweave import Implies, Prop, Theory
from axiomweave.language.proof import ProofContext

P, Q = Prop.symbol("P"), Prop.symbol("Q")

classical = Theory("classical")


@classical.axiom
def em() -> Prop:
    return P | ~P


@classical.theorem
def dne() -> Prop:
    return ~~P >> P


@classical.proof(dne)
def _prove_dne(ctx: ProofContext) -> None:
    h = ctx.intro()  # h : (P → ⊥) → ⊥
    hp, hnp = ctx.cases(ctx.thm(em))
    with ctx.focus():
        ctx.exact(hp)
    with ctx.focus():
        ctx.exfalso()
        ctx.exact(ctx.mp(h, hnp))


@classical.theorem
def peirce() -> Prop:
    return Implies(P >> Q, P) >> P


@classical.proof(peirce)
def _prove_peirce(ctx: ProofContext) -> None:
    h = ctx.intro()  # h : (P → Q) → P
    hp, hnp = ctx.cases(ctx.thm(em))
    with ctx.focus():
        ctx.exact(hp)
    with ctx.focus():
        ctx.apply(h)  # goal: P → Q
        hp2 = ctx.intro()
        ctx.exfalso()
        ctx.exact(ctx.mp(hnp, hp2))
