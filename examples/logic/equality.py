"""Equality examples (language-spec §13.5).

Run with:  uv run axw check examples/logic/equality.py
"""

from axiomweave import Eq, ForAll, Prop, Theory, Var
from axiomweave.language.proof import ProofContext

thy = Theory("examples.equality")
U = thy.sort("U")
f = thy.const("f", [U], U)
Even = thy.const("Even", [U], Prop)
x, y, z = Var("x", U), Var("y", U), Var("z", U)


@thy.theorem
def eq_symm() -> Prop:
    return ForAll([x, y], Eq(x, y) >> Eq(y, x))


@thy.proof(eq_symm)
def _prove_eq_symm(ctx: ProofContext) -> None:
    ctx.intro()
    ctx.intro()
    h = ctx.intro()
    ctx.exact(ctx.symm(h))


@thy.theorem
def even_congr() -> Prop:
    return ForAll([x, y], Eq(x, y) >> (Even(f(x)) >> Even(f(y))))


@thy.proof(even_congr)
def _prove_even_congr(ctx: ProofContext) -> None:
    ctx.intro()
    ctx.intro()
    h = ctx.intro()
    he = ctx.intro()
    ctx.rewrite(h, reverse=True)  # goal: Even(f(x))
    ctx.exact(he)


@thy.theorem
def eq_trans() -> Prop:
    return ForAll([x, y, z], Eq(x, y) >> (Eq(y, z) >> Eq(x, z)))


@thy.proof(eq_trans)
def _prove_eq_trans(ctx: ProofContext) -> None:
    ctx.intro()
    ctx.intro()
    ctx.intro()
    h1 = ctx.intro()
    h2 = ctx.intro()
    ctx.exact(ctx.trans(h1, h2))


@thy.theorem
def f_congr() -> Prop:
    return ForAll([x, y], Eq(x, y) >> Eq(f(f(x)), f(f(y))))


@thy.proof(f_congr)
def _prove_f_congr(ctx: ProofContext) -> None:
    ctx.intro()
    ctx.intro()
    h = ctx.intro()
    w = Var("w", U)
    ctx.exact(ctx.congr(h, (w, f(f(w)))))
