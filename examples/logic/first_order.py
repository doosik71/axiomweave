"""First-order logic examples (language-spec §12.7).

Run with:  uv run axw check examples/logic/first_order.py
"""

from axiomweave import Exists, ForAll, Prop, Theory, Var
from axiomweave.language.proof import ProofContext

thy = Theory("examples.first_order")
U = thy.sort("U")
a = thy.const("a", [], U)
Even = thy.const("Even", [U], Prop)
P, Q = Prop.symbol("P", U), Prop.symbol("Q", U)
x = Var("x", U)


@thy.theorem
def all_and_left() -> Prop:
    return ForAll(x, P(x) & Q(x)) >> ForAll(x, P(x))


@thy.proof(all_and_left)
def _prove_all_and_left(ctx: ProofContext) -> None:
    h = ctx.intro()
    y = ctx.intro()  # y : U
    ctx.exact(ctx.and_left(ctx.spec(h, y)))


@thy.theorem
def even_witness() -> Prop:
    return Even(a) >> Exists(x, Even(x))


@thy.proof(even_witness)
def _prove_even_witness(ctx: ProofContext) -> None:
    h = ctx.intro()
    ctx.exists(a)  # goal: Even(a)
    ctx.exact(h)


@thy.theorem
def ex_not_all_not() -> Prop:
    return Exists(x, P(x)) >> ~ForAll(x, ~P(x))


@thy.proof(ex_not_all_not)
def _prove_ex_not_all_not(ctx: ProofContext) -> None:
    h1 = ctx.intro()
    h2 = ctx.intro()
    y, hy = ctx.obtain(h1)  # y : U, hy : P(y)
    ctx.exact(ctx.mp(ctx.spec(h2, y), hy))
