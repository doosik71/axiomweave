"""First-order benchmark problems with equality (ai-spec §5.2)."""

from collections.abc import Callable

from axiomweave.bench.core import Problem
from axiomweave.core.expressions import Eq, Exists, ForAll, Prop, Var
from axiomweave.language.proof import ProofContext
from axiomweave.language.theory import Theory

signature = Theory("bench.sig")
U = signature.sort("U")
a = signature.const("a", [], U)
f = signature.const("f", [U], U)

x, y, z, w = Var("x", U), Var("y", U), Var("z", U), Var("w", U)
A, C = Prop.symbol("A", U), Prop.symbol("C", U)
B = Prop.symbol("B", U, U)


def _provable(name: str, statement: Prop, proof: Callable[[ProofContext], None]) -> Problem:
    return Problem(f"fol.{name}", "first_order", lambda: statement, "provable", (signature,), proof)


def _unprovable(name: str, statement: Prop, note: str) -> Problem:
    return Problem(
        f"fol.{name}", "first_order", lambda: statement, "unprovable", (signature,), None, note
    )


def _all_comm(ctx: ProofContext) -> None:
    h = ctx.intro()
    y0 = ctx.intro()
    x0 = ctx.intro()
    ctx.exact(ctx.spec(h, x0, y0))


def _ex_comm(ctx: ProofContext) -> None:
    h = ctx.intro()
    x0, h1 = ctx.obtain(h)
    y0, h2 = ctx.obtain(h1)
    ctx.exists(y0)
    ctx.exists(x0)
    ctx.exact(h2)


def _ex_all(ctx: ProofContext) -> None:
    h = ctx.intro()
    y0 = ctx.intro()
    x0, h1 = ctx.obtain(h)
    ctx.exists(x0)
    ctx.exact(ctx.spec(h1, y0))


def _all_and(ctx: ProofContext) -> None:
    h = ctx.intro()
    ctx.split()
    with ctx.focus():
        x0 = ctx.intro()
        ctx.exact(ctx.and_left(ctx.spec(h, x0)))
    with ctx.focus():
        x0 = ctx.intro()
        ctx.exact(ctx.and_right(ctx.spec(h, x0)))


def _and_all(ctx: ProofContext) -> None:
    h = ctx.intro()
    x0 = ctx.intro()
    ctx.exact(ctx.and_intro(ctx.spec(ctx.and_left(h), x0), ctx.spec(ctx.and_right(h), x0)))


def _ex_or(ctx: ProofContext) -> None:
    h = ctx.intro()
    x0, h1 = ctx.obtain(h)
    left, right = ctx.cases(h1)
    with ctx.focus():
        ctx.left()
        ctx.exists(x0)
        ctx.exact(left)
    with ctx.focus():
        ctx.right()
        ctx.exists(x0)
        ctx.exact(right)


def _not_ex(ctx: ProofContext) -> None:
    h = ctx.intro()
    x0 = ctx.intro()
    hx = ctx.intro()
    e = ctx.have(Exists(x, A(x)))
    with ctx.focus():
        ctx.exists(x0)
        ctx.exact(hx)
    ctx.exact(ctx.mp(h, e))


def _all_not(ctx: ProofContext) -> None:
    h = ctx.intro()
    e = ctx.intro()
    x0, hx = ctx.obtain(e)
    ctx.exact(ctx.mp(ctx.spec(h, x0), hx))


def _inst(ctx: ProofContext) -> None:
    h = ctx.intro()
    ctx.exact(ctx.spec(h, f(a)))


def _eq_symm(ctx: ProofContext) -> None:
    ctx.intro()
    ctx.intro()
    ctx.exact(ctx.symm(ctx.intro()))


def _eq_trans(ctx: ProofContext) -> None:
    for _ in range(3):
        ctx.intro()
    h1 = ctx.intro()
    h2 = ctx.intro()
    ctx.exact(ctx.trans(h1, h2))


def _congr(ctx: ProofContext) -> None:
    ctx.intro()
    ctx.intro()
    h = ctx.intro()
    ctx.exact(ctx.congr(h, (w, f(w))))


def _iff_all(ctx: ProofContext) -> None:
    h = ctx.intro()
    hb = ctx.intro()
    x0 = ctx.intro()
    ctx.exact(ctx.mp(ctx.spec(h, x0), hb))


PROBLEMS: tuple[Problem, ...] = (
    _provable(
        "all_comm", ForAll(x, ForAll(y, B(x, y))) >> ForAll(y, ForAll(x, B(x, y))), _all_comm
    ),
    _provable("ex_comm", Exists(x, Exists(y, B(x, y))) >> Exists(y, Exists(x, B(x, y))), _ex_comm),
    _provable("ex_all", Exists(x, ForAll(y, B(x, y))) >> ForAll(y, Exists(x, B(x, y))), _ex_all),
    _provable("all_and", ForAll(x, A(x) & C(x)) >> (ForAll(x, A(x)) & ForAll(x, C(x))), _all_and),
    _provable("and_all", (ForAll(x, A(x)) & ForAll(x, C(x))) >> ForAll(x, A(x) & C(x)), _and_all),
    _provable("ex_or", Exists(x, A(x) | C(x)) >> (Exists(x, A(x)) | Exists(x, C(x))), _ex_or),
    _provable("not_ex", ~Exists(x, A(x)) >> ForAll(x, ~A(x)), _not_ex),
    _provable("all_not", ForAll(x, ~A(x)) >> ~Exists(x, A(x)), _all_not),
    _provable("instance", ForAll(x, A(x)) >> A(f(a)), _inst),
    _provable("eq_symm", ForAll([x, y], Eq(x, y) >> Eq(y, x)), _eq_symm),
    _provable("eq_trans", ForAll([x, y, z], Eq(x, y) >> (Eq(y, z) >> Eq(x, z))), _eq_trans),
    _provable("congr", ForAll([x, y], Eq(x, y) >> Eq(f(x), f(y))), _congr),
    _provable(
        "all_imp_const",
        ForAll(x, A(a) >> C(x)) >> (A(a) >> ForAll(x, C(x))),
        _iff_all,
    ),
    _unprovable("drinker", Exists(x, A(x) >> ForAll(y, A(y))), "drinker paradox"),
    _unprovable("not_all", ~ForAll(x, A(x)) >> Exists(x, ~A(x)), "classical quantifier duality"),
)
