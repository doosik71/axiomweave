"""Arithmetic benchmark problems over the standard theory `arith` (ai-spec §5.2)."""

from collections.abc import Callable

from axiomweave.bench.core import Problem
from axiomweave.core.expressions import Eq, Exists, ForAll, Ne, Prop, Var
from axiomweave.language.proof import ProofContext
from axiomweave.lib.arithmetic.peano import (
    Nat,
    add,
    add_succ,
    add_zero,
    arith,
    mul,
    numeral,
    succ,
    succ_inj,
    succ_ne_zero,
    zero,
)

a, b, c, d = (Var(name, Nat) for name in ("a", "b", "c", "d"))
k, m, n = Var("k", Nat), Var("m", Nat), Var("n", Nat)
w = Var("w", Nat)
one, two, three = numeral(1), numeral(2), numeral(3)


def _by_ring(ctx: ProofContext) -> None:
    while ctx.goals[0].target.tag == "forall":
        ctx.intro()
    ctx.ring()


def _provable(
    name: str, statement: Prop, proof: Callable[[ProofContext], None] = _by_ring
) -> Problem:
    return Problem(f"arith.{name}", "arithmetic", lambda: statement, "provable", (arith,), proof)


def _unprovable(name: str, statement: Prop, note: str) -> Problem:
    return Problem(
        f"arith.{name}", "arithmetic", lambda: statement, "unprovable", (arith,), None, note
    )


def _n_ne_succ(ctx: ProofContext) -> None:
    ctx.induction()
    with ctx.focus():  # 0 ≠ S(0)
        h = ctx.intro()
        ctx.exact(ctx.mp(ctx.spec(ctx.thm(succ_ne_zero), zero), ctx.symm(h)))
    with ctx.focus():  # n ≠ S(n) → S(n) ≠ S(S(n))
        x = ctx.intro()
        ih = ctx.intro()
        h = ctx.intro()
        ctx.exact(ctx.mp(ih, ctx.mp(ctx.spec(ctx.thm(succ_inj), x, succ(x)), h)))


def _add_cancel_right(ctx: ProofContext) -> None:
    p = ctx.intro()
    q = ctx.intro()
    ctx.induction()
    with ctx.focus():  # p + 0 = q + 0 → p = q
        h = ctx.intro()
        left = ctx.symm(ctx.spec(ctx.thm(add_zero), p))
        ctx.exact(ctx.trans(left, ctx.trans(h, ctx.spec(ctx.thm(add_zero), q))))
    with ctx.focus():  # (p + x = q + x → p = q) → p + S(x) = q + S(x) → p = q
        x = ctx.intro()
        ih = ctx.intro()
        h = ctx.intro()
        left = ctx.symm(ctx.spec(ctx.thm(add_succ), p, x))
        right = ctx.spec(ctx.thm(add_succ), q, x)
        succ_eq = ctx.trans(left, ctx.trans(h, right))  # S(p + x) = S(q + x)
        inner = ctx.mp(ctx.spec(ctx.thm(succ_inj), add(p, x), add(q, x)), succ_eq)
        ctx.exact(ctx.mp(ih, inner))


def _add_eq_zero(ctx: ProofContext) -> None:
    p = ctx.intro()
    ctx.induction()
    with ctx.focus():  # p + 0 = 0 → p = 0
        h = ctx.intro()
        ctx.exact(ctx.trans(ctx.symm(ctx.spec(ctx.thm(add_zero), p)), h))
    with ctx.focus():  # p + S(x) = 0 is impossible
        x = ctx.intro()
        ctx.intro()
        h = ctx.intro()
        succ_zero = ctx.trans(ctx.symm(ctx.spec(ctx.thm(add_succ), p, x)), h)
        bottom = ctx.mp(ctx.spec(ctx.thm(succ_ne_zero), add(p, x)), succ_zero)
        ctx.exact(ctx.absurd(bottom, ctx.goals[0].target))


def _succ_inj_add(ctx: ProofContext) -> None:
    p = ctx.intro()
    q = ctx.intro()
    h = ctx.intro()
    same = ctx.mp(ctx.spec(ctx.thm(succ_inj), p, q), h)
    ctx.exact(ctx.congr(same, (w, add(w, one))))


def _one_ne_two(ctx: ProofContext) -> None:
    h = ctx.intro()
    zero_one = ctx.mp(ctx.spec(ctx.thm(succ_inj), zero, one), h)
    ctx.exact(ctx.mp(ctx.spec(ctx.thm(succ_ne_zero), zero), ctx.symm(zero_one)))


PROBLEMS: tuple[Problem, ...] = (
    _provable("two_plus_two", Eq(add(two, two), numeral(4))),
    _provable("three_times_two", Eq(mul(three, two), numeral(6))),
    _provable("add_zero_comm", ForAll(n, Eq(add(n, zero), add(zero, n)))),
    _provable("zero_mul_comm", ForAll(n, Eq(mul(zero, n), mul(n, zero)))),
    _provable("double", ForAll(n, Eq(add(n, n), mul(two, n)))),
    _provable("succ_add_succ", ForAll([m, n], Eq(add(succ(m), succ(n)), succ(succ(add(m, n)))))),
    _provable(
        "add_four", ForAll([a, b, c, d], Eq(add(add(a, b), add(c, d)), add(add(d, c), add(b, a))))
    ),
    _provable("mul_three", ForAll([k, m, n], Eq(mul(mul(m, n), k), mul(n, mul(k, m))))),
    _provable("mul_add_comm", ForAll([k, m, n], Eq(mul(k, add(m, n)), add(mul(n, k), mul(m, k))))),
    _provable(
        "succ_square",
        ForAll(n, Eq(mul(succ(n), succ(n)), add(add(mul(n, n), mul(two, n)), one))),
    ),
    _provable(
        "binomial_square",
        ForAll(
            [m, n],
            Eq(mul(add(m, n), add(m, n)), add(add(mul(m, m), mul(two, mul(m, n))), mul(n, n))),
        ),
    ),
    _provable(
        "trinomial_square",
        ForAll(
            [a, b, c],
            Eq(
                mul(add(add(a, b), c), add(add(a, b), c)),
                add(
                    add(add(mul(a, a), mul(b, b)), mul(c, c)),
                    mul(two, add(add(mul(a, b), mul(b, c)), mul(a, c))),
                ),
            ),
        ),
    ),
    _provable(
        "succ_cube",
        ForAll(
            n,
            Eq(
                mul(succ(n), mul(succ(n), succ(n))),
                add(
                    add(add(mul(n, mul(n, n)), mul(three, mul(n, n))), mul(three, n)),
                    one,
                ),
            ),
        ),
    ),
    _provable("n_ne_succ", ForAll(n, Ne(n, succ(n))), _n_ne_succ),
    _provable(
        "add_cancel_right",
        ForAll([m, n, k], Eq(add(m, k), add(n, k)) >> Eq(m, n)),
        _add_cancel_right,
    ),
    _provable("add_eq_zero", ForAll([m, n], Eq(add(m, n), zero) >> Eq(m, zero)), _add_eq_zero),
    _provable(
        "succ_inj_add",
        ForAll([m, n], Eq(succ(m), succ(n)) >> Eq(add(m, one), add(n, one))),
        _succ_inj_add,
    ),
    _provable("one_ne_two", Ne(one, two), _one_ne_two),
    _unprovable("add_one_self", ForAll(n, Eq(add(n, one), n)), "false: n + 1 ≠ n"),
    _unprovable("succ_zero", Exists(n, Eq(succ(n), zero)), "false: 0 is not a successor"),
)
