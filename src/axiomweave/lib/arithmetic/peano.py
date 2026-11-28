"""The standard arithmetic theory `arith` (logic-spec §14, language-spec §14).

Natural numbers are introduced axiomatically: the sort `Nat`, the constants
`zero`, `succ`, `add`, `mul`, six Peano axioms and one induction schema. The
axiom statements must match the kernel's standard allow list (kernel-spec §15).
Without `classical.em` this is Heyting arithmetic.
"""

from typing import Any

from axiomweave import Eq, ForAll, Ne, Prop, Term, Theory, Var
from axiomweave.errors import AxwTypeError
from axiomweave.language.proof import ProofContext

arith = Theory("arith")

Nat = arith.sort("Nat")
zero: Term = arith.const("zero", [], Nat)
succ: Any = arith.const("succ", [Nat], Nat)
add: Any = arith.const("add", [Nat, Nat], Nat)
mul: Any = arith.const("mul", [Nat, Nat], Nat)

k, m, n = Var("k", Nat), Var("m", Nat), Var("n", Nat)
P = Prop.symbol("P", Nat)


def numeral(value: int) -> Term:
    """The term succ(…succ(zero)…) with `value` applications of succ."""
    if type(value) is not int or value < 0:
        raise AxwTypeError(f"numeral expects a non-negative int, got {value!r}")
    term = zero
    for _ in range(value):
        term = succ(term)
    return term


# --- axioms (logic-spec §14.3) ------------------------------------------------------


@arith.axiom
def succ_ne_zero() -> Prop:
    return ForAll(n, Ne(succ(n), zero))


@arith.axiom
def succ_inj() -> Prop:
    return ForAll([m, n], Eq(succ(m), succ(n)) >> Eq(m, n))


@arith.axiom
def add_zero() -> Prop:
    return ForAll(n, Eq(add(n, zero), n))


@arith.axiom
def add_succ() -> Prop:
    return ForAll([m, n], Eq(add(m, succ(n)), succ(add(m, n))))


@arith.axiom
def mul_zero() -> Prop:
    return ForAll(n, Eq(mul(n, zero), zero))


@arith.axiom
def mul_succ() -> Prop:
    return ForAll([m, n], Eq(mul(m, succ(n)), add(mul(m, n), m)))


@arith.axiom
def induction() -> Prop:
    return P(zero) >> (ForAll(n, P(n) >> P(succ(n))) >> ForAll(n, P(n)))


# --- theorems (language-spec §14.3) ---------------------------------------------------


def _eq(ctx: ProofContext, axiom: object, *terms: Term) -> Any:
    """An instance of a universally quantified equation."""
    return ctx.spec(ctx.thm(axiom), *terms)


@arith.theorem
def zero_add() -> Prop:
    return ForAll(n, Eq(add(zero, n), n))


@arith.proof(zero_add)
def _prove_zero_add(ctx: ProofContext) -> None:
    ctx.induction()
    with ctx.focus():  # 0 + 0 = 0
        ctx.exact(_eq(ctx, add_zero, zero))
    with ctx.focus():  # ∀n. 0 + n = n → 0 + S(n) = S(n)
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, add_succ, zero, x))  # S(0 + n) = S(n)
        ctx.rewrite(ih)
        ctx.rfl()


@arith.theorem
def succ_add() -> Prop:
    return ForAll([m, n], Eq(add(succ(m), n), succ(add(m, n))))


@arith.proof(succ_add)
def _prove_succ_add(ctx: ProofContext) -> None:
    a = ctx.intro()
    ctx.induction()
    with ctx.focus():  # S(m) + 0 = S(m + 0)
        ctx.rewrite(_eq(ctx, add_zero, succ(a)))
        ctx.rewrite(_eq(ctx, add_zero, a))
        ctx.rfl()
    with ctx.focus():  # S(m) + S(n) = S(m + S(n))
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, add_succ, succ(a), x))  # S(S(m) + n) = S(m + S(n))
        ctx.rewrite(ih)  # S(S(m + n)) = S(m + S(n))
        ctx.rewrite(_eq(ctx, add_succ, a, x))  # S(S(m + n)) = S(S(m + n))
        ctx.rfl()


@arith.theorem
def add_comm() -> Prop:
    return ForAll([m, n], Eq(add(m, n), add(n, m)))


@arith.proof(add_comm)
def _prove_add_comm(ctx: ProofContext) -> None:
    a = ctx.intro()
    ctx.induction()
    with ctx.focus():  # m + 0 = 0 + m
        ctx.rewrite(_eq(ctx, add_zero, a))
        ctx.rewrite(_eq(ctx, zero_add, a))
        ctx.rfl()
    with ctx.focus():  # m + S(n) = S(n) + m
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, add_succ, a, x))  # S(m + n) = S(n) + m
        ctx.rewrite(_eq(ctx, succ_add, x, a))  # S(m + n) = S(n + m)
        ctx.rewrite(ih)
        ctx.rfl()


@arith.theorem
def add_assoc() -> Prop:
    return ForAll([k, m, n], Eq(add(add(k, m), n), add(k, add(m, n))))


@arith.proof(add_assoc)
def _prove_add_assoc(ctx: ProofContext) -> None:
    a = ctx.intro()
    b = ctx.intro()
    ctx.induction()
    with ctx.focus():  # (k + m) + 0 = k + (m + 0)
        ctx.rewrite(_eq(ctx, add_zero, add(a, b)))
        ctx.rewrite(_eq(ctx, add_zero, b))
        ctx.rfl()
    with ctx.focus():  # (k + m) + S(n) = k + (m + S(n))
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, add_succ, add(a, b), x))
        ctx.rewrite(_eq(ctx, add_succ, b, x))
        ctx.rewrite(_eq(ctx, add_succ, a, add(b, x)))
        ctx.rewrite(ih)
        ctx.rfl()
