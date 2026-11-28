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


# --- commutative semiring laws (interop-spec §5.5, used by `ctx.ring()`) ----------------


@arith.theorem
def add_right_comm() -> Prop:
    return ForAll([k, m, n], Eq(add(add(k, m), n), add(add(k, n), m)))


@arith.proof(add_right_comm)
def _prove_add_right_comm(ctx: ProofContext) -> None:
    a, b, c = ctx.intro(), ctx.intro(), ctx.intro()
    ctx.rewrite(_eq(ctx, add_assoc, a, b, c))  # k + (m + n) = (k + n) + m
    ctx.rewrite(_eq(ctx, add_assoc, a, c, b))  # k + (m + n) = k + (n + m)
    ctx.rewrite(_eq(ctx, add_comm, b, c))
    ctx.rfl()


@arith.theorem
def succ_eq_add_one() -> Prop:
    return ForAll(n, Eq(succ(n), add(n, succ(zero))))


@arith.proof(succ_eq_add_one)
def _prove_succ_eq_add_one(ctx: ProofContext) -> None:
    a = ctx.intro()
    ctx.rewrite(_eq(ctx, add_succ, a, zero))  # S(n) = S(n + 0)
    ctx.rewrite(_eq(ctx, add_zero, a))
    ctx.rfl()


@arith.theorem
def zero_mul() -> Prop:
    return ForAll(n, Eq(mul(zero, n), zero))


@arith.proof(zero_mul)
def _prove_zero_mul(ctx: ProofContext) -> None:
    ctx.induction()
    with ctx.focus():  # 0 × 0 = 0
        ctx.exact(_eq(ctx, mul_zero, zero))
    with ctx.focus():  # 0 × S(n) = 0
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, mul_succ, zero, x))  # 0 × n + 0 = 0
        ctx.rewrite(_eq(ctx, add_zero, mul(zero, x)))
        ctx.exact(ih)


@arith.theorem
def mul_one() -> Prop:
    return ForAll(n, Eq(mul(n, succ(zero)), n))


@arith.proof(mul_one)
def _prove_mul_one(ctx: ProofContext) -> None:
    a = ctx.intro()
    ctx.rewrite(_eq(ctx, mul_succ, a, zero))  # n × 0 + n = n
    ctx.rewrite(_eq(ctx, mul_zero, a))  # 0 + n = n
    ctx.rewrite(_eq(ctx, zero_add, a))
    ctx.rfl()


@arith.theorem
def succ_mul() -> Prop:
    return ForAll([m, n], Eq(mul(succ(m), n), add(mul(m, n), n)))


@arith.proof(succ_mul)
def _prove_succ_mul(ctx: ProofContext) -> None:
    a = ctx.intro()
    ctx.induction()
    with ctx.focus():  # S(m) × 0 = m × 0 + 0
        ctx.rewrite(_eq(ctx, mul_zero, succ(a)))
        ctx.rewrite(_eq(ctx, mul_zero, a))
        ctx.rewrite(_eq(ctx, add_zero, zero))
        ctx.rfl()
    with ctx.focus():  # S(m) × S(n) = m × S(n) + S(n)
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, mul_succ, succ(a), x))  # S(m) × n + S(m) = …
        ctx.rewrite(ih)  # (m × n + n) + S(m) = …
        ctx.rewrite(_eq(ctx, mul_succ, a, x))  # … = (m × n + m) + S(n)
        ctx.rewrite(_eq(ctx, add_succ, add(mul(a, x), x), a))
        ctx.rewrite(_eq(ctx, add_succ, add(mul(a, x), a), x))
        ctx.rewrite(_eq(ctx, add_right_comm, mul(a, x), x, a))
        ctx.rfl()


@arith.theorem
def one_mul() -> Prop:
    return ForAll(n, Eq(mul(succ(zero), n), n))


@arith.proof(one_mul)
def _prove_one_mul(ctx: ProofContext) -> None:
    a = ctx.intro()
    ctx.rewrite(_eq(ctx, succ_mul, zero, a))  # 0 × n + n = n
    ctx.rewrite(_eq(ctx, zero_mul, a))
    ctx.rewrite(_eq(ctx, zero_add, a))
    ctx.rfl()


@arith.theorem
def mul_comm() -> Prop:
    return ForAll([m, n], Eq(mul(m, n), mul(n, m)))


@arith.proof(mul_comm)
def _prove_mul_comm(ctx: ProofContext) -> None:
    a = ctx.intro()
    ctx.induction()
    with ctx.focus():  # m × 0 = 0 × m
        ctx.rewrite(_eq(ctx, mul_zero, a))
        ctx.rewrite(_eq(ctx, zero_mul, a))
        ctx.rfl()
    with ctx.focus():  # m × S(n) = S(n) × m
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, mul_succ, a, x))  # m × n + m = S(n) × m
        ctx.rewrite(_eq(ctx, succ_mul, x, a))  # m × n + m = n × m + m
        ctx.rewrite(ih)
        ctx.rfl()


@arith.theorem
def mul_add() -> Prop:
    return ForAll([k, m, n], Eq(mul(k, add(m, n)), add(mul(k, m), mul(k, n))))


@arith.proof(mul_add)
def _prove_mul_add(ctx: ProofContext) -> None:
    a = ctx.intro()
    b = ctx.intro()
    ctx.induction()
    with ctx.focus():  # k × (m + 0) = k × m + k × 0
        ctx.rewrite(_eq(ctx, add_zero, b))
        ctx.rewrite(_eq(ctx, mul_zero, a))
        ctx.rewrite(_eq(ctx, add_zero, mul(a, b)))
        ctx.rfl()
    with ctx.focus():  # k × (m + S(n)) = k × m + k × S(n)
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, add_succ, b, x))  # k × S(m + n) = …
        ctx.rewrite(_eq(ctx, mul_succ, a, add(b, x)))  # k × (m + n) + k = …
        ctx.rewrite(ih)  # (k × m + k × n) + k = …
        ctx.rewrite(_eq(ctx, mul_succ, a, x))  # … = k × m + (k × n + k)
        ctx.rewrite(_eq(ctx, add_assoc, mul(a, b), mul(a, x), a))
        ctx.rfl()


@arith.theorem
def add_mul() -> Prop:
    return ForAll([k, m, n], Eq(mul(add(k, m), n), add(mul(k, n), mul(m, n))))


@arith.proof(add_mul)
def _prove_add_mul(ctx: ProofContext) -> None:
    a, b, c = ctx.intro(), ctx.intro(), ctx.intro()
    ctx.rewrite(_eq(ctx, mul_comm, add(a, b), c))  # n × (k + m) = k × n + m × n
    ctx.rewrite(_eq(ctx, mul_add, c, a, b))  # n × k + n × m = …
    ctx.rewrite(_eq(ctx, mul_comm, c, a))
    ctx.rewrite(_eq(ctx, mul_comm, c, b))
    ctx.rfl()


@arith.theorem
def mul_assoc() -> Prop:
    return ForAll([k, m, n], Eq(mul(mul(k, m), n), mul(k, mul(m, n))))


@arith.proof(mul_assoc)
def _prove_mul_assoc(ctx: ProofContext) -> None:
    a = ctx.intro()
    b = ctx.intro()
    ctx.induction()
    with ctx.focus():  # (k × m) × 0 = k × (m × 0)
        ctx.rewrite(_eq(ctx, mul_zero, mul(a, b)))
        ctx.rewrite(_eq(ctx, mul_zero, b))
        ctx.rewrite(_eq(ctx, mul_zero, a))
        ctx.rfl()
    with ctx.focus():  # (k × m) × S(n) = k × (m × S(n))
        x = ctx.intro()
        ih = ctx.intro()
        ctx.rewrite(_eq(ctx, mul_succ, mul(a, b), x))  # (k × m) × n + k × m = …
        ctx.rewrite(_eq(ctx, mul_succ, b, x))  # … = k × (m × n + m)
        ctx.rewrite(_eq(ctx, mul_add, a, mul(b, x), b))  # … = k × (m × n) + k × m
        ctx.rewrite(ih)
        ctx.rfl()


@arith.theorem
def mul_right_comm() -> Prop:
    return ForAll([k, m, n], Eq(mul(mul(k, m), n), mul(mul(k, n), m)))


@arith.proof(mul_right_comm)
def _prove_mul_right_comm(ctx: ProofContext) -> None:
    a, b, c = ctx.intro(), ctx.intro(), ctx.intro()
    ctx.rewrite(_eq(ctx, mul_assoc, a, b, c))  # k × (m × n) = (k × n) × m
    ctx.rewrite(_eq(ctx, mul_assoc, a, c, b))  # k × (m × n) = k × (n × m)
    ctx.rewrite(_eq(ctx, mul_comm, b, c))
    ctx.rfl()
