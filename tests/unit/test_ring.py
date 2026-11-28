"""SymPy-backed `ctx.ring()` with proof reconstruction (interop-spec §5)."""

import importlib
import tempfile
from pathlib import Path

import pytest

from axiomweave import (
    BackendUnavailableError,
    Eq,
    ForAll,
    ProofContext,
    Prop,
    Status,
    Theory,
    Var,
)
from axiomweave.backends import symbolic
from axiomweave.kernel import STANDARD_AXIOMS, check_bundle
from axiomweave.kernel.axioms import ARITH_STATEMENTS
from axiomweave.language import ring
from axiomweave.lib.arithmetic.peano import Nat, add, arith, mul, numeral, succ, zero

pytest.importorskip("sympy")

m, n = Var("m", Nat), Var("n", Nat)


def ring_theory(statement: Prop, name: str = "demo.ring") -> Theory:
    """A theory with one theorem proved by intro… then ring."""
    thy = Theory(name, imports=[arith])

    @thy.theorem
    def t() -> Prop:
        return statement

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        while ctx.goals[0].target.tag == "forall":
            ctx.intro()
        ctx.ring()

    return thy


def result_of(statement: Prop) -> object:
    return ring_theory(statement).check().results[-1]


SQUARE = ForAll(
    [m, n],
    Eq(
        mul(add(m, n), add(m, n)),
        add(add(mul(m, m), mul(numeral(2), mul(m, n))), mul(n, n)),
    ),
)


def test_square_is_verified_without_classical_logic() -> None:
    result = result_of(SQUARE)
    assert result.status is Status.VERIFIED, str(result)  # type: ignore[attr-defined]
    assert result.axioms <= set(ARITH_STATEMENTS)  # type: ignore[attr-defined]


@pytest.mark.parametrize(
    "statement",
    [
        ForAll(n, Eq(mul(succ(n), succ(n)), add(add(mul(n, n), mul(numeral(2), n)), numeral(1)))),
        Eq(mul(zero, numeral(3)), zero),
        Eq(add(numeral(2), numeral(3)), numeral(5)),
        ForAll([m, n], Eq(add(m, n), add(n, m))),
        ForAll(n, Eq(n, n)),
    ],
    ids=["succ", "zero", "numerals", "add_comm", "refl"],
)
def test_identities(statement: Prop) -> None:
    result = result_of(statement)
    assert result.status is Status.VERIFIED, str(result)  # type: ignore[attr-defined]


def test_other_terms_are_atoms() -> None:
    thy = Theory("demo.ring.atoms", imports=[arith])
    g = thy.const("g", [Nat], Nat)

    @thy.theorem
    def t() -> Prop:
        return ForAll(n, Eq(add(g(n), mul(n, g(n))), mul(succ(n), g(n))))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.ring()

    @thy.theorem
    def inside() -> Prop:  # arguments of atoms are not normalized
        return ForAll([m, n], Eq(g(add(m, n)), g(add(n, m))))

    @thy.proof(inside)
    def _(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.intro()
        ctx.ring()

    first, second = thy.check().results[-2:]
    assert first.status is Status.VERIFIED, str(first)
    assert second.status is Status.REJECTED
    assert "not a polynomial identity" in str(second.diagnostics[0])


def test_non_identity_shows_the_difference() -> None:
    result = result_of(ForAll([m, n], Eq(mul(add(m, n), add(m, n)), add(mul(m, m), mul(n, n)))))
    assert result.status is Status.REJECTED  # type: ignore[attr-defined]
    message = str(result.diagnostics[0])  # type: ignore[attr-defined]
    assert "TacticError: ring: not a polynomial identity: lhs - rhs = 2*m*n" in message


def test_size_limit() -> None:
    power = add(m, n)
    for _ in range(5):
        power = mul(power, add(m, n))  # (m + n)^6: 64 unit monomials
    result = result_of(ForAll([m, n], Eq(power, power)))
    assert result.status is Status.REJECTED  # type: ignore[attr-defined]
    assert "too large" in str(result.diagnostics[0])  # type: ignore[attr-defined]


def test_ring_needs_a_nat_equation() -> None:
    thy = Theory("demo.ring.sort", imports=[arith])
    U = thy.sort("U")
    x = Var("x", U)

    @thy.theorem
    def t() -> Prop:
        return ForAll(x, Eq(x, x))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.ring()

    result = thy.check().results[-1]
    assert result.status is Status.REJECTED
    assert "sort Nat" in str(result.diagnostics[0])


def test_ring_eq_gives_a_fact() -> None:
    thy = Theory("demo.ring.fact", imports=[arith])
    P = Prop.symbol("P", Nat)
    errors: list[Exception] = []

    @thy.theorem
    def t() -> Prop:
        return ForAll([m, n], P(add(m, n)) >> P(add(n, m)))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        a = ctx.intro()
        b = ctx.intro()
        h = ctx.intro()
        try:
            ctx.ring_eq(a, Var("other", Nat))
        except Exception as exc:  # noqa: BLE001 - recorded and asserted below
            errors.append(exc)
        ctx.exact(ctx.subst(ctx.ring_eq(add(a, b), add(b, a)), h))

    assert thy.check().ok
    assert [type(e).__name__ for e in errors] == ["ScopeError"]


def test_missing_arith_is_a_declaration_error() -> None:
    thy = Theory("demo.ring.no_arith")
    Q = Prop.symbol("Q")

    @thy.theorem
    def t() -> Prop:
        return Q >> Q

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.have(ForAll(n, Eq(add(n, zero), n)))
        ctx.intro()
        ctx.ring()

    result = thy.check().results[-1]
    assert result.status is Status.REJECTED
    assert "DeclarationError" in str(result.diagnostics[0])


def test_certificate_verifies_independently() -> None:
    thy = ring_theory(SQUARE)
    assert thy.check().ok
    with tempfile.TemporaryDirectory() as tmp:
        data = thy.export(Path(tmp) / "ring.axwp").read_bytes()
    assert check_bundle(data, STANDARD_AXIOMS).ok


def test_wrong_sympy_answer_cannot_prove(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(symbolic, "check_identity", lambda t, u: symbolic.IdentityCheck(True, "0"))
    result = result_of(ForAll([m, n], Eq(add(m, n), mul(m, n))))
    assert result.status is Status.REJECTED  # type: ignore[attr-defined]
    assert "possible defect" in str(result.diagnostics[0])  # type: ignore[attr-defined]


def test_missing_sympy(monkeypatch: pytest.MonkeyPatch) -> None:
    real = importlib.import_module

    def fake(name: str, *args: object) -> object:
        if name == "sympy":
            raise ImportError("no sympy")
        return real(name, *args)  # type: ignore[arg-type]

    monkeypatch.setattr(importlib, "import_module", fake)
    with pytest.raises(BackendUnavailableError, match="uv sync --extra symbolic"):
        symbolic.check_identity(zero, zero)


def test_limits_are_module_constants() -> None:
    assert (ring.MAX_UNITS, ring.MAX_DEGREE) == (40, 8)
