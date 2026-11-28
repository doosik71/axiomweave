"""The standard arithmetic theory `arith` and the induction tactic (logic-spec §14,
kernel-spec §15, language-spec §14)."""

import json
from pathlib import Path

import pytest

from axiomweave import (
    Axiom,
    AxwTypeError,
    Eq,
    ForAll,
    ProofContext,
    Prop,
    Status,
    Theory,
    Var,
)
from axiomweave.kernel import STANDARD_AXIOMS, check_bundle
from axiomweave.kernel.axioms import ARITH_STATEMENTS
from axiomweave.kernel.errors import E_AXIOM_NOT_ALLOWED, E_TYPE
from axiomweave.lib.arithmetic.peano import (
    Nat,
    add,
    add_succ,
    add_zero,
    arith,
    mul,
    mul_succ,
    mul_zero,
    numeral,
    succ,
    zero,
)
from tests.helpers import axiom, const, encode, l2_bundle, sort

n = Var("n", Nat)


def test_library_verifies_without_classical_logic() -> None:
    report = arith.check()
    assert report.ok, str(report)
    for result in report.results:
        assert result.axioms is not None
        assert result.axioms <= set(ARITH_STATEMENTS)


def test_library_axioms_match_standard_allow_list() -> None:
    axioms = {d.name: d for d in arith.environment() if isinstance(d, Axiom)}
    assert set(axioms) == set(ARITH_STATEMENTS)
    for name, decl in axioms.items():
        assert decl.statement.to_json() == ARITH_STATEMENTS[name]
        assert decl.to_json()["hash"] == STANDARD_AXIOMS[name]


def test_numeral() -> None:
    assert numeral(0) == zero
    assert numeral(2) == succ(succ(zero))
    assert str(numeral(1)) == "succ(zero)"
    for bad in (-1, True, 1.0, "2"):
        with pytest.raises(AxwTypeError):
            numeral(bad)  # type: ignore[arg-type]


def user_theory(name: str = "demo.nat") -> Theory:
    return Theory(name, imports=[arith])


def test_induction_in_user_theory() -> None:
    thy = user_theory()

    @thy.theorem
    def zero_mul() -> Prop:
        return ForAll(n, Eq(mul(zero, n), zero))

    @thy.proof(zero_mul)
    def _(ctx: ProofContext) -> None:
        ctx.induction()
        with ctx.focus():  # 0 × 0 = 0
            ctx.exact(ctx.spec(ctx.thm(mul_zero), zero))
        with ctx.focus():  # ∀n. 0 × n = 0 → 0 × S(n) = 0
            x = ctx.intro()
            ih = ctx.intro()
            ctx.rewrite(ctx.spec(ctx.thm(mul_succ), zero, x))  # 0 × n + 0 = 0
            ctx.rewrite(ctx.spec(ctx.thm(add_zero), mul(zero, x)))  # 0 × n = 0
            ctx.exact(ih)

    report = thy.check()
    assert report.ok, str(report)
    assert zero_mul.axioms == {
        "arith.add_zero",
        "arith.induction",
        "arith.mul_succ",
        "arith.mul_zero",
    }


def test_numeral_arithmetic_without_induction() -> None:
    thy = user_theory()

    @thy.theorem
    def add_one() -> Prop:
        return ForAll(n, Eq(add(n, numeral(1)), succ(n)))

    @thy.proof(add_one)
    def _(ctx: ProofContext) -> None:
        x = ctx.intro()
        ctx.rewrite(ctx.spec(ctx.thm(add_succ), x, zero))  # S(n + 0) = S(n)
        ctx.rewrite(ctx.spec(ctx.thm(add_zero), x))
        ctx.rfl()

    assert thy.check().ok
    assert add_one.axioms == {"arith.add_succ", "arith.add_zero"}


def test_induction_needs_a_nat_goal() -> None:
    thy = user_theory()
    U = thy.sort("U")
    x = Var("x", U)

    @thy.theorem
    def t() -> Prop:
        return ForAll(x, Eq(x, x))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.induction()

    result = thy.check().results[-1]
    assert result.status is Status.REJECTED
    assert "TacticError" in str(result.diagnostics[0])


def test_induction_needs_arith_imported() -> None:
    # Without importing arith the statement cannot mention Nat, but `have` can still
    # create a ∀n:Nat goal; induction must then refuse to use the unimported axiom.
    thy = Theory("demo.no_arith")

    @thy.theorem
    def t() -> Prop:
        return Prop.symbol("Q") >> Prop.symbol("Q")

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.have(ForAll(n, Eq(n, n)))
        ctx.induction()

    result = thy.check().results[-1]
    assert result.status is Status.REJECTED
    assert "DeclarationError" in str(result.diagnostics[0])
    assert "import" in str(result.diagnostics[0])


def test_arith_axioms_can_be_disallowed() -> None:
    thy = user_theory()

    @thy.theorem
    def t() -> Prop:
        return ForAll(n, Eq(add(n, zero), n))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(add_zero))

    assert thy.check().ok
    report = thy.check(allowed_axioms=["classical.em"])
    assert not report.ok
    assert report.results[-1].diagnostics[0].stage == "environment"


def test_export_verifies_with_default_policy(tmp_path: Path) -> None:
    assert arith.check().ok
    path = arith.export(tmp_path / "arith.axwp")
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["fragment"] == "L2"
    assert check_bundle(path.read_bytes(), STANDARD_AXIOMS).ok
    assert not check_bundle(path.read_bytes(), {"classical.em": STANDARD_AXIOMS["classical.em"]}).ok


# --- certificate-level rejections (logic-spec §14.5) ---------------------------------------

N = "arith.Nat"
DECLS = (
    sort(N),
    const("arith.zero", [], N),
    const("arith.succ", [N], N),
    const("arith.add", [N, N], N),
    const("arith.mul", [N, N], N),
)


def test_forged_induction_axiom_is_not_allowed() -> None:
    # Induction without the base case: same name, different statement.
    forged = ARITH_STATEMENTS["arith.induction"][2]
    bad = axiom("arith.induction", forged)
    report = check_bundle(encode(l2_bundle(*DECLS, bad, theory="arith")), STANDARD_AXIOMS)
    assert report.bundle_error is not None
    assert report.bundle_error.code == E_AXIOM_NOT_ALLOWED


def test_axiom_with_mistyped_constant_is_rejected() -> None:
    wrong_succ = const("arith.succ", [N, N], N)
    decls = (*DECLS[:2], wrong_succ, *DECLS[3:])
    ax = axiom("arith.succ_inj", ARITH_STATEMENTS["arith.succ_inj"])
    report = check_bundle(encode(l2_bundle(*decls, ax, theory="arith")), STANDARD_AXIOMS)
    assert report.bundle_ok
    error = report.results[-1].error
    assert error is not None and error.code == E_TYPE
