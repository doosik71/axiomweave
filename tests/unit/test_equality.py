"""The L2 DSL: equality and its tactics (language-spec §13)."""

import json
import runpy
from pathlib import Path
from typing import Any

import pytest

from axiomweave import (
    AxwTypeError,
    Eq,
    Falsehood,
    ForAll,
    Implies,
    Ne,
    ProofContext,
    Prop,
    Status,
    Theory,
    Var,
)
from axiomweave.kernel import STANDARD_AXIOMS, check_bundle

ROOT = Path(__file__).resolve().parents[2]


def signature() -> Any:
    thy = Theory("demo.eq")
    U = thy.sort("U")
    a = thy.const("a", [], U)
    f = thy.const("f", [U], U)
    Even = thy.const("Even", [U], Prop)
    R = thy.const("R", [U, U], Prop)
    return thy, U, a, f, Even, R


def prove(thy: Theory, statement: Prop, proof: Any) -> tuple[Status, str]:
    """Declare `statement`, prove it with `proof`, and return the result."""
    count = sum(1 for _ in thy.environment())

    def stmt() -> Prop:
        return statement

    stmt.__name__ = f"t{count}"
    theorem = thy.theorem(stmt)
    thy.proof(theorem)(proof)
    result = thy.check().results[-1]
    return result.status, "\n".join(str(d) for d in result.diagnostics)


# --- expressions (language-spec §13.2) ---------------------------------------------


def test_eq_construction_and_display() -> None:
    thy, U, a, f, Even, _R = signature()
    x = Var("x", U)
    assert str(Eq(f(x), a)) == "f(x) = a"
    assert str(ForAll(x, Eq(x, x) >> Even(x))) == "∀x:U. x = x → Even(x)"
    assert Ne(x, a) == Implies(Eq(x, a), Falsehood)
    V = thy.sort("V")
    with pytest.raises(AxwTypeError):
        Eq(x, Var("v", V))
    with pytest.raises(AxwTypeError):
        Eq(Prop.symbol("P"), Prop.symbol("Q"))  # type: ignore[arg-type]


def test_eq_alpha_equivalence_and_encoding() -> None:
    _thy, U, a, f, _Even, _R = signature()
    x, y = Var("x", U), Var("y", U)
    assert ForAll(x, Eq(f(x), a)) == ForAll(y, Eq(f(y), a))
    assert ForAll(x, Eq(x, a)).to_json() == [
        "forall",
        "demo.eq.U",
        ["eq", ["var", 0], ["app", "demo.eq.a", []]],
    ]


def test_free_occurrences() -> None:
    _thy, U, _a, f, Even, _R = signature()
    x, y, w = Var("x", U), Var("y", U), Var("w", U)
    assert Even(f(x)).contains(f(x))
    assert not Even(f(x)).contains(f(y))
    bound = ForAll(x, Even(f(x)))
    assert not bound.contains(f(x))  # x is rebound: not a free occurrence
    mixed = Even(f(x)) & ForAll(x, Even(f(x)))
    assert mixed.abstract(f(x), w) == Even(w) & ForAll(x, Even(f(x)))


# --- tactics (language-spec §13.3) -------------------------------------------------


def test_rfl_and_refl() -> None:
    thy, _U, a, f, _Even, _R = signature()
    assert prove(thy, Eq(f(a), f(a)), lambda ctx: ctx.rfl()) == (Status.VERIFIED, "")
    assert prove(thy, Eq(a, a), lambda ctx: ctx.exact(ctx.refl(a))) == (Status.VERIFIED, "")
    status, diag = prove(thy, Eq(f(a), a), lambda ctx: ctx.rfl())
    assert status is Status.REJECTED and "TacticError" in diag


def _intro_all(ctx: ProofContext, n: int) -> list[Any]:
    return [ctx.intro() for _ in range(n)]


def test_rewrite_forward_and_reverse() -> None:
    thy, U, _a, f, Even, _R = signature()
    x, y = Var("x", U), Var("y", U)
    statement = ForAll([x, y], Eq(x, y) >> (Even(f(x)) >> Even(f(y))))

    def forward(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        he = ctx.intro()
        ctx.rewrite(ctx.symm(h))  # goal: Even(f(x))
        ctx.exact(he)

    def backward(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        he = ctx.intro()
        ctx.rewrite(h, reverse=True)
        ctx.exact(he)

    assert prove(thy, statement, forward) == (Status.VERIFIED, "")
    assert prove(thy, statement, backward) == (Status.VERIFIED, "")


def test_rewrite_under_binder() -> None:
    thy, U, _a, _f, _Even, R = signature()
    x, y, w = Var("x", U), Var("y", U), Var("w", U)
    statement = ForAll([x, y], Eq(x, y) >> (ForAll(w, R(y, w)) >> ForAll(w, R(x, w))))

    def proof(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        hr = ctx.intro()
        ctx.rewrite(h)  # goal: ∀w. R(y, w)
        ctx.exact(hr)

    assert prove(thy, statement, proof) == (Status.VERIFIED, "")


def test_rewrite_needs_an_occurrence() -> None:
    thy, U, a, _f, Even, _R = signature()
    x, y = Var("x", U), Var("y", U)
    statement = ForAll([x, y], Implies(Eq(x, y), Even(a), Even(a)))

    def proof(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        ctx.intro()
        ctx.rewrite(h)  # neither x nor y occurs in Even(a)

    status, diag = prove(thy, statement, proof)
    assert status is Status.REJECTED and "does not occur" in diag


def test_trans_symm_congr() -> None:
    thy, U, _a, f, _Even, _R = signature()
    x, y, z, w = Var("x", U), Var("y", U), Var("z", U), Var("w", U)
    statement = ForAll([x, y, z], Eq(x, y) >> (Eq(z, y) >> Eq(f(x), f(z))))

    def proof(ctx: ProofContext) -> None:
        _intro_all(ctx, 3)
        h1 = ctx.intro()
        h2 = ctx.intro()
        xz = ctx.trans(h1, ctx.symm(h2))
        ctx.exact(ctx.congr(xz, (w, f(w))))

    assert prove(thy, statement, proof) == (Status.VERIFIED, "")


def test_trans_needs_shared_middle() -> None:
    thy, U, _a, _f, _Even, _R = signature()
    x, y = Var("x", U), Var("y", U)
    statement = ForAll([x, y], Eq(x, y) >> Eq(x, y))

    def proof(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        ctx.exact(ctx.trans(h, h))

    status, diag = prove(thy, statement, proof)
    assert status is Status.REJECTED and "TacticError" in diag


def test_subst_default_and_with_motive() -> None:
    thy, U, a, _f, _Even, R = signature()
    x, y, w = Var("x", U), Var("y", U), Var("w", U)

    def all_occurrences(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        hr = ctx.intro()
        ctx.exact(ctx.subst(h, hr))  # R(x, x) becomes R(y, y)

    statement = ForAll([x, y], Eq(x, y) >> (R(x, x) >> R(y, y)))
    assert prove(thy, statement, all_occurrences) == (Status.VERIFIED, "")

    def one_occurrence(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        hr = ctx.intro()
        ctx.exact(ctx.subst(h, hr, motive=(w, R(x, w))))  # only the second argument

    statement = ForAll([x, y], Eq(x, y) >> (R(x, x) >> R(x, y)))
    assert prove(thy, statement, one_occurrence) == (Status.VERIFIED, "")

    def wrong_motive(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        hr = ctx.intro()
        ctx.subst(h, hr, motive=(w, R(w, a)))

    status, diag = prove(thy, statement, wrong_motive)
    assert status is Status.REJECTED and "TacticError" in diag


def test_congr_sort_mismatch() -> None:
    thy, U, _a, _f, _Even, _R = signature()
    V = thy.sort("V")
    x, y = Var("x", U), Var("y", U)
    v = Var("v", V)
    statement = ForAll([x, y], Eq(x, y) >> Eq(x, y))

    def proof(ctx: ProofContext) -> None:
        _intro_all(ctx, 2)
        h = ctx.intro()
        ctx.congr(h, (v, v))

    status, diag = prove(thy, statement, proof)
    assert status is Status.REJECTED and "TacticError" in diag


# --- certificates --------------------------------------------------------------------


def test_equality_theory_exports_l2(tmp_path: Path) -> None:
    module = runpy.run_path(str(ROOT / "examples" / "logic" / "equality.py"))
    thy = module["thy"]
    assert thy.check().ok
    path = thy.export(tmp_path / "eq.axwp")
    assert json.loads(path.read_text(encoding="utf-8"))["fragment"] == "L2"
    assert check_bundle(path.read_bytes(), STANDARD_AXIOMS).ok


def test_first_order_theory_without_equality_stays_l1(tmp_path: Path) -> None:
    module = runpy.run_path(str(ROOT / "examples" / "logic" / "first_order.py"))
    thy = module["thy"]
    assert thy.check().ok
    path = thy.export(tmp_path / "fo.axwp")
    assert json.loads(path.read_text(encoding="utf-8"))["fragment"] == "L1"
