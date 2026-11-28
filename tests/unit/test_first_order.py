"""The L1 DSL: sorts, constants, quantifiers and their tactics (language-spec §12)."""

import json
from pathlib import Path

import pytest

from axiomweave import (
    AxwTypeError,
    DeclarationError,
    Exists,
    Falsehood,
    ForAll,
    ProofContext,
    Prop,
    ScopeError,
    Status,
    Theory,
    Var,
)
from axiomweave.kernel import STANDARD_AXIOMS, check_bundle
from axiomweave.lib.logic.classical import classical, em
from axiomweave.lib.logic.propositional import and_comm, propositional


def signature(name: str = "demo.fol") -> tuple[Theory, object, object, object, object]:
    thy = Theory(name)
    U = thy.sort("U")
    a = thy.const("a", [], U)
    f = thy.const("f", [U], U)
    Even = thy.const("Even", [U], Prop)
    return thy, U, a, f, Even


def only(thy: Theory) -> tuple[Status, str]:
    """Status and diagnostics of the last theorem."""
    result = thy.check().results[-1]
    return result.status, "\n".join(str(d) for d in result.diagnostics)


# --- expressions (language-spec §12.2–12.4) -------------------------------------


def test_terms_and_predicates() -> None:
    _thy, U, a, f, Even = signature()
    x = Var("x", U)
    assert str(f(f(x))) == "f(f(x))"
    assert str(Even(a)) == "Even(a)"
    assert f(x).sort == U
    with pytest.raises(AxwTypeError):
        Even(Prop.symbol("R"))
    with pytest.raises(AxwTypeError):
        Even(a, a)
    with pytest.raises(AxwTypeError):
        bool(x)


def test_alpha_equivalence() -> None:
    _thy, U, a, _f, Even = signature()
    x, y = Var("x", U), Var("y", U)
    assert ForAll(x, Even(x)) == ForAll(y, Even(y))
    assert hash(ForAll(x, Even(x))) == hash(ForAll(y, Even(y)))
    assert ForAll(x, Even(x)) != ForAll(x, Even(a))
    assert ForAll([x, y], Even(x)) == ForAll(x, ForAll(y, Even(x)))
    assert ForAll([x, y], Even(x)) != ForAll([x, y], Even(y))


def test_display() -> None:
    _thy, U, _a, _f, Even = signature()
    x = Var("x", U)
    P = Prop.symbol("P", U)
    assert str(ForAll(x, P(x) >> Even(x))) == "∀x:U. P(x) → Even(x)"
    assert str(Exists(x, P(x)) >> Falsehood) == "(∃x:U. P(x)) → ⊥"


def test_same_name_with_two_sorts_is_an_error() -> None:
    thy, U, _a, _f, Even = signature()
    V = thy.sort("V")
    with pytest.raises(AxwTypeError):
        ForAll(Var("x", U), Even(Var("x", U))) & Prop.symbol("P", V)(Var("x", V))


def test_de_bruijn_encoding() -> None:
    _thy, U, _a, f, Even = signature()
    x, y = Var("x", U), Var("y", U)
    prop = ForAll(x, ForAll(y, Even(f(x))))
    assert prop.to_json() == [
        "forall",
        "demo.fol.U",
        ["forall", "demo.fol.U", ["pred", "demo.fol.Even", [["app", "demo.fol.f", [["var", 1]]]]]],
    ]
    with pytest.raises(ScopeError):
        Even(x).to_json()


def test_capture_avoiding_substitution() -> None:
    _thy, U, _a, _f, _Even = signature()
    x, y = Var("x", U), Var("y", U)
    R = Prop.symbol("R", U, U)
    body = ForAll(y, R(x, y))
    result = body.subst_var(x, y)  # must not capture y
    assert result == ForAll(Var("z", U), R(y, Var("z", U)))
    assert result != ForAll(y, R(y, y))


def test_predicate_symbols() -> None:
    _thy, U, a, _f, _Even = signature()
    P = Prop.symbol("P", U)
    assert P(a).atoms() == {"P"}
    assert Prop.symbol("P").atoms() == {"P"}
    with pytest.raises(AxwTypeError):
        P(Prop.symbol("Q"))


# --- declarations ------------------------------------------------------------------


def test_statements_must_be_closed() -> None:
    thy, U, _a, _f, Even = signature()
    x = Var("x", U)
    with pytest.raises(DeclarationError, match="free variables"):

        @thy.theorem
        def bad() -> Prop:
            return Even(x)


def test_schematic_name_needs_one_arity() -> None:
    thy, U, a, _f, _Even = signature()
    with pytest.raises(DeclarationError):

        @thy.theorem
        def bad() -> Prop:
            return Prop.symbol("P") & Prop.symbol("P", U)(a)


def test_sorts_need_imports() -> None:
    other, U, a, _f, Even = signature("demo.other")
    thy = Theory("demo.user")
    with pytest.raises(DeclarationError, match="import"):

        @thy.theorem
        def bad() -> Prop:
            return Even(a) >> Even(a)

    with pytest.raises(DeclarationError, match="import"):
        thy.const("g", [U], U)
    ok = Theory("demo.importer", imports=[other])

    @ok.theorem
    def fine() -> Prop:
        return Even(a) >> Even(a)


def test_duplicate_and_invalid_declarations() -> None:
    thy, U, _a, _f, _Even = signature()
    with pytest.raises(DeclarationError):
        thy.sort("U")
    with pytest.raises(DeclarationError):
        thy.const("a", [], U)
    with pytest.raises(AxwTypeError):
        thy.const("g", [U], "U")


# --- tactics (language-spec §12.5) ---------------------------------------------------


def test_intro_on_forall_and_spec() -> None:
    thy, U, a, f, Even = signature()
    x = Var("x", U)

    @thy.theorem
    def t() -> Prop:
        return ForAll(x, Even(x)) >> Even(f(a))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        ctx.exact(ctx.spec(h, f(a)))

    assert only(thy) == (Status.VERIFIED, "")


def test_goal_display_shows_variables() -> None:
    thy, U, _a, _f, Even = signature()
    x = Var("x", U)
    seen: list[str] = []

    @thy.theorem
    def t() -> Prop:
        return ForAll(x, Even(x) >> Even(x))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.intro()
        h = ctx.intro()
        seen.append(str(ctx))
        ctx.exact(h)

    assert only(thy)[0] is Status.VERIFIED
    assert seen == ["goal 1/1\n  x : U\n  h1 : Even(x)\n  ⊢ Even(x)"]


def test_intro_renames_used_variable_names() -> None:
    thy, U, _a, _f, Even = signature()
    x = Var("x", U)
    names: list[str] = []

    @thy.theorem
    def t() -> Prop:
        inner = ForAll(x, Even(x))
        return (inner & inner) >> (inner & inner)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        ctx.split()
        for part in (ctx.and_left(h), ctx.and_right(h)):
            with ctx.focus():
                v = ctx.intro()
                names.append(v.name)
                ctx.exact(ctx.spec(part, v))

    assert only(thy)[0] is Status.VERIFIED
    assert names == ["x", "x1"]


def test_exists_requires_matching_sort() -> None:
    thy, U, a, _f, Even = signature()
    V = thy.sort("V")
    b = thy.const("b", [], V)
    x = Var("x", U)

    @thy.theorem
    def t() -> Prop:
        return Even(a) >> Exists(x, Even(x))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.exists(b)

    status, diagnostics = only(thy)
    assert status is Status.REJECTED and "TacticError" in diagnostics


def test_obtained_names_do_not_leak_into_sibling_goal() -> None:
    thy, U, _a, _f, _Even = signature()
    x = Var("x", U)
    P = Prop.symbol("P", U)

    @thy.theorem
    def t() -> Prop:
        return Exists(x, P(x)) >> (Exists(x, P(x)) & Exists(x, P(x)))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        ctx.split()
        with ctx.focus():
            y, hy = ctx.obtain(h)
            ctx.exists(y)
            ctx.exact(hy)
        with ctx.focus():
            ctx.exists(y)  # y belongs to the first goal

    status, diagnostics = only(thy)
    assert status is Status.REJECTED and "ScopeError" in diagnostics


def test_have_with_variable_not_in_goal() -> None:
    thy, U, a, _f, Even = signature()

    @thy.theorem
    def t() -> Prop:
        return Even(a) >> Even(a)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.have(Even(Var("z", U)))

    status, diagnostics = only(thy)
    assert status is Status.REJECTED and "ScopeError" in diagnostics


def test_spec_then_combine_with_later_hypothesis() -> None:
    thy, U, a, _f, Even = signature()
    x = Var("x", U)
    P = Prop.symbol("P", U)

    @thy.theorem
    def t() -> Prop:
        return ForAll(x, P(x)) >> (Even(a) >> ForAll(x, P(x) & Even(a)))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        he = ctx.intro()
        y = ctx.intro()
        ctx.exact(ctx.and_intro(ctx.spec(h, y), he))

    assert only(thy) == (Status.VERIFIED, "")


# --- schematic substitution -------------------------------------------------------------


def _all_and_left(thy: Theory, U: object) -> tuple[object, object, object]:
    x = Var("x", U)
    P, Q = Prop.symbol("P", U), Prop.symbol("Q", U)

    @thy.theorem
    def all_and_left() -> Prop:
        return ForAll(x, P(x) & Q(x)) >> ForAll(x, P(x))

    @thy.proof(all_and_left)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        y = ctx.intro()
        ctx.exact(ctx.and_left(ctx.spec(h, y)))

    return all_and_left, P, Q


def test_predicate_instantiation() -> None:
    # logic-spec §12.12 (4)
    thy, U, _a, _f, Even = signature()
    all_and_left, P, Q = _all_and_left(thy, U)
    x, z = Var("x", U), Var("z", U)

    @thy.theorem
    def inst() -> Prop:
        return ForAll(x, Even(x) & Falsehood) >> ForAll(x, Even(x))

    @thy.proof(inst)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(all_and_left, {P: ([z], Even(z)), Q: ([z], Falsehood)}))

    assert only(thy) == (Status.VERIFIED, "")


def test_instantiation_with_variable_from_context() -> None:
    # Inside ∀y, instantiate P ↦ λz. R(z, y): y must not be captured by the theorem's binder.
    thy, U, _a, _f, _Even = signature()
    all_and_left, P, Q = _all_and_left(thy, U)
    R = thy.const("R", [U, U], Prop)
    x, y, z = Var("x", U), Var("y", U), Var("z", U)

    @thy.theorem
    def t() -> Prop:
        inner = ForAll(x, R(x, y) & R(x, y)) >> ForAll(x, R(x, y))
        return ForAll(y, inner)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        w = ctx.intro()
        lam = ([z], R(z, w))
        ctx.exact(ctx.thm(all_and_left, {P: lam, Q: lam}))

    assert only(thy) == (Status.VERIFIED, "")


def test_predicate_instantiation_needs_matching_sorts() -> None:
    thy, U, _a, _f, _Even = signature()
    V = thy.sort("V")
    all_and_left, P, _Q = _all_and_left(thy, U)

    @thy.theorem
    def t() -> Prop:
        return Falsehood >> Falsehood

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.thm(all_and_left, {P: ([Var("v", V)], Falsehood)})

    status, diagnostics = only(thy)
    assert status is Status.REJECTED and "TacticError" in diagnostics


def test_l0_library_with_quantified_instances() -> None:
    thy = Theory("demo.lib_use", imports=[propositional, classical])
    U = thy.sort("U")
    x = Var("x", U)
    P = Prop.symbol("P", U)
    A = ForAll(x, P(x))
    B = Exists(x, P(x))

    @thy.theorem
    def comm() -> Prop:
        return (A & B) >> (B & A)

    @thy.proof(comm)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(and_comm, {Prop.symbol("P"): A, Prop.symbol("Q"): B}))

    @thy.theorem
    def em_all() -> Prop:
        return A | ~A

    @thy.proof(em_all)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(em, {Prop.symbol("P"): A}))

    report = thy.check()
    assert report.ok, str(report)
    assert em_all.axioms == {"classical.em"}


# --- certificates -------------------------------------------------------------------------


def test_fragment_and_export(tmp_path: Path) -> None:
    thy, U, _a, _f, _Even = signature()
    _all_and_left(thy, U)
    assert thy.check().ok
    path = thy.export(tmp_path / "fol.axwp")
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["fragment"] == "L1"
    assert [d["kind"] for d in data["declarations"]] == [
        "sort",
        "const",
        "const",
        "const",
        "theorem",
    ]
    assert check_bundle(path.read_bytes(), STANDARD_AXIOMS).ok


def test_l0_theories_still_export_l0(tmp_path: Path) -> None:
    assert propositional.check().ok
    data = json.loads(propositional.export(tmp_path / "p.axwp").read_text(encoding="utf-8"))
    assert data["fragment"] == "L0"
