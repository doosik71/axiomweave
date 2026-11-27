"""Theories, proof contexts and checking (language-spec §5–7, §10–11)."""

import json
from pathlib import Path

import pytest

from axiomweave import (
    AxwError,
    DeclarationError,
    Falsehood,
    Implies,
    ProofContext,
    Prop,
    ScopeError,
    Status,
    TacticError,
    Theory,
)
from axiomweave.kernel import STANDARD_AXIOMS, check_bundle
from axiomweave.lib.logic.classical import classical, dne, em, peirce

P, Q, R = (Prop.symbol(name) for name in ("P", "Q", "R"))
A, B, C = (Prop.symbol(name) for name in ("A", "B", "C"))


def statuses(thy: Theory, **kwargs: object) -> dict[str, Status]:
    report = thy.check(**kwargs)  # type: ignore[arg-type]
    return {r.name.rsplit(".", 1)[1]: r.status for r in report.results}


def single(thy: Theory) -> tuple[Status, str]:
    [result] = [r for r in thy.check().results if r.name.startswith(thy.name + ".")]
    return result.status, "\n".join(str(d) for d in result.diagnostics)


# --- language-spec §11 examples ---------------------------------------------------


def logic_theory() -> Theory:
    thy = Theory("demo.logic")

    @thy.theorem
    def imp_trans() -> Prop:
        return Implies(P >> Q, Q >> R, P >> R)

    @thy.proof(imp_trans)
    def _(ctx: ProofContext) -> None:
        hpq = ctx.intro()
        hqr = ctx.intro()
        hp = ctx.intro()
        hq = ctx.mp(hpq, hp)
        ctx.exact(ctx.mp(hqr, hq))

    @thy.theorem
    def and_comm() -> Prop:
        return (P & Q) >> (Q & P)

    @thy.proof(and_comm)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        ctx.split()
        with ctx.focus():
            ctx.exact(ctx.and_right(h))
        with ctx.focus():
            ctx.exact(ctx.and_left(h))

    @thy.theorem
    def or_comm() -> Prop:
        return (P | Q) >> (Q | P)

    @thy.proof(or_comm)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        hp, hq = ctx.cases(h)
        with ctx.focus():
            ctx.right()
            ctx.exact(hp)
        with ctx.focus():
            ctx.left()
            ctx.exact(hq)

    @thy.theorem
    def curry() -> Prop:
        return ((P & Q) >> R) >> Implies(P, Q, R)

    @thy.proof(curry)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        hp = ctx.intro()
        hq = ctx.intro()
        ctx.apply(h)
        ctx.exact(ctx.and_intro(hp, hq))

    @thy.theorem
    def and_comm_inst() -> Prop:
        return ((A | B) & C) >> (C & (A | B))

    @thy.proof(and_comm_inst)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(and_comm, {P: A | B, Q: C}))

    return thy


def test_language_spec_examples_verify() -> None:
    thy = logic_theory()
    report = thy.check()
    assert report.ok, str(report)
    assert all(r.axioms == frozenset() for r in report.results)


def test_classical_theory() -> None:  # language-spec §10
    report = classical.check()
    assert report.ok, str(report)
    assert dne.axioms == peirce.axioms == {"classical.em"}
    assert em.to_json()["hash"] == STANDARD_AXIOMS["classical.em"]


def test_classical_principle_use() -> None:  # language-spec §11.6
    cthy = Theory("demo.classical", imports=[classical])

    @cthy.theorem
    def dne_again() -> Prop:
        return ~~P >> P

    @cthy.proof(dne_again)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        hp, hnp = ctx.cases(ctx.thm(em))
        with ctx.focus():
            ctx.exact(hp)
        with ctx.focus():
            ctx.exfalso()
            ctx.exact(ctx.mp(h, hnp))

    report = cthy.check()
    assert report.ok, str(report)
    assert dne_again.status is Status.VERIFIED
    assert dne_again.axioms == {"classical.em"}


def test_have_and_assumption() -> None:
    thy = Theory("demo.have")

    @thy.theorem
    def t() -> Prop:
        return Implies(P, P >> Q, Q)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        hp = ctx.intro()
        hpq = ctx.intro()
        hq = ctx.have(Q, name="hq")
        with ctx.focus():
            ctx.exact(ctx.mp(hpq, hp))
        with ctx.focus():
            assert hq.prop == Q
            ctx.assumption()

    assert single(thy)[0] is Status.VERIFIED


def test_forward_rules() -> None:
    thy = Theory("demo.forward")

    @thy.theorem
    def t() -> Prop:
        return Implies(P, ~P, Q | R)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        hp = ctx.intro()
        hnp = ctx.intro()
        bottom = ctx.mp(hnp, hp)
        ctx.exact(ctx.or_inl(ctx.absurd(bottom, Q), R))

    assert single(thy)[0] is Status.VERIFIED


def test_goal_display() -> None:  # language-spec §6.6
    seen: list[str] = []
    thy = Theory("demo.display")

    @thy.theorem
    def t() -> Prop:
        return (P >> Q) >> (P >> Q)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        hpq = ctx.intro()
        hp = ctx.intro()
        seen.append(str(ctx))
        ctx.exact(ctx.mp(hpq, hp))
        seen.append(str(ctx))

    assert thy.check().ok
    assert seen == ["goal 1/1\n  h1 : P → Q\n  h2 : P\n  ⊢ Q", "no goals"]


# --- language-spec §11.7 and §5.7 failures --------------------------------------------


def failing(body: object, statement: Prop = P >> P) -> tuple[Status, str]:
    thy = Theory("demo.fail")

    @thy.theorem
    def t() -> Prop:
        return statement

    thy.proof(t)(body)  # type: ignore[arg-type]
    return single(thy)


def test_tactic_on_wrong_goal_shape() -> None:
    status, text = failing(lambda ctx: ctx.split())
    assert status is Status.REJECTED and "TacticError" in text and "[elaboration]" in text


def test_scope_error() -> None:
    def body(ctx: ProofContext) -> None:
        h = ctx.intro()
        _hp, hq = ctx.cases(h)  # hq belongs to the second goal
        with ctx.focus():
            ctx.right()
            ctx.exact(hq)

    status, text = failing(body, (P | Q) >> (Q | P))
    assert status is Status.REJECTED and "ScopeError" in text


def test_open_goals_leave_theorem_unproven() -> None:
    status, text = failing(lambda ctx: (ctx.intro(), ctx.split()), P >> (P & P))
    assert status is Status.UNPROVEN and "open goals" in text


def test_missing_proof_is_unproven() -> None:
    thy = Theory("demo.none")

    @thy.theorem
    def t() -> Prop:
        return P >> P

    assert single(thy) == (Status.UNPROVEN, "")


def test_python_exception_rejects_with_location() -> None:
    def body(ctx: ProofContext) -> None:
        raise ValueError("boom")

    status, text = failing(body)
    assert status is Status.REJECTED and "ValueError: boom" in text and "test_theory.py:" in text


def test_substitution_outside_statement() -> None:
    thy = logic_theory()
    and_comm = next(d for d in thy.environment() if d.name.endswith(".and_comm"))

    @thy.theorem
    def bad() -> Prop:
        return P >> P

    @thy.proof(bad)
    def _(ctx: ProofContext) -> None:
        ctx.thm(and_comm, {R: C})

    assert statuses(thy)["bad"] is Status.REJECTED


def test_reference_to_later_declaration() -> None:
    thy = Theory("demo.order")

    @thy.theorem
    def first() -> Prop:
        return P >> P

    @thy.theorem
    def second() -> Prop:
        return P >> P

    @thy.proof(first)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(second))

    @thy.proof(second)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.intro())

    result = statuses(thy)
    assert result == {"first": Status.REJECTED, "second": Status.VERIFIED}


def test_reference_to_unverified_theorem() -> None:
    thy = Theory("demo.chain")

    @thy.theorem
    def broken() -> Prop:
        return P >> Q

    @thy.proof(broken)
    def _(ctx: ProofContext) -> None:
        ctx.intro()

    @thy.theorem
    def user() -> Prop:
        return P >> Q

    @thy.proof(user)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(broken))

    assert statuses(thy) == {"broken": Status.UNPROVEN, "user": Status.REJECTED}


def test_theorem_from_unimported_theory() -> None:
    other = logic_theory()
    and_comm = next(d for d in other.environment() if d.name.endswith(".and_comm"))
    thy = Theory("demo.isolated")

    @thy.theorem
    def t() -> Prop:
        return (P & Q) >> (Q & P)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(and_comm))

    status, text = single(thy)
    assert status is Status.REJECTED and "import its theory" in text


def test_disallowed_axiom_rejects_environment() -> None:  # language-spec §5.6
    thy = Theory("demo.axioms")

    @thy.axiom
    def strong() -> Prop:
        return P

    @thy.theorem
    def anything() -> Prop:
        return Q

    @thy.proof(anything)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(strong, {P: Q}))

    report = thy.check()
    [result] = report.results
    assert result.status is Status.REJECTED
    assert result.diagnostics[0].stage == "environment"
    allowed = thy.check(allowed_axioms={"demo.axioms.strong"})
    assert allowed.ok and anything.axioms == {"demo.axioms.strong"}


def test_unknown_allowed_axiom_is_api_misuse() -> None:
    with pytest.raises(DeclarationError):
        Theory("demo.x").check(allowed_axioms={"demo.x.nothing"})


# --- declarations -----------------------------------------------------------------------


def test_declaration_errors() -> None:
    thy = Theory("demo.decl")

    @thy.theorem
    def t() -> Prop:
        return P

    with pytest.raises(DeclarationError):
        thy.theorem(t)  # type: ignore[arg-type]
    with pytest.raises(DeclarationError):

        @thy.theorem
        def t() -> Prop:
            return Q

    with pytest.raises(DeclarationError):

        @thy.theorem  # type: ignore[arg-type]
        def with_param(x: int) -> Prop:
            return P

    with pytest.raises(DeclarationError):

        @thy.theorem
        def not_prop() -> Prop:
            return True  # type: ignore[return-value]

    thy.proof(t)(lambda ctx: None)
    with pytest.raises(DeclarationError):
        thy.proof(t)
    with pytest.raises(DeclarationError):
        Theory("bad name")


def test_duplicate_hypothesis_names() -> None:
    def body(ctx: ProofContext) -> None:
        ctx.intro("h")
        ctx.intro("h")

    status, text = failing(body, Implies(P, Q, P))
    assert status is Status.REJECTED and "already used" in text


def test_focus_must_close_goal() -> None:
    def body(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.split()
        with ctx.focus():
            pass

    status, text = failing(body, P >> (P & P))
    assert status is Status.REJECTED and "not closed" in text


def test_exfalso_and_falsehood_goal() -> None:
    def body(ctx: ProofContext) -> None:
        h = ctx.intro()
        ctx.exfalso()
        assert ctx.goals[0].target == Falsehood
        ctx.exact(h)

    assert failing(body, Falsehood >> P)[0] is Status.VERIFIED


# --- export and kernel re-verification --------------------------------------------------


def test_export_round_trip(tmp_path: Path) -> None:
    cthy = Theory("demo.export", imports=[classical])

    @cthy.theorem
    def em_q() -> Prop:
        return Q | ~Q

    @cthy.proof(em_q)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(em, {P: Q}))

    with pytest.raises(AxwError):
        cthy.export(tmp_path / "early.axwp")
    assert cthy.check().ok
    path = cthy.export(tmp_path / "demo.axwp")
    data = path.read_bytes()
    report = check_bundle(data, STANDARD_AXIOMS)
    assert report.ok
    assert [r.name for r in report.results] == [
        "classical.em",
        "classical.dne",
        "classical.peirce",
        "demo.export.em_q",
    ]
    bundle = json.loads(data)
    assert bundle["theory"] == "demo.export"


def test_export_skips_unverified_theorems(tmp_path: Path) -> None:
    thy = Theory("demo.partial")

    @thy.theorem
    def good() -> Prop:
        return P >> P

    @thy.proof(good)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.intro())

    @thy.theorem
    def open_goal() -> Prop:
        return P >> Q

    thy.check()
    bundle = json.loads(thy.export(tmp_path / "p.axwp").read_text(encoding="utf-8"))
    assert [d["name"] for d in bundle["declarations"]] == ["demo.partial.good"]


def test_elaboration_is_deterministic() -> None:
    first = logic_theory()
    second = logic_theory()
    first.check()
    second.check()
    assert first._export == second._export


def test_tactic_error_type_is_public() -> None:
    assert issubclass(TacticError, AxwError) and issubclass(ScopeError, AxwError)
