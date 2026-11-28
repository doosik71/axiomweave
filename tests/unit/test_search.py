"""Goal-directed theorem search `ctx.search()` (ai-spec §4)."""

from collections.abc import Callable

import pytest

from axiomweave import Eq, ForAll, ProofContext, Prop, Status, Theory, Var
from axiomweave.ai.search import SearchResult
from axiomweave.lib.arithmetic.peano import Nat, add, arith, mul, succ, zero
from axiomweave.lib.logic.classical import classical
from axiomweave.lib.logic.propositional import propositional

P, Q, R = Prop.symbol("P"), Prop.symbol("Q"), Prop.symbol("R")
m, n = Var("m", Nat), Var("n", Nat)


def run(
    statement: Prop,
    body: Callable[[ProofContext], None],
    imports: tuple[Theory, ...] = (arith, propositional, classical),
    extra: Callable[[Theory], None] | None = None,
) -> object:
    thy = Theory("demo.search", imports=list(imports))
    if extra is not None:
        extra(thy)

    @thy.theorem
    def t() -> Prop:
        return statement

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        body(ctx)

    return thy.check().results[-1]


def first_closes(seen: list[tuple[SearchResult, ...]]) -> Callable[[ProofContext], None]:
    def body(ctx: ProofContext) -> None:
        while ctx.goals[0].target.tag == "forall" and not seen:
            ctx.intro()
        results = ctx.search()
        seen.append(results)
        assert not results[0].premises
        ctx.exact(results[0].fact)

    return body


def test_equation_with_instantiated_universals() -> None:
    seen: list[tuple[SearchResult, ...]] = []
    result = run(ForAll([m, n], Eq(add(m, n), add(n, m))), first_closes(seen))
    assert result.status is Status.VERIFIED, str(result)  # type: ignore[attr-defined]
    top = seen[0][0]
    assert top.name == "arith.add_comm"
    assert str(top) == "arith.add_comm : ctx.spec(ctx.thm(add_comm), m, n)"
    assert top.axioms == {"arith.add_succ", "arith.add_zero", "arith.induction"}


def test_universal_goal_matches_without_stripping() -> None:
    seen: list[tuple[SearchResult, ...]] = []

    def body(ctx: ProofContext) -> None:
        results = ctx.search()
        seen.append(results)
        ctx.exact(results[0].fact)

    result = run(ForAll(n, Eq(mul(n, succ(zero)), n)), body)
    assert result.status is Status.VERIFIED, str(result)  # type: ignore[attr-defined]
    assert seen[0][0].name == "arith.mul_one"
    assert str(seen[0][0]) == "arith.mul_one : ctx.thm(mul_one)"


def test_schematic_atoms_and_predicates() -> None:
    seen: list[tuple[SearchResult, ...]] = []

    def body(ctx: ProofContext) -> None:
        results = ctx.search()
        seen.append(results)
        ctx.exact(results[0].fact)

    result = run((P >> Q) >> ((Q >> R) >> (P >> R)), body)
    assert result.status is Status.VERIFIED  # type: ignore[attr-defined]
    assert seen[0][0].name == "propositional.imp_trans"
    # Miller pattern: ∀n. P(n) in the induction axiom matches a ∀ goal.
    names: list[tuple[str, int]] = []

    def induction_body(ctx: ProofContext) -> None:
        names.extend((r.name, len(r.premises)) for r in ctx.search(limit=20))

    run(ForAll(n, Eq(mul(n, succ(zero)), n)), induction_body)
    assert ("arith.induction", 2) in names


def test_ranking_and_no_progress_filter() -> None:
    collected: list[tuple[SearchResult, ...]] = []

    def body(ctx: ProofContext) -> None:
        collected.append(ctx.search(limit=50))

    run(Q & P, body)
    results = collected[0]
    keys = [
        (len(r.premises), r.generic, "classical.em" in r.axioms, len(r.axioms)) for r in results
    ]
    assert keys == sorted(keys)
    assert results[0].name == "propositional.and_comm"
    assert all(Q & P not in r.premises for r in results)
    assert any(r.generic for r in results)  # e.g. false_elim, after the specific ones


def test_variables_only_in_premises_are_excluded() -> None:
    a, b, c = Var("a", Nat), Var("b", Nat), Var("c", Nat)
    names: list[str] = []

    def lemma(thy: Theory) -> None:
        @thy.theorem
        def eq_chain() -> Prop:
            return ForAll([a, b, c], Eq(a, b) >> (Eq(b, c) >> Eq(a, c)))

        @thy.proof(eq_chain)
        def _(ctx: ProofContext) -> None:
            ctx.intro()
            ctx.intro()
            ctx.intro()
            f = ctx.intro()
            g = ctx.intro()
            ctx.exact(ctx.trans(f, g))

    def body(ctx: ProofContext) -> None:
        ctx.intro()
        ctx.intro()
        names.extend(r.name for r in ctx.search(limit=50))

    run(ForAll([m, n], Eq(m, n)), body, imports=(arith,), extra=lemma)
    assert "demo.search.eq_chain" not in names


def test_search_does_not_change_the_state() -> None:
    states: list[str] = []

    def body(ctx: ProofContext) -> None:
        h = ctx.intro()
        states.append(str(ctx))
        ctx.search()
        states.append(str(ctx))
        ctx.exact(h)

    result = run(P >> P, body)
    assert result.status is Status.VERIFIED  # type: ignore[attr-defined]
    assert states[0] == states[1]


def test_no_candidates_and_limit() -> None:
    seen: list[object] = []

    def body(ctx: ProofContext) -> None:
        seen.append(ctx.search())
        seen.append(len(ctx.search(limit=1)))
        with pytest.raises(Exception, match="positive int"):
            ctx.search(limit=0)
        ctx.intro()
        ctx.assumption()

    run(P >> P, body, imports=())
    assert seen == [(), 0]
