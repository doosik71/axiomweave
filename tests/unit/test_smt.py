"""Z3 counterexample search (interop-spec §4)."""

import importlib

import pytest

from axiomweave import (
    AxwTypeError,
    BackendUnavailableError,
    Eq,
    Exists,
    ForAll,
    Ne,
    ProofContext,
    Prop,
    ScopeError,
    Theory,
    Var,
)
from axiomweave.backends import smt
from axiomweave.backends.smt import counterexample
from axiomweave.lib.arithmetic.peano import Nat, add, add_zero, arith, mul, numeral, zero

pytest.importorskip("z3")

thy = Theory("demo.smt", imports=[arith])
U = thy.sort("U")
a = thy.const("a", [], U)
Even = thy.const("Even", [U], Prop)
f = thy.const("f", [U], U)
g = thy.const("g", [Nat], Nat)
x = Var("x", U)
m, n = Var("m", Nat), Var("n", Nat)
P, Q = Prop.symbol("P"), Prop.symbol("Q")
S = Prop.symbol("S", U)


def lines(result: object) -> list[str]:
    return str(result).splitlines()


def test_propositional() -> None:
    result = counterexample(P >> Q)
    assert result.status == "found" and result.found and result.checked
    assert lines(result)[1:] == ["  P = true", "  Q = false"]
    assert counterexample(P >> P).status == "none"


def test_classically_valid_is_not_a_proof() -> None:
    # P ∨ ¬P has no classical counterexample but needs classical.em (§4.1).
    result = counterexample(P | ~P)
    assert result.status == "none"
    assert result.model is None
    assert lines(result)[0].startswith("no counterexample (Z3 ")


def test_first_order_model() -> None:
    result = counterexample(S(a) >> ForAll(x, S(x)))
    assert result.found and result.checked
    assert result.model is not None
    ((sort, elements),) = result.model.domains
    assert sort == "U" and len(elements) >= 2
    values = dict(result.model.values)
    assert values[f"S({values['a']})"] == "true"
    assert "false" in values.values()
    assert counterexample(ForAll(x, S(x)) >> S(a)).status == "none"


def test_leading_universals_become_witnesses() -> None:
    result = counterexample(ForAll(x, Eq(f(x), x)))
    assert result.found and result.checked
    values = dict(result.model.values) if result.model else {}
    assert values[f"f({values['x']})"] != values["x"]


def test_witness_name_avoids_free_variables() -> None:
    result = counterexample(ForAll(x, Eq(f(x), x)), using=[Eq(f(x), x)])
    assert result.found
    names = [name for name, _ in result.model.values] if result.model else []
    assert "x" in names and "x1" in names


def test_standard_arithmetic() -> None:
    result = counterexample(ForAll(n, Eq(add(n, n), n)))
    assert result.found and result.checked
    assert result.model is not None
    assert dict(result.model.values)["n"] != "0"
    assert counterexample(ForAll([m, n], Eq(add(m, n), add(n, m)))).status == "none"
    assert counterexample(ForAll(n, Ne(mul(n, n), numeral(2)))).status == "none"
    assert counterexample(~Exists(n, Eq(add(n, numeral(1)), zero))).status == "none"
    assert counterexample(Exists(n, Eq(add(n, numeral(1)), zero))).found


def test_uninterpreted_nat_function_is_non_negative() -> None:
    # Over Int, g(0) = -1 would make "∃n. g(0) + 1 = 0" satisfiable; over Nat it is not.
    assert counterexample(Ne(add(g(zero), numeral(1)), zero)).status == "none"
    result = counterexample(ForAll(n, Eq(g(n), n)))
    assert result.found
    assert any(name.startswith("g(") for name, _ in result.model.values)  # type: ignore[union-attr]


def test_nat_quantifier_in_premise_is_not_rechecked() -> None:
    premise = ForAll(m, Eq(add(g(m), zero), g(m)))
    result = counterexample(Eq(g(n), n), using=[premise], timeout_ms=2000)
    assert result.found and not result.checked
    assert "premises: context + 1 using, not re-checked" in lines(result)[0]
    values = dict(result.model.values) if result.model else {}
    assert values[f"g({values['n']})"] != values["n"]


def test_output_is_deterministic() -> None:
    goal = S(a) >> ForAll(x, S(x))
    assert str(counterexample(goal)) == str(counterexample(goal))


def test_counterexample_leaves_the_proof_unchanged() -> None:
    demo = Theory("demo.smt.ctx", imports=[thy])
    results: list[smt.Counterexample] = []

    @demo.theorem
    def t() -> Prop:
        return (P >> Q) >> (P >> Q)

    @demo.proof(t)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        p = ctx.intro()
        before = str(ctx)
        results.append(ctx.counterexample())
        assert str(ctx) == before
        ctx.exact(ctx.mp(h, p))

    assert demo.check().ok
    assert results[0].status == "none"


def test_context_hypotheses_and_using() -> None:
    demo = Theory("demo.smt.using", imports=[thy])
    results: list[smt.Counterexample] = []

    @demo.theorem
    def t() -> Prop:
        return ForAll(n, Eq(add(n, zero), n))

    @demo.proof(t)
    def _(ctx: ProofContext) -> None:
        k = ctx.intro()
        results.append(ctx.counterexample())
        results.append(ctx.counterexample(using=[ctx.spec(ctx.thm(add_zero), k)]))
        results.append(ctx.counterexample(using=[Eq(add(k, zero), k)]))
        with pytest.raises(ScopeError):
            ctx.counterexample(using=[Eq(add(m, zero), m)])
        ctx.exact(ctx.spec(ctx.thm(add_zero), k))

    assert demo.check().ok
    # Standard arithmetic makes the goal true in ℕ already.
    assert [r.status for r in results] == ["none", "none", "none"]
    assert results[1].premises == "context + 1 using"


def test_hypotheses_are_premises() -> None:
    demo = Theory("demo.smt.hyp", imports=[thy])
    results: list[smt.Counterexample] = []

    @demo.theorem
    def t() -> Prop:
        return Even(a) >> Exists(x, Even(x))

    @demo.proof(t)
    def _(ctx: ProofContext) -> None:
        h = ctx.intro()
        results.append(ctx.counterexample())
        ctx.exists(a)
        ctx.exact(h)

    assert demo.check().ok
    assert results[0].status == "none"
    assert counterexample(Exists(x, Even(x))).found


def test_disagreeing_evaluator_gives_unknown(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(smt._Reader, "holds", lambda self, prop, env=None: True)
    result = counterexample(P >> Q)
    assert result.status == "unknown"
    assert "does not confirm" in result.reason


def test_missing_z3(monkeypatch: pytest.MonkeyPatch) -> None:
    real = importlib.import_module

    def fake(name: str, *args: object) -> object:
        if name == "z3":
            raise ImportError("no z3")
        return real(name, *args)  # type: ignore[arg-type]

    monkeypatch.setattr(importlib, "import_module", fake)
    with pytest.raises(BackendUnavailableError, match="uv sync --extra smt"):
        counterexample(P)


def test_argument_errors() -> None:
    with pytest.raises(AxwTypeError):
        counterexample("P")
    with pytest.raises(AxwTypeError):
        counterexample(P, using=["Q"])
    with pytest.raises(AxwTypeError):
        counterexample(P, timeout_ms=0)
