"""Intuitionistic propositional decision procedure `ctx.auto()` (ai-spec §3)."""

import itertools
from collections.abc import Callable
from pathlib import Path

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from axiomweave import (
    Eq,
    Exists,
    ForAll,
    ProofContext,
    Prop,
    ScopeError,
    Status,
    Theorem,
    Theory,
    Var,
)
from axiomweave.ai.propositional import Search, classical_hint
from axiomweave.core.expressions import Falsehood
from axiomweave.lib.logic.classical import classical, em
from axiomweave.lib.logic.propositional import propositional

P, Q, R = Prop.symbol("P"), Prop.symbol("Q"), Prop.symbol("R")


def auto_result(statement: Prop, name: str = "demo.auto", **kwargs: object) -> object:
    thy = Theory(name, imports=[classical])

    @thy.theorem
    def t() -> Prop:
        return statement

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.auto(**kwargs)  # type: ignore[arg-type]

    return thy.check().results[-1]


def message(result: object) -> str:
    return str(result.diagnostics[0])  # type: ignore[attr-defined]


@pytest.mark.parametrize(
    "statement",
    [
        ~~(P | ~P),
        ((P & Q) >> R) >> (P >> (Q >> R)),
        (P & (Q | R)) >> ((P & Q) | (P & R)),
        (P >> Q) >> (~Q >> ~P),
        ~~(((P >> Q) >> P) >> P),
        ~~~P >> ~P,
        ~(P | Q) >> (~P & ~Q),
        Falsehood >> P,
    ],
)
def test_proves_intuitionistic_tautologies(statement: Prop) -> None:
    result = auto_result(statement)
    assert result.status is Status.VERIFIED, str(result)  # type: ignore[attr-defined]
    assert result.axioms == set()  # type: ignore[attr-defined]


@pytest.mark.parametrize(
    "statement",
    [P | ~P, ~~P >> P, ((P >> Q) >> P) >> P, (P >> Q) | (Q >> P), (~P >> ~Q) >> (Q >> P)],
)
def test_classical_tautologies_are_not_intuitionistic(statement: Prop) -> None:
    result = auto_result(statement)
    assert result.status is Status.REJECTED  # type: ignore[attr-defined]
    assert "not provable in intuitionistic propositional logic" in message(result)
    assert "classically valid; it may need classical.em" in message(result)


def test_falsifying_valuation_hint() -> None:
    result = auto_result(P >> Q)
    assert "(false under P = true, Q = false)" in message(result)


def test_using_an_instance_of_em() -> None:
    thy = Theory("demo.auto.em", imports=[classical])

    @thy.theorem
    def peirce() -> Prop:
        return ((P >> Q) >> P) >> P

    @thy.proof(peirce)
    def _(ctx: ProofContext) -> None:
        ctx.auto(using=[ctx.thm(em, {P: P})])

    result = thy.check().results[-1]
    assert result.status is Status.VERIFIED, str(result)
    assert result.axioms == {"classical.em"}


def test_context_hypotheses_and_opaque_atoms() -> None:
    thy = Theory("demo.auto.fol")
    U = thy.sort("U")
    x = Var("x", U)
    S = Prop.symbol("S", U)

    @thy.theorem
    def t() -> Prop:
        return (ForAll(x, S(x)) >> Q) >> ((ForAll(x, S(x)) & R) >> (Q & R))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.intro()  # hypotheses become premises
        ctx.auto()

    assert thy.check().ok


def test_library_theorems_are_found() -> None:
    thy = Theory("demo.auto.lib")
    count = 0
    for decl in propositional.environment():
        if not (isinstance(decl, Theorem) and decl.theory is propositional):
            continue
        handle = thy.theorem(_constant(decl.statement, decl.name.rsplit(".", 1)[1]))

        @thy.proof(handle)
        def _(ctx: ProofContext) -> None:
            ctx.auto()

        count += 1
    report = thy.check()
    assert count == 34
    assert report.ok, str(report)


def _constant(statement: Prop, name: str) -> Callable[[], Prop]:
    def function() -> Prop:
        return statement

    function.__name__ = name
    return function


def test_limit_and_arguments() -> None:
    result = auto_result(~~(P | ~P), limit=1)
    assert "auto: search limit reached (1 steps)" in message(result)
    result = auto_result(P >> P, limit=0)
    assert "AxwTypeError" in message(result)


def test_scope_of_using() -> None:
    thy = Theory("demo.auto.scope")
    errors: list[Exception] = []

    @thy.theorem
    def t() -> Prop:
        return (P >> P) & (Q >> Q)

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.split()
        with ctx.focus():
            h = ctx.intro()
            ctx.exact(h)
        with ctx.focus():
            try:
                ctx.auto(using=[h])
            except ScopeError as exc:
                errors.append(exc)
            ctx.auto()

    assert thy.check().ok
    assert len(errors) == 1


def test_deterministic_derivation(tmp_path: Path) -> None:
    def certificate(index: int) -> bytes:
        thy = Theory("demo.auto.det")

        @thy.theorem
        def t() -> Prop:
            return ((P | Q) & (P >> R) & (Q >> R)) >> R

        @thy.proof(t)
        def _(ctx: ProofContext) -> None:
            ctx.auto()

        assert thy.check().ok
        return thy.export(tmp_path / f"{index}.axwp").read_bytes()

    assert certificate(1) == certificate(2)


# --- property: soundness via the kernel and agreement with truth tables --------------

ATOMS = [P, Q, R]
formulas = st.recursive(
    st.sampled_from([*ATOMS, Falsehood]),
    lambda sub: st.one_of(
        st.builds(lambda a, b: a & b, sub, sub),
        st.builds(lambda a, b: a | b, sub, sub),
        st.builds(lambda a, b: a >> b, sub, sub),
    ),
    max_leaves=8,
)


def classically_valid(prop: Prop) -> bool:
    def value(p: Prop, v: dict[Prop, bool]) -> bool:
        if p.tag == "false":
            return False
        if p.tag == "atom":
            return v[p]
        a, b = value(p.left, v), value(p.right, v)
        return {"and": a and b, "or": a or b, "imp": (not a) or b}[p.tag]

    return all(
        value(prop, dict(zip(ATOMS, values, strict=True)))
        for values in itertools.product((True, False), repeat=len(ATOMS))
    )


@settings(max_examples=150, deadline=None)
@given(formulas)
def test_random_formulas(prop: Prop) -> None:
    result = auto_result(prop, name="demo.auto.random")
    if result.status is Status.VERIFIED:  # type: ignore[attr-defined]
        assert classically_valid(prop)  # kernel-checked, hence intuitionistically valid
    else:
        text = message(result)
        assert "not provable in intuitionistic propositional logic" in text
        if not classically_valid(prop):
            assert "false under" in text


def test_search_and_hint_directly() -> None:
    assert Search(100).prove((P, P >> Q), Q) is not None
    assert Search(100).prove((), P | ~P) is None
    assert classical_hint((), P | ~P) == "classically valid; it may need classical.em"


# --- first-order rules (ai-spec §6) ------------------------------------------------------


def fol_result(build: Callable[..., Prop], **kwargs: object) -> object:
    thy = Theory("demo.auto.fo")
    U = thy.sort("U")
    a = thy.const("a", [], U)
    f = thy.const("f", [U], U)
    x, y, z = Var("x", U), Var("y", U), Var("z", U)
    A, B = Prop.symbol("A", U), Prop.symbol("B", U, U)
    statement = build(U=U, a=a, f=f, x=x, y=y, z=z, A=A, B=B)

    @thy.theorem
    def t() -> Prop:
        return statement

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.auto(**kwargs)  # type: ignore[arg-type]

    return thy.check().results[-1]


@pytest.mark.parametrize(
    "build",
    [
        lambda x, y, B, **_: ForAll(x, ForAll(y, B(x, y))) >> ForAll(y, ForAll(x, B(x, y))),
        lambda x, y, B, **_: Exists(x, ForAll(y, B(x, y))) >> ForAll(y, Exists(x, B(x, y))),
        lambda x, A, f, a, **_: ForAll(x, A(x)) >> A(f(a)),
        lambda x, A, **_: ForAll(x, ~A(x)) >> ~Exists(x, A(x)),
        lambda x, y, z, f, **_: ForAll(
            [x, y, z], Eq(x, y) >> (Eq(z, y) >> Eq(f(x), f(z)))
        ),  # symmetry, transitivity and congruence
        lambda a, f, **_: Eq(f(a), f(a)),
    ],
    ids=["all_comm", "ex_all", "instance", "all_not", "eq_closure", "refl"],
)
def test_first_order_goals(build: Callable[..., Prop]) -> None:
    result = fol_result(build)
    assert result.status is Status.VERIFIED, str(result)  # type: ignore[attr-defined]


def test_first_order_failure_is_bounded() -> None:
    drinker = fol_result(lambda x, y, A, **_: Exists(x, A(x) >> ForAll(y, A(y))))
    assert drinker.status is Status.REJECTED  # type: ignore[attr-defined]
    text = message(drinker)
    assert "auto: no proof found within depth 3 (first-order search is incomplete)" in text
    assert "false under" not in text and "classically valid" not in text


def test_first_order_can_be_turned_off_and_depth_limits_instances() -> None:
    off = fol_result(lambda x, A, f, a, **_: ForAll(x, A(x)) >> A(f(a)), first_order=False)
    assert "not provable in intuitionistic propositional logic" in message(off)
    shallow = fol_result(lambda x, A, f, a, **_: ForAll(x, A(x)) >> A(f(a)), depth=0)
    assert "within depth 0" in message(shallow)
    deep = fol_result(lambda x, A, f, a, **_: ForAll(x, A(x)) >> A(f(a)), depth=1)
    assert deep.status is Status.VERIFIED  # type: ignore[attr-defined]
    bad = fol_result(lambda x, A, **_: ForAll(x, A(x)) >> ForAll(x, A(x)), depth=-1)
    assert "AxwTypeError" in message(bad)


def test_eigenvariable_names_avoid_used_names() -> None:
    thy = Theory("demo.auto.names")
    U = thy.sort("U")
    x = Var("x", U)
    A = Prop.symbol("A", U)

    @thy.theorem
    def t() -> Prop:
        return ForAll(x, A(x) >> A(x)) & ForAll(x, A(x) >> A(x))

    @thy.proof(t)
    def _(ctx: ProofContext) -> None:
        ctx.split()
        with ctx.focus():
            ctx.intro("x")  # uses the name x in this proof
            h = ctx.intro()
            ctx.exact(h)
        with ctx.focus():
            ctx.auto()  # must pick another eigenvariable name

    assert thy.check().ok
