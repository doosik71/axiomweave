"""Propositions of the DSL (language-spec §4)."""

import pytest

from axiomweave import And, AxwTypeError, Falsehood, Iff, Implies, Not, Or, Prop, Truth

P, Q, R = (Prop.symbol(name) for name in ("P", "Q", "R"))


def test_atoms_are_identified_by_name() -> None:
    assert Prop.symbol("P") == P
    assert hash(Prop.symbol("P")) == hash(P)
    assert P != Q


@pytest.mark.parametrize("name", ["", "1P", "a-b", "and", "or", "imp", "false", "é", 3])
def test_invalid_atom_names(name: object) -> None:
    with pytest.raises(AxwTypeError):
        Prop.symbol(name)  # type: ignore[arg-type]


def test_operators_match_constructors() -> None:
    assert (P & Q) == And(P, Q)
    assert (P | Q) == Or(P, Q)
    assert (P >> Q) == Implies(P, Q)
    assert ~P == Not(P)


def test_implies_is_right_associative() -> None:
    assert Implies(P, Q, R) == P >> (Q >> R)
    assert Implies(P, Q, R) != (P >> Q) >> R  # what Python builds for P >> Q >> R


def test_abbreviations_expand_on_construction() -> None:  # language-spec §4.4
    assert Not(P) == Implies(P, Falsehood)
    assert ~~P == Implies(Implies(P, Falsehood), Falsehood)
    assert Truth == Implies(Falsehood, Falsehood)
    assert Iff(P, Q) == And(Implies(P, Q), Implies(Q, P))


def test_no_associativity() -> None:
    assert (P & Q & R) == And(And(P, Q), R)
    assert (P & Q & R) != And(P, And(Q, R))


@pytest.mark.parametrize(
    "build",
    [
        lambda: bool(P),
        lambda: P and Q,
        lambda: not P,
    ],
)
def test_no_truth_value(build: object) -> None:  # language-spec §4.6
    with pytest.raises(AxwTypeError):
        build()  # type: ignore[operator]


def test_no_coercion_of_python_values() -> None:
    with pytest.raises(TypeError):
        P & True  # type: ignore[operator]
    with pytest.raises(TypeError):
        1 >> P  # type: ignore[operator]
    with pytest.raises(AxwTypeError):
        And(P, True)  # type: ignore[arg-type]
    with pytest.raises(AxwTypeError):
        Implies(P)


def test_no_ordering() -> None:
    with pytest.raises(TypeError):
        P < Q  # type: ignore[operator]  # noqa: B015


def test_immutable() -> None:
    with pytest.raises(AttributeError):
        P._node = ("atom", "Q")  # type: ignore[misc]


@pytest.mark.parametrize(
    ("prop", "text"),
    [
        (Implies(P, Q, R), "P → Q → R"),
        ((P >> Q) >> R, "(P → Q) → R"),
        ((P & Q) >> (R | P), "P ∧ Q → R ∨ P"),
        (P & (Q | R), "P ∧ (Q ∨ R)"),
        ((P & Q) & R, "(P ∧ Q) ∧ R"),
        (~P, "P → ⊥"),
    ],
)
def test_str_uses_minimal_parentheses(prop: Prop, text: str) -> None:  # language-spec §4.7
    assert str(prop) == text


def test_repr_round_trips() -> None:
    prop = Implies(P & Q, ~R)
    assert eval(repr(prop), {"Prop": Prop, "And": And, "Or": Or, "Implies": Implies,
                             "Falsehood": Falsehood}) == prop  # fmt: skip


def test_kernel_encoding_and_substitution() -> None:
    assert (P >> ~Q).to_json() == ["imp", ["atom", "P"], ["imp", ["atom", "Q"], ["false"]]]
    assert (P >> Q).atoms() == {"P", "Q"}
    assert (P >> Q).substitute({"P": Q, "Q": P}) == (Q >> P)
