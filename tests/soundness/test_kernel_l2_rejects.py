"""Invalid L2 certificates are rejected with the right code (logic-spec §13.9–13.10,
kernel-spec §14). Hashes are recomputed so that the intended defect is what fails."""

import pytest

from axiomweave.kernel import STANDARD_AXIOMS, check_bundle
from axiomweave.kernel.errors import E_FORMAT, E_FRAGMENT, E_RULE_MISMATCH, E_TYPE
from tests.helpers import (
    FALSE,
    P,
    Q,
    all_i,
    app,
    bundle,
    const,
    encode,
    eq,
    eq_e,
    eq_refl,
    forall,
    hyp,
    imp,
    imp_i,
    l1_bundle,
    l2_bundle,
    pred,
    sort,
    theorem,
    var,
)

U = "demo.eq.U"
V = "demo.eq.V"
A = "demo.eq.a"
B = "demo.eq.b"
F = "demo.eq.f"
EVEN = "demo.eq.Even"
SIGNATURE = (
    sort(U),
    sort(V),
    const(A, [], U),
    const(B, [], V),
    const(F, [U], U),
    const(EVEN, [U], "prop"),
)
X, Y = var(1), var(0)  # under ∀x ∀y of sort U


def last_error(*decls: object) -> str | None:
    report = check_bundle(encode(l2_bundle(*SIGNATURE, *decls)), STANDARD_AXIOMS)
    assert report.bundle_ok, report.bundle_error
    result = report.results[-1]
    return result.error.code if result.error else None


def bundle_error(obj: object) -> str:
    report = check_bundle(encode(obj), STANDARD_AXIOMS)
    assert not report.bundle_ok and report.bundle_error is not None
    return report.bundle_error.code


def under_xy(hyp_prop: object, body: object, conclusion: object) -> tuple[object, object]:
    """Statement ∀x y. hyp → conclusion and proof ∀I ∀I →I h. body."""
    statement = forall(U, forall(U, imp(hyp_prop, conclusion)))
    return statement, all_i(U, all_i(U, imp_i("h", hyp_prop, body)))


# --- logic-spec §13.9 (3) ---------------------------------------------------------


def test_equality_between_different_sorts() -> None:
    bad = eq(app(A), app(B))
    t = theorem("demo.eq.sorts", imp(bad, bad), imp_i("h", bad, hyp("h")))
    assert last_error(t) == E_TYPE


def test_substitution_premise_does_not_match_motive() -> None:
    # Motive λz. Even(z) needs Even(x), but the second premise proves x = x.
    statement, proof = under_xy(
        eq(X, Y), eq_e(hyp("h"), pred(EVEN, var(0)), eq_refl(X)), pred(EVEN, Y)
    )
    assert last_error(theorem("demo.eq.motive", statement, proof)) == E_RULE_MISMATCH


def test_substitution_first_premise_not_an_equality() -> None:
    even_x = pred(EVEN, var(0))
    statement = forall(U, imp(even_x, even_x))
    proof = all_i(U, imp_i("h", even_x, eq_e(hyp("h"), pred(EVEN, var(0)), hyp("h"))))
    assert last_error(theorem("demo.eq.not_eq", statement, proof)) == E_RULE_MISMATCH


def test_motive_variable_of_wrong_sort() -> None:
    # The equality is between U terms, so the motive variable z has sort U and
    # z = b (with b : V) is ill-typed.
    statement, proof = under_xy(eq(X, Y), eq_e(hyp("h"), eq(var(0), app(B)), eq_refl(X)), eq(Y, X))
    assert last_error(theorem("demo.eq.motive_sort", statement, proof)) == E_TYPE


def test_equality_between_propositions_is_malformed() -> None:
    t = theorem("demo.eq.props", imp(eq(P, Q), eq(P, Q)), imp_i("h", eq(P, Q), hyp("h")))
    assert bundle_error(l2_bundle(*SIGNATURE, t)) == E_FORMAT


def test_equality_in_l1_bundle() -> None:
    e = eq(app(A), app(A))
    t = theorem("demo.eq.l1", e, eq_refl(app(A)))
    assert bundle_error(l1_bundle(*SIGNATURE, t)) == E_FRAGMENT


# --- logic-spec §13.10 additional cases -------------------------------------------


def test_motive_with_unbound_index() -> None:
    statement, proof = under_xy(eq(X, Y), eq_e(hyp("h"), eq(var(0), var(5)), eq_refl(X)), eq(Y, X))
    assert last_error(theorem("demo.eq.index", statement, proof)) == E_TYPE


def test_reflexivity_with_ill_typed_term() -> None:
    t = theorem("demo.eq.refl_bad", eq(app(F), app(F)), eq_refl(app(F)))
    assert last_error(t) == E_TYPE


def test_reflexivity_with_unbound_variable() -> None:
    t = theorem("demo.eq.refl_var", imp(FALSE, FALSE), imp_i("h", FALSE, eq_refl(var(0))))
    assert last_error(t) == E_TYPE


def test_conclusion_must_match_rewritten_motive() -> None:
    # A motive without the variable (λz. x = x) proves x = x again, not the claimed y = x.
    statement, proof = under_xy(eq(X, Y), eq_e(hyp("h"), eq(var(2), var(2)), eq_refl(X)), eq(Y, X))
    report = check_bundle(
        encode(l2_bundle(*SIGNATURE, theorem("demo.eq.concl", statement, proof))), STANDARD_AXIOMS
    )
    assert report.results[-1].error is not None
    assert report.results[-1].error.code == "E_CONCLUSION_MISMATCH"


@pytest.mark.parametrize(
    ("make", "fragment_bundle"),
    [
        (lambda: theorem("demo.logic.r", imp(P, P), eq_refl(app(A))), bundle),
        (lambda: theorem("demo.eq.r", eq(app(A), app(A)), eq_refl(app(A))), l1_bundle),
        (
            lambda: theorem("demo.eq.e", imp(P, P), imp_i("h", P, eq_e(hyp("h"), FALSE, hyp("h")))),
            l1_bundle,
        ),
    ],
)
def test_equality_rules_outside_l2(make: object, fragment_bundle: object) -> None:
    decls = SIGNATURE if fragment_bundle is l1_bundle else ()
    obj = fragment_bundle(*decls, make())  # type: ignore[operator]
    assert bundle_error(obj) == E_FRAGMENT


def test_lambda_still_outside_l2() -> None:
    t = theorem("demo.eq.lam", ["lam", U, FALSE], hyp("h"))
    assert bundle_error(l2_bundle(*SIGNATURE, t)) == E_FRAGMENT
