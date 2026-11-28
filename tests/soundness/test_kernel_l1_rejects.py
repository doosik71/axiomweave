"""Invalid L1 certificates are rejected with the right code (logic-spec §12.12–12.13,
kernel-spec §13.9). Hashes are recomputed so that the intended defect is what fails."""

import pytest

from axiomweave.kernel import REJECTED, STANDARD_AXIOMS, VERIFIED, check_bundle
from axiomweave.kernel.errors import (
    E_FORMAT,
    E_FRAGMENT,
    E_HYP_NOT_FRESH,
    E_RULE_MISMATCH,
    E_SUBST_DOMAIN,
    E_TYPE,
    E_UNKNOWN_DECL,
    E_VAR_ESCAPE,
)
from tests.helpers import (
    FALSE,
    P,
    all_e,
    all_i,
    and_,
    and_e1,
    app,
    axiom,
    bundle,
    const,
    encode,
    ex_e,
    ex_i,
    exists,
    forall,
    hyp,
    imp,
    imp_i,
    l1_bundle,
    lam,
    pred,
    pvar,
    ref,
    sort,
    theorem,
    var,
)

U = "demo.fol.U"
V = "demo.fol.V"
A = "demo.fol.a"
B = "demo.fol.b"
F = "demo.fol.f"
EVEN = "demo.fol.Even"
SIGNATURE = (
    sort(U),
    sort(V),
    const(A, [], U),
    const(B, [], V),
    const(F, [U], U),
    const(EVEN, [U], "prop"),
)

PX = pvar("P", var(0))
ALL_P = forall(U, PX)
ALL_P_ID = theorem("demo.fol.all_p_id", imp(ALL_P, ALL_P), imp_i("h", ALL_P, hyp("h")))
ALL_P_REFL = theorem(  # ∀x. P(x) → P(x)
    "demo.fol.all_refl", forall(U, imp(PX, PX)), all_i(U, imp_i("h", PX, hyp("h")))
)


def results(*decls: object, signature: tuple[object, ...] = SIGNATURE) -> list[str | None]:
    """Error code per declaration after the signature (None = accepted/verified)."""
    report = check_bundle(encode(l1_bundle(*signature, *decls)), STANDARD_AXIOMS)
    assert report.bundle_ok, report.bundle_error
    tail = report.results[len(signature) :]
    for r in tail:
        assert (r.status == REJECTED) == (r.error is not None)
    return [r.error.code if r.error else None for r in tail]


def last_error(*decls: object) -> str | None:
    return results(*decls)[-1]


def bundle_error(obj: object) -> str:
    report = check_bundle(encode(obj), STANDARD_AXIOMS)
    assert not report.bundle_ok and report.bundle_error is not None
    return report.bundle_error.code


# --- logic-spec §12.12 (5) ------------------------------------------------------


def test_witness_variable_escapes_exists_elimination() -> None:
    # From ∃x. P(x) "derive" P(x): the body concludes P(#0), which mentions the witness.
    ex_p = exists(U, PX)
    proof = imp_i("h", ex_p, ex_e(hyp("h"), "k", hyp("k")))
    bad = theorem("demo.fol.escape", imp(ex_p, ex_p), proof)
    assert last_error(bad) == E_VAR_ESCAPE


def test_hypothesis_cannot_mention_unbound_variable() -> None:
    # Assume P(x) with no x in scope, then generalise: the hypothesis is ill-scoped
    # (the closed statement P(a) → ∀x. P(x) is not derivable).
    pa = pvar("P", app(A))
    bad = theorem("demo.fol.gen", imp(pa, ALL_P), imp_i("h", PX, all_i(U, hyp("h"))))
    assert last_error(bad) == E_TYPE


def test_universal_elimination_with_term_of_wrong_sort() -> None:
    # The statement is well typed; only the proof instantiates ∀x:U with b : V.
    bad = theorem(
        "demo.fol.sort", imp(ALL_P, pvar("P", app(A))), imp_i("h", ALL_P, all_e(hyp("h"), app(B)))
    )
    assert last_error(bad) == E_TYPE


def test_open_statement() -> None:
    bad = theorem("demo.fol.open", imp(PX, PX), imp_i("h", PX, hyp("h")))
    assert last_error(bad) == E_TYPE


def test_schematic_name_used_with_two_arities() -> None:
    statement = imp(and_(P, pvar("P", app(A))), P)
    bad = theorem(
        "demo.fol.arity", statement, imp_i("h", and_(P, pvar("P", app(A))), and_e1(hyp("h")))
    )
    assert last_error(bad) == E_TYPE


def test_lambda_tag_is_outside_l1() -> None:
    bad = theorem("demo.fol.lam", ["lam", U, FALSE], {"rule": "hyp", "name": "h"})
    assert bundle_error(l1_bundle(*SIGNATURE, bad)) == E_FRAGMENT


@pytest.mark.parametrize(
    "statement",
    [
        imp(forall("demo.fol.W", FALSE), forall("demo.fol.W", FALSE)),  # unknown sort
        imp(pred("demo.fol.Odd", app(A)), pred("demo.fol.Odd", app(A))),  # unknown const
    ],
)
def test_undeclared_sort_or_constant(statement: object) -> None:
    bad = theorem("demo.fol.undeclared", statement, imp_i("h", statement[1], hyp("h")))  # type: ignore[index]
    assert last_error(bad) == E_UNKNOWN_DECL


def test_sort_declared_after_use() -> None:
    late = "demo.fol.Late"
    statement = imp(forall(late, FALSE), forall(late, FALSE))
    t = theorem("demo.fol.early", statement, imp_i("h", forall(late, FALSE), hyp("h")))
    assert results(t, sort(late)) == [E_UNKNOWN_DECL, None]


def test_predicate_instantiation_with_wrong_param_sort() -> None:
    subst = {"P": lam([V], FALSE)}
    t = theorem(
        "demo.fol.inst", imp(forall(U, FALSE), forall(U, FALSE)), ref("thm", ALL_P_ID, subst)
    )
    assert results(ALL_P_ID, t) == [None, E_TYPE]


# --- kernel-spec §13 / logic-spec §12.13 additional cases ------------------------


def test_unbound_index_in_derivation_proposition() -> None:
    bad = theorem(
        "demo.fol.idx", imp(FALSE, FALSE), imp_i("h", FALSE, all_e(all_i(U, hyp("h")), var(3)))
    )
    assert last_error(bad) == E_TYPE


def test_exists_elimination_with_stale_hypothesis_name() -> None:
    ex_p = exists(U, PX)
    proof = imp_i("h", ex_p, ex_e(hyp("h"), "h", imp_i("k", FALSE, hyp("k"))))
    bad = theorem("demo.fol.fresh", imp(ex_p, imp(FALSE, FALSE)), proof)
    assert last_error(bad) == E_HYP_NOT_FRESH


def test_exists_introduction_premise_mismatch() -> None:
    even_a = pred(EVEN, app(A))
    # The witness is f(a) but the premise proves Even(a).
    proof = imp_i("h", even_a, ex_i(pred(EVEN, var(0)), app(F, app(A)), hyp("h")))
    bad = theorem("demo.fol.wit", imp(even_a, exists(U, pred(EVEN, var(0)))), proof)
    assert last_error(bad) == E_RULE_MISMATCH


def test_exists_introduction_witness_of_wrong_sort() -> None:
    # The witness b has sort V, so Even(#0) is checked under a V variable.
    proof = imp_i("h", FALSE, ex_i(pred(EVEN, var(0)), app(B), hyp("h")))
    bad = theorem("demo.fol.wit_sort", imp(FALSE, exists(U, pred(EVEN, var(0)))), proof)
    assert last_error(bad) == E_TYPE


def test_universal_elimination_of_non_universal() -> None:
    proof = imp_i("h", FALSE, all_e(hyp("h"), app(A)))
    assert last_error(theorem("demo.fol.ae", imp(FALSE, FALSE), proof)) == E_RULE_MISMATCH


@pytest.mark.parametrize(
    "prop",
    [
        pred(F, app(A)),  # function symbol used as a predicate
        pred(EVEN, app(EVEN, app(A))),  # predicate symbol used as a term
        pred(EVEN, app(A), app(A)),  # wrong arity
        pred(EVEN, app(F)),  # wrong arity of a function
    ],
)
def test_ill_typed_applications(prop: object) -> None:
    t = theorem("demo.fol.ty", imp(prop, prop), imp_i("h", prop, hyp("h")))
    assert last_error(t) == E_TYPE


def test_proposition_in_term_position_is_malformed() -> None:
    prop = pred(EVEN, pred(EVEN, app(A)))
    t = theorem("demo.fol.ty", imp(prop, prop), imp_i("h", prop, hyp("h")))
    assert bundle_error(l1_bundle(*SIGNATURE, t)) == E_FORMAT


def test_substitution_shape_must_match_arity() -> None:
    prop_for_pvar = {"P": FALSE}  # P takes a U argument, value is a plain proposition
    lam_for_atom = {"P": lam([U], FALSE)}  # P is an atom, value is an abstraction
    atom_thm = theorem("demo.fol.atom_id", imp(P, P), imp_i("h", P, hyp("h")))
    t1 = theorem(
        "demo.fol.t1", imp(forall(U, FALSE), forall(U, FALSE)), ref("thm", ALL_P_ID, prop_for_pvar)
    )
    t2 = theorem("demo.fol.t2", imp(FALSE, FALSE), ref("thm", atom_thm, lam_for_atom))
    assert results(ALL_P_ID, atom_thm, t1, t2) == [None, None, E_TYPE, E_TYPE]


def test_substitution_domain_still_checked() -> None:
    t = theorem("demo.fol.dom", imp(ALL_P, ALL_P), ref("thm", ALL_P_ID, {"Q": lam([U], FALSE)}))
    assert results(ALL_P_ID, t) == [None, E_SUBST_DOMAIN]


def test_substitution_value_must_be_well_formed_in_context() -> None:
    # Index 1 is unbound: the value body only has the parameter (index 0) in scope.
    value = lam([U], pred(EVEN, var(1)))
    t = theorem("demo.fol.wf", forall(U, imp(FALSE, FALSE)), ref("thm", ALL_P_REFL, {"P": value}))
    assert results(ALL_P_REFL, t) == [None, E_TYPE]


def test_pvar_without_arguments_is_malformed() -> None:
    bad = theorem("demo.fol.p0", imp(["pvar", "P", []], P), imp_i("h", P, hyp("h")))
    assert bundle_error(l1_bundle(*SIGNATURE, bad)) == E_FORMAT


def test_const_with_unknown_sort() -> None:
    assert results(const("demo.fol.g", ["demo.fol.W"], U)) == [E_UNKNOWN_DECL]
    assert results(const("demo.fol.h", [U], "demo.fol.W")) == [E_UNKNOWN_DECL]


def test_ill_typed_axiom_is_rejected_and_unusable() -> None:
    ax = axiom("demo.fol.bad_ax", pvar("P", var(0)))
    use = theorem("demo.fol.use", FALSE, ref("ax", ax), ("demo.fol.bad_ax",))
    report = check_bundle(
        encode(l1_bundle(*SIGNATURE, ax, use)), {**STANDARD_AXIOMS, ax["name"]: ax["hash"]}
    )
    codes = [r.error.code if r.error else None for r in report.results[len(SIGNATURE) :]]
    assert codes == [E_TYPE, E_UNKNOWN_DECL]


def test_valid_l1_theorem_still_verifies_after_rejections() -> None:
    report = check_bundle(encode(l1_bundle(*SIGNATURE, ALL_P_ID)), STANDARD_AXIOMS)
    assert report.results[-1].status == VERIFIED


# --- L1 constructs in L0 bundles --------------------------------------------------


@pytest.mark.parametrize(
    "decls",
    [
        (sort(U),),
        (theorem("demo.logic.q", imp(ALL_P, ALL_P), imp_i("h", ALL_P, hyp("h"))),),
        (theorem("demo.logic.r", imp(P, P), all_i(U, imp_i("h", P, hyp("h")))),),
    ],
)
def test_l1_constructs_in_l0_bundle(decls: tuple[object, ...]) -> None:
    assert bundle_error(bundle(*decls)) == E_FRAGMENT


def test_predicate_substitution_in_l0_bundle() -> None:
    atom_thm = theorem("demo.logic.atom_id", imp(P, P), imp_i("h", P, hyp("h")))
    t = theorem("demo.logic.t", imp(P, P), ref("thm", atom_thm, {"P": lam([U], FALSE)}))
    assert bundle_error(bundle(atom_thm, t)) == E_FRAGMENT
