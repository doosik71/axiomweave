"""Invalid certificates are rejected with the right code (specification §8, kernel-spec §10.2).

Each test builds an otherwise well-formed bundle (hashes recomputed) so that
the intended defect, not an incidental hash mismatch, is what the kernel finds.
"""

import copy

import pytest

from axiomweave.kernel import (
    REJECTED,
    STANDARD_AXIOMS,
    VERIFIED,
    KernelReport,
    Limits,
    bundle_hash,
    check_bundle,
)
from axiomweave.kernel.errors import (
    E_AXIOM_NOT_ALLOWED,
    E_AXIOMS_MISMATCH,
    E_CONCLUSION_MISMATCH,
    E_DUPLICATE_DECL,
    E_FORMAT,
    E_FRAGMENT,
    E_HASH_MISMATCH,
    E_HYP_NOT_FRESH,
    E_HYP_UNKNOWN,
    E_LIMIT,
    E_NAME,
    E_RULE_MISMATCH,
    E_SUBST_DOMAIN,
    E_UNKNOWN_DECL,
    E_VERSION,
)
from tests.helpers import (
    P,
    Q,
    and_,
    and_e1,
    and_i,
    atom,
    axiom,
    bundle,
    encode,
    false_e,
    hyp,
    imp,
    imp_e,
    imp_i,
    neg,
    or_,
    or_e,
    ref,
    rehash,
    theorem,
)

ID = theorem("demo.logic.id", imp(P, P), imp_i("h", P, hyp("h")))


def run(
    obj: object, allowed: dict[str, str] | None = None, limits: Limits | None = None
) -> KernelReport:
    data = obj if isinstance(obj, bytes) else encode(obj)
    policy = STANDARD_AXIOMS if allowed is None else allowed
    if limits is None:
        return check_bundle(data, policy)
    return check_bundle(data, policy, limits)


def bundle_error(obj: object, **kwargs: object) -> str:
    report = run(obj, **kwargs)  # type: ignore[arg-type]
    assert not report.bundle_ok and report.bundle_error is not None
    assert not report.ok
    return report.bundle_error.code


def decl_errors(*decls: object) -> list[str | None]:
    report = run(bundle(*decls))
    assert report.bundle_ok, report.bundle_error
    return [r.error.code if r.error else None for r in report.results]


def single_error(statement: object, proof: object) -> str | None:
    [code] = decl_errors(theorem("demo.logic.t", statement, proof))
    return code


# --- specification §8 failure types ------------------------------------------


def test_rule_premise_mismatch() -> None:
    proof = imp_i("f", imp(P, Q), imp_i("r", atom("R"), imp_e(hyp("f"), hyp("r"))))
    assert single_error(imp(imp(P, Q), atom("R"), Q), proof) == E_RULE_MISMATCH


def test_main_connective_mismatch() -> None:
    proof = imp_i("h", or_(P, Q), and_e1(hyp("h")))
    assert single_error(imp(or_(P, Q), P), proof) == E_RULE_MISMATCH


def test_false_elimination_needs_falsehood() -> None:
    proof = imp_i("h", P, false_e(hyp("h"), Q))
    assert single_error(imp(P, Q), proof) == E_RULE_MISMATCH


def test_or_elimination_branches_must_agree() -> None:
    proof = imp_i("h", or_(P, Q), or_e(hyp("h"), "a", hyp("a"), "b", hyp("b")))
    assert single_error(imp(or_(P, Q), P), proof) == E_RULE_MISMATCH


def test_undischarged_hypothesis() -> None:
    assert single_error(P, hyp("h")) == E_HYP_UNKNOWN


def test_hypothesis_out_of_scope() -> None:
    proof = and_i(imp_i("h", P, hyp("h")), hyp("h"))
    assert single_error(and_(imp(P, P), P), proof) == E_HYP_UNKNOWN


def test_hypothesis_name_not_fresh() -> None:
    proof = imp_i("h", P, imp_i("h", Q, hyp("h")))
    assert single_error(imp(P, Q, Q), proof) == E_HYP_NOT_FRESH


def test_or_elimination_name_not_fresh() -> None:
    proof = imp_i("h", or_(P, P), or_e(hyp("h"), "h", hyp("h"), "x", hyp("x")))
    assert single_error(imp(or_(P, P), P), proof) == E_HYP_NOT_FRESH


def test_conclusion_mismatch() -> None:
    assert single_error(imp(Q, Q), imp_i("h", P, hyp("h"))) == E_CONCLUSION_MISMATCH


def test_no_commutativity_in_equality() -> None:
    proof = imp_i("h", and_(P, Q), hyp("h"))
    assert single_error(imp(and_(P, Q), and_(Q, P)), proof) == E_CONCLUSION_MISMATCH


def test_type_error_wrong_arity() -> None:
    bad = theorem("demo.logic.t", ["and", P], hyp("h"))
    assert bundle_error(bundle(bad)) == E_FORMAT


def test_type_error_reserved_atom_name() -> None:
    bad = theorem("demo.logic.t", imp(atom("and"), atom("and")), imp_i("h", atom("and"), hyp("h")))
    assert bundle_error(bundle(bad)) == E_NAME


def test_abbreviation_is_not_a_kernel_term() -> None:
    bad = theorem("demo.logic.t", ["not", P], hyp("h"))
    assert bundle_error(bundle(bad)) == E_FORMAT


def test_fragment_violation() -> None:
    bad = theorem("demo.logic.t", ["forall", "x", P], hyp("h"))
    assert bundle_error(bundle(bad)) == E_FRAGMENT


def test_reference_to_rejected_theorem() -> None:
    broken = theorem("demo.logic.broken", imp(Q, Q), imp_i("h", P, hyp("h")))
    user = theorem("demo.logic.user", imp(Q, Q), ref("thm", broken))
    assert decl_errors(broken, user) == [E_CONCLUSION_MISMATCH, E_UNKNOWN_DECL]


def test_reference_to_later_declaration() -> None:
    user = theorem("demo.logic.user", imp(P, P), ref("thm", ID))
    assert decl_errors(user, ID) == [E_UNKNOWN_DECL, None]


def test_self_reference() -> None:
    proof = {"rule": "thm", "name": "demo.logic.loop", "hash": ID["hash"], "subst": {}}
    assert decl_errors(theorem("demo.logic.loop", imp(P, P), proof)) == [E_UNKNOWN_DECL]


def test_theorem_rule_cannot_reference_an_axiom() -> None:
    em = axiom("classical.em", or_(P, neg(P)))
    user = theorem("demo.c.user", or_(P, neg(P)), ref("thm", em))
    assert decl_errors(em, user) == [None, E_UNKNOWN_DECL]


def test_unlisted_axiom() -> None:
    bad = axiom("demo.logic.bad", P)
    assert bundle_error(bundle(bad)) == E_AXIOM_NOT_ALLOWED


def test_axiom_with_standard_name_but_other_statement() -> None:
    fake = axiom("classical.em", P)
    assert bundle_error(bundle(fake)) == E_AXIOM_NOT_ALLOWED


def test_custom_axiom_allowed_by_hash() -> None:
    custom = axiom("demo.logic.custom", imp(P, P))
    report = run(bundle(custom), allowed={"demo.logic.custom": custom["hash"]})
    assert report.ok


def test_classical_axiom_needs_policy() -> None:
    em = axiom("classical.em", or_(P, neg(P)))
    assert bundle_error(bundle(em), allowed={}) == E_AXIOM_NOT_ALLOWED


# --- certificate tampering -----------------------------------------------------


def test_tampered_bundle_hash() -> None:
    obj = bundle(ID)
    obj["declarations"][0]["statement"] = imp(Q, Q)
    assert bundle_error(obj) == E_HASH_MISMATCH


def test_tampered_declaration_with_new_bundle_hash() -> None:
    tampered = copy.deepcopy(ID)
    tampered["statement"] = imp(Q, Q)
    assert decl_errors(tampered) == [E_HASH_MISMATCH]


def test_tampered_declaration_with_all_hashes_recomputed() -> None:
    tampered = rehash(copy.deepcopy(ID))
    tampered["statement"] = imp(Q, Q)
    rehash(tampered)
    user = theorem("demo.logic.user", imp(P, P), ref("thm", ID))
    assert decl_errors(tampered, user) == [E_CONCLUSION_MISMATCH, E_UNKNOWN_DECL]


def test_tampered_reference_hash() -> None:
    user = theorem("demo.logic.user", imp(P, P), ref("thm", ID))
    user["proof"]["hash"] = "sha256:" + "0" * 64
    rehash(user)
    assert decl_errors(ID, user) == [None, E_HASH_MISMATCH]


def test_tampered_axiom_list() -> None:
    lying = copy.deepcopy(ID)
    lying["axioms"] = ["classical.em"]
    assert decl_errors(lying) == [E_AXIOMS_MISMATCH]


def test_hidden_axiom_dependency() -> None:
    em = axiom("classical.em", or_(P, neg(P)))
    hiding = theorem("demo.c.em", or_(P, neg(P)), ref("ax", em))  # records no axioms
    assert decl_errors(em, hiding) == [None, E_AXIOMS_MISMATCH]


# --- other kernel checks --------------------------------------------------------


def test_substitution_outside_statement_atoms() -> None:
    user = theorem("demo.logic.user", imp(P, P), ref("thm", ID, {"R": Q}))
    assert decl_errors(ID, user) == [None, E_SUBST_DOMAIN]


def test_duplicate_declaration() -> None:
    assert bundle_error(bundle(ID, ID)) == E_DUPLICATE_DECL


@pytest.mark.parametrize(
    ("field", "value", "code"),
    [
        ("format", "other", E_VERSION),
        ("format_version", 2, E_VERSION),
        ("format_version", "1", E_FORMAT),
        ("fragment", "L1", E_VERSION),
        ("theory", "bad name", E_NAME),
    ],
)
def test_header_fields(field: str, value: object, code: str) -> None:
    obj = bundle(ID)
    obj[field] = value
    obj["bundle_hash"] = bundle_hash(obj)
    assert bundle_error(obj) == code


def test_extra_key_in_derivation() -> None:
    bad = theorem("demo.logic.t", imp(P, P), imp_i("h", P, {"rule": "hyp", "name": "h", "x": "y"}))
    assert bundle_error(bundle(bad)) == E_FORMAT


def test_missing_key_in_declaration() -> None:
    bad = copy.deepcopy(ID)
    del bad["axioms"]
    assert bundle_error(bundle(bad)) == E_FORMAT


def test_unknown_rule() -> None:
    bad = theorem("demo.logic.t", imp(P, P), {"rule": "magic"})
    assert bundle_error(bundle(bad)) == E_FORMAT


def test_unsorted_axiom_list() -> None:
    bad = copy.deepcopy(ID)
    bad["axioms"] = ["z.b", "a.b"]
    assert bundle_error(bundle(bad)) == E_FORMAT


@pytest.mark.parametrize(
    "data",
    [
        b"\xef\xbb\xbf{}",  # BOM
        b"\xff\xfe",  # not UTF-8
        b'{"a": 1, "a": 2}',  # duplicate key
        b'{"a": 1.5}',  # float
        b'{"a": NaN}',  # constant
        b'{"a": true}',  # boolean
        b'{"a": null}',  # null
        b'{"a": -1}',  # negative integer
        '{"a": "é"}'.encode(),  # non-ASCII string
        b"[1,",  # invalid JSON
    ],
)
def test_json_restrictions(data: bytes) -> None:
    assert bundle_error(data) == E_FORMAT


def test_non_bytes_input() -> None:
    report = check_bundle("{}", STANDARD_AXIOMS)  # type: ignore[arg-type]
    assert report.bundle_error is not None and report.bundle_error.code == E_FORMAT


def test_nesting_depth_limit() -> None:
    deep: object = P
    for _ in range(600):
        deep = imp(P, deep)
    bad = theorem("demo.logic.t", deep, hyp("h"))
    assert bundle_error(bundle(bad)) == E_LIMIT


def test_very_deep_input_does_not_crash() -> None:
    data = b"[" * 100_000 + b"]" * 100_000
    assert bundle_error(data) == E_LIMIT


def test_size_limit() -> None:
    assert bundle_error(encode(bundle(ID)), limits=Limits(max_bytes=10)) == E_LIMIT


def test_node_budget_limit() -> None:
    # The instance big -> big is a new node; ID itself needs none (its nodes come from decoding).
    big = and_(and_(P, Q), and_(Q, P))
    user = theorem("demo.logic.user", imp(Q, Q), ref("thm", ID, {"P": big}))
    report = run(bundle(ID, user), limits=Limits(max_nodes=0))
    assert [r.status for r in report.results] == [VERIFIED, REJECTED]
    assert report.results[1].error is not None and report.results[1].error.code == E_LIMIT


def test_rejection_does_not_stop_later_declarations() -> None:
    broken = theorem("demo.logic.broken", Q, hyp("h"))
    report = run(bundle(broken, ID))
    assert [r.status for r in report.results] == [REJECTED, VERIFIED]
    assert not report.ok


def test_error_reports_location() -> None:
    proof = imp_i("h", P, imp_e(hyp("h"), hyp("h")))
    report = run(bundle(theorem("demo.logic.t", imp(P, P), proof)))
    error = report.results[0].error
    assert error is not None
    assert error.path == "$.declarations[0].proof.body"
