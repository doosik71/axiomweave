"""Valid L0 certificates are accepted (logic-spec §11, kernel-spec §12)."""

import json
import re
from pathlib import Path

from axiomweave.kernel import (
    ACCEPTED,
    STANDARD_AXIOMS,
    VERIFIED,
    canonical_json,
    check_bundle,
    declaration_hash,
)
from tests.helpers import (
    FALSE,
    P,
    Q,
    R,
    and_,
    and_e1,
    and_e2,
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
    or_i1,
    or_i2,
    ref,
    theorem,
)

DOCS = Path(__file__).resolve().parents[2] / "docs"
EM = axiom("classical.em", or_(P, neg(P)))


def check(*decls: object) -> tuple[str, ...]:
    report = check_bundle(encode(bundle(*decls)), STANDARD_AXIOMS)
    assert report.bundle_ok, report.bundle_error
    return tuple(r.status for r in report.results)


def test_identity() -> None:  # logic-spec §11.1
    assert check(theorem("demo.logic.id", imp(P, P), imp_i("h", P, hyp("h")))) == (VERIFIED,)


def test_implication_transitivity() -> None:  # logic-spec §11.2
    proof = imp_i(
        "h1",
        imp(P, Q),
        imp_i(
            "h2",
            imp(Q, R),
            imp_i("h3", P, imp_e(hyp("h2"), imp_e(hyp("h1"), hyp("h3")))),
        ),
    )
    stmt = imp(imp(P, Q), imp(Q, R), imp(P, R))
    assert check(theorem("demo.logic.imp_trans", stmt, proof)) == (VERIFIED,)


def test_and_comm() -> None:  # logic-spec §11.3
    proof = imp_i("h", and_(P, Q), and_i(and_e2(hyp("h")), and_e1(hyp("h"))))
    assert check(theorem("demo.logic.and_comm", imp(and_(P, Q), and_(Q, P)), proof)) == (VERIFIED,)


def test_or_comm() -> None:
    proof = imp_i(
        "h",
        or_(P, Q),
        or_e(hyp("h"), "a", or_i2(Q, hyp("a")), "b", or_i1(hyp("b"), P)),
    )
    assert check(theorem("demo.logic.or_comm", imp(or_(P, Q), or_(Q, P)), proof)) == (VERIFIED,)


def test_explosion() -> None:  # logic-spec §11.4
    proof = imp_i(
        "h1",
        neg(P),
        imp_i("h2", P, false_e(imp_e(hyp("h1"), hyp("h2")), Q)),
    )
    assert check(theorem("demo.logic.explode", imp(neg(P), P, Q), proof)) == (VERIFIED,)


def test_theorem_instantiation() -> None:  # logic-spec §11.5
    comm = theorem(
        "demo.logic.and_comm",
        imp(and_(P, Q), and_(Q, P)),
        imp_i("h", and_(P, Q), and_i(and_e2(hyp("h")), and_e1(hyp("h")))),
    )
    a_or_b, c = or_(atom("A"), atom("B")), atom("C")
    inst = theorem(
        "demo.logic.and_comm_inst",
        imp(and_(a_or_b, c), and_(c, a_or_b)),
        ref("thm", comm, {"P": a_or_b, "Q": c}),
    )
    assert check(comm, inst) == (VERIFIED, VERIFIED)


def test_simultaneous_substitution() -> None:
    k = theorem("demo.logic.k", imp(P, Q, P), imp_i("a", P, imp_i("b", Q, hyp("a"))))
    swapped = theorem("demo.logic.k_swap", imp(Q, P, Q), ref("thm", k, {"P": Q, "Q": P}))
    assert check(k, swapped) == (VERIFIED, VERIFIED)


def test_double_negation_with_excluded_middle() -> None:  # logic-spec §11.6
    proof = imp_i(
        "h",
        neg(neg(P)),
        or_e(
            ref("ax", EM),
            "a",
            hyp("a"),
            "b",
            false_e(imp_e(hyp("h"), hyp("b")), P),
        ),
    )
    dne = theorem("demo.classical.dne", imp(neg(neg(P)), P), proof, axioms=("classical.em",))
    report = check_bundle(encode(bundle(EM, dne, theory="demo.classical")), STANDARD_AXIOMS)
    assert [r.status for r in report.results] == [ACCEPTED, VERIFIED]
    assert report.results[1].axioms == ("classical.em",)
    assert report.ok


def test_axiom_dependencies_propagate_through_theorems() -> None:
    em_q = theorem("demo.c.em_q", or_(Q, neg(Q)), ref("ax", EM, {"P": Q}), axioms=("classical.em",))
    reuse = theorem("demo.c.reuse", or_(Q, neg(Q)), ref("thm", em_q), axioms=("classical.em",))
    assert check(EM, em_q, reuse) == (ACCEPTED, VERIFIED, VERIFIED)


def test_or_e_branches_may_reuse_a_name() -> None:
    proof = imp_i("h", or_(P, P), or_e(hyp("h"), "x", hyp("x"), "x", hyp("x")))
    assert check(theorem("demo.logic.or_idem", imp(or_(P, P), P), proof)) == (VERIFIED,)


def test_weakening_unused_hypothesis() -> None:
    proof = imp_i("a", P, imp_i("b", FALSE, hyp("a")))
    assert check(theorem("demo.logic.weak", imp(P, FALSE, P), proof)) == (VERIFIED,)


# kernel-spec §9.2 (classical.em) and §15 (standard arithmetic).
SPEC_HASHES = {
    "classical.em": "sha256:e3dde0812143549271fc6753bfb9f64adce3be606a7b1eedfdd7feff7282c0dc",
    "arith.succ_ne_zero": "sha256:756e2b6a0efec199b64ec6aa4e3e49407a16bc4fb14130af5bd6765bdfd7bd56",
    "arith.succ_inj": "sha256:fde2203bfef7f1ccf157aa7b975f46b7ddd9c9e545a9d36de32c9bee438d3f4b",
    "arith.add_zero": "sha256:811b749e6d0bcb653f48075bef18d9552b7855bca3750ed14a522aa40d066ba4",
    "arith.add_succ": "sha256:40292ce86e7e2590f7db45aaf6195ec0f7b372d4abc8c51f59e293ad75123087",
    "arith.mul_zero": "sha256:ed7db7a8ebb11ea9ba0a5110b05e9a330e8e7bc990dcbec68d0015c1daf066f1",
    "arith.mul_succ": "sha256:baf1f29869d1ebc264b5d6220b854553ba76adc8715b012f0c8902d08d89067a",
    "arith.induction": "sha256:b34d4328e56bf5d1eea2660ea593047f902ededfebb8a082ec6e7b5252339115",
}


def test_standard_axiom_hashes_match_kernel_spec() -> None:
    assert dict(STANDARD_AXIOMS) == SPEC_HASHES
    assert EM["hash"] == SPEC_HASHES["classical.em"]


def _kernel_spec_example() -> dict[str, object]:
    text = (DOCS / "kernel-spec.md").read_text(encoding="utf-8")
    match = re.search(r"```json\n(.*?)\n```", text, re.DOTALL)
    assert match is not None
    loaded: dict[str, object] = json.loads(match.group(1))
    return loaded


def test_kernel_spec_example_bundle() -> None:  # kernel-spec §12
    example = _kernel_spec_example()
    report = check_bundle(json.dumps(example).encode(), STANDARD_AXIOMS)
    assert report.ok, report
    assert [r.status for r in report.results] == [VERIFIED, VERIFIED]


def test_kernel_spec_canonical_bytes() -> None:  # kernel-spec §12
    example = _kernel_spec_example()
    decls = example["declarations"]
    assert isinstance(decls, list)
    first = {k: v for k, v in decls[0].items() if k not in ("hash", "axioms")}
    assert canonical_json(first) == (
        b'{"kind":"theorem","name":"demo.logic.imp_self","proof":{"body":{"name":"h1",'
        b'"rule":"hyp"},"hyp":["atom","P"],"name":"h1","rule":"imp_i"},'
        b'"statement":["imp",["atom","P"],["atom","P"]]}'
    )
    assert declaration_hash(decls[0]) == decls[0]["hash"]


def test_deep_proof_within_depth_limit() -> None:
    n = 300
    names = [f"h{i}" for i in range(n)]
    proof: object = hyp(names[0])
    for name in reversed(names):
        proof = imp_i(name, P, proof)
    assert check(theorem("demo.logic.deep", imp(*([P] * (n + 1))), proof)) == (VERIFIED,)


def test_result_is_deterministic() -> None:
    data = encode(bundle(theorem("demo.logic.id", imp(P, P), imp_i("h", P, hyp("h")))))
    assert check_bundle(data, STANDARD_AXIOMS) == check_bundle(data, STANDARD_AXIOMS)
