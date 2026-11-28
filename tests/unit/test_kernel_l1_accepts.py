"""The kernel accepts valid L1 derivations (logic-spec §12, kernel-spec §13)."""

from axiomweave.kernel import ACCEPTED, STANDARD_AXIOMS, VERIFIED, KernelReport, check_bundle
from tests.helpers import (
    FALSE,
    P,
    Q,
    all_e,
    all_i,
    and_,
    and_e1,
    app,
    axiom,
    const,
    encode,
    ex_e,
    ex_i,
    exists,
    false_e,
    forall,
    hyp,
    imp,
    imp_e,
    imp_i,
    l1_bundle,
    lam,
    neg,
    or_,
    or_e,
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
F = "demo.fol.f"
EVEN = "demo.fol.Even"
REL = "demo.fol.R"
SIGNATURE = (
    sort(U),
    sort(V),
    const(A, [], U),
    const(F, [U], U),
    const(EVEN, [U], "prop"),
    const(REL, [U, U], "prop"),
)
EM = axiom("classical.em", or_(P, neg(P)))


def px(i: int = 0) -> list[object]:
    return pvar("P", var(i))


def qx(i: int = 0) -> list[object]:
    return pvar("Q", var(i))


# logic-spec §12.12 (1): (∀x. P(x) ∧ Q(x)) → ∀x. P(x)
ALL_AND = forall(U, and_(px(), qx()))
ALL_AND_LEFT = theorem(
    "demo.fol.all_and_left",
    imp(ALL_AND, forall(U, px())),
    imp_i("h", ALL_AND, all_i(U, and_e1(all_e(hyp("h"), var(0))))),
)


def run(*decls: object, allowed: dict[str, str] | None = None) -> KernelReport:
    policy = STANDARD_AXIOMS if allowed is None else allowed
    return check_bundle(encode(l1_bundle(*SIGNATURE, *decls)), policy)


def verified(*decls: object) -> KernelReport:
    report = run(*decls)
    assert report.ok, [r.error for r in report.results if r.error]
    return report


def test_signature_declarations_are_accepted() -> None:
    report = verified()
    assert [r.status for r in report.results] == [ACCEPTED] * len(SIGNATURE)


def test_spec_example_universal_and_left() -> None:
    report = verified(ALL_AND_LEFT)
    assert report.results[-1].status == VERIFIED
    assert report.results[-1].axioms == ()


def test_spec_example_exists_not_forall_not() -> None:
    # logic-spec §12.12 (2): (∃x. P(x)) → (∀x. P(x) → ⊥) → ⊥
    ex_p = exists(U, px())
    all_not = forall(U, imp(px(), FALSE))
    body = imp_e(all_e(hyp("h2"), var(0)), hyp("k"))
    proof = imp_i("h1", ex_p, imp_i("h2", all_not, ex_e(hyp("h1"), "k", body)))
    verified(theorem("demo.fol.ex_not_all_not", imp(ex_p, all_not, FALSE), proof))


def test_spec_example_witness() -> None:
    # logic-spec §12.12 (3): Even(a) → ∃x. Even(x)
    even_a = pred(EVEN, app(A))
    proof = imp_i("h", even_a, ex_i(pred(EVEN, var(0)), app(A), hyp("h")))
    verified(theorem("demo.fol.witness", imp(even_a, exists(U, pred(EVEN, var(0)))), proof))


def test_spec_example_predicate_instantiation() -> None:
    # logic-spec §12.12 (4): P ↦ λz. Even(z), Q ↦ λz. ⊥
    subst = {"P": lam([U], pred(EVEN, var(0))), "Q": lam([U], FALSE)}
    statement = imp(forall(U, and_(pred(EVEN, var(0)), FALSE)), forall(U, pred(EVEN, var(0))))
    inst = theorem("demo.fol.inst", statement, ref("thm", ALL_AND_LEFT, subst))
    verified(ALL_AND_LEFT, inst)


def test_instantiation_under_binder_avoids_capture() -> None:
    # Inside ∀y, use all_and_left with P ↦ λz. R(z, y), Q ↦ λz. R(z, y); the outer
    # variable y must become index 1 under the statement's own binder.
    r_zy = pred(REL, var(0), var(1))
    subst = {"P": lam([U], r_zy), "Q": lam([U], r_zy)}
    instance = imp(forall(U, and_(r_zy, r_zy)), forall(U, r_zy))
    statement = forall(U, instance)
    t = theorem("demo.fol.capture", statement, all_i(U, ref("thm", ALL_AND_LEFT, subst)))
    verified(ALL_AND_LEFT, t)


def test_hypothesis_is_shifted_under_binders() -> None:
    # ∀x. Even(x) → ∀y. Even(x): the hypothesis mentions x and is used under ∀y.
    even_x = pred(EVEN, var(0))
    statement = forall(U, imp(even_x, forall(U, pred(EVEN, var(1)))))
    proof = all_i(U, imp_i("h", even_x, all_i(U, hyp("h"))))
    verified(theorem("demo.fol.shift", statement, proof))


def test_nested_quantifiers_and_function_terms() -> None:
    # (∀x. ∀y. R(x, y)) → ∀z. R(f(z), z)
    rxy = pred(REL, var(1), var(0))
    statement = imp(forall(U, forall(U, rxy)), forall(U, pred(REL, app(F, var(0)), var(0))))
    proof = imp_i(
        "h", forall(U, forall(U, rxy)), all_i(U, all_e(all_e(hyp("h"), app(F, var(0))), var(0)))
    )
    verified(theorem("demo.fol.nested", statement, proof))


def test_exists_elimination_with_closed_conclusion() -> None:
    # (∃x. P(x) ∧ Q(x)) → ∃x. P(x)
    ex_pq = exists(U, and_(px(), qx()))
    body = ex_i(px(), var(0), and_e1(hyp("k")))
    proof = imp_i("h", ex_pq, ex_e(hyp("h"), "k", body))
    verified(theorem("demo.fol.ex_and_left", imp(ex_pq, exists(U, px())), proof))


def test_l0_theorems_inside_l1_bundle() -> None:
    proof = imp_i("h", P, hyp("h"))
    report = verified(theorem("demo.fol.id", imp(P, P), proof))
    assert report.results[-1].status == VERIFIED


def test_classical_axiom_instantiated_with_quantified_proposition() -> None:
    # ¬¬(∀x. P(x)) → ∀x. P(x) from em with P ↦ ∀x. P(x) (an L0 atom instantiated in L1).
    all_p = forall(U, px())
    nn = neg(neg(all_p))
    em_inst = ref("ax", EM, {"P": all_p})
    proof = imp_i(
        "h",
        nn,
        or_e(em_inst, "a", hyp("a"), "b", false_e(imp_e(hyp("h"), hyp("b")), all_p)),
    )
    report = verified(EM, theorem("demo.fol.dne_all", imp(nn, all_p), proof, ("classical.em",)))
    assert report.results[-1].axioms == ("classical.em",)


def test_constant_proposition_and_axiom_about_constants() -> None:
    # A user axiom ∀x. Even(f(x)) used through ax, then specialised at a.
    ax = axiom("demo.fol.even_f", forall(U, pred(EVEN, app(F, var(0)))))
    goal = pred(EVEN, app(F, app(A)))
    t = theorem("demo.fol.even_fa", goal, all_e(ref("ax", ax), app(A)), ("demo.fol.even_f",))
    report = run(ax, t, allowed={**STANDARD_AXIOMS, ax["name"]: ax["hash"]})
    assert report.ok, [r.error for r in report.results if r.error]


def test_atom_and_predicate_variable_with_different_names() -> None:
    statement = imp(and_(Q, forall(U, px())), Q)
    proof = imp_i("h", and_(Q, forall(U, px())), and_e1(hyp("h")))
    verified(theorem("demo.fol.q", statement, proof))
