"""The kernel accepts valid L2 (equality) derivations (logic-spec §13, kernel-spec §14)."""

from axiomweave.kernel import STANDARD_AXIOMS, VERIFIED, KernelReport, check_bundle
from tests.helpers import (
    P,
    all_i,
    app,
    axiom,
    const,
    encode,
    eq,
    eq_e,
    eq_refl,
    forall,
    hyp,
    imp,
    imp_i,
    l2_bundle,
    lam,
    neg,
    or_,
    pred,
    ref,
    sort,
    theorem,
    var,
)

U = "demo.eq.U"
A = "demo.eq.a"
F = "demo.eq.f"
EVEN = "demo.eq.Even"
SIGNATURE = (sort(U), const(A, [], U), const(F, [U], U), const(EVEN, [U], "prop"))

X, Y = var(1), var(0)  # under ∀x ∀y
# logic-spec §13.9 (1) / kernel-spec §14.6: ∀x y. x = y → y = x
SYMM = theorem(
    "demo.eq.symm",
    forall(U, forall(U, imp(eq(X, Y), eq(Y, X)))),
    all_i(
        U,
        all_i(
            U,
            imp_i(
                "h",
                eq(X, Y),
                eq_e(hyp("h"), eq(var(0), var(2)), eq_refl(X)),
            ),
        ),
    ),
)


def run(*decls: object, allowed: dict[str, str] | None = None) -> KernelReport:
    policy = STANDARD_AXIOMS if allowed is None else allowed
    return check_bundle(encode(l2_bundle(*SIGNATURE, *decls)), policy)


def verified(*decls: object, allowed: dict[str, str] | None = None) -> KernelReport:
    report = run(*decls, allowed=allowed)
    assert report.ok, [r.error for r in report.results if r.error]
    return report


def test_reflexivity() -> None:
    t = theorem("demo.eq.refl_fa", eq(app(F, app(A)), app(F, app(A))), eq_refl(app(F, app(A))))
    assert verified(t).results[-1].status == VERIFIED


def test_spec_example_symmetry() -> None:
    assert verified(SYMM).results[-1].axioms == ()


def test_spec_example_predicate_substitution() -> None:
    # logic-spec §13.9 (2): ∀x y. x = y → Even(f(x)) → Even(f(y))
    even_fx = pred(EVEN, app(F, X))
    statement = forall(U, forall(U, imp(eq(X, Y), even_fx, pred(EVEN, app(F, Y)))))
    motive = pred(EVEN, app(F, var(0)))  # λz. Even(f(z)) under Δ = [x, y, z]
    proof = all_i(
        U, all_i(U, imp_i("h1", eq(X, Y), imp_i("h2", even_fx, eq_e(hyp("h1"), motive, hyp("h2")))))
    )
    verified(theorem("demo.eq.subst", statement, proof))


def test_transitivity() -> None:
    # ∀x y z. x = y → y = z → x = z, motive λw. x = w
    x, y, z = var(2), var(1), var(0)
    statement = forall(U, forall(U, forall(U, imp(eq(x, y), eq(y, z), eq(x, z)))))
    proof = all_i(
        U,
        all_i(
            U,
            all_i(
                U,
                imp_i(
                    "h1",
                    eq(x, y),
                    imp_i("h2", eq(y, z), eq_e(hyp("h2"), eq(var(3), var(0)), hyp("h1"))),
                ),
            ),
        ),
    )
    verified(theorem("demo.eq.trans", statement, proof))


def test_congruence() -> None:
    # ∀x y. x = y → f(x) = f(y), motive λw. f(x) = f(w)
    statement = forall(U, forall(U, imp(eq(X, Y), eq(app(F, X), app(F, Y)))))
    motive = eq(app(F, var(2)), app(F, var(0)))
    proof = all_i(U, all_i(U, imp_i("h", eq(X, Y), eq_e(hyp("h"), motive, eq_refl(app(F, X))))))
    verified(theorem("demo.eq.congr", statement, proof))


def test_motive_rewrites_only_marked_positions() -> None:
    # From x = y and x = x conclude x = y: the motive λw. x = w keeps the left x.
    statement = forall(U, forall(U, imp(eq(X, Y), eq(X, Y))))
    proof = all_i(U, all_i(U, imp_i("h", eq(X, Y), eq_e(hyp("h"), eq(var(2), var(0)), eq_refl(X)))))
    verified(theorem("demo.eq.partial", statement, proof))


def test_symmetry_reused_with_thm() -> None:
    # Instantiate nothing: thm refers to the closed symmetry theorem.
    t = theorem("demo.eq.symm_again", SYMM["statement"], ref("thm", SYMM))
    verified(SYMM, t)


def test_classical_decidable_equality_instance() -> None:
    em = axiom("classical.em", or_(P, neg(P)))
    statement = forall(U, forall(U, or_(eq(X, Y), neg(eq(X, Y)))))
    proof = all_i(U, all_i(U, ref("ax", em, {"P": eq(var(1), var(0))})))
    report = verified(em, theorem("demo.eq.dec", statement, proof, ("classical.em",)))
    assert report.results[-1].axioms == ("classical.em",)


def test_predicate_variable_instantiated_with_equality() -> None:
    # all_refl: ∀x. Q(x) → Q(x); instantiate Q ↦ λz. z = a.
    q = ["pvar", "Q", [var(0)]]
    all_refl = theorem("demo.eq.all_refl", forall(U, imp(q, q)), all_i(U, imp_i("h", q, hyp("h"))))
    value = lam([U], eq(var(0), app(A)))
    instance = forall(U, imp(eq(var(0), app(A)), eq(var(0), app(A))))
    t = theorem("demo.eq.inst", instance, ref("thm", all_refl, {"Q": value}))
    verified(all_refl, t)


def test_l1_content_in_l2_bundle() -> None:
    p = ["pvar", "P", [var(0)]]
    t = theorem("demo.eq.l1", forall(U, imp(p, p)), all_i(U, imp_i("h", p, hyp("h"))))
    verified(t)
