"""The standard `propositional` theory (language-spec §10.2)."""

import json
from pathlib import Path

from axiomweave import Falsehood, Iff, Implies, ProofContext, Prop, Status, Theorem, Theory, Truth
from axiomweave.kernel import STANDARD_AXIOMS, check_bundle
from axiomweave.lib.logic import propositional as lib
from axiomweave.lib.logic.propositional import and_comm, iff_trans, propositional

P, Q, R = (Prop.symbol(name) for name in ("P", "Q", "R"))
A, B, C = (Prop.symbol(name) for name in ("A", "B", "C"))

# The table of language-spec §10.2, in declaration order.
SPEC = [
    ("imp_refl", P >> P),
    ("imp_const", Implies(P, Q, P)),
    ("imp_trans", Implies(P >> Q, Q >> R, P >> R)),
    ("imp_swap", Implies(P, Q, R) >> Implies(Q, P, R)),
    ("imp_distrib", Implies(Implies(P, Q, R), P >> Q, P >> R)),
    ("and_intro", Implies(P, Q, P & Q)),
    ("and_left", (P & Q) >> P),
    ("and_right", (P & Q) >> Q),
    ("and_comm", (P & Q) >> (Q & P)),
    ("and_assoc", Iff((P & Q) & R, P & (Q & R))),
    ("and_self", Iff(P & P, P)),
    ("or_inl", P >> (P | Q)),
    ("or_inr", Q >> (P | Q)),
    ("or_elim", Implies(P | Q, P >> R, Q >> R, R)),
    ("or_comm", (P | Q) >> (Q | P)),
    ("or_assoc", Iff((P | Q) | R, P | (Q | R))),
    ("or_self", Iff(P | P, P)),
    ("and_or_distrib", Iff(P & (Q | R), (P & Q) | (P & R))),
    ("or_and_distrib", Iff(P | (Q & R), (P | Q) & (P | R))),
    ("curry", Iff((P & Q) >> R, Implies(P, Q, R))),
    ("or_imp", Iff((P | Q) >> R, (P >> R) & (Q >> R))),
    ("false_elim", Falsehood >> P),
    ("truth_intro", Truth),
    ("explosion", Implies(~P, P, Q)),
    ("not_contradiction", ~(P & ~P)),
    ("contrapositive", (P >> Q) >> (~Q >> ~P)),
    ("dni", P >> ~~P),
    ("tne", Iff(~~~P, ~P)),
    ("not_not_em", ~~(P | ~P)),
    ("not_or", Iff(~(P | Q), ~P & ~Q)),
    ("not_and_of_or_not", (~P | ~Q) >> ~(P & Q)),
    ("iff_refl", Iff(P, P)),
    ("iff_symm", Iff(P, Q) >> Iff(Q, P)),
    ("iff_trans", Implies(Iff(P, Q), Iff(Q, R), Iff(P, R))),
]


def test_declarations_match_spec() -> None:
    declared = [(d.name, d.statement) for d in propositional.environment()]
    assert declared == [(f"propositional.{name}", prop) for name, prop in SPEC]
    for name, prop in SPEC:
        handle = getattr(lib, name)
        assert isinstance(handle, Theorem)
        assert handle.statement == prop


def test_all_verified_without_axioms() -> None:
    report = propositional.check()
    assert report.ok, str(report)
    assert len(report.results) == len(SPEC)
    assert all(r.axioms == frozenset() for r in report.results)


def test_no_axioms_allowed_still_verifies() -> None:
    report = propositional.check(allowed_axioms=[])
    assert report.ok, str(report)


def test_certificate_reverifies(tmp_path: Path) -> None:
    propositional.check()
    path = propositional.export(tmp_path / "propositional.axwp")
    report = check_bundle(path.read_bytes(), {})
    assert report.ok
    assert len(json.loads(path.read_text(encoding="utf-8"))["declarations"]) == len(SPEC)
    assert check_bundle(path.read_bytes(), STANDARD_AXIOMS).ok


def test_use_from_importing_theory() -> None:
    thy = Theory("demo.uses_lib", imports=[propositional])

    @thy.theorem
    def comm_inst() -> Prop:
        return ((A | B) & C) >> (C & (A | B))

    @thy.proof(comm_inst)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(and_comm, {P: A | B, Q: C}))

    @thy.theorem
    def chain() -> Prop:
        return Implies(Iff(A, B), Iff(B, C), Iff(A, C))

    @thy.proof(chain)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(iff_trans, {P: A, Q: B, R: C}))

    report = thy.check()
    assert report.ok, str(report)
    assert comm_inst.status is Status.VERIFIED
    assert chain.axioms == frozenset()


def test_unimported_library_theorem_is_rejected() -> None:
    thy = Theory("demo.no_import")

    @thy.theorem
    def comm() -> Prop:
        return (P & Q) >> (Q & P)

    @thy.proof(comm)
    def _(ctx: ProofContext) -> None:
        ctx.exact(ctx.thm(and_comm))

    report = thy.check()
    [result] = report.results
    assert result.status is Status.REJECTED
