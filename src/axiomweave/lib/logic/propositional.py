"""Intuitionistic propositional laws (language-spec §10.2).

The theory declares no axioms and imports nothing, so every theorem must be
verified with an empty set of axiom dependencies. Declaration order follows the
table in the language spec; later proofs may use earlier theorems.
"""

from axiomweave import Falsehood, Iff, Implies, Prop, Theory, Truth
from axiomweave.language.proof import ProofContext

P, Q, R = (Prop.symbol(name) for name in ("P", "Q", "R"))

propositional = Theory("propositional")


# --- implication ------------------------------------------------------------------


@propositional.theorem
def imp_refl() -> Prop:
    return P >> P


@propositional.proof(imp_refl)
def _prove_imp_refl(ctx: ProofContext) -> None:
    ctx.exact(ctx.intro())


@propositional.theorem
def imp_const() -> Prop:
    return Implies(P, Q, P)


@propositional.proof(imp_const)
def _prove_imp_const(ctx: ProofContext) -> None:
    hp = ctx.intro()
    ctx.intro()
    ctx.exact(hp)


@propositional.theorem
def imp_trans() -> Prop:
    return Implies(P >> Q, Q >> R, P >> R)


@propositional.proof(imp_trans)
def _prove_imp_trans(ctx: ProofContext) -> None:
    hpq = ctx.intro()
    hqr = ctx.intro()
    hp = ctx.intro()
    ctx.exact(ctx.mp(hqr, ctx.mp(hpq, hp)))


@propositional.theorem
def imp_swap() -> Prop:
    return Implies(P, Q, R) >> Implies(Q, P, R)


@propositional.proof(imp_swap)
def _prove_imp_swap(ctx: ProofContext) -> None:
    h = ctx.intro()
    hq = ctx.intro()
    hp = ctx.intro()
    ctx.exact(ctx.mp(ctx.mp(h, hp), hq))


@propositional.theorem
def imp_distrib() -> Prop:
    return Implies(Implies(P, Q, R), P >> Q, P >> R)


@propositional.proof(imp_distrib)
def _prove_imp_distrib(ctx: ProofContext) -> None:
    h = ctx.intro()
    hpq = ctx.intro()
    hp = ctx.intro()
    ctx.exact(ctx.mp(ctx.mp(h, hp), ctx.mp(hpq, hp)))


# --- conjunction ------------------------------------------------------------------


@propositional.theorem
def and_intro() -> Prop:
    return Implies(P, Q, P & Q)


@propositional.proof(and_intro)
def _prove_and_intro(ctx: ProofContext) -> None:
    hp = ctx.intro()
    hq = ctx.intro()
    ctx.exact(ctx.and_intro(hp, hq))


@propositional.theorem
def and_left() -> Prop:
    return (P & Q) >> P


@propositional.proof(and_left)
def _prove_and_left(ctx: ProofContext) -> None:
    ctx.exact(ctx.and_left(ctx.intro()))


@propositional.theorem
def and_right() -> Prop:
    return (P & Q) >> Q


@propositional.proof(and_right)
def _prove_and_right(ctx: ProofContext) -> None:
    ctx.exact(ctx.and_right(ctx.intro()))


@propositional.theorem
def and_comm() -> Prop:
    return (P & Q) >> (Q & P)


@propositional.proof(and_comm)
def _prove_and_comm(ctx: ProofContext) -> None:
    h = ctx.intro()
    ctx.exact(ctx.and_intro(ctx.and_right(h), ctx.and_left(h)))


@propositional.theorem
def and_assoc() -> Prop:
    return Iff((P & Q) & R, P & (Q & R))


@propositional.proof(and_assoc)
def _prove_and_assoc(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        hpq = ctx.and_left(h)
        qr = ctx.and_intro(ctx.and_right(hpq), ctx.and_right(h))
        ctx.exact(ctx.and_intro(ctx.and_left(hpq), qr))
    with ctx.focus():
        h = ctx.intro()
        hqr = ctx.and_right(h)
        pq = ctx.and_intro(ctx.and_left(h), ctx.and_left(hqr))
        ctx.exact(ctx.and_intro(pq, ctx.and_right(hqr)))


@propositional.theorem
def and_self() -> Prop:
    return Iff(P & P, P)


@propositional.proof(and_self)
def _prove_and_self(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        ctx.exact(ctx.thm(and_left, {Q: P}))
    with ctx.focus():
        hp = ctx.intro()
        ctx.exact(ctx.and_intro(hp, hp))


# --- disjunction ------------------------------------------------------------------


@propositional.theorem
def or_inl() -> Prop:
    return P >> (P | Q)


@propositional.proof(or_inl)
def _prove_or_inl(ctx: ProofContext) -> None:
    ctx.exact(ctx.or_inl(ctx.intro(), Q))


@propositional.theorem
def or_inr() -> Prop:
    return Q >> (P | Q)


@propositional.proof(or_inr)
def _prove_or_inr(ctx: ProofContext) -> None:
    ctx.exact(ctx.or_inr(P, ctx.intro()))


@propositional.theorem
def or_elim() -> Prop:
    return Implies(P | Q, P >> R, Q >> R, R)


@propositional.proof(or_elim)
def _prove_or_elim(ctx: ProofContext) -> None:
    h = ctx.intro()
    hpr = ctx.intro()
    hqr = ctx.intro()
    hp, hq = ctx.cases(h)
    with ctx.focus():
        ctx.exact(ctx.mp(hpr, hp))
    with ctx.focus():
        ctx.exact(ctx.mp(hqr, hq))


@propositional.theorem
def or_comm() -> Prop:
    return (P | Q) >> (Q | P)


@propositional.proof(or_comm)
def _prove_or_comm(ctx: ProofContext) -> None:
    h = ctx.intro()
    hp, hq = ctx.cases(h)
    with ctx.focus():
        ctx.exact(ctx.or_inr(Q, hp))
    with ctx.focus():
        ctx.exact(ctx.or_inl(hq, P))


@propositional.theorem
def or_assoc() -> Prop:
    return Iff((P | Q) | R, P | (Q | R))


@propositional.proof(or_assoc)
def _prove_or_assoc(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        hpq, hr = ctx.cases(h)
        with ctx.focus():
            hp, hq = ctx.cases(hpq)
            with ctx.focus():
                ctx.exact(ctx.or_inl(hp, Q | R))
            with ctx.focus():
                ctx.exact(ctx.or_inr(P, ctx.or_inl(hq, R)))
        with ctx.focus():
            ctx.exact(ctx.or_inr(P, ctx.or_inr(Q, hr)))
    with ctx.focus():
        h = ctx.intro()
        hp, hqr = ctx.cases(h)
        with ctx.focus():
            ctx.exact(ctx.or_inl(ctx.or_inl(hp, Q), R))
        with ctx.focus():
            hq, hr = ctx.cases(hqr)
            with ctx.focus():
                ctx.exact(ctx.or_inl(ctx.or_inr(P, hq), R))
            with ctx.focus():
                ctx.exact(ctx.or_inr(P | Q, hr))


@propositional.theorem
def or_self() -> Prop:
    return Iff(P | P, P)


@propositional.proof(or_self)
def _prove_or_self(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        ha, hb = ctx.cases(h)
        with ctx.focus():
            ctx.exact(ha)
        with ctx.focus():
            ctx.exact(hb)
    with ctx.focus():
        ctx.exact(ctx.thm(or_inl, {Q: P}))


# --- distributivity and currying --------------------------------------------------


@propositional.theorem
def and_or_distrib() -> Prop:
    return Iff(P & (Q | R), (P & Q) | (P & R))


@propositional.proof(and_or_distrib)
def _prove_and_or_distrib(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        hp = ctx.and_left(h)
        hq, hr = ctx.cases(ctx.and_right(h))
        with ctx.focus():
            ctx.exact(ctx.or_inl(ctx.and_intro(hp, hq), P & R))
        with ctx.focus():
            ctx.exact(ctx.or_inr(P & Q, ctx.and_intro(hp, hr)))
    with ctx.focus():
        h = ctx.intro()
        hpq, hpr = ctx.cases(h)
        with ctx.focus():
            ctx.exact(ctx.and_intro(ctx.and_left(hpq), ctx.or_inl(ctx.and_right(hpq), R)))
        with ctx.focus():
            ctx.exact(ctx.and_intro(ctx.and_left(hpr), ctx.or_inr(Q, ctx.and_right(hpr))))


@propositional.theorem
def or_and_distrib() -> Prop:
    return Iff(P | (Q & R), (P | Q) & (P | R))


@propositional.proof(or_and_distrib)
def _prove_or_and_distrib(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        hp, hqr = ctx.cases(h)
        with ctx.focus():
            ctx.exact(ctx.and_intro(ctx.or_inl(hp, Q), ctx.or_inl(hp, R)))
        with ctx.focus():
            left = ctx.or_inr(P, ctx.and_left(hqr))
            ctx.exact(ctx.and_intro(left, ctx.or_inr(P, ctx.and_right(hqr))))
    with ctx.focus():
        h = ctx.intro()
        hp, hq = ctx.cases(ctx.and_left(h))
        with ctx.focus():
            ctx.exact(ctx.or_inl(hp, Q & R))
        with ctx.focus():
            hp2, hr = ctx.cases(ctx.and_right(h))
            with ctx.focus():
                ctx.exact(ctx.or_inl(hp2, Q & R))
            with ctx.focus():
                ctx.exact(ctx.or_inr(P, ctx.and_intro(hq, hr)))


@propositional.theorem
def curry() -> Prop:
    return Iff((P & Q) >> R, Implies(P, Q, R))


@propositional.proof(curry)
def _prove_curry(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        hp = ctx.intro()
        hq = ctx.intro()
        ctx.exact(ctx.mp(h, ctx.and_intro(hp, hq)))
    with ctx.focus():
        h = ctx.intro()
        hpq = ctx.intro()
        ctx.exact(ctx.mp(ctx.mp(h, ctx.and_left(hpq)), ctx.and_right(hpq)))


@propositional.theorem
def or_imp() -> Prop:
    return Iff((P | Q) >> R, (P >> R) & (Q >> R))


@propositional.proof(or_imp)
def _prove_or_imp(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        ctx.split()
        with ctx.focus():
            hp = ctx.intro()
            ctx.exact(ctx.mp(h, ctx.or_inl(hp, Q)))
        with ctx.focus():
            hq = ctx.intro()
            ctx.exact(ctx.mp(h, ctx.or_inr(P, hq)))
    with ctx.focus():
        h = ctx.intro()
        hpq = ctx.intro()
        ctx.exact(ctx.mp(ctx.mp(ctx.mp(ctx.thm(or_elim), hpq), ctx.and_left(h)), ctx.and_right(h)))


# --- negation ---------------------------------------------------------------------


@propositional.theorem
def false_elim() -> Prop:
    return Falsehood >> P


@propositional.proof(false_elim)
def _prove_false_elim(ctx: ProofContext) -> None:
    ctx.exact(ctx.absurd(ctx.intro(), P))


@propositional.theorem
def truth_intro() -> Prop:
    return Truth


@propositional.proof(truth_intro)
def _prove_truth_intro(ctx: ProofContext) -> None:
    ctx.exact(ctx.intro())  # Truth is ⊥ → ⊥


@propositional.theorem
def explosion() -> Prop:
    return Implies(~P, P, Q)


@propositional.proof(explosion)
def _prove_explosion(ctx: ProofContext) -> None:
    hnp = ctx.intro()
    hp = ctx.intro()
    ctx.exact(ctx.absurd(ctx.mp(hnp, hp), Q))


@propositional.theorem
def not_contradiction() -> Prop:
    return ~(P & ~P)


@propositional.proof(not_contradiction)
def _prove_not_contradiction(ctx: ProofContext) -> None:
    h = ctx.intro()
    ctx.exact(ctx.mp(ctx.and_right(h), ctx.and_left(h)))


@propositional.theorem
def contrapositive() -> Prop:
    return (P >> Q) >> (~Q >> ~P)


@propositional.proof(contrapositive)
def _prove_contrapositive(ctx: ProofContext) -> None:
    hpq = ctx.intro()
    hnq = ctx.intro()
    hp = ctx.intro()
    ctx.exact(ctx.mp(hnq, ctx.mp(hpq, hp)))


@propositional.theorem
def dni() -> Prop:
    return P >> ~~P


@propositional.proof(dni)
def _prove_dni(ctx: ProofContext) -> None:
    hp = ctx.intro()
    hnp = ctx.intro()
    ctx.exact(ctx.mp(hnp, hp))


@propositional.theorem
def tne() -> Prop:
    return Iff(~~~P, ~P)


@propositional.proof(tne)
def _prove_tne(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        hp = ctx.intro()
        ctx.exact(ctx.mp(h, ctx.mp(ctx.thm(dni), hp)))
    with ctx.focus():
        ctx.exact(ctx.thm(dni, {P: ~P}))


@propositional.theorem
def not_not_em() -> Prop:
    return ~~(P | ~P)


@propositional.proof(not_not_em)
def _prove_not_not_em(ctx: ProofContext) -> None:
    h = ctx.intro()  # h : ¬(P ∨ ¬P)
    ctx.apply(h)  # goal: P ∨ ¬P
    ctx.right()
    hp = ctx.intro()
    ctx.exact(ctx.mp(h, ctx.or_inl(hp, ~P)))


@propositional.theorem
def not_or() -> Prop:
    return Iff(~(P | Q), ~P & ~Q)


@propositional.proof(not_or)
def _prove_not_or(ctx: ProofContext) -> None:
    ctx.split()
    with ctx.focus():
        h = ctx.intro()
        ctx.split()
        with ctx.focus():
            hp = ctx.intro()
            ctx.exact(ctx.mp(h, ctx.or_inl(hp, Q)))
        with ctx.focus():
            hq = ctx.intro()
            ctx.exact(ctx.mp(h, ctx.or_inr(P, hq)))
    with ctx.focus():
        h = ctx.intro()
        hpq = ctx.intro()
        hp, hq = ctx.cases(hpq)
        with ctx.focus():
            ctx.exact(ctx.mp(ctx.and_left(h), hp))
        with ctx.focus():
            ctx.exact(ctx.mp(ctx.and_right(h), hq))


@propositional.theorem
def not_and_of_or_not() -> Prop:
    return (~P | ~Q) >> ~(P & Q)


@propositional.proof(not_and_of_or_not)
def _prove_not_and_of_or_not(ctx: ProofContext) -> None:
    h = ctx.intro()
    hpq = ctx.intro()
    hnp, hnq = ctx.cases(h)
    with ctx.focus():
        ctx.exact(ctx.mp(hnp, ctx.and_left(hpq)))
    with ctx.focus():
        ctx.exact(ctx.mp(hnq, ctx.and_right(hpq)))


# --- equivalence ------------------------------------------------------------------


@propositional.theorem
def iff_refl() -> Prop:
    return Iff(P, P)


@propositional.proof(iff_refl)
def _prove_iff_refl(ctx: ProofContext) -> None:
    refl = ctx.thm(imp_refl)
    ctx.exact(ctx.and_intro(refl, refl))


@propositional.theorem
def iff_symm() -> Prop:
    return Iff(P, Q) >> Iff(Q, P)


@propositional.proof(iff_symm)
def _prove_iff_symm(ctx: ProofContext) -> None:
    h = ctx.intro()
    ctx.exact(ctx.and_intro(ctx.and_right(h), ctx.and_left(h)))


@propositional.theorem
def iff_trans() -> Prop:
    return Implies(Iff(P, Q), Iff(Q, R), Iff(P, R))


@propositional.proof(iff_trans)
def _prove_iff_trans(ctx: ProofContext) -> None:
    hpq = ctx.intro()
    hqr = ctx.intro()
    ctx.split()
    with ctx.focus():
        hp = ctx.intro()
        ctx.exact(ctx.mp(ctx.and_left(hqr), ctx.mp(ctx.and_left(hpq), hp)))
    with ctx.focus():
        hr = ctx.intro()
        ctx.exact(ctx.mp(ctx.and_right(hpq), ctx.mp(ctx.and_right(hqr), hr)))
