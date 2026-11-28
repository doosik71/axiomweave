"""Propositional benchmark problems (ai-spec §5.2)."""

import functools

from axiomweave.bench.core import Problem
from axiomweave.core.expressions import Iff, Prop
from axiomweave.language.proof import ProofContext

P, Q, R = Prop.symbol("P"), Prop.symbol("Q"), Prop.symbol("R")


def _by_auto(ctx: ProofContext) -> None:
    ctx.auto()


def _conj(props: list[Prop]) -> Prop:
    return functools.reduce(lambda a, b: a & b, props)


def _disj(props: list[Prop]) -> Prop:
    return functools.reduce(lambda a, b: a | b, props)


def _pigeonhole(holes: int) -> Prop:
    """PHP(holes + 1, holes): if every pigeon sits in some hole, two share one."""
    p = {(i, j): Prop.symbol(f"p{i}_{j}") for i in range(holes + 1) for j in range(holes)}
    seated = _conj([_disj([p[i, j] for j in range(holes)]) for i in range(holes + 1)])
    shared = _disj(
        [
            p[i, j] & p[k, j]
            for j in range(holes)
            for i in range(holes + 1)
            for k in range(i + 1, holes + 1)
        ]
    )
    return seated >> shared


def _chain(length: int) -> Prop:
    atoms = [Prop.symbol(f"C{i}") for i in range(length)]
    links = _conj([atoms[i] >> atoms[i + 1] for i in range(length - 1)])
    return links >> (atoms[0] >> atoms[-1])


def _provable(name: str, statement: Prop, note: str = "") -> Problem:
    return Problem(
        f"prop.{name}", "propositional", lambda: statement, "provable", (), _by_auto, note
    )


def _unprovable(name: str, statement: Prop, note: str) -> Problem:
    return Problem(f"prop.{name}", "propositional", lambda: statement, "unprovable", (), None, note)


PROBLEMS: tuple[Problem, ...] = (
    _provable("curry", ((P & Q) >> R) >> (P >> (Q >> R))),
    _provable("uncurry", (P >> (Q >> R)) >> ((P & Q) >> R)),
    _provable("and_or_distrib", (P & (Q | R)) >> ((P & Q) | (P & R))),
    _provable("or_and_distrib", (P | (Q & R)) >> ((P | Q) & (P | R))),
    _provable("or_and_distrib_back", ((P | Q) & (P | R)) >> (P | (Q & R))),
    _provable("dn_intro", P >> ~~P),
    _provable("triple_neg", ~~~P >> ~P),
    _provable("dn_em", ~~(P | ~P)),
    _provable("dn_peirce", ~~(((P >> Q) >> P) >> P)),
    _provable("de_morgan_or", Iff(~(P | Q), ~P & ~Q)),
    _provable("de_morgan_and_weak", (~P | ~Q) >> ~(P & Q)),
    _provable("contrapose", (P >> Q) >> (~Q >> ~P)),
    _provable("imp_distrib", (P >> (Q >> R)) >> ((P >> Q) >> (P >> R))),
    _provable("dn_imp", ~~(P >> Q) >> (~~P >> ~~Q)),
    _provable("or_elim", ((P >> R) & (Q >> R)) >> ((P | Q) >> R)),
    _provable("not_or_imp", (~P | Q) >> (P >> Q)),
    _provable("dn_de_morgan", ~~(~(P & Q) >> (~P | ~Q))),
    _provable("pigeonhole_3_2", _pigeonhole(2), "PHP(3, 2)"),
    _provable("pigeonhole_4_3", _pigeonhole(3), "PHP(4, 3)"),
    _provable("chain_8", _chain(8)),
    _unprovable("em", P | ~P, "excluded middle"),
    _unprovable("dne", ~~P >> P, "double negation elimination"),
    _unprovable("peirce", ((P >> Q) >> P) >> P, "Peirce's law"),
    _unprovable("dummett", (P >> Q) | (Q >> P), "Gödel–Dummett"),
    _unprovable("de_morgan_and", ~(P & Q) >> (~P | ~Q), "classical De Morgan direction"),
)
