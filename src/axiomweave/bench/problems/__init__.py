"""The v0.1 benchmark problem set (ai-spec §5.2)."""

from axiomweave.bench.core import Problem
from axiomweave.bench.problems import arithmetic, first_order, propositional

PROBLEMS: tuple[Problem, ...] = (
    *propositional.PROBLEMS,
    *first_order.PROBLEMS,
    *arithmetic.PROBLEMS,
)
