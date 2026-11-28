"""Benchmark problems, baseline solvers and the measuring harness (ai-spec §5).

Success is counted only when the kernel verifies the problem theorem. Every
attempt runs in a fresh problem theory, so a failed attempt cannot affect the
next one.
"""

import time
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from typing import Any

from axiomweave.core.expressions import Prop
from axiomweave.errors import TacticError
from axiomweave.language.proof import ProofContext
from axiomweave.language.theory import Status, Theory

CATEGORIES = ("propositional", "first_order", "arithmetic")
Proof = Callable[[ProofContext], None]


@dataclass(frozen=True)
class Problem:
    """A benchmark problem (ai-spec §5.2). `name` is `<tag>.<short name>`."""

    name: str
    category: str
    statement: Callable[[], Prop]
    expected: str  # "provable" or "unprovable"
    imports: tuple[Theory, ...] = ()
    reference: Proof | None = None
    note: str = ""


@dataclass(frozen=True)
class Record:
    """The measurement of one problem with one solver (ai-spec §5.4)."""

    solver: str
    problem: str
    category: str
    expected: str
    status: str
    seconds: float
    nodes: int | None
    axioms: tuple[str, ...]
    error: str = ""
    via: str = ""  # for `portfolio`: the solver that succeeded

    @property
    def solved(self) -> bool:
        return self.status == Status.VERIFIED.value

    def to_json(self) -> dict[str, Any]:
        return {
            "solver": self.solver,
            "problem": self.problem,
            "category": self.category,
            "expected": self.expected,
            "status": self.status,
            "seconds": round(self.seconds, 4),
            "nodes": self.nodes,
            "axioms": list(self.axioms),
            "error": self.error,
            "via": self.via,
        }


# --- baseline solvers (ai-spec §5.3) --------------------------------------------------


def _intro_all(ctx: ProofContext, implications: bool) -> None:
    while ctx.goals[0].target.tag == "forall" or (
        implications and ctx.goals[0].target.tag == "imp"
    ):
        ctx.intro()


def solve_auto(ctx: ProofContext) -> None:
    ctx.auto()


def solve_search(ctx: ProofContext) -> None:
    _intro_all(ctx, implications=True)
    for result in ctx.search():
        if not result.premises:
            ctx.exact(result.fact)
            return
    raise TacticError("search: no theorem closes the goal")


def solve_ring(ctx: ProofContext) -> None:
    _intro_all(ctx, implications=False)
    ctx.ring()


SOLVERS: dict[str, Proof] = {"auto": solve_auto, "search": solve_search, "ring": solve_ring}
PORTFOLIO = ("auto", "search", "ring")
SOLVER_NAMES = (*SOLVERS, "portfolio")


# --- harness (ai-spec §5.4) ----------------------------------------------------------


@dataclass
class _Attempt:
    status: str
    seconds: float
    nodes: int | None
    axioms: tuple[str, ...]
    error: str = ""
    extra: dict[str, Any] = field(default_factory=dict)


def _count_nodes(value: object) -> int:
    if isinstance(value, dict):
        own = 1 if "rule" in value else 0
        return own + sum(_count_nodes(v) for v in value.values())
    if isinstance(value, list):
        return sum(_count_nodes(v) for v in value)
    return 0


def problem_theory(problem: Problem, proof: Proof) -> Theory:
    """A fresh theory `bench.<tag>` with the problem theorem proved by `proof`."""
    tag, short = problem.name.split(".", 1)
    thy = Theory(f"bench.{tag}", imports=list(problem.imports))
    statement = problem.statement()

    def function() -> Prop:
        return statement

    function.__name__ = short
    thy.proof(thy.theorem(function))(proof)
    return thy


def attempt(problem: Problem, proof: Proof) -> _Attempt:
    start = time.perf_counter()
    thy = problem_theory(problem, proof)
    result = thy.check().results[-1]
    seconds = time.perf_counter() - start
    nodes = None
    if result.status is Status.VERIFIED:
        bundle = thy._export or {}
        decl = next(d for d in bundle["declarations"] if d["name"] == result.name)
        nodes = _count_nodes(decl["proof"])
    error = str(result.diagnostics[0]).splitlines()[0] if result.diagnostics else ""
    return _Attempt(result.status.value, seconds, nodes, tuple(sorted(result.axioms or ())), error)


def run(problem: Problem, solver: str) -> Record:
    """Measure one problem with one solver."""
    names = PORTFOLIO if solver == "portfolio" else (solver,)
    total = 0.0
    last: _Attempt | None = None
    via = ""
    for name in names:
        last = attempt(problem, SOLVERS[name])
        total += last.seconds
        if last.status == Status.VERIFIED.value:
            via = name if solver == "portfolio" else ""
            break
    assert last is not None
    return Record(
        solver,
        problem.name,
        problem.category,
        problem.expected,
        last.status,
        total,
        last.nodes,
        last.axioms,
        "" if via or last.status == Status.VERIFIED.value else last.error,
        via,
    )


def run_all(problems: Iterable[Problem], solvers: Sequence[str]) -> list[Record]:
    return [run(problem, solver) for problem in problems for solver in solvers]


def check_references(problems: Iterable[Problem]) -> list[Record]:
    """Verify the problem set itself: every provable problem's reference proof."""
    records = []
    for problem in problems:
        if problem.reference is None:
            continue
        result = attempt(problem, problem.reference)
        records.append(
            Record(
                "reference",
                problem.name,
                problem.category,
                problem.expected,
                result.status,
                result.seconds,
                result.nodes,
                result.axioms,
                result.error,
            )
        )
    return records


def alarms(records: Iterable[Record]) -> list[str]:
    """Defect signals: verified unprovable problems and failing reference proofs."""
    found = []
    for r in records:
        if r.expected == "unprovable" and r.solved:
            found.append(f"{r.problem}: expected unprovable but {r.solver} verified it")
        if r.solver == "reference" and not r.solved:
            found.append(f"{r.problem}: reference proof failed: {r.error}")
    return found
