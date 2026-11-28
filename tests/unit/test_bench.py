"""Benchmark problem set, baseline solvers and harness (ai-spec §5)."""

from collections import Counter

import pytest

from axiomweave import Axiom, Theorem
from axiomweave.bench import CATEGORIES, SOLVER_NAMES, Record, alarms, check_references, run
from axiomweave.bench.problems import PROBLEMS

BY_NAME = {p.name: p for p in PROBLEMS}


def test_problem_set_shape() -> None:
    assert len(BY_NAME) == len(PROBLEMS) == 60
    assert Counter(p.category for p in PROBLEMS) == {
        "propositional": 25,
        "first_order": 15,
        "arithmetic": 20,
    }
    for p in PROBLEMS:
        assert p.category in CATEGORIES
        assert p.expected in ("provable", "unprovable")
        assert (p.reference is not None) == (p.expected == "provable"), p.name
        assert p.name.count(".") == 1


def test_reference_proofs_verify() -> None:
    pytest.importorskip("sympy")  # some arithmetic references use ctx.ring()
    records = check_references(PROBLEMS)
    assert len(records) == sum(p.expected == "provable" for p in PROBLEMS) == 51
    assert alarms(records) == []
    assert all(r.solved and r.nodes for r in records)


def test_problems_do_not_repeat_imported_theorems() -> None:
    for p in PROBLEMS:
        statement = p.statement()
        for theory in p.imports:
            for decl in theory.environment():
                if isinstance(decl, Axiom | Theorem):
                    assert decl.statement != statement, f"{p.name} repeats {decl.name}"


def test_solvers_and_portfolio() -> None:
    curry = run(BY_NAME["prop.curry"], "auto")
    assert curry.solved and curry.nodes and curry.axioms == ()
    assert not run(BY_NAME["prop.curry"], "ring").solved
    pytest.importorskip("sympy")
    two = run(BY_NAME["arith.two_plus_two"], "portfolio")
    assert two.solved and two.via == "ring" and two.error == ""
    open_problem = run(BY_NAME["arith.n_ne_succ"], "portfolio")
    assert not open_problem.solved and open_problem.via == "" and open_problem.error


def test_unprovable_problems_are_never_verified() -> None:
    records = [
        run(p, solver)
        for p in PROBLEMS
        if p.expected == "unprovable"
        for solver in ("auto", "search", "ring")
    ]
    assert records and alarms(records) == []


def test_records_and_alarms() -> None:
    record = Record("auto", "x.y", "propositional", "unprovable", "VERIFIED", 0.5, 3, ())
    assert record.to_json()["solver"] == "auto"
    assert set(record.to_json()) == {
        "solver",
        "problem",
        "category",
        "expected",
        "status",
        "seconds",
        "nodes",
        "axioms",
        "error",
        "via",
    }
    assert alarms([record]) == ["x.y: expected unprovable but auto verified it"]
    failed = Record("reference", "x.z", "propositional", "provable", "REJECTED", 0.1, None, (), "e")
    assert alarms([failed]) == ["x.z: reference proof failed: e"]
    assert SOLVER_NAMES == ("auto", "search", "ring", "portfolio")
