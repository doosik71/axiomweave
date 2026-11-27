"""Builders for L0 certificate JSON used by kernel tests."""

import json
from typing import Any

from axiomweave.kernel import bundle_hash, declaration_hash

JSON = Any


def atom(name: str) -> JSON:
    return ["atom", name]


FALSE: JSON = ["false"]


def and_(a: JSON, b: JSON) -> JSON:
    return ["and", a, b]


def or_(a: JSON, b: JSON) -> JSON:
    return ["or", a, b]


def imp(*parts: JSON) -> JSON:
    """Right-associative implication: imp(A, B, C) = A -> (B -> C)."""
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = ["imp", part, result]
    return result


def neg(a: JSON) -> JSON:
    return imp(a, FALSE)


P, Q, R = atom("P"), atom("Q"), atom("R")


def hyp(name: str) -> JSON:
    return {"rule": "hyp", "name": name}


def imp_i(name: str, hyp_prop: JSON, body: JSON) -> JSON:
    return {"rule": "imp_i", "name": name, "hyp": hyp_prop, "body": body}


def imp_e(fn: JSON, arg: JSON) -> JSON:
    return {"rule": "imp_e", "fn": fn, "arg": arg}


def and_i(left: JSON, right: JSON) -> JSON:
    return {"rule": "and_i", "left": left, "right": right}


def and_e1(of: JSON) -> JSON:
    return {"rule": "and_e1", "of": of}


def and_e2(of: JSON) -> JSON:
    return {"rule": "and_e2", "of": of}


def or_i1(of: JSON, right: JSON) -> JSON:
    return {"rule": "or_i1", "of": of, "right": right}


def or_i2(left: JSON, of: JSON) -> JSON:
    return {"rule": "or_i2", "left": left, "of": of}


def or_e(of: JSON, left_name: str, left: JSON, right_name: str, right: JSON) -> JSON:
    return {
        "rule": "or_e",
        "of": of,
        "left_name": left_name,
        "left": left,
        "right_name": right_name,
        "right": right,
    }


def false_e(of: JSON, goal: JSON) -> JSON:
    return {"rule": "false_e", "of": of, "goal": goal}


def ref(rule: str, decl: JSON, subst: dict[str, JSON] | None = None) -> JSON:
    """A `thm` or `ax` node referring to a declaration built by `axiom`/`theorem`."""
    return {"rule": rule, "name": decl["name"], "hash": decl["hash"], "subst": subst or {}}


def axiom(name: str, statement: JSON) -> JSON:
    decl = {"kind": "axiom", "name": name, "statement": statement}
    decl["hash"] = declaration_hash(decl)
    return decl


def theorem(name: str, statement: JSON, proof: JSON, axioms: tuple[str, ...] = ()) -> JSON:
    decl = {"kind": "theorem", "name": name, "statement": statement, "proof": proof}
    decl["hash"] = declaration_hash(decl)
    decl["axioms"] = sorted(axioms)
    return decl


def rehash(decl: JSON) -> JSON:
    """Recompute a declaration's hash after a test modified it."""
    decl["hash"] = declaration_hash(decl)
    return decl


def bundle(*decls: JSON, theory: str = "demo.logic") -> JSON:
    obj = {
        "format": "axwp",
        "format_version": 1,
        "spec_version": "0.1",
        "fragment": "L0",
        "kernel_version": "0.1.0.dev0",
        "theory": theory,
        # JSON round trip copies without Python-level recursion (deep test inputs).
        "declarations": json.loads(json.dumps(list(decls))),
    }
    obj["bundle_hash"] = bundle_hash(obj)
    return obj


def encode(obj: JSON) -> bytes:
    return json.dumps(obj, indent=2).encode("utf-8")
