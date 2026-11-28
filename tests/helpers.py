"""Builders for L0/L1 certificate JSON used by kernel tests."""

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


def bundle(*decls: JSON, theory: str = "demo.logic", fragment: str = "L0") -> JSON:
    obj = {
        "format": "axwp",
        "format_version": 1,
        "spec_version": "0.1",
        "fragment": fragment,
        "kernel_version": "0.1.0.dev0",
        "theory": theory,
        # JSON round trip copies without Python-level recursion (deep test inputs).
        "declarations": json.loads(json.dumps(list(decls))),
    }
    obj["bundle_hash"] = bundle_hash(obj)
    return obj


def l1_bundle(*decls: JSON, theory: str = "demo.fol") -> JSON:
    return bundle(*decls, theory=theory, fragment="L1")


# --- fragment L1 (kernel-spec §13) --------------------------------------------


def var(index: int) -> JSON:
    return ["var", index]


def app(const: str, *args: JSON) -> JSON:
    return ["app", const, list(args)]


def pred(const: str, *args: JSON) -> JSON:
    return ["pred", const, list(args)]


def pvar(name: str, *args: JSON) -> JSON:
    return ["pvar", name, list(args)]


def forall(sort: str, body: JSON) -> JSON:
    return ["forall", sort, body]


def exists(sort: str, body: JSON) -> JSON:
    return ["exists", sort, body]


def all_i(sort: str, body: JSON) -> JSON:
    return {"rule": "all_i", "sort": sort, "body": body}


def all_e(of: JSON, term: JSON) -> JSON:
    return {"rule": "all_e", "of": of, "term": term}


def ex_i(prop: JSON, witness: JSON, of: JSON) -> JSON:
    return {"rule": "ex_i", "prop": prop, "witness": witness, "of": of}


def ex_e(of: JSON, name: str, body: JSON) -> JSON:
    return {"rule": "ex_e", "of": of, "name": name, "body": body}


def lam(params: list[str], body: JSON) -> JSON:
    """A predicate-abstraction substitution value."""
    return {"params": params, "body": body}


def sort(name: str) -> JSON:
    decl = {"kind": "sort", "name": name}
    decl["hash"] = declaration_hash(decl)
    return decl


def const(name: str, args: list[str], result: str) -> JSON:
    decl = {"kind": "const", "name": name, "args": args, "result": result}
    decl["hash"] = declaration_hash(decl)
    return decl


def encode(obj: JSON) -> bytes:
    return json.dumps(obj, indent=2).encode("utf-8")


# --- fragment L2 (kernel-spec §14) --------------------------------------------


def l2_bundle(*decls: JSON, theory: str = "demo.eq") -> JSON:
    return bundle(*decls, theory=theory, fragment="L2")


def eq(left: JSON, right: JSON) -> JSON:
    return ["eq", left, right]


def eq_refl(term: JSON) -> JSON:
    return {"rule": "eq_refl", "term": term}


def eq_e(eq_proof: JSON, motive: JSON, of: JSON) -> JSON:
    return {"rule": "eq_e", "eq": eq_proof, "motive": motive, "of": of}
