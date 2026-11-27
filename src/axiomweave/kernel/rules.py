"""Conclusion recomputation for L0 derivations (kernel-spec §8.4, logic-spec §8.1)."""

from dataclasses import dataclass
from typing import NoReturn

from axiomweave.kernel.certificate import Node, Prop, PropTable
from axiomweave.kernel.errors import (
    E_HASH_MISMATCH,
    E_HYP_NOT_FRESH,
    E_HYP_UNKNOWN,
    E_RULE_MISMATCH,
    E_SUBST_DOMAIN,
    E_UNKNOWN_DECL,
    KernelError,
)


@dataclass(frozen=True)
class Accepted:
    """An accepted declaration in the environment E."""

    kind: str  # "axiom" or "theorem"
    hash: str
    statement: Prop
    axioms: frozenset[str]


Environment = dict[str, Accepted]
Context = dict[str, Prop]
Result = tuple[Prop, frozenset[str]]  # conclusion, axiom dependencies


def _fail(code: str, path: str, message: str) -> NoReturn:
    raise KernelError(code, path, message)


def _expect(table: PropTable, prop: Prop, tag: str, path: str, rule: str) -> tuple[Prop, Prop]:
    node = table.nodes[prop]
    if node[0] != tag:
        _fail(E_RULE_MISMATCH, path, f"{rule} needs a '{tag}' premise, got {table.show(prop)}")
    return node[1], node[2]


def _fresh(gamma: Context, name: str, path: str) -> None:
    if name in gamma:
        _fail(E_HYP_NOT_FRESH, path, f"hypothesis name {name!r} is already in the context")


def infer(env: Environment, table: PropTable, gamma: Context, node: Node) -> Result:
    """Recompute the conclusion of a derivation node in context gamma."""
    rule, path = node[0], node[1]

    if rule == "hyp":
        name = node[2]
        if name not in gamma:
            _fail(E_HYP_UNKNOWN, path, f"hypothesis {name!r} is not in the context")
        return gamma[name], frozenset()

    if rule == "and_i":
        left, ax1 = infer(env, table, gamma, node[2])
        right, ax2 = infer(env, table, gamma, node[3])
        return table.make(("and", left, right)), ax1 | ax2

    if rule in ("and_e1", "and_e2"):
        premise, axioms = infer(env, table, gamma, node[2])
        left, right = _expect(table, premise, "and", path, rule)
        return (left if rule == "and_e1" else right), axioms

    if rule == "or_i1":
        left, axioms = infer(env, table, gamma, node[2])
        return table.make(("or", left, node[3])), axioms

    if rule == "or_i2":
        right, axioms = infer(env, table, gamma, node[3])
        return table.make(("or", node[2], right)), axioms

    if rule == "or_e":
        _, _, of, left_name, left, right_name, right = node
        premise, ax0 = infer(env, table, gamma, of)
        a, b = _expect(table, premise, "or", path, rule)
        _fresh(gamma, left_name, f"{path}.left_name")
        _fresh(gamma, right_name, f"{path}.right_name")
        c1, ax1 = infer(env, table, {**gamma, left_name: a}, left)
        c2, ax2 = infer(env, table, {**gamma, right_name: b}, right)
        if c1 != c2:
            _fail(
                E_RULE_MISMATCH,
                path,
                f"or_e branches conclude {table.show(c1)} and {table.show(c2)}",
            )
        return c1, ax0 | ax1 | ax2

    if rule == "imp_i":
        _, _, name, hyp, body = node
        _fresh(gamma, name, f"{path}.name")
        conclusion, axioms = infer(env, table, {**gamma, name: hyp}, body)
        return table.make(("imp", hyp, conclusion)), axioms

    if rule == "imp_e":
        fn, ax1 = infer(env, table, gamma, node[2])
        arg, ax2 = infer(env, table, gamma, node[3])
        antecedent, consequent = _expect(table, fn, "imp", path, rule)
        if arg != antecedent:
            _fail(
                E_RULE_MISMATCH,
                path,
                f"imp_e argument is {table.show(arg)}, expected {table.show(antecedent)}",
            )
        return consequent, ax1 | ax2

    if rule == "false_e":
        premise, axioms = infer(env, table, gamma, node[2])
        if table.nodes[premise][0] != "false":
            _fail(E_RULE_MISMATCH, path, f"false_e needs ⊥, got {table.show(premise)}")
        return node[3], axioms

    if rule in ("thm", "ax"):
        _, _, name, ref_hash, subst = node
        kind = "theorem" if rule == "thm" else "axiom"
        decl = env.get(name)
        if decl is None or decl.kind != kind:
            _fail(E_UNKNOWN_DECL, path, f"no accepted {kind} named {name!r} before this point")
        if ref_hash != decl.hash:
            _fail(E_HASH_MISMATCH, f"{path}.hash", f"reference hash does not match {name!r}")
        extra = sorted(set(subst) - table.atoms(decl.statement))
        if extra:
            _fail(E_SUBST_DOMAIN, f"{path}.subst", f"atoms {extra} do not occur in {name!r}")
        conclusion = table.substitute(decl.statement, subst)
        axioms = frozenset({name}) if rule == "ax" else decl.axioms
        return conclusion, axioms

    raise AssertionError(f"unhandled rule {rule!r}")  # decoding admits only known rules
