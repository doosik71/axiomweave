"""Type checking and conclusion recomputation (kernel-spec §8.4, §13.7–13.8; logic-spec §8, §12).

Individual variables are de Bruijn indices. `delta` is the tuple of sorts of
the variables in scope; index i refers to delta[-1 - i]. A hypothesis records
the depth len(delta) at which it was introduced and is shifted on lookup.
"""

from dataclasses import dataclass, field
from typing import NoReturn

from axiomweave.kernel.certificate import PROP_RESULT, Node, Prop, PropTable
from axiomweave.kernel.errors import (
    E_HASH_MISMATCH,
    E_HYP_NOT_FRESH,
    E_HYP_UNKNOWN,
    E_RULE_MISMATCH,
    E_SUBST_DOMAIN,
    E_TYPE,
    E_UNKNOWN_DECL,
    KernelError,
)


@dataclass(frozen=True)
class Accepted:
    """An accepted declaration in the environment E."""

    kind: str  # "axiom", "theorem", "sort" or "const"
    hash: str
    statement: Prop | None = None
    axioms: frozenset[str] = frozenset()
    # Argument sorts of each schematic variable of the statement (() for atoms).
    signature: dict[str, tuple[str, ...]] = field(default_factory=dict)
    args: tuple[str, ...] = ()  # const argument sorts
    result: str = ""  # const result sort or PROP_RESULT


Environment = dict[str, Accepted]
Delta = tuple[str, ...]
Context = dict[str, tuple[Prop, int]]  # hypothesis name -> (proposition, depth)
Result = tuple[Prop, frozenset[str]]  # conclusion, axiom dependencies


def _fail(code: str, path: str, message: str) -> NoReturn:
    raise KernelError(code, path, message)


# --- type checking (kernel-spec §13.7) -----------------------------------------


def _sort_decl(env: Environment, name: str, path: str) -> None:
    decl = env.get(name)
    if decl is None or decl.kind != "sort":
        _fail(E_UNKNOWN_DECL, path, f"no accepted sort named {name!r} before this point")


def _const(env: Environment, name: str, path: str) -> Accepted:
    decl = env.get(name)
    if decl is None or decl.kind != "const":
        _fail(E_UNKNOWN_DECL, path, f"no accepted constant named {name!r} before this point")
    return decl


def _check_args(
    env: Environment,
    table: PropTable,
    args: tuple[Prop, ...],
    expected: tuple[str, ...],
    delta: Delta,
    path: str,
    name: str,
) -> None:
    if len(args) != len(expected):
        _fail(E_TYPE, path, f"{name!r} takes {len(expected)} arguments, got {len(args)}")
    for i, (arg, sort) in enumerate(zip(args, expected, strict=True)):
        actual = sort_of(env, table, arg, delta, path)
        if actual != sort:
            _fail(E_TYPE, path, f"argument {i} of {name!r} has sort {actual!r}, expected {sort!r}")


def sort_of(env: Environment, table: PropTable, term: Prop, delta: Delta, path: str) -> str:
    """The sort of an individual term in variable context delta."""
    node = table.nodes[term]
    if node[0] == "var":
        index = node[1]
        if index >= len(delta):
            _fail(E_TYPE, path, f"variable index {index} is not bound ({len(delta)} in scope)")
        return delta[-1 - index]
    if node[0] == "app":
        decl = _const(env, node[1], path)
        if decl.result == PROP_RESULT:
            _fail(E_TYPE, path, f"predicate {node[1]!r} is used as a term")
        _check_args(env, table, node[2], decl.args, delta, path, node[1])
        return decl.result
    _fail(E_TYPE, path, f"expected a term, got {table.show(term)}")


def check_prop(
    env: Environment,
    table: PropTable,
    prop: Prop,
    delta: Delta,
    path: str,
    signature: dict[str, tuple[str, ...]] | None = None,
) -> None:
    """Check that prop is well formed in delta. With `signature`, also record the
    argument sorts of each schematic variable and require them to be unique."""

    def record(name: str, sorts: tuple[str, ...]) -> None:
        if signature is None:
            return
        previous = signature.setdefault(name, sorts)
        if previous != sorts:
            _fail(
                E_TYPE,
                path,
                f"schematic variable {name!r} is used with argument sorts {list(previous)} "
                f"and {list(sorts)}",
            )

    def go(p: Prop, d: Delta) -> None:
        node = table.nodes[p]
        tag = node[0]
        if tag == "atom":
            record(node[1], ())
        elif tag == "pvar":
            record(node[1], tuple(sort_of(env, table, a, d, path) for a in node[2]))
        elif tag == "pred":
            decl = _const(env, node[1], path)
            if decl.result != PROP_RESULT:
                _fail(E_TYPE, path, f"function {node[1]!r} is used as a predicate")
            _check_args(env, table, node[2], decl.args, d, path, node[1])
        elif tag in ("and", "or", "imp"):
            go(node[1], d)
            go(node[2], d)
        elif tag in ("forall", "exists"):
            _sort_decl(env, node[1], path)
            go(node[2], (*d, node[1]))
        elif tag != "false":
            _fail(E_TYPE, path, f"expected a proposition, got {table.show(p)}")

    go(prop, delta)


def check_statement(
    env: Environment, table: PropTable, prop: Prop, path: str
) -> dict[str, tuple[str, ...]]:
    """A declared statement must be closed with unique schematic variable names."""
    signature: dict[str, tuple[str, ...]] = {}
    check_prop(env, table, prop, (), path, signature)
    return signature


# --- conclusion recomputation (kernel-spec §8.4, §13.8) --------------------------


def _expect(table: PropTable, prop: Prop, tag: str, path: str, rule: str) -> tuple[Prop, Prop]:
    node = table.nodes[prop]
    if node[0] != tag:
        _fail(E_RULE_MISMATCH, path, f"{rule} needs a '{tag}' premise, got {table.show(prop)}")
    return node[1], node[2]


def _expect_quantifier(
    table: PropTable, prop: Prop, tag: str, path: str, rule: str
) -> tuple[str, Prop]:
    sort, body = _expect(table, prop, tag, path, rule)
    return str(sort), body


def _fresh(gamma: Context, name: str, path: str) -> None:
    if name in gamma:
        _fail(E_HYP_NOT_FRESH, path, f"hypothesis name {name!r} is already in the context")


class Checker:
    """Recomputes conclusions. `typed` enables the L1 well-formedness checks of the
    propositions and terms written in derivation nodes (always true for L1 bundles)."""

    def __init__(self, env: Environment, table: PropTable, typed: bool) -> None:
        self.env = env
        self.table = table
        self.typed = typed

    def _wf(self, prop: Prop, delta: Delta, path: str) -> Prop:
        if self.typed:
            check_prop(self.env, self.table, prop, delta, path)
        return prop

    def infer(self, delta: Delta, gamma: Context, node: Node) -> Result:
        table = self.table
        rule, path = node[0], node[1]

        if rule == "hyp":
            name = node[2]
            if name not in gamma:
                _fail(E_HYP_UNKNOWN, path, f"hypothesis {name!r} is not in the context")
            prop, depth = gamma[name]
            return table.shift(prop, len(delta) - depth), frozenset()

        if rule == "and_i":
            left, ax1 = self.infer(delta, gamma, node[2])
            right, ax2 = self.infer(delta, gamma, node[3])
            return table.make(("and", left, right)), ax1 | ax2

        if rule in ("and_e1", "and_e2"):
            premise, axioms = self.infer(delta, gamma, node[2])
            left, right = _expect(table, premise, "and", path, rule)
            return (left if rule == "and_e1" else right), axioms

        if rule == "or_i1":
            left, axioms = self.infer(delta, gamma, node[2])
            right = self._wf(node[3], delta, f"{path}.right")
            return table.make(("or", left, right)), axioms

        if rule == "or_i2":
            left = self._wf(node[2], delta, f"{path}.left")
            right, axioms = self.infer(delta, gamma, node[3])
            return table.make(("or", left, right)), axioms

        if rule == "or_e":
            _, _, of, left_name, left, right_name, right = node
            premise, ax0 = self.infer(delta, gamma, of)
            a, b = _expect(table, premise, "or", path, rule)
            _fresh(gamma, left_name, f"{path}.left_name")
            _fresh(gamma, right_name, f"{path}.right_name")
            depth = len(delta)
            c1, ax1 = self.infer(delta, {**gamma, left_name: (a, depth)}, left)
            c2, ax2 = self.infer(delta, {**gamma, right_name: (b, depth)}, right)
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
            self._wf(hyp, delta, f"{path}.hyp")
            conclusion, axioms = self.infer(delta, {**gamma, name: (hyp, len(delta))}, body)
            return table.make(("imp", hyp, conclusion)), axioms

        if rule == "imp_e":
            fn, ax1 = self.infer(delta, gamma, node[2])
            arg, ax2 = self.infer(delta, gamma, node[3])
            antecedent, consequent = _expect(table, fn, "imp", path, rule)
            if arg != antecedent:
                _fail(
                    E_RULE_MISMATCH,
                    path,
                    f"imp_e argument is {table.show(arg)}, expected {table.show(antecedent)}",
                )
            return consequent, ax1 | ax2

        if rule == "false_e":
            premise, axioms = self.infer(delta, gamma, node[2])
            if table.nodes[premise][0] != "false":
                _fail(E_RULE_MISMATCH, path, f"false_e needs ⊥, got {table.show(premise)}")
            return self._wf(node[3], delta, f"{path}.goal"), axioms

        if rule == "all_i":
            _, _, sort, body = node
            _sort_decl(self.env, sort, f"{path}.sort")
            conclusion, axioms = self.infer((*delta, sort), gamma, body)
            return table.make(("forall", sort, conclusion)), axioms

        if rule == "all_e":
            premise, axioms = self.infer(delta, gamma, node[2])
            sort, body = _expect_quantifier(table, premise, "forall", path, rule)
            actual = sort_of(self.env, table, node[3], delta, f"{path}.term")
            if actual != sort:
                _fail(E_TYPE, f"{path}.term", f"term has sort {actual!r}, expected {sort!r}")
            return table.instantiate(body, (node[3],)), axioms

        if rule == "ex_i":
            _, _, prop, witness, of = node
            sort = sort_of(self.env, table, witness, delta, f"{path}.witness")
            self._wf(prop, (*delta, sort), f"{path}.prop")
            premise, axioms = self.infer(delta, gamma, of)
            expected = table.instantiate(prop, (witness,))
            if premise != expected:
                _fail(
                    E_RULE_MISMATCH,
                    path,
                    f"ex_i premise is {table.show(premise)}, expected {table.show(expected)}",
                )
            return table.make(("exists", sort, prop)), axioms

        if rule == "ex_e":
            _, _, of, name, body = node
            premise, ax0 = self.infer(delta, gamma, of)
            sort, prop = _expect_quantifier(table, premise, "exists", path, rule)
            _fresh(gamma, name, f"{path}.name")
            inner = (*delta, sort)
            conclusion, ax1 = self.infer(inner, {**gamma, name: (prop, len(inner))}, body)
            return table.lower(conclusion, f"{path}.body"), ax0 | ax1

        if rule in ("thm", "ax"):
            return self._instance(delta, node)

        raise AssertionError(f"unhandled rule {rule!r}")  # decoding admits only known rules

    def _instance(self, delta: Delta, node: Node) -> Result:
        rule, path, name, ref_hash, subst = node
        table = self.table
        kind = "theorem" if rule == "thm" else "axiom"
        decl = self.env.get(name)
        if decl is None or decl.kind != kind:
            _fail(E_UNKNOWN_DECL, path, f"no accepted {kind} named {name!r} before this point")
        if ref_hash != decl.hash:
            _fail(E_HASH_MISMATCH, f"{path}.hash", f"reference hash does not match {name!r}")
        assert decl.statement is not None
        extra = sorted(set(subst) - table.atoms(decl.statement))
        if extra:
            _fail(E_SUBST_DOMAIN, f"{path}.subst", f"atoms {extra} do not occur in {name!r}")
        for key, (params, body) in subst.items():
            sub = f"{path}.subst.{key}"
            expected = decl.signature.get(key, ())
            if params != expected:
                _fail(
                    E_TYPE,
                    sub,
                    f"{key!r} takes argument sorts {list(expected)}, value has {list(params)}",
                )
            self._wf(body, (*delta, *params), sub)
        conclusion = table.substitute(decl.statement, subst)
        axioms = frozenset({name}) if rule == "ax" else decl.axioms
        return conclusion, axioms
