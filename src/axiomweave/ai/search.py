"""Goal-directed theorem search (ai-spec §4).

A candidate `∀x̄. B₁ → … → Bₙ → C` matches the goal when its conclusion, after
dropping the fewest premises, can be made α-equivalent to the goal by choosing
the universal variables x̄ and the schematic variables. The instance is built
with `ctx.thm` and `ctx.spec`, so nothing here is trusted.
"""

from collections.abc import Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any

from axiomweave.core.expressions import PredicateSymbol, Prop, Term, VarKey
from axiomweave.errors import AxwError

if TYPE_CHECKING:
    from axiomweave.language.proof import Fact, ProofContext

DEFAULT_LIMIT = 10

# A pairing of bound variables: (pattern variable, target variable), innermost last.
Bound = tuple[tuple[VarKey, VarKey], ...]


class _NoMatch(Exception):
    pass


@dataclass(frozen=True)
class SearchResult:
    """A theorem or axiom that fits the current goal (ai-spec §4.4)."""

    name: str
    fact: "Fact"
    premises: tuple[Prop, ...]
    axioms: frozenset[str]
    code: str
    generic: bool = False  # the matched conclusion is a bare schematic variable

    def __str__(self) -> str:
        return f"{self.name} : {self.code}"


# --- matching (ai-spec §4.3) ---------------------------------------------------------


def _lookup(bound: Bound, key: VarKey, side: int) -> int | None:
    for i in range(len(bound) - 1, -1, -1):
        if bound[i][side] == key:
            return i
    return None


class _Matcher:
    def __init__(self, metavars: Sequence[Term]) -> None:
        self.metavars = {v.key: v for v in metavars}
        self.terms: dict[VarKey, Term] = {}
        self.atoms: dict[str, Prop] = {}
        self.predicates: dict[str, tuple[tuple[Term, ...], Prop]] = {}

    def _closed_under(self, free: frozenset[VarKey], bound: Bound, allowed: set[VarKey]) -> None:
        """Fail if a target variable bound in the pattern scope escapes (except `allowed`)."""
        for key in free:
            if key not in allowed and _lookup(bound, key, 1) is not None:
                raise _NoMatch

    def term(self, p: Term, t: Term, bound: Bound) -> None:
        if p.sort != t.sort:
            raise _NoMatch
        pn = p._node
        if pn[0] == "var":
            index = _lookup(bound, p.key, 0)
            if index is not None:
                if not t.is_var or _lookup(bound, t.key, 1) != index:
                    raise _NoMatch
                return
            if p.key not in self.metavars:
                raise _NoMatch
            self._closed_under(t.free_vars(), bound, set())
            known = self.terms.get(p.key)
            if known is None:
                self.terms[p.key] = t
            elif known != t:
                raise _NoMatch
            return
        tn = t._node
        if tn[0] != "app" or tn[1].name != pn[1].name or len(tn[2]) != len(pn[2]):
            raise _NoMatch
        for a, b in zip(pn[2], tn[2], strict=True):
            self.term(a, b, bound)

    def prop(self, p: Prop, t: Prop, bound: Bound) -> None:
        tag = p.tag
        if tag == "atom":
            self._closed_under(t.free_vars(), bound, set())
            known = self.atoms.get(p.name)
            if known is None:
                self.atoms[p.name] = t
            elif known != t:
                raise _NoMatch
            return
        if tag == "pvar":
            self._pvar(p, t, bound)
            return
        if tag != t.tag:
            raise _NoMatch
        if tag == "false":
            return
        if tag == "pred":
            if p._node[1].name != t._node[1].name:
                raise _NoMatch
            for a, b in zip(p.args, t.args, strict=True):
                self.term(a, b, bound)
            return
        if tag == "eq":
            for a, b in zip(p.sides, t.sides, strict=True):
                self.term(a, b, bound)
            return
        if tag in ("forall", "exists"):
            if p.var.sort != t.var.sort:
                raise _NoMatch
            self.prop(p.body, t.body, (*bound, (p.var.key, t.var.key)))
            return
        self.prop(p.left, t.left, bound)
        self.prop(p.right, t.right, bound)

    def _pvar(self, p: Prop, t: Prop, bound: Bound) -> None:
        """Miller pattern P(y₁, …, yₘ) with distinct variables bound in the pattern."""
        indices = []
        for arg in p.args:
            index = _lookup(bound, arg.key, 0) if arg.is_var else None
            if index is None:
                raise _NoMatch  # unsupported argument form
            indices.append(index)
        if len(set(indices)) != len(indices):
            raise _NoMatch
        params = tuple(
            _target_var(bound[i][1], arg) for i, arg in zip(indices, p.args, strict=True)
        )
        self._closed_under(t.free_vars(), bound, {v.key for v in params})
        known = self.predicates.get(p.name)
        if known is None:
            self.predicates[p.name] = (params, t)
            return
        old_params, body = known
        renamed = body
        for old, new in zip(old_params, params, strict=True):
            renamed = renamed.subst_var(old, new)
        if renamed != t:
            raise _NoMatch


def _target_var(key: VarKey, pattern_arg: Term) -> Term:
    from axiomweave.core.expressions import Var

    return Var(key[0], pattern_arg.sort)


# --- candidates and results (ai-spec §4.2, §4.4) -------------------------------------


def _splits(statement: Prop) -> list[tuple[list[Term], Prop]]:
    """(universal variables to instantiate, rest), stripping 0, 1, … leading ∀."""
    result: list[tuple[list[Term], Prop]] = [([], statement)]
    prefix: list[Term] = []
    body = statement
    while body.tag == "forall":
        prefix.append(body.var)
        body = body.body
        result.append((list(prefix), body))
    return result


def _premise_split(fact_prop: Prop, goal: Prop) -> tuple[Prop, ...] | None:
    """Premises in the shortest unfolding of fact_prop whose conclusion is the goal."""
    premises: list[Prop] = []
    current = fact_prop
    while True:
        if current == goal:
            return tuple(premises)
        if current.tag != "imp":
            return None
        premises.append(current.left)
        current = current.right


def _code(short: str, subst: dict[Any, Any], terms: Sequence[Term]) -> str:
    text = f"ctx.thm({short})"
    if subst:
        parts = []
        for key, value in subst.items():
            if isinstance(value, tuple):
                params = ", ".join(v.name for v in value[0])
                parts.append(f"{key.name}: (({params},), {value[1]})")
            else:
                parts.append(f"{key.name}: {value}")
        text = f"ctx.thm({short}, {{{', '.join(parts)}}})"
    if terms:
        text = f"ctx.spec({text}, {', '.join(str(t) for t in terms)})"
    return text


def candidate(
    ctx: "ProofContext", handle: object, axioms: frozenset[str], goal: Prop
) -> SearchResult | None:
    """The best instance of one declaration for the goal, or None."""
    ref = ctx._resolve(handle)
    best: SearchResult | None = None
    for prefix, body in _splits(ref.statement):
        conclusion = body
        while True:
            result = _instance(ctx, ref, axioms, goal, prefix, conclusion)
            if result is not None:
                if best is None or len(result.premises) < len(best.premises):
                    best = result
                break
            if conclusion.tag != "imp":
                break
            conclusion = conclusion.right
    return best


def _instance(
    ctx: "ProofContext",
    ref: Any,
    axioms: frozenset[str],
    goal: Prop,
    prefix: list[Term],
    conclusion: Prop,
) -> SearchResult | None:
    matcher = _Matcher(prefix)
    try:
        matcher.prop(conclusion, goal, ())
    except _NoMatch:
        return None
    signature = ref.statement.signature()
    if any(v.key not in matcher.terms for v in prefix):
        return None
    subst: dict[Any, Any] = {}
    for name, sorts in signature.items():
        if sorts:
            if name not in matcher.predicates:
                return None
            subst[PredicateSymbol(name, sorts)] = matcher.predicates[name]
        else:
            if name not in matcher.atoms:
                return None
            subst[Prop.symbol(name)] = matcher.atoms[name]
    terms = [matcher.terms[v.key] for v in prefix]
    try:
        fact = ctx._instance(ref, subst)
        if terms:
            fact = ctx.spec(fact, *terms)
        ctx._in_scope(fact, ctx._current())
    except AxwError:
        return None
    premises = _premise_split(fact.prop, goal)
    if premises is None or goal in premises:  # a premise equal to the goal makes no progress
        return None
    short = ref.name.rsplit(".", 1)[1]
    generic = conclusion.tag in ("atom", "pvar")
    return SearchResult(ref.name, fact, premises, axioms, _code(short, subst, terms), generic)


def search(
    ctx: "ProofContext",
    candidates: Sequence[tuple[object, frozenset[str]]],
    limit: int,
) -> tuple[SearchResult, ...]:
    goal = ctx._current().target
    found: list[tuple[tuple[int, bool, bool, int, int], SearchResult]] = []
    for index, (handle, axioms) in enumerate(candidates):
        result = candidate(ctx, handle, axioms, goal)
        if result is not None:
            classical = "classical.em" in axioms
            key = (len(result.premises), result.generic, classical, len(axioms), index)
            found.append((key, result))
    found.sort(key=lambda item: item[0])
    return tuple(result for _, result in found[:limit])
