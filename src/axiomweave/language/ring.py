"""Proof-producing normalization of semiring terms over `arith.Nat` (interop-spec §5.5).

Terms built from `zero`, `succ`, `add` and `mul` are read as polynomials whose
variables are the other subterms (atoms). The normalizer proves `t = nf(t)`
with the `arith` semiring theorems, using only `spec`, `congr`, `symm` and
`trans`, so the kernel checks every step. It is independent of SymPy.

Normal form: a left-nested sum of unit monomials in a fixed order, where a
unit monomial is a left-nested product of atoms in a fixed order, and the
empty monomial is `succ(zero)`. A coefficient c is written as c copies of its
monomial, so no numeral arithmetic is needed. The empty sum is `zero`.
"""

from collections.abc import Callable
from typing import TYPE_CHECKING, Any

from axiomweave.core.expressions import Term, Var
from axiomweave.errors import TacticError

if TYPE_CHECKING:
    from axiomweave.language.proof import Fact, ProofContext

NAT = "arith.Nat"
_SIGNATURES: dict[str, tuple[tuple[str, ...], str]] = {
    "arith.zero": ((), NAT),
    "arith.succ": ((NAT,), NAT),
    "arith.add": ((NAT, NAT), NAT),
    "arith.mul": ((NAT, NAT), NAT),
}

# Size limits (interop-spec §5.5). The certificate grows about cubically in the
# number of unit monomials, because every step restates the whole polynomial.
MAX_UNITS = 40
MAX_DEGREE = 8

Monomial = tuple[str, ...]  # sorted atom keys; () is the constant 1
Poly = tuple[Monomial, ...]  # sorted unit monomials, repeated for coefficients


def classify(term: Term) -> tuple[str, tuple[Term, ...]]:
    """("zero" | "succ" | "add" | "mul" | "atom", arguments) for a Nat term."""
    node = term._node
    if node[0] == "app":
        const = node[1]
        signature = _SIGNATURES.get(const.name)
        if (
            signature is not None
            and const.result is not None
            and (tuple(s.name for s in const.args), const.result.name) == signature
        ):
            return const.name.removeprefix("arith."), node[2]
    return "atom", ()


def atom_key(term: Term) -> str:
    """A canonical key of an atom (canonical names, so short-name clashes differ)."""
    node = term._node
    if node[0] == "var":
        return f"{node[1]}:{term.sort.name}"
    args = ",".join(atom_key(a) for a in node[2])
    return f"{node[1].name}({args})"


def _monomial_order(m: Monomial) -> tuple[int, Monomial]:
    return (len(m), m)


class Normalizer:
    """Builds `t = nf(t)` facts inside a proof context."""

    def __init__(self, ctx: "ProofContext") -> None:
        self.ctx = ctx
        self.atoms: dict[str, Term] = {}
        self._lemmas: dict[str, Fact] = {}
        self._consts: dict[str, Any] = {}

    # --- building blocks ----------------------------------------------------------

    def _lemma(self, name: str, *terms: Term) -> "Fact":
        fact = self._lemmas.get(name)
        if fact is None:
            ref = self.ctx._resolve(f"arith.{name}")
            fact = self._lemmas[name] = self.ctx._instance(ref, None)
            self._learn_consts(fact)
        return self.ctx.spec(fact, *terms) if terms else fact

    def _learn_consts(self, fact: "Fact") -> None:
        """Remember the arith constants as they appear in the environment's statements."""
        stack: list[Any] = [fact.prop]
        while stack:
            item = stack.pop()
            if isinstance(item, Term):
                kind, args = classify(item)
                if kind != "atom":
                    self._consts.setdefault(kind, item._node[1])
                stack.extend(args)
            elif item.tag in ("forall", "exists"):
                stack.append(item.body)
            elif item.tag == "eq":
                stack.extend(item.sides)
            elif item.tag in ("and", "or", "imp"):
                stack.extend((item.left, item.right))

    def _const(self, kind: str) -> Any:
        if kind not in self._consts:
            for name in ("succ_eq_add_one", "mul_one"):  # mention zero, succ, add, mul
                self._lemma(name)
        return self._consts[kind]

    def zero(self) -> Term:
        result: Term = self._const("zero")()
        return result

    def one(self) -> Term:
        result: Term = self._const("succ")(self.zero())
        return result

    def add(self, a: Term, b: Term) -> Term:
        result: Term = self._const("add")(a, b)
        return result

    def mul(self, a: Term, b: Term) -> Term:
        result: Term = self._const("mul")(a, b)
        return result

    def _trans(self, *facts: "Fact") -> "Fact":
        result = facts[0]
        for fact in facts[1:]:
            left, right = fact.prop.sides
            if left == right:
                continue
            first, second = result.prop.sides
            result = fact if first == second else self.ctx.trans(result, fact)
        return result

    def _congr(self, fact: "Fact", build: Callable[[Term], Term]) -> "Fact":
        """From a = b derive build(a) = build(b)."""
        left, right = fact.prop.sides
        if left == right:
            return self.ctx.refl(build(left))
        sample = build(left)
        z = self._fresh(sample, right)
        return self.ctx.congr(fact, (z, build(z)))

    def _fresh(self, *terms: Term) -> Term:
        taken = {name for t in terms for name, _ in t.free_vars()}
        i = 0
        while f"_r{i}" in taken:
            i += 1
        return Var(f"_r{i}", terms[0].sort)

    def _congr2(self, f: "Fact", g: "Fact", op: Callable[[Term, Term], Term]) -> "Fact":
        """From a = A and b = B derive op(a, b) = op(A, B)."""
        b = g.prop.sides[0]
        big_a = f.prop.sides[1]
        return self._trans(
            self._congr(f, lambda z: op(z, b)), self._congr(g, lambda z: op(big_a, z))
        )

    # --- terms of normal forms -----------------------------------------------------

    def mono_term(self, m: Monomial) -> Term:
        if not m:
            return self.one()
        term = self.atoms[m[0]]
        for key in m[1:]:
            term = self.mul(term, self.atoms[key])
        return term

    def poly_term(self, p: Poly) -> Term:
        if not p:
            return self.zero()
        term = self.mono_term(p[0])
        for m in p[1:]:
            term = self.add(term, self.mono_term(m))
        return term

    def _refl_poly(self, p: Poly) -> "Fact":
        return self.ctx.refl(self.poly_term(p))

    # --- normalization ------------------------------------------------------------

    def normalize(self, term: Term) -> tuple[Poly, "Fact"]:
        """nf(t) and a fact t = nf(t)."""
        kind, args = classify(term)
        if kind == "zero":
            return (), self.ctx.refl(term)
        if kind == "atom":
            key = atom_key(term)
            self.atoms.setdefault(key, term)
            return ((key,),), self.ctx.refl(term)
        if kind == "succ":
            (u,) = args
            first = self._lemma("succ_eq_add_one", u)  # S(u) = u + 1
            p, fu = self.normalize(u)
            _check_size(p, ((),), "add")
            moved = self._congr(fu, lambda z: self.add(z, self.one()))
            q, merged = self.add_insert(p, ())
            return q, self._trans(first, moved, merged)
        a, b = args
        pa, fa = self.normalize(a)
        pb, fb = self.normalize(b)
        _check_size(pa, pb, kind)
        if kind == "add":
            both = self._congr2(fa, fb, self.add)
            q, merged = self.add_nf(pa, pb)
        else:
            both = self._congr2(fa, fb, self.mul)
            q, merged = self.mul_nf(pa, pb)
        return q, self._trans(both, merged)

    # sums

    def add_nf(self, a: Poly, b: Poly) -> tuple[Poly, "Fact"]:
        """A + B = nf(A + B) for normal forms A and B."""
        ta, tb = self.poly_term(a), self.poly_term(b)
        if not b:
            return a, self._lemma("add_zero", ta)
        if not a:
            return b, self._lemma("zero_add", tb)
        if len(b) == 1:
            return self.add_insert(a, b[0])
        rest, last = b[:-1], b[-1]
        # A + (B' + m) = (A + B') + m
        regroup = self.ctx.symm(
            self._lemma("add_assoc", ta, self.poly_term(rest), self.mono_term(last))
        )
        c, fc = self.add_nf(a, rest)
        moved = self._congr(fc, lambda z: self.add(z, self.mono_term(last)))
        d, fd = self.add_insert(c, last)
        return d, self._trans(regroup, moved, fd)

    def add_insert(self, a: Poly, m: Monomial) -> tuple[Poly, "Fact"]:
        """A + m = nf(A + m) for a normal form A and a unit monomial m."""
        tm = self.mono_term(m)
        if not a:
            return (m,), self._lemma("zero_add", tm)
        last = a[-1]
        if _monomial_order(last) <= _monomial_order(m):
            result = (*a, m)
            return result, self._refl_poly(result)
        if len(a) == 1:
            return (m, last), self._lemma("add_comm", self.mono_term(last), tm)
        rest = a[:-1]
        # (A' + l) + m = (A' + m) + l
        swap = self._lemma("add_right_comm", self.poly_term(rest), self.mono_term(last), tm)
        c, fc = self.add_insert(rest, m)
        moved = self._congr(fc, lambda z: self.add(z, self.mono_term(last)))
        return (*c, last), self._trans(swap, moved)

    # products

    def mul_nf(self, a: Poly, b: Poly) -> tuple[Poly, "Fact"]:
        """A × B = nf(A × B) for normal forms A and B."""
        ta, tb = self.poly_term(a), self.poly_term(b)
        if not b:
            return (), self._lemma("mul_zero", ta)
        if not a:
            return (), self._lemma("zero_mul", tb)
        if len(b) > 1:
            rest, last = b[:-1], b[-1]
            # A × (B' + m) = A × B' + A × m
            split = self._lemma("mul_add", ta, self.poly_term(rest), self.mono_term(last))
            p, fp = self.mul_nf(a, rest)
            q, fq = self.mul_nf(a, (last,))
        elif len(a) > 1:
            rest, last = a[:-1], a[-1]
            # (A' + m) × n = A' × n + m × n
            split = self._lemma("add_mul", self.poly_term(rest), self.mono_term(last), tb)
            p, fp = self.mul_nf(rest, b)
            q, fq = self.mul_nf((last,), b)
        else:
            m, fm = self.mono_mul(a[0], b[0])
            return (m,), fm
        both = self._congr2(fp, fq, self.add)
        r, fr = self.add_nf(p, q)
        return r, self._trans(split, both, fr)

    def mono_mul(self, a: Monomial, b: Monomial) -> tuple[Monomial, "Fact"]:
        """a × b = nf(a × b) for unit monomials."""
        ta, tb = self.mono_term(a), self.mono_term(b)
        if not a:
            return b, self._lemma("one_mul", tb)
        if not b:
            return a, self._lemma("mul_one", ta)
        if len(b) == 1:
            return self.mono_insert(a, b[0])
        rest, last = b[:-1], b[-1]
        last_term = self.atoms[last]
        # a × (b' × y) = (a × b') × y
        regroup = self.ctx.symm(self._lemma("mul_assoc", ta, self.mono_term(rest), last_term))
        c, fc = self.mono_mul(a, rest)
        moved = self._congr(fc, lambda z: self.mul(z, last_term))
        d, fd = self.mono_insert(c, last)
        return d, self._trans(regroup, moved, fd)

    def mono_insert(self, a: Monomial, key: str) -> tuple[Monomial, "Fact"]:
        """a × y = nf(a × y) for a non-empty unit monomial a and an atom y."""
        ty = self.atoms[key]
        last = a[-1]
        if last <= key:
            result = (*a, key)
            return result, self.ctx.refl(self.mono_term(result))
        last_term = self.atoms[last]
        if len(a) == 1:
            return (key, last), self._lemma("mul_comm", last_term, ty)
        rest = a[:-1]
        # (a' × x) × y = (a' × y) × x
        swap = self._lemma("mul_right_comm", self.mono_term(rest), last_term, ty)
        c, fc = self.mono_insert(rest, key)
        moved = self._congr(fc, lambda z: self.mul(z, last_term))
        return (*c, last), self._trans(swap, moved)


def _check_size(a: Poly, b: Poly, kind: str) -> None:
    """Refuse before building a normal form beyond the size limits."""
    if kind == "add":
        units = len(a) + len(b)
        degree = max((len(m) for m in (*a, *b)), default=0)
    else:
        units = len(a) * len(b)
        degree = max((len(m) for m in a), default=0) + max((len(m) for m in b), default=0)
    if units > MAX_UNITS:
        raise TacticError(
            f"ring: the polynomial is too large: {units} unit monomials (limit {MAX_UNITS}; "
            "a coefficient c counts c times)"
        )
    if degree > MAX_DEGREE:
        raise TacticError(
            f"ring: the polynomial is too large: degree {degree} (limit {MAX_DEGREE})"
        )


def prove_equal(ctx: "ProofContext", t: Term, u: Term) -> "Fact":
    """A fact t = u, if both sides have the same normal form."""
    normalizer = Normalizer(ctx)
    p, ft = normalizer.normalize(t)
    q, fu = normalizer.normalize(u)
    if p != q:
        raise TacticError(
            "ring: the normal forms differ although SymPy reported an identity "
            f"(possible defect): {normalizer.poly_term(p)} and {normalizer.poly_term(q)}"
        )
    return normalizer._trans(ft, ctx.symm(fu))
