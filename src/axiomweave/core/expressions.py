"""Propositions and terms for the Python DSL (language-spec §4, §12).

A `Prop` is an immutable tree of schematic variables (atoms and predicate
symbols), `Falsehood`, the primitive connectives `and`, `or`, `imp`, and in
fragment L1 predicate constants and the quantifiers `forall`/`exists`.
Abbreviations (`Not`, `Truth`, `Iff`) are expanded when constructed, so they
never reach the kernel.

Variables are named here; the kernel encoding uses de Bruijn indices
(kernel-spec §13). `==` on propositions is α-equivalence.
"""

import re
from collections.abc import Iterable, Mapping, Sequence
from typing import Any, NoReturn

from axiomweave.errors import AxwTypeError, ScopeError

RESERVED_WORDS = frozenset({"and", "or", "imp", "false"})
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_BINARY = ("and", "or", "imp")
_QUANTIFIERS = ("forall", "exists")
_SYMBOL = {"and": "∧", "or": "∨", "imp": "→"}
_PRECEDENCE = {"and": 3, "or": 2, "imp": 1}
_CONSTRUCTOR = {"and": "And", "or": "Or", "imp": "Implies"}
_ATOMIC_PRECEDENCE = 4
_QUANTIFIER_PRECEDENCE = 0

VarKey = tuple[str, str]  # (variable name, sort name)
# Schematic substitution value: (parameter variables, body).
SchemaValue = tuple[tuple["Term", ...], "Prop"]


def is_local_name(name: object) -> bool:
    """True for a valid atom, variable or hypothesis name (kernel-spec §3)."""
    return (
        isinstance(name, str)
        and len(name) <= 255
        and _IDENTIFIER.fullmatch(name) is not None
        and name not in RESERVED_WORDS
    )


def _merge_sorts(*maps: Mapping[str, "Sort"] | None) -> dict[str, "Sort"] | None:
    """Union of name -> sort maps; the same name may not have two sorts (language-spec §12.3)."""
    result: dict[str, Sort] | None = None
    for m in maps:
        if not m:
            continue
        if result is None:
            result = dict(m)
            continue
        for name, sort in m.items():
            previous = result.setdefault(name, sort)
            if previous != sort:
                raise AxwTypeError(
                    f"variable name {name!r} is used with sorts {previous} and {sort}"
                )
    return result


# --- sorts and constants ---------------------------------------------------------


class Sort:
    """A base type declared with `thy.sort` (language-spec §12.2)."""

    __slots__ = ("name", "short", "theory")

    def __init__(self, name: str, short: str, theory: object) -> None:
        self.name = name  # canonical declaration name
        self.short = short
        self.theory = theory

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Sort) and other.name == self.name

    def __hash__(self) -> int:
        return hash(("sort", self.name))

    def __str__(self) -> str:
        return self.short

    def __repr__(self) -> str:
        return f"<Sort {self.name}>"

    def to_json(self) -> dict[str, Any]:
        return {"kind": "sort", "name": self.name}


class Const:
    """A function or predicate symbol declared with `thy.const` (language-spec §12.2)."""

    __slots__ = ("args", "name", "result", "short", "theory")

    def __init__(
        self, name: str, short: str, args: tuple[Sort, ...], result: "Sort | None", theory: object
    ) -> None:
        self.name = name
        self.short = short
        self.args = args
        self.result = result  # None means Prop
        self.theory = theory

    @property
    def is_predicate(self) -> bool:
        return self.result is None

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Const) and other.name == self.name

    def __hash__(self) -> int:
        return hash(("const", self.name))

    def __repr__(self) -> str:
        return f"<Const {self.name}>"

    def __call__(self, *args: "Term") -> "Term | Prop":
        checked = _check_args(self.short, self.args, args)
        if self.result is None:
            return Prop(("pred", self, checked))
        return Term(("app", self, checked), self.result)

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": "const",
            "name": self.name,
            "args": [s.name for s in self.args],
            "result": "prop" if self.result is None else self.result.name,
        }


def _check_args(name: str, sorts: tuple[Sort, ...], args: Sequence[object]) -> tuple["Term", ...]:
    if len(args) != len(sorts):
        raise AxwTypeError(f"{name} takes {len(sorts)} arguments, got {len(args)}")
    for i, (arg, sort) in enumerate(zip(args, sorts, strict=True)):
        if not isinstance(arg, Term):
            raise AxwTypeError(f"argument {i} of {name} must be a Term, got {type(arg).__name__}")
        if arg.sort != sort:
            raise AxwTypeError(f"argument {i} of {name} has sort {arg.sort}, expected {sort}")
    return tuple(args)  # type: ignore[arg-type]


class PredicateSymbol:
    """A schematic predicate variable with argument sorts (language-spec §12.4)."""

    __slots__ = ("name", "sorts")

    def __init__(self, name: str, sorts: tuple[Sort, ...]) -> None:
        self.name = name
        self.sorts = sorts

    def __call__(self, *args: "Term") -> "Prop":
        return Prop(("pvar", self.name, _check_args(self.name, self.sorts, args)))

    def __eq__(self, other: object) -> bool:
        return isinstance(other, PredicateSymbol) and (other.name, other.sorts) == (
            self.name,
            self.sorts,
        )

    def __hash__(self) -> int:
        return hash(("pvar", self.name, self.sorts))

    def __repr__(self) -> str:
        sorts = "".join(f", {s.short}" for s in self.sorts)
        return f"Prop.symbol({self.name!r}{sorts})"


# --- terms ---------------------------------------------------------------------------


class Term:
    """An individual term: a variable or a function symbol applied to terms."""

    __slots__ = ("_free", "_names", "_node", "sort")

    _node: tuple[Any, ...]
    sort: Sort
    _free: frozenset[VarKey]
    _names: dict[str, Sort] | None

    def __init__(self, node: tuple[Any, ...], sort: Sort) -> None:
        object.__setattr__(self, "_node", node)
        object.__setattr__(self, "sort", sort)
        if node[0] == "var":
            free = frozenset({(node[1], sort.name)})
            names: dict[str, Sort] | None = {node[1]: sort}
        else:
            free = frozenset().union(*(a._free for a in node[2]))
            names = _merge_sorts(*(a._names for a in node[2]))
        object.__setattr__(self, "_free", free)
        object.__setattr__(self, "_names", names)

    def __setattr__(self, name: str, value: object) -> NoReturn:
        raise AttributeError("Term is immutable")

    @property
    def is_var(self) -> bool:
        return self._node[0] == "var"

    @property
    def name(self) -> str:
        if not self.is_var:
            raise AttributeError("only variables have a name")
        name: str = self._node[1]
        return name

    @property
    def key(self) -> VarKey:
        return (self.name, self.sort.name)

    def free_vars(self) -> frozenset[VarKey]:
        return self._free

    def _replace(self, terms: Mapping[VarKey, "Term"]) -> "Term":
        if not terms or not (self._free & terms.keys()):
            return self
        if self.is_var:
            return terms[self.key]
        const, args = self._node[1], self._node[2]
        return Term(("app", const, tuple(a._replace(terms) for a in args)), self.sort)

    def to_json(self, scope: Sequence["Term"] = ()) -> list[Any]:
        """Kernel encoding with de Bruijn indices; `scope` lists the variables in scope,
        innermost last (kernel-spec §13.3)."""
        if self.is_var:
            for depth, var in enumerate(reversed(scope)):
                if var.name == self.name:
                    if var.sort != self.sort:
                        raise AxwTypeError(
                            f"variable {self.name} has sort {self.sort}, bound with {var.sort}"
                        )
                    return ["var", depth]
            raise ScopeError(f"variable {self.name} is not in scope")
        const, args = self._node[1], self._node[2]
        return ["app", const.name, [a.to_json(scope) for a in args]]

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Term):
            return NotImplemented
        return self._node == other._node and self.sort == other.sort

    def __hash__(self) -> int:
        return hash((self._node, self.sort))

    def __bool__(self) -> bool:
        raise AxwTypeError("a Term has no truth value")

    def __str__(self) -> str:
        if self.is_var:
            return self.name
        const, args = self._node[1], self._node[2]
        if not args:
            return str(const.short)
        return f"{const.short}({', '.join(str(a) for a in args)})"

    def __repr__(self) -> str:
        if self.is_var:
            return f"Var({self.name!r}, {self.sort.short})"
        return f"<Term {self}: {self.sort.short}>"


def Var(name: str, sort: Sort) -> Term:
    """The individual variable `name` of sort `sort` (language-spec §12.3)."""
    if not is_local_name(name):
        raise AxwTypeError(f"invalid variable name {name!r}")
    if not isinstance(sort, Sort):
        raise AxwTypeError(f"Var expects a Sort, got {type(sort).__name__}")
    return Term(("var", name), sort)


# --- propositions ----------------------------------------------------------------------


class Prop:
    """A proposition. Build it with `Prop.symbol`, the constructors, or operators."""

    __slots__ = ("_free", "_hash", "_key", "_names", "_node", "_schemas")

    _node: tuple[Any, ...]
    _free: frozenset[VarKey]
    _names: dict[str, Sort] | None
    _schemas: frozenset[str]
    _key: Any
    _hash: int | None

    def __init__(self, node: tuple[Any, ...]) -> None:
        object.__setattr__(self, "_node", node)
        tag = node[0]
        free: frozenset[VarKey] = frozenset()
        names: dict[str, Sort] | None = None
        schemas: frozenset[str] = frozenset()
        if tag == "atom":
            schemas = frozenset({node[1]})
        elif tag in ("pvar", "pred"):
            args: tuple[Term, ...] = node[2]
            free = frozenset().union(*(a._free for a in args))
            names = _merge_sorts(*(a._names for a in args))
            if tag == "pvar":
                schemas = frozenset({node[1]})
        elif tag in _BINARY:
            left, right = node[1], node[2]
            free = left._free | right._free
            names = _merge_sorts(left._names, right._names)
            schemas = left._schemas | right._schemas
        elif tag in _QUANTIFIERS:
            var, body = node[1], node[2]
            free = body._free - {var.key}
            names = _merge_sorts({var.name: var.sort}, body._names)
            schemas = body._schemas
        object.__setattr__(self, "_free", free)
        object.__setattr__(self, "_names", names)
        object.__setattr__(self, "_schemas", schemas)
        object.__setattr__(self, "_key", None)
        object.__setattr__(self, "_hash", None)

    def __setattr__(self, name: str, value: object) -> NoReturn:
        raise AttributeError("Prop is immutable")

    @staticmethod
    def symbol(name: str, *sorts: Sort) -> "Any":
        """The atom `name`, or with argument sorts a schematic predicate symbol."""
        if not is_local_name(name):
            raise AxwTypeError(f"invalid atom name {name!r}")
        if not sorts:
            return Prop(("atom", name))
        for sort in sorts:
            if not isinstance(sort, Sort):
                raise AxwTypeError(f"Prop.symbol expects Sort arguments, got {sort!r}")
        return PredicateSymbol(name, tuple(sorts))

    # structure

    @property
    def tag(self) -> str:
        """One of "atom", "false", "and", "or", "imp", "pvar", "pred", "forall", "exists"."""
        tag: str = self._node[0]
        return tag

    @property
    def is_atom(self) -> bool:
        return self.tag == "atom"

    @property
    def name(self) -> str:
        if self.tag not in ("atom", "pvar"):
            raise AttributeError("only schematic variables have a name")
        name: str = self._node[1]
        return name

    @property
    def left(self) -> "Prop":
        return self._child(1)

    @property
    def right(self) -> "Prop":
        return self._child(2)

    def _child(self, index: int) -> "Prop":
        if self.tag not in _BINARY:
            raise AttributeError(f"{self.tag} has no operands")
        child: Prop = self._node[index]
        return child

    @property
    def var(self) -> Term:
        """The bound variable of a quantifier."""
        if self.tag not in _QUANTIFIERS:
            raise AttributeError(f"{self.tag} has no bound variable")
        var: Term = self._node[1]
        return var

    @property
    def body(self) -> "Prop":
        if self.tag not in _QUANTIFIERS:
            raise AttributeError(f"{self.tag} has no body")
        body: Prop = self._node[2]
        return body

    @property
    def args(self) -> tuple[Term, ...]:
        if self.tag not in ("pvar", "pred"):
            raise AttributeError(f"{self.tag} has no arguments")
        args: tuple[Term, ...] = self._node[2]
        return args

    def atoms(self) -> frozenset[str]:
        """Names of the schematic variables (atoms and predicate symbols) in this proposition."""
        return self._schemas

    def free_vars(self) -> frozenset[VarKey]:
        """(name, sort name) of the free individual variables."""
        return self._free

    def var_names(self) -> frozenset[str]:
        """Names of all individual variables, free or bound."""
        return frozenset(self._names or ())

    def var_sorts(self) -> dict[str, Sort]:
        """Sort of every individual variable name, free or bound."""
        return dict(self._names or {})

    def signature(self) -> dict[str, tuple[Sort, ...]]:
        """Argument sorts of each schematic variable; raises if a name has two."""
        result: dict[str, tuple[Sort, ...]] = {}

        def go(p: Prop) -> None:
            tag = p.tag
            if tag in ("atom", "pvar"):
                sorts = tuple(a.sort for a in p.args) if tag == "pvar" else ()
                previous = result.setdefault(p.name, sorts)
                if previous != sorts:
                    raise AxwTypeError(f"schematic variable {p.name!r} is used with two arities")
            elif tag in _BINARY:
                go(p.left)
                go(p.right)
            elif tag in _QUANTIFIERS:
                go(p.body)

        go(self)
        return result

    def symbols(self) -> tuple[set[Sort], set[Const]]:
        """Sorts and constants this proposition mentions."""
        sorts: set[Sort] = set()
        consts: set[Const] = set()

        def term(t: Term) -> None:
            sorts.add(t.sort)
            if not t.is_var:
                consts.add(t._node[1])
                for a in t._node[2]:
                    term(a)

        def go(p: Prop) -> None:
            tag = p.tag
            if tag in ("pvar", "pred"):
                if tag == "pred":
                    consts.add(p._node[1])
                for a in p.args:
                    term(a)
            elif tag in _BINARY:
                go(p.left)
                go(p.right)
            elif tag in _QUANTIFIERS:
                sorts.add(p.var.sort)
                go(p.body)

        go(self)
        return sorts, consts

    # substitution

    def substitute(self, mapping: Mapping[str, "Prop"]) -> "Prop":
        """Simultaneously replace atoms by propositions (logic-spec §6.1)."""
        return self.instantiate({name: ((), prop) for name, prop in mapping.items()})

    def instantiate(self, schema: Mapping[str, SchemaValue]) -> "Prop":
        """Simultaneous schematic substitution with capture avoidance (logic-spec §12.6)."""
        return _replace(self, {}, dict(schema))

    def subst_var(self, var: Term, term: Term) -> "Prop":
        """Capture-avoiding substitution of `term` for the free variable `var`."""
        return _replace(self, {var.key: term}, {})

    def open(self, var: Term) -> "Prop":
        """The body of a quantifier with its bound variable replaced by `var`."""
        return self.body.subst_var(self.var, var)

    # kernel encoding

    def to_json(self, scope: Sequence[Term] = ()) -> list[Any]:
        """Kernel encoding (kernel-spec §4, §13.3); `scope` lists the variables in scope,
        innermost last."""
        tag = self.tag
        if tag == "atom":
            return ["atom", self.name]
        if tag == "false":
            return ["false"]
        if tag in ("pvar", "pred"):
            name = self.name if tag == "pvar" else self._node[1].name
            return [tag, name, [a.to_json(scope) for a in self.args]]
        if tag in _QUANTIFIERS:
            return [tag, self.var.sort.name, self.body.to_json((*scope, self.var))]
        return [tag, self.left.to_json(scope), self.right.to_json(scope)]

    # Python protocol

    def _alpha_key(self, bound: tuple[VarKey, ...] = ()) -> Any:
        """A key equal for α-equivalent propositions; bound variables become indices."""
        if not bound or not (self._free & set(bound)):
            if self._key is None:
                object.__setattr__(self, "_key", self._compute_key(()))
            return self._key
        return self._compute_key(bound)

    def _compute_key(self, bound: tuple[VarKey, ...]) -> Any:
        tag = self.tag
        if tag in ("atom", "false"):
            return self._node
        if tag in ("pvar", "pred"):
            head = self.name if tag == "pvar" else self._node[1].name
            return (tag, head, tuple(_term_key(a, bound) for a in self.args))
        if tag in _QUANTIFIERS:
            return (tag, self.var.sort.name, self.body._alpha_key((*bound, self.var.key)))
        return (tag, self.left._alpha_key(bound), self.right._alpha_key(bound))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Prop):
            return NotImplemented
        if self is other:
            return True
        return bool(self._alpha_key() == other._alpha_key())

    def __hash__(self) -> int:
        if self._hash is None:
            object.__setattr__(self, "_hash", hash(self._alpha_key()))
        assert self._hash is not None
        return self._hash

    def __bool__(self) -> bool:
        raise AxwTypeError(
            "a Prop has no truth value; use &, |, >>, ~ or And/Or/Implies/Not, "
            "not Python's and/or/not/if"
        )

    def __and__(self, other: object) -> "Prop":
        return Prop(("and", self, other)) if isinstance(other, Prop) else NotImplemented

    def __or__(self, other: object) -> "Prop":
        return Prop(("or", self, other)) if isinstance(other, Prop) else NotImplemented

    def __rshift__(self, other: object) -> "Prop":
        return Prop(("imp", self, other)) if isinstance(other, Prop) else NotImplemented

    def __invert__(self) -> "Prop":
        return Not(self)

    def __str__(self) -> str:
        return self._format()[0]

    def _format(self) -> tuple[str, int]:
        tag = self.tag
        if tag == "atom":
            return self.name, _ATOMIC_PRECEDENCE
        if tag == "false":
            return "⊥", _ATOMIC_PRECEDENCE
        if tag in ("pvar", "pred"):
            head = self.name if tag == "pvar" else self._node[1].short
            if not self.args:
                return head, _ATOMIC_PRECEDENCE
            return f"{head}({', '.join(str(a) for a in self.args)})", _ATOMIC_PRECEDENCE
        if tag in _QUANTIFIERS:
            symbol = "∀" if tag == "forall" else "∃"
            body = self.body._format()[0]
            return f"{symbol}{self.var.name}:{self.var.sort}. {body}", _QUANTIFIER_PRECEDENCE
        prec = _PRECEDENCE[tag]
        left, left_prec = self.left._format()
        right, right_prec = self.right._format()
        if left_prec <= prec:
            left = f"({left})"
        # `→` is right-associative; `∧`/`∨` chains are always parenthesized.
        if right_prec < prec or (right_prec == prec and tag != "imp"):
            right = f"({right})"
        return f"{left} {_SYMBOL[tag]} {right}", prec

    def __repr__(self) -> str:
        tag = self.tag
        if tag == "atom":
            return f"Prop.symbol({self.name!r})"
        if tag == "false":
            return "Falsehood"
        if tag in _BINARY:
            return f"{_CONSTRUCTOR[tag]}({self.left!r}, {self.right!r})"
        if tag in _QUANTIFIERS:
            constructor = "ForAll" if tag == "forall" else "Exists"
            return f"{constructor}({self.var!r}, {self.body!r})"
        return f"<Prop {self}>"


def _term_key(term: Term, bound: tuple[VarKey, ...]) -> Any:
    if term.is_var:
        key = term.key
        for depth in range(len(bound) - 1, -1, -1):
            if bound[depth] == key:
                return ("b", len(bound) - 1 - depth)
        return ("f", *key)
    return ("app", term._node[1].name, tuple(_term_key(a, bound) for a in term._node[2]))


def _fresh_name(base: str, avoid: Iterable[str]) -> str:
    taken = set(avoid)
    stem = base.rstrip("0123456789") or base
    n = 1
    while f"{stem}{n}" in taken:
        n += 1
    return f"{stem}{n}"


def _replace(prop: Prop, terms: dict[VarKey, Term], schema: dict[str, SchemaValue]) -> Prop:
    """Simultaneous capture-avoiding substitution of free variables and schematic variables."""
    touches_terms = bool(terms) and bool(prop._free & terms.keys())
    touches_schema = bool(schema) and bool(prop._schemas & schema.keys())
    if not (touches_terms or touches_schema):
        return prop
    tag = prop.tag
    if tag == "atom":
        return schema[prop.name][1]
    if tag in ("pvar", "pred"):
        args = tuple(a._replace(terms) for a in prop.args)
        if tag == "pvar" and prop.name in schema:
            params, body = schema[prop.name]
            return _replace(body, {p.key: a for p, a in zip(params, args, strict=True)}, {})
        return Prop((tag, prop._node[1], args))
    if tag in _BINARY:
        return Prop((tag, _replace(prop.left, terms, schema), _replace(prop.right, terms, schema)))
    # quantifier
    var, body = prop.var, prop.body
    inner = {k: t for k, t in terms.items() if k != var.key}
    incoming: set[str] = set()
    for t in inner.values():
        incoming |= {name for name, _ in t._free}
    for params, value in schema.values():
        param_keys = {p.key for p in params}
        incoming |= {name for name, s in value._free if (name, s) not in param_keys}
    if var.name in incoming:
        avoid = incoming | body.var_names() | {name for name, _ in prop._free}
        renamed = Var(_fresh_name(var.name, avoid), var.sort)
        inner[var.key] = renamed
        var = renamed
    return Prop((tag, var, _replace(body, inner, schema)))


def _require(value: object, where: str) -> Prop:
    if not isinstance(value, Prop):
        raise AxwTypeError(f"{where} expects Prop arguments, got {type(value).__name__}")
    return value


Falsehood = Prop(("false",))


def And(a: Prop, b: Prop) -> Prop:
    return Prop(("and", _require(a, "And"), _require(b, "And")))


def Or(a: Prop, b: Prop) -> Prop:
    return Prop(("or", _require(a, "Or"), _require(b, "Or")))


def Implies(*parts: Prop) -> Prop:
    """Right-associative implication: Implies(A, B, C) is A → (B → C)."""
    if len(parts) < 2:
        raise AxwTypeError("Implies expects at least two arguments")
    result = _require(parts[-1], "Implies")
    for part in reversed(parts[:-1]):
        result = Prop(("imp", _require(part, "Implies"), result))
    return result


def Not(a: Prop) -> Prop:
    """¬A, expanded to A → ⊥."""
    return Prop(("imp", _require(a, "Not"), Falsehood))


def Iff(a: Prop, b: Prop) -> Prop:
    """A ↔ B, expanded to (A → B) ∧ (B → A)."""
    a, b = _require(a, "Iff"), _require(b, "Iff")
    return Prop(("and", Prop(("imp", a, b)), Prop(("imp", b, a))))


Truth = Prop(("imp", Falsehood, Falsehood))
"""⊤, expanded to ⊥ → ⊥."""


def _quantify(tag: str, variables: object, body: object, where: str) -> Prop:
    items = list(variables) if isinstance(variables, list | tuple) else [variables]
    if not items:
        raise AxwTypeError(f"{where} needs at least one variable")
    result = _require(body, where)
    for var in reversed(items):
        if not isinstance(var, Term) or not var.is_var:
            raise AxwTypeError(f"{where} binds variables made with Var, got {var!r}")
        result = Prop((tag, var, result))
    return result


def ForAll(variables: Term | Sequence[Term], body: Prop) -> Prop:
    """∀x:S. body; a list of variables nests the quantifiers (language-spec §12.3)."""
    return _quantify("forall", variables, body, "ForAll")


def Exists(variables: Term | Sequence[Term], body: Prop) -> Prop:
    """∃x:S. body; a list of variables nests the quantifiers (language-spec §12.3)."""
    return _quantify("exists", variables, body, "Exists")
