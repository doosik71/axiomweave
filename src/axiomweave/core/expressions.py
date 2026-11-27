"""L0 propositions for the Python DSL (language-spec §4).

A `Prop` is an immutable tree of atoms, `Falsehood` and the primitive
connectives `and`, `or`, `imp`. Abbreviations (`Not`, `Truth`, `Iff`) are
expanded when constructed, so they never reach the kernel.
"""

import re
from collections.abc import Mapping
from typing import Any, NoReturn

from axiomweave.errors import AxwTypeError

RESERVED_WORDS = frozenset({"and", "or", "imp", "false"})
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_BINARY = ("and", "or", "imp")
_SYMBOL = {"and": "∧", "or": "∨", "imp": "→"}
_PRECEDENCE = {"and": 3, "or": 2, "imp": 1}
_CONSTRUCTOR = {"and": "And", "or": "Or", "imp": "Implies"}
_ATOMIC_PRECEDENCE = 4


def is_local_name(name: object) -> bool:
    """True for a valid atom or hypothesis name (kernel-spec §3)."""
    return (
        isinstance(name, str)
        and len(name) <= 255
        and _IDENTIFIER.fullmatch(name) is not None
        and name not in RESERVED_WORDS
    )


class Prop:
    """An L0 proposition. Build it with `Prop.symbol`, the constructors, or operators."""

    __slots__ = ("_hash", "_node")

    _node: tuple[Any, ...]
    _hash: int

    def __init__(self, node: tuple[Any, ...]) -> None:
        object.__setattr__(self, "_node", node)
        object.__setattr__(self, "_hash", hash(node))

    def __setattr__(self, name: str, value: object) -> NoReturn:
        raise AttributeError("Prop is immutable")

    @staticmethod
    def symbol(name: str) -> "Prop":
        """The propositional atom called `name`."""
        if not is_local_name(name):
            raise AxwTypeError(f"invalid atom name {name!r}")
        return Prop(("atom", name))

    # structure

    @property
    def tag(self) -> str:
        """One of "atom", "false", "and", "or", "imp"."""
        tag: str = self._node[0]
        return tag

    @property
    def is_atom(self) -> bool:
        return self.tag == "atom"

    @property
    def name(self) -> str:
        if not self.is_atom:
            raise AttributeError("only atoms have a name")
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

    def atoms(self) -> frozenset[str]:
        """Names of the atoms occurring in this proposition."""
        if self.tag == "atom":
            return frozenset({self.name})
        if self.tag == "false":
            return frozenset()
        return self.left.atoms() | self.right.atoms()

    def substitute(self, mapping: Mapping[str, "Prop"]) -> "Prop":
        """Simultaneously replace atoms by propositions (logic-spec §6.1)."""
        if self.tag == "atom":
            return mapping.get(self.name, self)
        if self.tag == "false":
            return self
        return Prop((self.tag, self.left.substitute(mapping), self.right.substitute(mapping)))

    def to_json(self) -> list[Any]:
        """Kernel encoding (kernel-spec §4)."""
        if self.tag == "atom":
            return ["atom", self.name]
        if self.tag == "false":
            return ["false"]
        return [self.tag, self.left.to_json(), self.right.to_json()]

    # Python protocol

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Prop):
            return NotImplemented
        return self._node == other._node

    def __hash__(self) -> int:
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
        if self.tag == "atom":
            return self.name, _ATOMIC_PRECEDENCE
        if self.tag == "false":
            return "⊥", _ATOMIC_PRECEDENCE
        prec = _PRECEDENCE[self.tag]
        left, left_prec = self.left._format()
        right, right_prec = self.right._format()
        if left_prec <= prec:
            left = f"({left})"
        # `→` is right-associative; `∧`/`∨` chains are always parenthesized.
        if right_prec < prec or (right_prec == prec and self.tag != "imp"):
            right = f"({right})"
        return f"{left} {_SYMBOL[self.tag]} {right}", prec

    def __repr__(self) -> str:
        if self.tag == "atom":
            return f"Prop.symbol({self.name!r})"
        if self.tag == "false":
            return "Falsehood"
        return f"{_CONSTRUCTOR[self.tag]}({self.left!r}, {self.right!r})"


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
