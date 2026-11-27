"""JSON restrictions, canonical form, hashes and decoding of L0 certificates.

Implements kernel-spec §3 (names), §4 (propositions), §5 (derivation trees),
§6 (bundle structure) and §7 (canonical JSON and SHA-256 hashes).
"""

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Any, NoReturn

from axiomweave.kernel.errors import (
    E_FORMAT,
    E_FRAGMENT,
    E_LIMIT,
    E_NAME,
    E_VERSION,
    KernelError,
)

FORMAT = "axwp"
FORMAT_VERSION = 1
FRAGMENT = "L0"

RESERVED_WORDS = frozenset({"and", "or", "imp", "false"})
FRAGMENT_TAGS = frozenset({"lam", "forall", "exists", "eq"})

_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_HASH = re.compile(r"sha256:[0-9a-f]{64}")
_MAX_IDENTIFIER = 255
_MAX_DECL_NAME = 1023


@dataclass(frozen=True)
class Limits:
    """Resource limits (kernel-spec §8.5)."""

    max_bytes: int = 64 * 1024 * 1024
    max_depth: int = 512
    max_nodes: int = 10_000_000
    max_declarations: int = 100_000


DEFAULT_LIMITS = Limits()


def _fail(code: str, path: str, message: str) -> NoReturn:
    raise KernelError(code, path, message)


# --- canonical JSON and hashes (kernel-spec §7.2–7.4) -------------------------


def canonical_json(value: Any) -> bytes:
    """Return the canonical ASCII bytes of a JSON value that satisfies §7.1."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
        "ascii"
    )


def sha256_tag(value: Any) -> str:
    return "sha256:" + hashlib.sha256(canonical_json(value)).hexdigest()


def declaration_hash(decl: dict[str, Any]) -> str:
    """Hash of a declaration object without its `hash` and `axioms` keys (§7.3)."""
    core = {k: v for k, v in decl.items() if k not in ("hash", "axioms")}
    return sha256_tag(core)


def bundle_hash(bundle: dict[str, Any]) -> str:
    """Hash of a bundle object without its `bundle_hash` key (§7.4)."""
    return sha256_tag({k: v for k, v in bundle.items() if k != "bundle_hash"})


# --- parsing with JSON restrictions (kernel-spec §7.1, §8.5) ------------------


def _nesting_depth(text: str) -> int:
    """Maximum array/object nesting depth, ignoring brackets inside strings."""
    depth = deepest = 0
    in_string = escaped = False
    for ch in text:
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
        elif ch == '"':
            in_string = True
        elif ch in "[{":
            depth += 1
            deepest = max(deepest, depth)
        elif ch in "]}":
            depth -= 1
    return deepest


def _reject_float(text: str) -> NoReturn:
    _fail(E_FORMAT, "$", f"non-integer number {text!r} is not allowed")


def _reject_constant(text: str) -> NoReturn:
    _fail(E_FORMAT, "$", f"constant {text} is not allowed")


def _no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _fail(E_FORMAT, "$", f"duplicate key {key!r}")
        result[key] = value
    return result


def _check_values(value: Any, path: str) -> None:
    """Allow only objects, arrays, printable-ASCII strings and non-negative integers."""
    if isinstance(value, dict):
        for key, item in value.items():
            _check_string(key, path)
            _check_values(item, f"{path}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            _check_values(item, f"{path}[{index}]")
    elif isinstance(value, str):
        _check_string(value, path)
    elif type(value) is int:
        if value < 0:
            _fail(E_FORMAT, path, "negative integers are not allowed")
    else:
        _fail(E_FORMAT, path, f"JSON value {value!r} is not allowed")


def _check_string(text: str, path: str) -> None:
    if not all(" " <= ch <= "~" for ch in text):
        _fail(E_FORMAT, path, "strings must be printable ASCII")


def parse_json(data: bytes, limits: Limits) -> Any:
    """Parse certificate bytes, enforcing size, depth and §7.1 value restrictions."""
    if not isinstance(data, bytes):
        _fail(E_FORMAT, "$", "input must be bytes")
    if len(data) > limits.max_bytes:
        _fail(E_LIMIT, "$", f"input exceeds {limits.max_bytes} bytes")
    if data.startswith(b"\xef\xbb\xbf"):
        _fail(E_FORMAT, "$", "UTF-8 BOM is not allowed")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        _fail(E_FORMAT, "$", "input is not valid UTF-8")
    if _nesting_depth(text) > limits.max_depth:
        _fail(E_LIMIT, "$", f"nesting depth exceeds {limits.max_depth}")
    try:
        value = json.loads(
            text,
            object_pairs_hook=_no_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
        )
    except json.JSONDecodeError as exc:
        _fail(E_FORMAT, "$", f"invalid JSON: {exc.msg}")
    _check_values(value, "$")
    return value


# --- names (kernel-spec §3) ---------------------------------------------------


def _is_identifier(text: object) -> bool:
    return (
        isinstance(text, str)
        and len(text) <= _MAX_IDENTIFIER
        and _IDENTIFIER.fullmatch(text) is not None
    )


def check_local_name(name: object, path: str) -> str:
    """Validate an atom or hypothesis name."""
    if not _is_identifier(name) or name in RESERVED_WORDS:
        _fail(E_NAME, path, f"invalid atom or hypothesis name {name!r}")
    assert isinstance(name, str)
    return name


def check_decl_name(name: object, path: str, min_segments: int = 2) -> str:
    """Validate a dotted declaration (or theory) name."""
    if not isinstance(name, str) or len(name) > _MAX_DECL_NAME:
        _fail(E_NAME, path, f"invalid declaration name {name!r}")
    segments = name.split(".")
    if len(segments) < min_segments or not all(_is_identifier(s) for s in segments):
        _fail(E_NAME, path, f"invalid declaration name {name!r}")
    return name


def check_hash(value: object, path: str) -> str:
    if not isinstance(value, str) or _HASH.fullmatch(value) is None:
        _fail(E_FORMAT, path, "hash must be 'sha256:' followed by 64 lowercase hex digits")
    return value


def check_keys(obj: object, expected: set[str], path: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        _fail(E_FORMAT, path, "expected an object")
    if set(obj) != expected:
        missing = sorted(expected - set(obj))
        extra = sorted(set(obj) - expected)
        _fail(E_FORMAT, path, f"wrong keys (missing {missing}, unexpected {extra})")
    return obj


def check_str(value: object, path: str) -> str:
    if not isinstance(value, str):
        _fail(E_FORMAT, path, "expected a string")
    return value


# --- propositions (kernel-spec §4) --------------------------------------------

Prop = int  # index into a PropTable


class PropTable:
    """Hash-consed proposition nodes, so that structural equality is integer equality.

    Nodes are ("atom", name), ("false",), or (tag, left_id, right_id) for
    tag in {"and", "or", "imp"}.
    """

    def __init__(self) -> None:
        self.nodes: list[tuple[Any, ...]] = []
        self._index: dict[tuple[Any, ...], int] = {}
        self._budget: int | None = None
        self._atoms: dict[int, frozenset[str]] = {}

    def set_budget(self, budget: int | None) -> None:
        """Limit the number of new nodes until the next call (None = unlimited)."""
        self._budget = budget

    def make(self, node: tuple[Any, ...]) -> Prop:
        found = self._index.get(node)
        if found is not None:
            return found
        if self._budget is not None:
            if self._budget <= 0:
                _fail(E_LIMIT, "$", "too many proposition nodes")
            self._budget -= 1
        self.nodes.append(node)
        self._index[node] = len(self.nodes) - 1
        return len(self.nodes) - 1

    def atoms(self, prop: Prop) -> frozenset[str]:
        cached = self._atoms.get(prop)
        if cached is not None:
            return cached
        node = self.nodes[prop]
        if node[0] == "atom":
            result = frozenset({node[1]})
        elif node[0] == "false":
            result = frozenset()
        else:
            result = self.atoms(node[1]) | self.atoms(node[2])
        self._atoms[prop] = result
        return result

    def substitute(self, prop: Prop, subst: dict[str, Prop]) -> Prop:
        """Simultaneous substitution of atoms (logic-spec §6.1)."""
        memo: dict[Prop, Prop] = {}

        def go(p: Prop) -> Prop:
            if p in memo:
                return memo[p]
            node = self.nodes[p]
            if node[0] == "atom":
                result = subst.get(node[1], p)
            elif node[0] == "false":
                result = p
            else:
                result = self.make((node[0], go(node[1]), go(node[2])))
            memo[p] = result
            return result

        return go(prop)

    def show(self, prop: Prop) -> str:
        node = self.nodes[prop]
        if node[0] == "atom":
            return str(node[1])
        if node[0] == "false":
            return "⊥"
        symbol = {"and": "∧", "or": "∨", "imp": "→"}[node[0]]
        return f"({self.show(node[1])} {symbol} {self.show(node[2])})"


def decode_prop(value: object, table: PropTable, path: str) -> Prop:
    if not isinstance(value, list) or not value or not isinstance(value[0], str):
        _fail(E_FORMAT, path, "a proposition must be an array starting with a tag")
    tag = value[0]
    if tag == "atom" and len(value) == 2:
        return table.make(("atom", check_local_name(value[1], f"{path}[1]")))
    if tag == "false" and len(value) == 1:
        return table.make(("false",))
    if tag in ("and", "or", "imp") and len(value) == 3:
        left = decode_prop(value[1], table, f"{path}[1]")
        right = decode_prop(value[2], table, f"{path}[2]")
        return table.make((tag, left, right))
    if tag in FRAGMENT_TAGS:
        _fail(E_FRAGMENT, path, f"'{tag}' is outside fragment L0")
    _fail(E_FORMAT, path, f"malformed proposition with tag {tag!r} and {len(value)} elements")


# --- derivation trees (kernel-spec §5) ----------------------------------------

# Decoded derivation node: (rule, path, *fields). Fields keep the visiting
# order of kernel-spec §8.4.
Node = tuple[Any, ...]

_RULE_KEYS: dict[str, tuple[str, ...]] = {
    "hyp": ("name",),
    "and_i": ("left", "right"),
    "and_e1": ("of",),
    "and_e2": ("of",),
    "or_i1": ("of", "right"),
    "or_i2": ("left", "of"),
    "or_e": ("of", "left_name", "left", "right_name", "right"),
    "imp_i": ("name", "hyp", "body"),
    "imp_e": ("fn", "arg"),
    "false_e": ("of", "goal"),
    "thm": ("name", "hash", "subst"),
    "ax": ("name", "hash", "subst"),
}

# Which fields hold sub-derivations, propositions, or local names, per rule.
_DERIVATION_FIELDS = {"of", "body", "fn", "arg"} | {"left", "right"}
_PROP_FIELDS: dict[str, set[str]] = {
    "or_i1": {"right"},
    "or_i2": {"left"},
    "imp_i": {"hyp"},
    "false_e": {"goal"},
}
_LOCAL_NAME_FIELDS = {"left_name", "right_name"}


def decode_derivation(value: object, table: PropTable, path: str) -> Node:
    if not isinstance(value, dict) or not isinstance(value.get("rule"), str):
        _fail(E_FORMAT, path, "a derivation node must be an object with a 'rule' string")
    rule = value["rule"]
    keys = _RULE_KEYS.get(rule)
    if keys is None:
        _fail(E_FORMAT, path, f"unknown rule {rule!r}")
    check_keys(value, {"rule", *keys}, path)

    fields: list[Any] = []
    for key in keys:
        item = value[key]
        sub = f"{path}.{key}"
        if rule in ("thm", "ax"):
            if key == "name":
                fields.append(check_decl_name(item, sub))
            elif key == "hash":
                fields.append(check_hash(item, sub))
            else:
                fields.append(decode_subst(item, table, sub))
        elif key in _PROP_FIELDS.get(rule, set()):
            fields.append(decode_prop(item, table, sub))
        elif key == "name" or key in _LOCAL_NAME_FIELDS:
            fields.append(check_local_name(item, sub))
        elif key in _DERIVATION_FIELDS:
            fields.append(decode_derivation(item, table, sub))
        else:  # pragma: no cover - every key of _RULE_KEYS is classified above
            _fail(E_FORMAT, sub, f"unclassified field {key!r}")
    return (rule, path, *fields)


def decode_subst(value: object, table: PropTable, path: str) -> dict[str, Prop]:
    if not isinstance(value, dict):
        _fail(E_FORMAT, path, "a substitution must be an object")
    result: dict[str, Prop] = {}
    for key in sorted(value):
        name = check_local_name(key, f"{path}.{key}")
        result[name] = decode_prop(value[key], table, f"{path}.{key}")
    return result


# --- bundle structure (kernel-spec §6) ----------------------------------------

_BUNDLE_KEYS = {
    "format",
    "format_version",
    "spec_version",
    "fragment",
    "kernel_version",
    "theory",
    "declarations",
    "bundle_hash",
}
_AXIOM_KEYS = {"kind", "name", "statement", "hash"}
_THEOREM_KEYS = {"kind", "name", "statement", "proof", "hash", "axioms"}


@dataclass(frozen=True)
class Declaration:
    """A structurally valid declaration (kernel-spec §6.1)."""

    index: int
    kind: str
    name: str
    statement: Prop
    proof: Node | None
    recorded_hash: str
    computed_hash: str
    recorded_axioms: tuple[str, ...]
    path: str


def check_bundle_header(bundle: object, limits: Limits) -> dict[str, Any]:
    """Stage 2: bundle keys, version fields and bundle hash."""
    obj = check_keys(bundle, _BUNDLE_KEYS, "$")
    if obj["format"] != FORMAT:
        _fail(E_VERSION, "$.format", f"unsupported format {obj['format']!r}")
    if type(obj["format_version"]) is not int:
        _fail(E_FORMAT, "$.format_version", "format_version must be an integer")
    if obj["format_version"] != FORMAT_VERSION:
        _fail(E_VERSION, "$.format_version", f"unsupported version {obj['format_version']}")
    if obj["fragment"] != FRAGMENT:
        _fail(E_VERSION, "$.fragment", f"unsupported fragment {obj['fragment']!r}")
    check_str(obj["spec_version"], "$.spec_version")
    check_str(obj["kernel_version"], "$.kernel_version")
    check_decl_name(obj["theory"], "$.theory", min_segments=1)
    if not isinstance(obj["declarations"], list):
        _fail(E_FORMAT, "$.declarations", "declarations must be an array")
    if len(obj["declarations"]) > limits.max_declarations:
        _fail(E_LIMIT, "$.declarations", f"more than {limits.max_declarations} declarations")
    check_hash(obj["bundle_hash"], "$.bundle_hash")
    return obj


def decode_declaration(value: object, index: int, table: PropTable) -> Declaration:
    """Stage 3: structure, names and encodings of one declaration."""
    path = f"$.declarations[{index}]"
    if not isinstance(value, dict):
        _fail(E_FORMAT, path, "a declaration must be an object")
    kind = value.get("kind")
    if kind == "axiom":
        check_keys(value, _AXIOM_KEYS, path)
    elif kind == "theorem":
        check_keys(value, _THEOREM_KEYS, path)
    else:
        _fail(E_FORMAT, f"{path}.kind", f"unknown declaration kind {kind!r}")

    name = check_decl_name(value["name"], f"{path}.name")
    statement = decode_prop(value["statement"], table, f"{path}.statement")
    proof = None
    axioms: tuple[str, ...] = ()
    if kind == "theorem":
        proof = decode_derivation(value["proof"], table, f"{path}.proof")
        axioms = _decode_axiom_list(value["axioms"], f"{path}.axioms")
    recorded = check_hash(value["hash"], f"{path}.hash")
    return Declaration(
        index=index,
        kind=kind,
        name=name,
        statement=statement,
        proof=proof,
        recorded_hash=recorded,
        computed_hash=declaration_hash(value),
        recorded_axioms=axioms,
        path=path,
    )


def _decode_axiom_list(value: object, path: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        _fail(E_FORMAT, path, "axioms must be an array")
    names = tuple(check_decl_name(v, f"{path}[{i}]") for i, v in enumerate(value))
    if list(names) != sorted(set(names)):
        _fail(E_FORMAT, path, "axioms must be sorted and without duplicates")
    return names
