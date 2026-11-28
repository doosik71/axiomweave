"""JSON restrictions, canonical form, hashes and decoding of L0/L1 certificates.

Implements kernel-spec §3 (names), §4 (propositions), §5 (derivation trees),
§6 (bundle structure), §7 (canonical JSON and SHA-256 hashes) and, for
fragment L1, §13.2–13.6 (terms, quantifiers, declarations, de Bruijn operations)
and, for fragment L2, §14 (equality).
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
    E_VAR_ESCAPE,
    E_VERSION,
    KernelError,
)

FORMAT = "axwp"
FORMAT_VERSION = 1
L0, L1, L2 = "L0", "L1", "L2"
FRAGMENTS = frozenset({L0, L1, L2})
FIRST_ORDER = frozenset({L1, L2})  # fragments with terms, sorts and quantifiers

RESERVED_WORDS = frozenset({"and", "or", "imp", "false"})
PROP_RESULT = "prop"  # `result` of a const declaration whose type ends in Prop

# Tags outside each fragment that are reported as E_FRAGMENT (kernel-spec §4, §13.3, §14.2).
_OUTSIDE_L2_TAGS = frozenset({"lam"})
_OUTSIDE_L1_TAGS = _OUTSIDE_L2_TAGS | {"eq"}
_OUTSIDE_L0_TAGS = _OUTSIDE_L1_TAGS | {"pvar", "pred", "forall", "exists", "var", "app"}
_OUTSIDE_TAGS = {L0: _OUTSIDE_L0_TAGS, L1: _OUTSIDE_L1_TAGS, L2: _OUTSIDE_L2_TAGS}

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
    """Validate an atom, schematic predicate or hypothesis name."""
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


# --- propositions and terms (kernel-spec §4, §13.3, §13.6) --------------------

Prop = int  # index into a PropTable (propositions and L1 terms share the table)

# A schematic substitution value: (argument sorts, body). An atom has no
# argument sorts; the body of a `pvar` value lives under one binder per sort.
SubstValue = tuple[tuple[str, ...], Prop]


class PropTable:
    """Hash-consed proposition and term nodes, so that structural equality is integer equality.

    Nodes are ("atom", name), ("false",), (tag, left_id, right_id) for tag in
    {"and", "or", "imp"}, and in fragment L1 additionally ("pvar", name, args),
    ("pred", const, args), ("forall", sort, body), ("exists", sort, body),
    ("var", index) and ("app", const, args), where args is a tuple of term ids;
    in fragment L2 also ("eq", left_term, right_term).
    Bound variables are de Bruijn indices (0 = innermost binder).
    """

    def __init__(self) -> None:
        self.nodes: list[tuple[Any, ...]] = []
        self._index: dict[tuple[Any, ...], int] = {}
        self._budget: int | None = None
        self._atoms: dict[int, frozenset[str]] = {}
        self._loose: dict[int, int] = {}

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
        """Names of the schematic variables (atoms and `pvar`s) occurring in `prop`."""
        cached = self._atoms.get(prop)
        if cached is not None:
            return cached
        node = self.nodes[prop]
        tag = node[0]
        if tag in ("atom", "pvar"):
            result = frozenset({node[1]})
        elif tag in ("and", "or", "imp"):
            result = self.atoms(node[1]) | self.atoms(node[2])
        elif tag in ("forall", "exists"):
            result = self.atoms(node[2])
        else:  # false, pred and terms contain no schematic variables
            result = frozenset()
        self._atoms[prop] = result
        return result

    def loose(self, prop: Prop) -> int:
        """One more than the largest free de Bruijn index (0 if there is none)."""
        cached = self._loose.get(prop)
        if cached is not None:
            return cached
        node = self.nodes[prop]
        tag = node[0]
        if tag == "var":
            result = node[1] + 1
        elif tag in ("app", "pred", "pvar"):
            result = max((self.loose(a) for a in node[2]), default=0)
        elif tag in ("and", "or", "imp", "eq"):
            result = max(self.loose(node[1]), self.loose(node[2]))
        elif tag in ("forall", "exists"):
            result = max(self.loose(node[2]) - 1, 0)
        else:
            result = 0
        self._loose[prop] = result
        return result

    def _map_vars(self, prop: Prop, leaf: Any, threshold: int) -> Prop:
        """Rebuild `prop`, replacing each ("var", i) at binder depth j by leaf(i, j).

        Subterms whose free indices are all below `threshold + j` are kept as is.
        """
        memo: dict[tuple[Prop, int], Prop] = {}

        def go(p: Prop, depth: int) -> Prop:
            if self.loose(p) <= threshold + depth:
                return p
            key = (p, depth)
            found = memo.get(key)
            if found is not None:
                return found
            node = self.nodes[p]
            tag = node[0]
            if tag == "var":
                result: Prop = leaf(node[1], depth)
            elif tag in ("app", "pred", "pvar"):
                result = self.make((tag, node[1], tuple(go(a, depth) for a in node[2])))
            elif tag in ("forall", "exists"):
                result = self.make((tag, node[1], go(node[2], depth + 1)))
            else:  # and, or, imp, eq
                result = self.make((tag, go(node[1], depth), go(node[2], depth)))
            memo[key] = result
            return result

        return go(prop, 0)

    def shift(self, prop: Prop, amount: int, cutoff: int = 0) -> Prop:
        """Add `amount` to free indices >= cutoff (kernel-spec §13.6 shift, shift')."""
        if amount == 0:
            return prop
        return self._map_vars(prop, lambda i, j: self.make(("var", i + amount)), cutoff)

    def instantiate(self, prop: Prop, terms: tuple[Prop, ...]) -> Prop:
        """Replace the n innermost free indices by `terms` (kernel-spec §13.6 inst).

        `prop` lives under n extra binders; the last term replaces index 0.
        """
        n = len(terms)

        def leaf(i: int, j: int) -> Prop:
            if i < j + n:
                return self.shift(terms[n - 1 - (i - j)], j)
            return self.make(("var", i - n))

        return self._map_vars(prop, leaf, 0)

    def lower(self, prop: Prop, path: str) -> Prop:
        """Drop the innermost binder from scope; fail if it occurs (kernel-spec §13.6)."""

        def leaf(i: int, j: int) -> Prop:
            if i == j:
                _fail(E_VAR_ESCAPE, path, "the witness variable occurs in the conclusion")
            return self.make(("var", i - 1))

        return self._map_vars(prop, leaf, 0)

    def substitute(self, prop: Prop, subst: dict[str, SubstValue]) -> Prop:
        """Simultaneous schematic substitution (logic-spec §6.1, §12.6; kernel-spec §13.6)."""
        memo: dict[tuple[Prop, int], Prop] = {}

        def go(p: Prop, depth: int) -> Prop:
            if not (self.atoms(p) & subst.keys()):
                return p
            key = (p, depth)
            found = memo.get(key)
            if found is not None:
                return found
            node = self.nodes[p]
            tag = node[0]
            if tag == "atom":
                result = self.shift(subst[node[1]][1], depth)
            elif tag == "pvar":
                params, body = subst[node[1]]
                result = self.instantiate(self.shift(body, depth, len(params)), node[2])
            elif tag in ("forall", "exists"):
                result = self.make((tag, node[1], go(node[2], depth + 1)))
            else:  # and, or, imp; other nodes contain no schematic variables
                result = self.make((tag, go(node[1], depth), go(node[2], depth)))
            memo[key] = result
            return result

        return go(prop, 0)

    def show(self, prop: Prop) -> str:
        node = self.nodes[prop]
        tag = node[0]
        if tag == "atom":
            return str(node[1])
        if tag == "false":
            return "⊥"
        if tag == "var":
            return f"#{node[1]}"
        if tag in ("app", "pred", "pvar"):
            return f"{node[1]}({', '.join(self.show(a) for a in node[2])})"
        if tag == "eq":
            return f"({self.show(node[1])} = {self.show(node[2])})"
        if tag in ("forall", "exists"):
            quantifier = "∀" if tag == "forall" else "∃"
            return f"({quantifier}:{node[1]}. {self.show(node[2])})"
        symbol = {"and": "∧", "or": "∨", "imp": "→"}[tag]
        return f"({self.show(node[1])} {symbol} {self.show(node[2])})"


def decode_term(value: object, table: PropTable, path: str) -> Prop:
    """Decode an L1 individual term (kernel-spec §13.3)."""
    if not isinstance(value, list) or not value or not isinstance(value[0], str):
        _fail(E_FORMAT, path, "a term must be an array starting with a tag")
    tag = value[0]
    if tag == "var" and len(value) == 2 and type(value[1]) is int:
        return table.make(("var", value[1]))
    if tag == "app" and len(value) == 3:
        name = check_decl_name(value[1], f"{path}[1]")
        return table.make(("app", name, _decode_args(value[2], table, f"{path}[2]")))
    _fail(E_FORMAT, path, f"malformed term with tag {tag!r} and {len(value)} elements")


def _decode_args(value: object, table: PropTable, path: str) -> tuple[Prop, ...]:
    if not isinstance(value, list):
        _fail(E_FORMAT, path, "arguments must be an array")
    return tuple(decode_term(v, table, f"{path}[{i}]") for i, v in enumerate(value))


def decode_prop(value: object, table: PropTable, path: str, fragment: str = L0) -> Prop:
    if not isinstance(value, list) or not value or not isinstance(value[0], str):
        _fail(E_FORMAT, path, "a proposition must be an array starting with a tag")
    tag = value[0]
    if tag == "atom" and len(value) == 2:
        return table.make(("atom", check_local_name(value[1], f"{path}[1]")))
    if tag == "false" and len(value) == 1:
        return table.make(("false",))
    if tag in ("and", "or", "imp") and len(value) == 3:
        left = decode_prop(value[1], table, f"{path}[1]", fragment)
        right = decode_prop(value[2], table, f"{path}[2]", fragment)
        return table.make((tag, left, right))
    if fragment == L2 and tag == "eq" and len(value) == 3:
        left = decode_term(value[1], table, f"{path}[1]")
        return table.make(("eq", left, decode_term(value[2], table, f"{path}[2]")))
    if fragment in FIRST_ORDER:
        if tag == "pvar" and len(value) == 3:
            name = check_local_name(value[1], f"{path}[1]")
            args = _decode_args(value[2], table, f"{path}[2]")
            if not args:
                _fail(E_FORMAT, path, "a 'pvar' without arguments must be written as 'atom'")
            return table.make(("pvar", name, args))
        if tag == "pred" and len(value) == 3:
            name = check_decl_name(value[1], f"{path}[1]")
            return table.make(("pred", name, _decode_args(value[2], table, f"{path}[2]")))
        if tag in ("forall", "exists") and len(value) == 3:
            sort = check_decl_name(value[1], f"{path}[1]")
            return table.make((tag, sort, decode_prop(value[2], table, f"{path}[2]", fragment)))
    if tag in _OUTSIDE_TAGS[fragment]:
        _fail(E_FRAGMENT, path, f"'{tag}' is outside fragment {fragment}")
    _fail(E_FORMAT, path, f"malformed proposition with tag {tag!r} and {len(value)} elements")


# --- derivation trees (kernel-spec §5, §13.5) ---------------------------------

# Decoded derivation node: (rule, path, *fields). Fields keep the visiting
# order of kernel-spec §8.4 and §13.8.
Node = tuple[Any, ...]

# Field kinds: D = derivation, P = proposition, H = local (hypothesis) name,
# N = declaration name, X = hash, S = substitution, T = term, Y = sort name.
_RULE_FIELDS: dict[str, tuple[tuple[str, str], ...]] = {
    "hyp": (("name", "H"),),
    "and_i": (("left", "D"), ("right", "D")),
    "and_e1": (("of", "D"),),
    "and_e2": (("of", "D"),),
    "or_i1": (("of", "D"), ("right", "P")),
    "or_i2": (("left", "P"), ("of", "D")),
    "or_e": (("of", "D"), ("left_name", "H"), ("left", "D"), ("right_name", "H"), ("right", "D")),
    "imp_i": (("name", "H"), ("hyp", "P"), ("body", "D")),
    "imp_e": (("fn", "D"), ("arg", "D")),
    "false_e": (("of", "D"), ("goal", "P")),
    "thm": (("name", "N"), ("hash", "X"), ("subst", "S")),
    "ax": (("name", "N"), ("hash", "X"), ("subst", "S")),
}
_L1_RULE_FIELDS: dict[str, tuple[tuple[str, str], ...]] = {
    "all_i": (("sort", "Y"), ("body", "D")),
    "all_e": (("of", "D"), ("term", "T")),
    "ex_i": (("prop", "P"), ("witness", "T"), ("of", "D")),
    "ex_e": (("of", "D"), ("name", "H"), ("body", "D")),
}
_L2_RULE_FIELDS: dict[str, tuple[tuple[str, str], ...]] = {
    "eq_refl": (("term", "T"),),
    "eq_e": (("eq", "D"), ("motive", "P"), ("of", "D")),
}


def decode_derivation(value: object, table: PropTable, path: str, fragment: str = L0) -> Node:
    if not isinstance(value, dict) or not isinstance(value.get("rule"), str):
        _fail(E_FORMAT, path, "a derivation node must be an object with a 'rule' string")
    rule = value["rule"]
    fields_spec = _RULE_FIELDS.get(rule)
    if fields_spec is None and rule in _L1_RULE_FIELDS:
        if fragment not in FIRST_ORDER:
            _fail(E_FRAGMENT, path, f"rule {rule!r} is outside fragment {fragment}")
        fields_spec = _L1_RULE_FIELDS[rule]
    if fields_spec is None and rule in _L2_RULE_FIELDS:
        if fragment != L2:
            _fail(E_FRAGMENT, path, f"rule {rule!r} is outside fragment {fragment}")
        fields_spec = _L2_RULE_FIELDS[rule]
    if fields_spec is None:
        _fail(E_FORMAT, path, f"unknown rule {rule!r}")
    check_keys(value, {"rule", *(key for key, _ in fields_spec)}, path)

    fields: list[Any] = []
    for key, kind in fields_spec:
        item = value[key]
        sub = f"{path}.{key}"
        if kind == "D":
            fields.append(decode_derivation(item, table, sub, fragment))
        elif kind == "P":
            fields.append(decode_prop(item, table, sub, fragment))
        elif kind == "H":
            fields.append(check_local_name(item, sub))
        elif kind in ("N", "Y"):
            fields.append(check_decl_name(item, sub))
        elif kind == "X":
            fields.append(check_hash(item, sub))
        elif kind == "T":
            fields.append(decode_term(item, table, sub))
        else:  # "S"
            fields.append(decode_subst(item, table, sub, fragment))
    return (rule, path, *fields)


def decode_subst(
    value: object, table: PropTable, path: str, fragment: str = L0
) -> dict[str, SubstValue]:
    """Decode a substitution. Array values are propositions for atoms; in L1, objects
    with exactly `params` and `body` are predicate abstractions (kernel-spec §13.5)."""
    if not isinstance(value, dict):
        _fail(E_FORMAT, path, "a substitution must be an object")
    result: dict[str, SubstValue] = {}
    for key in sorted(value):
        name = check_local_name(key, f"{path}.{key}")
        item = value[key]
        sub = f"{path}.{key}"
        if isinstance(item, dict):
            if fragment not in FIRST_ORDER:
                _fail(E_FRAGMENT, sub, f"predicate substitution is outside fragment {fragment}")
            check_keys(item, {"params", "body"}, sub)
            params = item["params"]
            if not isinstance(params, list) or not params:
                _fail(E_FORMAT, f"{sub}.params", "params must be a non-empty array of sorts")
            sorts = tuple(check_decl_name(s, f"{sub}.params[{i}]") for i, s in enumerate(params))
            result[name] = (sorts, decode_prop(item["body"], table, f"{sub}.body", fragment))
        else:
            result[name] = ((), decode_prop(item, table, sub, fragment))
    return result


# --- bundle structure (kernel-spec §6, §13.4) ---------------------------------

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
_DECL_KEYS: dict[str, set[str]] = {
    "axiom": {"kind", "name", "statement", "hash"},
    "theorem": {"kind", "name", "statement", "proof", "hash", "axioms"},
    "sort": {"kind", "name", "hash"},
    "const": {"kind", "name", "args", "result", "hash"},
}
_L1_KINDS = frozenset({"sort", "const"})


@dataclass(frozen=True)
class Declaration:
    """A structurally valid declaration (kernel-spec §6.1, §13.4)."""

    index: int
    kind: str
    name: str
    statement: Prop | None  # axioms and theorems
    proof: Node | None  # theorems
    recorded_hash: str
    computed_hash: str
    recorded_axioms: tuple[str, ...]
    path: str
    args: tuple[str, ...] = ()  # const argument sorts
    result: str = ""  # const result sort, or PROP_RESULT


def check_bundle_header(bundle: object, limits: Limits) -> dict[str, Any]:
    """Stage 2: bundle keys, version fields and bundle hash."""
    obj = check_keys(bundle, _BUNDLE_KEYS, "$")
    if obj["format"] != FORMAT:
        _fail(E_VERSION, "$.format", f"unsupported format {obj['format']!r}")
    if type(obj["format_version"]) is not int:
        _fail(E_FORMAT, "$.format_version", "format_version must be an integer")
    if obj["format_version"] != FORMAT_VERSION:
        _fail(E_VERSION, "$.format_version", f"unsupported version {obj['format_version']}")
    if obj["fragment"] not in FRAGMENTS:
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


def decode_declaration(
    value: object, index: int, table: PropTable, fragment: str = L0
) -> Declaration:
    """Stage 3: structure, names and encodings of one declaration."""
    path = f"$.declarations[{index}]"
    if not isinstance(value, dict):
        _fail(E_FORMAT, path, "a declaration must be an object")
    kind = value.get("kind")
    if not isinstance(kind, str) or kind not in _DECL_KEYS:
        _fail(E_FORMAT, f"{path}.kind", f"unknown declaration kind {kind!r}")
    if kind in _L1_KINDS and fragment not in FIRST_ORDER:
        _fail(E_FRAGMENT, f"{path}.kind", f"'{kind}' declarations are outside fragment {fragment}")
    check_keys(value, _DECL_KEYS[kind], path)

    name = check_decl_name(value["name"], f"{path}.name")
    statement = None
    proof = None
    axioms: tuple[str, ...] = ()
    args: tuple[str, ...] = ()
    result = ""
    if kind in ("axiom", "theorem"):
        statement = decode_prop(value["statement"], table, f"{path}.statement", fragment)
    if kind == "theorem":
        proof = decode_derivation(value["proof"], table, f"{path}.proof", fragment)
        axioms = _decode_axiom_list(value["axioms"], f"{path}.axioms")
    if kind == "const":
        if not isinstance(value["args"], list):
            _fail(E_FORMAT, f"{path}.args", "args must be an array of sort names")
        args = tuple(check_decl_name(s, f"{path}.args[{i}]") for i, s in enumerate(value["args"]))
        result = value["result"]
        if result != PROP_RESULT:
            result = check_decl_name(result, f"{path}.result")
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
        args=args,
        result=result,
    )


def _decode_axiom_list(value: object, path: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        _fail(E_FORMAT, path, "axioms must be an array")
    names = tuple(check_decl_name(v, f"{path}[{i}]") for i, v in enumerate(value))
    if list(names) != sorted(set(names)):
        _fail(E_FORMAT, path, "axioms must be sorted and without duplicates")
    return names
