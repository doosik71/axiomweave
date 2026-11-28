"""Kernel entry point: bundle checking stages and the report (kernel-spec §8, §10)."""

from collections.abc import Mapping
from dataclasses import dataclass

from axiomweave.kernel.certificate import (
    DEFAULT_LIMITS,
    FIRST_ORDER,
    PROP_RESULT,
    Declaration,
    Limits,
    PropTable,
    bundle_hash,
    check_bundle_header,
    decode_declaration,
    parse_json,
)
from axiomweave.kernel.errors import (
    E_AXIOM_NOT_ALLOWED,
    E_AXIOMS_MISMATCH,
    E_CONCLUSION_MISMATCH,
    E_DUPLICATE_DECL,
    E_HASH_MISMATCH,
    E_INTERNAL,
    E_UNKNOWN_DECL,
    Diagnostic,
    KernelError,
)
from axiomweave.kernel.rules import Accepted, Checker, Environment, check_statement

VERIFIED = "VERIFIED"
ACCEPTED = "ACCEPTED"
REJECTED = "REJECTED"


@dataclass(frozen=True)
class DeclarationResult:
    name: str
    kind: str
    status: str
    error: Diagnostic | None
    axioms: tuple[str, ...] | None  # computed dependencies of a verified theorem


@dataclass(frozen=True)
class KernelReport:
    bundle_ok: bool
    bundle_error: Diagnostic | None
    results: tuple[DeclarationResult, ...]

    @property
    def ok(self) -> bool:
        return self.bundle_ok and all(r.status != REJECTED for r in self.results)


def check_bundle(
    data: bytes,
    allowed_axioms: Mapping[str, str],
    limits: Limits = DEFAULT_LIMITS,
) -> KernelReport:
    """Check a certificate bundle. Never raises; every failure is a rejection."""
    try:
        declarations = _check_bundle_level(data, allowed_axioms, limits)
    except KernelError as exc:
        return KernelReport(False, exc.diagnostic, ())
    except Exception as exc:  # noqa: BLE001 - internal errors must become rejections
        return KernelReport(False, Diagnostic(E_INTERNAL, "$", repr(exc)), ())

    table, decls, fragment = declarations
    env: Environment = {}
    results = tuple(_check_declaration(env, table, d, limits, fragment) for d in decls)
    return KernelReport(True, None, results)


def _check_bundle_level(
    data: bytes, allowed_axioms: Mapping[str, str], limits: Limits
) -> tuple[PropTable, list[Declaration], str]:
    """Stages 1-5 (kernel-spec §8.2). Any failure rejects the whole bundle."""
    value = parse_json(data, limits)  # stage 1
    bundle = check_bundle_header(value, limits)  # stage 2
    if bundle_hash(bundle) != bundle["bundle_hash"]:
        raise KernelError(E_HASH_MISMATCH, "$.bundle_hash", "bundle hash does not match")

    table = PropTable()
    fragment = bundle["fragment"]
    decls = [
        decode_declaration(v, i, table, fragment) for i, v in enumerate(bundle["declarations"])
    ]

    seen: set[str] = set()  # stage 4
    for d in decls:
        if d.name in seen:
            raise KernelError(E_DUPLICATE_DECL, f"{d.path}.name", f"duplicate name {d.name!r}")
        seen.add(d.name)

    for d in decls:  # stage 5
        if d.kind == "axiom" and allowed_axioms.get(d.name) != d.computed_hash:
            raise KernelError(
                E_AXIOM_NOT_ALLOWED, d.path, f"axiom {d.name!r} is not in the allow list"
            )
    return table, decls, fragment


def _check_declaration(
    env: Environment, table: PropTable, d: Declaration, limits: Limits, fragment: str
) -> DeclarationResult:
    """Stage 6 for one declaration (kernel-spec §8.3, §13.8)."""
    try:
        if d.recorded_hash != d.computed_hash:
            raise KernelError(E_HASH_MISMATCH, f"{d.path}.hash", "declaration hash does not match")
        if d.kind == "sort":
            env[d.name] = Accepted("sort", d.computed_hash)
            return DeclarationResult(d.name, d.kind, ACCEPTED, None, None)
        if d.kind == "const":
            for i, sort in enumerate(d.args):
                _require_sort(env, sort, f"{d.path}.args[{i}]")
            if d.result != PROP_RESULT:
                _require_sort(env, d.result, f"{d.path}.result")
            env[d.name] = Accepted("const", d.computed_hash, args=d.args, result=d.result)
            return DeclarationResult(d.name, d.kind, ACCEPTED, None, None)

        assert d.statement is not None
        typed = fragment in FIRST_ORDER
        signature = check_statement(env, table, d.statement, f"{d.path}.statement") if typed else {}
        if d.kind == "axiom":
            env[d.name] = Accepted("axiom", d.computed_hash, d.statement, signature=signature)
            return DeclarationResult(d.name, d.kind, ACCEPTED, None, None)

        assert d.proof is not None
        table.set_budget(limits.max_nodes)
        try:
            conclusion, axioms = Checker(env, table, typed).infer((), {}, d.proof)
        finally:
            table.set_budget(None)
        if conclusion != d.statement:
            raise KernelError(
                E_CONCLUSION_MISMATCH,
                f"{d.path}.proof",
                f"proof concludes {table.show(conclusion)}, statement is {table.show(d.statement)}",
            )
        computed = tuple(sorted(axioms))
        if computed != d.recorded_axioms:
            raise KernelError(
                E_AXIOMS_MISMATCH,
                f"{d.path}.axioms",
                f"recorded {list(d.recorded_axioms)}, computed {list(computed)}",
            )
        env[d.name] = Accepted("theorem", d.computed_hash, d.statement, axioms, signature)
        return DeclarationResult(d.name, d.kind, VERIFIED, None, computed)
    except KernelError as exc:
        return DeclarationResult(d.name, d.kind, REJECTED, exc.diagnostic, None)
    except Exception as exc:  # noqa: BLE001 - internal errors must become rejections
        error = Diagnostic(E_INTERNAL, d.path, repr(exc))
        return DeclarationResult(d.name, d.kind, REJECTED, error, None)


def _require_sort(env: Environment, name: str, path: str) -> None:
    decl = env.get(name)
    if decl is None or decl.kind != "sort":
        raise KernelError(
            E_UNKNOWN_DECL, path, f"no accepted sort named {name!r} before this point"
        )
