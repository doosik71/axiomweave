"""Kernel entry point: bundle checking stages and the report (kernel-spec §8, §10)."""

from collections.abc import Mapping
from dataclasses import dataclass

from axiomweave.kernel.certificate import (
    DEFAULT_LIMITS,
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
    Diagnostic,
    KernelError,
)
from axiomweave.kernel.rules import Accepted, Environment, infer

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

    table, decls = declarations
    env: Environment = {}
    results = tuple(_check_declaration(env, table, d, limits) for d in decls)
    return KernelReport(True, None, results)


def _check_bundle_level(
    data: bytes, allowed_axioms: Mapping[str, str], limits: Limits
) -> tuple[PropTable, list[Declaration]]:
    """Stages 1-5 (kernel-spec §8.2). Any failure rejects the whole bundle."""
    value = parse_json(data, limits)  # stage 1
    bundle = check_bundle_header(value, limits)  # stage 2
    if bundle_hash(bundle) != bundle["bundle_hash"]:
        raise KernelError(E_HASH_MISMATCH, "$.bundle_hash", "bundle hash does not match")

    table = PropTable()
    decls = [decode_declaration(v, i, table) for i, v in enumerate(bundle["declarations"])]

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
    return table, decls


def _check_declaration(
    env: Environment, table: PropTable, d: Declaration, limits: Limits
) -> DeclarationResult:
    """Stage 6 for one declaration (kernel-spec §8.3)."""
    try:
        if d.recorded_hash != d.computed_hash:
            raise KernelError(E_HASH_MISMATCH, f"{d.path}.hash", "declaration hash does not match")
        if d.kind == "axiom":
            env[d.name] = Accepted("axiom", d.computed_hash, d.statement, frozenset())
            return DeclarationResult(d.name, d.kind, ACCEPTED, None, None)

        assert d.proof is not None
        table.set_budget(limits.max_nodes)
        try:
            conclusion, axioms = infer(env, table, {}, d.proof)
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
        env[d.name] = Accepted("theorem", d.computed_hash, d.statement, axioms)
        return DeclarationResult(d.name, d.kind, VERIFIED, None, computed)
    except KernelError as exc:
        return DeclarationResult(d.name, d.kind, REJECTED, exc.diagnostic, None)
    except Exception as exc:  # noqa: BLE001 - internal errors must become rejections
        error = Diagnostic(E_INTERNAL, d.path, repr(exc))
        return DeclarationResult(d.name, d.kind, REJECTED, error, None)
