"""Theories, declarations, checking and export (language-spec §5, §8, §12).

`Theory.check()` elaborates every proof in declaration order, packs the
results into a certificate bundle and passes its bytes to the kernel. Only the
kernel's verdict can make a theorem VERIFIED.
"""

import inspect
import json
import re
import traceback
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from enum import StrEnum
from importlib import metadata
from pathlib import Path
from typing import Any

from axiomweave.core.expressions import Const, Prop, Sort, is_local_name
from axiomweave.errors import AxwError, AxwTypeError, DeclarationError
from axiomweave.kernel import (
    STANDARD_AXIOMS,
    VERIFIED,
    bundle_hash,
    canonical_json,
    check_bundle,
    declaration_hash,
)
from axiomweave.kernel.errors import E_AXIOM_NOT_ALLOWED
from axiomweave.language.proof import DeclRef, ProofContext

ProofFunction = Callable[[ProofContext], object]

_THEORY_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*")


class Status(StrEnum):
    UNPROVEN = "UNPROVEN"
    VERIFIED = "VERIFIED"
    REJECTED = "REJECTED"


@dataclass(frozen=True)
class Diagnostic:
    stage: str  # "elaboration", "kernel" or "environment"
    message: str
    location: str | None = None  # "file:line" of the proof code
    goals: str | None = None  # goal state when elaboration stopped
    code: str | None = None  # kernel error code

    def __str__(self) -> str:
        parts = [f"[{self.stage}]"]
        if self.code:
            parts.append(self.code)
        if self.location:
            parts.append(self.location)
        text = " ".join(parts) + f": {self.message}"
        if self.goals:
            text += "\n" + self.goals
        return text


@dataclass(frozen=True)
class TheoremResult:
    name: str
    status: Status
    diagnostics: tuple[Diagnostic, ...]
    axioms: frozenset[str] | None


@dataclass(frozen=True)
class CheckReport:
    theory: str
    results: tuple[TheoremResult, ...]

    @property
    def ok(self) -> bool:
        return all(r.status is Status.VERIFIED for r in self.results)

    def __str__(self) -> str:
        lines = [f"theory {self.theory}: {'ok' if self.ok else 'FAILED'}"]
        for r in self.results:
            line = f"  {r.status.value:<9} {r.name}"
            if r.axioms:
                line += f"  [axioms: {', '.join(sorted(r.axioms))}]"
            lines.append(line)
            lines.extend("    " + str(d).replace("\n", "\n    ") for d in r.diagnostics)
        return "\n".join(lines)


class Axiom:
    """Handle of an axiom schema declared with `@thy.axiom`."""

    def __init__(self, theory: "Theory", name: str, statement: Prop) -> None:
        self.theory = theory
        self.name = name
        self.statement = statement

    def to_json(self) -> dict[str, Any]:
        decl: dict[str, Any] = {
            "kind": "axiom",
            "name": self.name,
            "statement": self.statement.to_json(),
        }
        decl["hash"] = declaration_hash(decl)
        return decl

    def __repr__(self) -> str:
        return f"<Axiom {self.name}: {self.statement}>"


class Theorem:
    """Handle of a theorem declared with `@thy.theorem`."""

    def __init__(self, theory: "Theory", name: str, statement: Prop) -> None:
        self.theory = theory
        self.name = name
        self.statement = statement
        self.status = Status.UNPROVEN
        self.axioms: frozenset[str] | None = None
        self._proof: ProofFunction | None = None

    def __repr__(self) -> str:
        return f"<Theorem {self.name}: {self.statement} ({self.status.value})>"


Declaration = Axiom | Theorem | Sort | Const


class Theory:
    """An ordered collection of axioms and theorems (language-spec §5)."""

    def __init__(self, name: str, imports: Sequence["Theory"] = ()) -> None:
        if not isinstance(name, str) or _THEORY_NAME.fullmatch(name) is None:
            raise DeclarationError(f"invalid theory name {name!r}")
        for imported in imports:
            if not isinstance(imported, Theory):
                raise AxwTypeError(f"imports must be Theory objects, got {imported!r}")
        self.name = name
        self.imports = tuple(imports)
        self._declarations: list[Declaration] = []
        self._export: dict[str, Any] | None = None
        self._fragment = "L0"

    def __repr__(self) -> str:
        return f"<Theory {self.name}>"

    # --- declarations -----------------------------------------------------------

    def _new_name(self, short: str) -> str:
        name = f"{self.name}.{short}"
        if not _THEORY_NAME.fullmatch(name):
            raise DeclarationError(f"invalid declaration name {name!r}")
        if any(d.name == name for d in self._declarations):
            raise DeclarationError(f"{name} is already declared")
        return name

    def _statement(self, function: Callable[[], Prop]) -> tuple[str, Prop]:
        if not callable(function):
            raise DeclarationError("a declaration decorator expects a function")
        if inspect.signature(function).parameters:
            raise DeclarationError(f"{function.__name__} must not take parameters in v0.1")
        name = self._new_name(function.__name__)
        statement = function()
        if not isinstance(statement, Prop):
            raise DeclarationError(f"{name} must return a Prop, got {type(statement).__name__}")
        self._check_statement(name, statement)
        return name, statement

    def _visible(self) -> list["Theory"]:
        """This theory and everything it imports, transitively."""
        order: list[Theory] = []
        seen: set[int] = set()

        def visit(theory: Theory) -> None:
            if id(theory) in seen:
                return
            seen.add(id(theory))
            for imported in theory.imports:
                visit(imported)
            order.append(theory)

        visit(self)
        return order

    def _require_visible(self, handle: Sort | Const, where: str) -> None:
        if not any(handle.theory is t for t in self._visible()):
            raise DeclarationError(
                f"{where} uses {handle.name}, which is not in the environment of {self.name}; "
                "import its theory"
            )

    def _check_statement(self, name: str, statement: Prop) -> None:
        """Statements are closed, use visible sorts and constants, and give each
        schematic variable one arity (language-spec §12.3–12.4)."""
        free = statement.free_vars()
        if free:
            names = ", ".join(sorted(n for n, _ in free))
            raise DeclarationError(f"{name} has free variables: {names}")
        try:
            statement.signature()
        except AxwTypeError as exc:
            raise DeclarationError(f"{name}: {exc}") from None
        sorts, consts = statement.symbols()
        for sort in sorted(sorts, key=lambda h: h.name):
            self._require_visible(sort, name)
        for const in sorted(consts, key=lambda h: h.name):
            self._require_visible(const, name)

    def sort(self, name: str) -> Sort:
        """Declare a base type (language-spec §12.2)."""
        if not is_local_name(name):
            raise DeclarationError(f"invalid sort name {name!r}")
        handle = Sort(self._new_name(name), name, self)
        self._declarations.append(handle)
        return handle

    def const(self, name: str, args: Sequence[Sort], result: object) -> Any:
        """Declare a function symbol (result is a Sort) or predicate symbol (result is
        `Prop`). Without arguments the constant itself is returned as a Term or Prop."""
        if not is_local_name(name):
            raise DeclarationError(f"invalid constant name {name!r}")
        arg_sorts = tuple(args)
        for sort in arg_sorts:
            if not isinstance(sort, Sort):
                raise AxwTypeError(f"const argument sorts must be Sort objects, got {sort!r}")
        if result is Prop:
            result_sort = None
        elif isinstance(result, Sort):
            result_sort = result
        else:
            raise AxwTypeError(f"const result must be a Sort or Prop, got {result!r}")
        full = self._new_name(name)
        for sort in (*arg_sorts, *([result_sort] if result_sort else [])):
            self._require_visible(sort, full)
        handle = Const(full, name, arg_sorts, result_sort, self)
        self._declarations.append(handle)
        return handle() if not arg_sorts else handle

    def axiom(self, function: Callable[[], Prop]) -> Axiom:
        """Declare an axiom schema; its atoms are schematic variables."""
        handle = Axiom(self, *self._statement(function))
        self._declarations.append(handle)
        return handle

    def theorem(self, function: Callable[[], Prop]) -> Theorem:
        """Declare a theorem; prove it with `@thy.proof` and verify it with `check()`."""
        handle = Theorem(self, *self._statement(function))
        self._declarations.append(handle)
        return handle

    def proof(self, theorem: Theorem) -> Callable[[ProofFunction], ProofFunction]:
        """Register a proof function for `theorem` without running it."""
        if not isinstance(theorem, Theorem) or theorem.theory is not self:
            raise DeclarationError("@proof needs a theorem declared in this theory")
        if theorem._proof is not None:
            raise DeclarationError(f"{theorem.name} already has a proof")

        def register(function: ProofFunction) -> ProofFunction:
            if theorem._proof is not None:
                raise DeclarationError(f"{theorem.name} already has a proof")
            theorem._proof = function
            return function

        return register

    def environment(self) -> list[Declaration]:
        """Imported declarations (transitively, each theory once) followed by our own."""
        declarations = [d for theory in self._visible() for d in theory._declarations]
        names: set[str] = set()
        for d in declarations:
            if d.name in names:
                raise DeclarationError(f"{d.name} is declared twice in the environment")
            names.add(d.name)
        return declarations

    # --- checking ---------------------------------------------------------------

    def check(self, allowed_axioms: Iterable[str] | None = None) -> CheckReport:
        """Elaborate all proofs and verify them with the kernel (language-spec §5.6)."""
        declarations = self.environment()
        position = {id(d): i for i, d in enumerate(declarations)}
        axiom_json = {d.name: d.to_json() for d in declarations if isinstance(d, Axiom)}
        policy = self._policy(allowed_axioms, axiom_json)

        bundle_declarations: list[dict[str, Any]] = []
        hashes: dict[str, str] = {}
        claimed_axioms: dict[str, frozenset[str]] = {}
        outcome: dict[str, TheoremResult] = {}

        for d in declarations:
            if isinstance(d, Sort | Const):
                signature_decl = d.to_json()
                signature_decl["hash"] = declaration_hash(signature_decl)
                bundle_declarations.append(signature_decl)
                continue
            if isinstance(d, Axiom):
                bundle_declarations.append(axiom_json[d.name])
                hashes[d.name] = axiom_json[d.name]["hash"]
                continue
            d.status, d.axioms = Status.UNPROVEN, None
            result, decl = self._elaborate(d, declarations, position, hashes, claimed_axioms)
            if decl is None:
                outcome[d.name] = result
                continue
            bundle_declarations.append(decl)
            hashes[d.name] = decl["hash"]
            claimed_axioms[d.name] = frozenset(decl["axioms"])

        if _uses_equality(bundle_declarations):
            self._fragment = "L2"
        elif any(isinstance(d, Sort) for d in declarations):
            self._fragment = "L1"
        else:
            self._fragment = "L0"
        bundle = self._bundle(bundle_declarations)
        report = check_bundle(canonical_json(bundle), policy)
        verified: list[dict[str, Any]] = []
        if not report.bundle_ok:
            assert report.bundle_error is not None
            error = report.bundle_error
            stage = "environment" if error.code == E_AXIOM_NOT_ALLOWED else "kernel"
            diagnostic = Diagnostic(stage, f"{error.message} ({error.path})", code=error.code)
            for decl in bundle_declarations:
                if decl["kind"] == "theorem":
                    outcome[decl["name"]] = TheoremResult(
                        decl["name"], Status.REJECTED, (diagnostic,), None
                    )
        else:
            by_name = {decl["name"]: decl for decl in bundle_declarations}
            for r in report.results:
                if r.kind != "theorem":
                    verified.append(by_name[r.name])
                elif r.status == VERIFIED:
                    axioms = frozenset(r.axioms or ())
                    outcome[r.name] = TheoremResult(r.name, Status.VERIFIED, (), axioms)
                    verified.append(by_name[r.name])
                else:
                    assert r.error is not None
                    diagnostic = Diagnostic(
                        "kernel", f"{r.error.message} ({r.error.path})", code=r.error.code
                    )
                    outcome[r.name] = TheoremResult(r.name, Status.REJECTED, (diagnostic,), None)

        results: list[TheoremResult] = []
        for d in declarations:
            if isinstance(d, Theorem):
                result = outcome[d.name]
                d.status, d.axioms = result.status, result.axioms
                results.append(result)
        self._export = self._bundle(verified)
        return CheckReport(self.name, tuple(results))

    def export(self, path: str | Path) -> Path:
        """Write the self-contained certificate bundle of the last `check()` (kernel-spec §6)."""
        if self._export is None:
            raise AxwError("call check() before export()")
        target = Path(path)
        target.write_text(json.dumps(self._export, indent=2) + "\n", encoding="utf-8")
        return target

    # --- internals --------------------------------------------------------------

    @staticmethod
    def _policy(
        allowed: Iterable[str] | None, axiom_json: dict[str, dict[str, Any]]
    ) -> dict[str, str]:
        names = list(STANDARD_AXIOMS) if allowed is None else allowed
        if isinstance(names, str):
            raise AxwTypeError("allowed_axioms must be a collection of names, not a string")
        policy: dict[str, str] = {}
        for name in names:
            if name in STANDARD_AXIOMS:
                policy[name] = STANDARD_AXIOMS[name]
            elif name in axiom_json:
                policy[name] = axiom_json[name]["hash"]
            else:
                raise DeclarationError(f"allowed axiom {name!r} is not declared")
        return policy

    def _elaborate(
        self,
        theorem: Theorem,
        declarations: list[Declaration],
        position: dict[int, int],
        hashes: dict[str, str],
        claimed_axioms: dict[str, frozenset[str]],
    ) -> tuple[TheoremResult, dict[str, Any] | None]:
        """Run the proof function; return the result so far and the bundle declaration."""

        def unproven(*diagnostics: Diagnostic) -> tuple[TheoremResult, None]:
            return TheoremResult(theorem.name, Status.UNPROVEN, diagnostics, None), None

        if theorem._proof is None:
            return unproven()

        def resolve(target: object) -> DeclRef:
            if isinstance(target, str):  # internal lookup by canonical name (ctx.induction)
                found = next((d for d in declarations if d.name == target), None)
                if found is None:
                    raise DeclarationError(
                        f"{target} is not in the environment of {self.name}; import its theory"
                    )
                target = found
            if not isinstance(target, Axiom | Theorem):  # sorts and constants are not facts
                raise AxwTypeError(f"thm expects a Theorem or Axiom, got {target!r}")
            index = position.get(id(target))
            if index is None:
                raise DeclarationError(
                    f"{target.name} is not in the environment of {self.name}; import its theory"
                )
            if index >= position[id(theorem)]:
                raise DeclarationError(f"{target.name} is not declared before {theorem.name}")
            if target.name not in hashes:
                raise DeclarationError(f"{target.name} has no elaborated proof")
            kind = "axiom" if isinstance(target, Axiom) else "theorem"
            return DeclRef(kind, target.name, hashes[target.name], target.statement)

        def candidates() -> list[tuple[object, frozenset[str]]]:
            before = declarations[: position[id(theorem)]]
            return [
                (d, frozenset({d.name}) if isinstance(d, Axiom) else claimed_axioms[d.name])
                for d in before
                if isinstance(d, Axiom | Theorem) and d.name in hashes
            ]

        ctx = ProofContext(theorem.statement, resolve, candidates)
        try:
            theorem._proof(ctx)
        except Exception as exc:  # noqa: BLE001 - any failure of the proof script rejects it
            diagnostic = Diagnostic(
                "elaboration",
                f"{type(exc).__name__}: {exc}",
                location=_location(exc, theorem._proof),
                goals=str(ctx),
            )
            return TheoremResult(theorem.name, Status.REJECTED, (diagnostic,), None), None

        try:
            derivation = ctx.finish()
        except AxwError as exc:  # e.g. a term whose variable is not in scope
            diagnostic = Diagnostic("elaboration", f"{type(exc).__name__}: {exc}")
            return TheoremResult(theorem.name, Status.REJECTED, (diagnostic,), None), None
        if derivation is None:
            return unproven(
                Diagnostic("elaboration", "proof ended with open goals", goals=str(ctx))
            )

        decl: dict[str, Any] = {
            "kind": "theorem",
            "name": theorem.name,
            "statement": theorem.statement.to_json(),
            "proof": derivation,
        }
        decl["hash"] = declaration_hash(decl)
        decl["axioms"] = sorted(_axioms_of(derivation, claimed_axioms))
        pending = TheoremResult(theorem.name, Status.UNPROVEN, (), None)
        return pending, decl

    def _bundle(self, declarations: list[dict[str, Any]]) -> dict[str, Any]:
        bundle: dict[str, Any] = {
            "format": "axwp",
            "format_version": 1,
            "spec_version": "0.1",
            "fragment": self._fragment,
            "kernel_version": _package_version(),
            "theory": self.name,
            "declarations": declarations,
        }
        bundle["bundle_hash"] = bundle_hash(bundle)
        return bundle


def _uses_equality(value: Any) -> bool:
    """True if a declaration JSON uses an L2 construct (language-spec §13.4)."""
    if isinstance(value, list):
        if value and value[0] == "eq":
            return True
        return any(_uses_equality(v) for v in value)
    if isinstance(value, dict):
        if value.get("rule") in ("eq_refl", "eq_e"):
            return True
        return any(_uses_equality(v) for v in value.values())
    return False


def _axioms_of(node: dict[str, Any], claimed: dict[str, frozenset[str]]) -> set[str]:
    """Axiom dependencies of a derivation (logic-spec §8.4); the kernel re-checks them."""
    if node["rule"] == "ax":
        return {node["name"]}
    if node["rule"] == "thm":
        return set(claimed.get(node["name"], ()))
    result: set[str] = set()
    for value in node.values():
        if isinstance(value, dict) and isinstance(value.get("rule"), str):
            result |= _axioms_of(value, claimed)
    return result


def _location(exc: BaseException, function: Callable[..., object]) -> str | None:
    filename = function.__code__.co_filename
    frames = [f for f in traceback.extract_tb(exc.__traceback__) if f.filename == filename]
    return f"{frames[-1].filename}:{frames[-1].lineno}" if frames else None


def _package_version() -> str:
    try:
        return metadata.version("axiomweave")
    except metadata.PackageNotFoundError:
        return "unknown"
