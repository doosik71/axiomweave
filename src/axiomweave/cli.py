"""`axw` command-line interface (language-spec §8, kernel-spec §11.2, interop-spec §3.7).

`axw check FILE.py` runs the user's proof code; `axw verify FILE.axwp` runs only
the kernel on a certificate and never imports user code; `axw export-lean`
translates a kernel-accepted certificate to Lean 4 for cross-checking.
"""

import argparse
import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path
from types import ModuleType


def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            reconfigure(errors="backslashreplace")

    parser = argparse.ArgumentParser(prog="axw", description="AxiomWeave proof checker")
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("check", help="elaborate and verify the theories in a Python file")
    check.add_argument("file", type=Path)
    verify = commands.add_parser("verify", help="verify a certificate bundle with the kernel")
    verify.add_argument("file", type=Path)
    export = commands.add_parser(
        "export-lean", help="translate a kernel-accepted certificate to a Lean 4 file"
    )
    export.add_argument("file", type=Path)
    export.add_argument("-o", "--output", type=Path, required=True, help="Lean file to write")
    export.add_argument("--check", action="store_true", help="also check the file with `lean`")
    for sub in (verify, export):
        sub.add_argument(
            "--allow",
            action="append",
            default=[],
            metavar="NAME=HASH",
            help="additionally allow an axiom with this declaration hash",
        )
    args = parser.parse_args(argv)

    if args.command == "check":
        return _check(args.file)
    policy = _policy(args.allow)
    if policy is None:
        return 2
    if args.command == "verify":
        return _verify(args.file, policy)
    return _export_lean(args.file, args.output, policy, args.check)


def _load_module(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(f"axw_user_{path.stem}", path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(path.resolve().parent))
    spec.loader.exec_module(module)
    return module


def _check(path: Path) -> int:
    from axiomweave.language.theory import Theory

    module = _load_module(path)
    theories = [v for v in vars(module).values() if isinstance(v, Theory)]
    imported = {id(t) for theory in theories for t in _imports_closure(theory)}
    roots = [t for t in theories if id(t) not in imported]
    if not roots:
        print(f"{path}: no Theory objects found", file=sys.stderr)
        return 1
    ok = True
    for theory in roots:
        report = theory.check()
        print(report)
        ok = ok and report.ok
    return 0 if ok else 1


def _imports_closure(theory: object) -> list[object]:
    from axiomweave.language.theory import Theory

    assert isinstance(theory, Theory)
    result: list[object] = []
    pending = list(theory.imports)
    while pending:
        current = pending.pop()
        result.append(current)
        pending.extend(current.imports)
    return result


def _policy(allow: list[str]) -> dict[str, str] | None:
    """The standard allow list plus `--allow` entries (None on a usage error)."""
    from axiomweave.kernel import STANDARD_AXIOMS

    policy = dict(STANDARD_AXIOMS)
    for item in allow:
        name, sep, value = item.partition("=")
        if not sep:
            print(f"--allow expects NAME=HASH, got {item!r}", file=sys.stderr)
            return None
        policy[name] = value
    return policy


def _verify(path: Path, policy: dict[str, str]) -> int:
    from axiomweave.kernel import check_bundle

    report = check_bundle(path.read_bytes(), policy)
    if not report.bundle_ok:
        assert report.bundle_error is not None
        error = report.bundle_error
        print(f"REJECTED bundle: {error.code} at {error.path}: {error.message}")
        return 1
    for r in report.results:
        print(f"{r.status:<9} {r.name}")
        if r.error is not None:
            print(f"    {r.error.code} at {r.error.path}: {r.error.message}")
    print("ok" if report.ok else "FAILED")
    return 0 if report.ok else 1


def _export_lean(path: Path, output: Path, policy: dict[str, str], check: bool) -> int:
    from axiomweave.backends.lean import ExportError, export_lean

    try:
        result = export_lean(path.read_bytes(), policy)
    except ExportError as exc:
        print(f"REJECTED bundle: {exc}")
        return 1
    output.write_text(result.text, encoding="utf-8", newline="\n")
    for name in result.skipped:
        print(f"skipped   {name} (rejected by the kernel)")
    print(f"exported  {len(result.exported)} declarations to {output}")
    if not result.report.ok:
        print("FAILED")
        return 1
    if not check:
        return 0

    lean = shutil.which("lean")
    if lean is None:
        print("lean      skipped (`lean` not found)")
        return 3
    version = subprocess.run(
        [lean, "--version"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    print(f"lean      {version.stdout.strip()}")
    checked = subprocess.run(
        [lean, str(output)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if checked.returncode != 0:
        print(checked.stdout + checked.stderr, end="")
        print("lean      FAILED")
        return 1
    print("lean      ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
