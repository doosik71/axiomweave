"""`axw` command-line interface (language-spec §8, kernel-spec §11.2).

`axw check FILE.py` runs the user's proof code; `axw verify FILE.axwp` runs only
the kernel on a certificate and never imports user code.
"""

import argparse
import importlib.util
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
    verify.add_argument(
        "--allow",
        action="append",
        default=[],
        metavar="NAME=HASH",
        help="additionally allow an axiom with this declaration hash",
    )
    args = parser.parse_args(argv)

    if args.command == "check":
        return _check(args.file)
    return _verify(args.file, args.allow)


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


def _verify(path: Path, allow: list[str]) -> int:
    from axiomweave.kernel import STANDARD_AXIOMS, check_bundle

    policy = dict(STANDARD_AXIOMS)
    for item in allow:
        name, sep, value = item.partition("=")
        if not sep:
            print(f"--allow expects NAME=HASH, got {item!r}", file=sys.stderr)
            return 2
        policy[name] = value

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


if __name__ == "__main__":
    sys.exit(main())
