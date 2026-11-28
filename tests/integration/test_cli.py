"""`axw check` and `axw verify` in separate processes (language-spec §8, kernel-spec §11.2)."""

import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / "examples" / "logic" / "implication.py"
FIRST_ORDER = ROOT / "examples" / "logic" / "first_order.py"
EQUALITY = ROOT / "examples" / "logic" / "equality.py"
PEANO = ROOT / "src" / "axiomweave" / "lib" / "arithmetic" / "peano.py"


def axw(*args: str, cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    env = {**os.environ, "PYTHONIOENCODING": "utf-8"}
    return subprocess.run(
        [sys.executable, "-m", "axiomweave.cli", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        cwd=cwd,
        env=env,
        check=False,
    )


def test_check_readme_example() -> None:
    result = axw("check", str(EXAMPLE))
    assert result.returncode == 0, result.stdout + result.stderr
    assert "VERIFIED  examples.implication.imp_trans" in result.stdout


def test_check_fails_on_bad_proof(tmp_path: Path) -> None:
    source = tmp_path / "bad.py"
    source.write_text(
        "from axiomweave import Prop, Theory\n"
        "P = Prop.symbol('P')\n"
        "thy = Theory('demo.bad')\n"
        "@thy.theorem\n"
        "def t():\n"
        "    return P\n"
        "@thy.proof(t)\n"
        "def _(ctx):\n"
        "    ctx.intro()\n",
        encoding="utf-8",
    )
    result = axw("check", str(source))
    assert result.returncode == 1
    assert "REJECTED" in result.stdout


def export_example(tmp_path: Path, example: Path = EXAMPLE) -> Path:
    script = tmp_path / "export.py"
    target = tmp_path / f"{example.stem}.axwp"
    script.write_text(
        "import runpy, sys\n"
        f"module = runpy.run_path({str(example)!r})\n"
        "thy = module['thy']\n"
        "assert thy.check().ok\n"
        f"thy.export({str(target)!r})\n",
        encoding="utf-8",
    )
    subprocess.run([sys.executable, str(script)], check=True, cwd=ROOT)
    return target


def test_check_first_order_example() -> None:
    result = axw("check", str(FIRST_ORDER))
    assert result.returncode == 0, result.stdout + result.stderr
    assert "VERIFIED  examples.first_order.ex_not_all_not" in result.stdout


def test_verify_first_order_certificate(tmp_path: Path) -> None:
    certificate = export_example(tmp_path, FIRST_ORDER)
    result = axw("verify", str(certificate))
    assert result.returncode == 0, result.stdout + result.stderr
    assert "ACCEPTED  examples.first_order.U" in result.stdout


def test_check_and_verify_equality_example(tmp_path: Path) -> None:
    result = axw("check", str(EQUALITY))
    assert result.returncode == 0, result.stdout + result.stderr
    assert "VERIFIED  examples.equality.f_congr" in result.stdout
    verified = axw("verify", str(export_example(tmp_path, EQUALITY)))
    assert verified.returncode == 0, verified.stdout + verified.stderr


def test_check_arith_library_loaded_from_its_file() -> None:
    # The file is loaded as a fresh module, so `ctx.induction()` must find the
    # induction axiom in that module's theory, not in the installed package.
    result = axw("check", str(PEANO))
    assert result.returncode == 0, result.stdout + result.stderr
    assert "VERIFIED  arith.add_assoc" in result.stdout


def test_verify_exported_certificate(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    result = axw("verify", str(certificate))
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip().endswith("ok")


def test_verify_rejects_tampered_certificate(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    bundle = json.loads(certificate.read_text(encoding="utf-8"))
    bundle["declarations"][0]["statement"] = ["imp", ["atom", "Q"], ["atom", "Q"]]
    certificate.write_text(json.dumps(bundle), encoding="utf-8")
    result = axw("verify", str(certificate))
    assert result.returncode == 1
    assert "E_HASH_MISMATCH" in result.stdout


def test_verify_allow_option_format(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    assert axw("verify", str(certificate), "--allow", "no-equals-sign").returncode == 2


def test_export_lean_writes_file(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    output = tmp_path / "implication.lean"
    result = axw("export-lean", str(certificate), "-o", str(output))
    assert result.returncode == 0, result.stdout + result.stderr
    assert "exported  4 declarations" in result.stdout
    assert "theorem «examples».«implication».«imp_trans»" in output.read_text(encoding="utf-8")


def test_export_lean_exit_codes(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    output = tmp_path / "out.lean"
    assert axw("export-lean", str(certificate)).returncode == 2  # -o is required
    bad_allow = axw("export-lean", str(certificate), "-o", str(output), "--allow", "x")
    assert bad_allow.returncode == 2

    bundle = json.loads(certificate.read_text(encoding="utf-8"))
    bundle["bundle_hash"] = "sha256:" + "0" * 64
    tampered = tmp_path / "tampered.axwp"
    tampered.write_text(json.dumps(bundle), encoding="utf-8")
    rejected = axw("export-lean", str(tampered), "-o", str(output))
    assert rejected.returncode == 1
    assert "E_HASH_MISMATCH" in rejected.stdout
    assert not output.exists()


def test_export_lean_check_without_lean(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    output = tmp_path / "out.lean"
    env = {**os.environ, "PYTHONIOENCODING": "utf-8", "PATH": str(tmp_path)}
    result = subprocess.run(
        [sys.executable, "-m", "axiomweave.cli", "export-lean", str(certificate)]
        + ["-o", str(output), "--check"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        cwd=ROOT,
        env=env,
        check=False,
    )
    assert result.returncode == 3, result.stdout + result.stderr
    assert "lean      skipped" in result.stdout
    assert output.exists()
