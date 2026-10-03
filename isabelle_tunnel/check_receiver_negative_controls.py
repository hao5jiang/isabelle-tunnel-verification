"""Run the real receiver harness against isolated faulty SML copies.

The Isabelle export is never rewritten. Disabling only the target gate must
produce a wrong-port acceptance detected by the behavioral oracle. A syntax
error must prevent execution, while a comment-only copy must pass behavior
checks with a different byte-level identity.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
CORE = HERE / "generated" / "ReceiverGate.ML"
TESTER = HERE / "check_generated_receiver.py"
TARGET_GATE = "(if equal_receiver_port (packet_destination p) r then SOME p else NONE)"


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def require(condition: bool, message: str,
            result: subprocess.CompletedProcess[str] | None = None) -> None:
    if not condition:
        details = ""
        if result is not None:
            details = (f"; exit={result.returncode}, "
                       f"stdout={result.stdout[:1800]!r}, "
                       f"stderr={result.stderr[:1800]!r}")
        raise RuntimeError(message + details)


def run_tester(core: Path, timeout: float,
               polyml: Path | None) -> subprocess.CompletedProcess[str]:
    command = [sys.executable, str(TESTER), "--smoke", "--core", str(core),
               "--timeout", str(timeout)]
    if polyml is not None:
        command.extend(("--polyml", str(polyml.resolve())))
    return subprocess.run(
        command, cwd=HERE, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="strict",
        shell=False, check=False, timeout=timeout + 15.0,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--polyml", type=Path,
                        help="Poly/ML executable; otherwise use the tester default")
    args = parser.parse_args()
    if args.timeout <= 0:
        raise ValueError("Timeout must be positive")
    original = CORE.read_bytes()
    original_hash = digest(original)
    source = original.decode("utf-8")
    require(source.count(TARGET_GATE) == 1,
            "The exact receiver target-gate mutation must occur once")
    try:
        with tempfile.TemporaryDirectory(prefix="receiver-codegen-controls-") as work:
            temporary = Path(work)

            # Keep frame parsing and port decoding intact, but ignore whether
            # the successfully parsed packet belongs to the receiving port.
            unbound = temporary / "ReceiverGate_ignored_target.ML"
            unbound.write_text(source.replace(TARGET_GATE, "(SOME p)", 1),
                               encoding="utf-8")
            unbound_result = run_tester(unbound, args.timeout, args.polyml)
            require(unbound_result.returncode == 1,
                    "The ignored-target fault did not fail the tester", unbound_result)
            require("FAIL: Request " in unbound_result.stderr
                    and "(explicit accepted/wrong-port gate)" in unbound_result.stderr
                    and "'R 1 255 0 84 75 1 1 0 1 42'" in unbound_result.stderr
                    and "expected 'N', received 'P 1 0 42'" in unbound_result.stderr,
                    "The gate control did not reach the expected wrong-port acceptance mismatch",
                    unbound_result)
            print("PASS: real SML target-gate fault detected: controller port accepted A entry; N versus P 1 0 42")

            # A compilation failure must identify the supplied faulty copy,
            # rather than silently loading the unchanged project core.
            syntax = temporary / "ReceiverGate_invalid_syntax.ML"
            syntax.write_text(source + "\nval = ;\n", encoding="utf-8")
            syntax_result = run_tester(syntax, args.timeout, args.polyml)
            require(syntax_result.returncode != 0,
                    "The invalid SML copy was accepted", syntax_result)
            diagnostic = syntax_result.stdout + syntax_result.stderr
            require("error:" in diagnostic.lower()
                    and syntax.name in diagnostic
                    and "SMOKE:" not in diagnostic,
                    "The syntax control lacks a compiler diagnostic from the supplied copy",
                    syntax_result)
            print("PASS: supplied invalid SML copy failed with its own compiler diagnostic")

            # Behavioral equivalence cannot substitute for export provenance.
            annotated = temporary / "ReceiverGate_comment_only.ML"
            annotated.write_bytes(original + b"\n(* Isolated receiver provenance control. *)\n")
            annotated_hash = digest(annotated.read_bytes())
            require(annotated_hash != original_hash,
                    "The comment-only copy unexpectedly has the original SHA256")
            annotated_result = run_tester(annotated, args.timeout, args.polyml)
            require(annotated_result.returncode == 0
                    and "SMOKE:" in annotated_result.stdout
                    and f"SHA256 {annotated.resolve()}: {annotated_hash}" in annotated_result.stdout,
                    "The comment-only copy did not pass executable checks with its own hash",
                    annotated_result)
            print("PASS: comment-only copy passed behavior checks with a different SHA256; "
                  + annotated_result.stdout.splitlines()[0])
    finally:
        require(digest(CORE.read_bytes()) == original_hash,
                "The original Isabelle export changed during controls")
    print(f"PASS: original export unchanged, SHA256 {original_hash}")
    print("Scope: actual faulty-copy execution and provenance controls, not formal verification of the test harness")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
