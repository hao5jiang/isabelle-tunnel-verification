"""Exercise the real frame harness against isolated faulty SML copies.

The Isabelle export is never rewritten. A wrong decoding radix must fail
against the standard-library oracle, a syntax error must prevent execution,
and a comment-only copy must pass behavior checks while changing file identity.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
CORE = HERE / "generated" / "FrameCodec.ML"
TESTER = HERE / "check_generated_frame.py"
VALUE_FACTOR = "(times_nata (nat_of_integer (256 : IntInf.int)) (epoch_value bs))"


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
    require(source.count(VALUE_FACTOR) == 1,
            "The exact decoding-radix mutation target must occur once")
    try:
        with tempfile.TemporaryDirectory(prefix="frame-codegen-controls-") as work:
            temporary = Path(work)

            # Alter the decoded epoch, leaving encoding and the startup probes
            # intact. The two-byte oracle then distinguishes 256 from 255.
            numeric = temporary / "FrameCodec_wrong_radix.ML"
            numeric.write_text(
                source.replace(VALUE_FACTOR, VALUE_FACTOR.replace("256", "255"), 1),
                encoding="utf-8",
            )
            numeric_result = run_tester(numeric, args.timeout, args.polyml)
            require(numeric_result.returncode == 1,
                    "The numeric fault did not fail the tester", numeric_result)
            require("FAIL: Request " in numeric_result.stderr
                    and "(two-byte full domain)" in numeric_result.stderr
                    and "expected 'P 1 0 256', received 'P 1 0 255'" in numeric_result.stderr,
                    "The numeric control did not reach the expected independent-oracle mismatch",
                    numeric_result)
            print("PASS: real SML radix fault rejected by the two-byte oracle: P 1 0 256 versus P 1 0 255")

            # Failure must identify the supplied copy, not a different export.
            syntax = temporary / "FrameCodec_invalid_syntax.ML"
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

            # Behavioral agreement alone cannot establish byte-level identity.
            annotated = temporary / "FrameCodec_comment_only.ML"
            annotated.write_bytes(original + b"\n(* Isolated frame provenance control. *)\n")
            annotated_hash = digest(annotated.read_bytes())
            require(annotated_hash != original_hash,
                    "The comment-only copy unexpectedly has the original SHA256")
            annotated_result = run_tester(annotated, args.timeout, args.polyml)
            require(annotated_result.returncode == 0
                    and "SMOKE:" in annotated_result.stdout
                    and f"SHA256 {annotated.resolve()}: {annotated_hash}" in annotated_result.stdout,
                    "The comment-only copy did not pass real executable checks with its own hash",
                    annotated_result)
            first_line = annotated_result.stdout.splitlines()[0]
            print(f"PASS: comment-only copy passed behavior checks with a different SHA256; {first_line}")
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
