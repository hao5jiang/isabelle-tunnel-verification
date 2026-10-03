"""Check that the executable test harness rejects isolated faulty SML copies.

The actual Isabelle export is read-only here. Temporary generated copies test
numeric fault detection, compilation failure, and the distinction between
behavioral agreement and byte-for-byte provenance.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
CORE = HERE / "generated" / "EpochCodec.ML"
TESTER = HERE / "check_generated_codec.py"
VALUE_FACTOR = (
    "(times_nata (nat_of_integer (256 : IntInf.int)) (epoch_value bs))"
)


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def run_tester(core: Path, timeout: float,
               polyml: Path | None) -> subprocess.CompletedProcess[str]:
    command = [sys.executable, str(TESTER), "--smoke", "--core", str(core),
               "--timeout", str(timeout)]
    if polyml is not None:
        command.extend(("--polyml", str(polyml.resolve())))
    return subprocess.run(
        command,
        cwd=HERE, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="strict",
        shell=False, check=False, timeout=timeout + 15.0,
    )


def require(condition: bool, message: str,
            result: subprocess.CompletedProcess[str] | None = None) -> None:
    if not condition:
        details = ""
        if result is not None:
            details = (f"; exit={result.returncode}, "
                       f"stdout={result.stdout[:1500]!r}, "
                       f"stderr={result.stderr[:1500]!r}")
        raise RuntimeError(message + details)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--polyml", type=Path,
                        help="Poly/ML executable; when omitted use the tester default")
    args = parser.parse_args()
    if args.timeout <= 0:
        raise ValueError("Timeout must be positive")
    original = CORE.read_bytes()
    original_hash = digest(original)
    source = original.decode("utf-8")
    require(source.count(VALUE_FACTOR) == 1,
            "Numeric mutation target must occur exactly once")
    try:
        with tempfile.TemporaryDirectory(prefix="epoch-codegen-controls-") as work:
            temporary = Path(work)

            # Change just the radix used while reading a multi-byte value.
            numeric = temporary / "EpochCodec_wrong_radix.ML"
            numeric.write_text(
                source.replace(VALUE_FACTOR, VALUE_FACTOR.replace("256", "255"), 1),
                encoding="utf-8",
            )
            numeric_result = run_tester(numeric, args.timeout, args.polyml)
            require(numeric_result.returncode == 1,
                    "Numeric fault did not fail the tester", numeric_result)
            require("FAIL: Request " in numeric_result.stderr
                    and "expected 'V 256', received 'V 255'" in numeric_result.stderr,
                    "Numeric control failed for a reason other than the expected value mismatch",
                    numeric_result)
            print("PASS: radix mutation rejected for V 256 versus V 255 (not a compile failure)")

            # A compile error must be reported before the service banner.
            syntax = temporary / "EpochCodec_invalid_syntax.ML"
            syntax.write_text(source + "\nval = ;\n", encoding="utf-8")
            syntax_result = run_tester(syntax, args.timeout, args.polyml)
            require(syntax_result.returncode != 0,
                    "Invalid SML was accepted or a different core was loaded", syntax_result)
            diagnostic = syntax_result.stdout + syntax_result.stderr
            require("error:" in diagnostic.lower()
                    and "EpochCodec_invalid_syntax.ML" in diagnostic
                    and "SMOKE:" not in diagnostic,
                    "Syntax control did not identify a compilation error in the supplied core",
                    syntax_result)
            print("PASS: invalid SML rejected with a compiler diagnostic from the supplied copy")

            # A harmless comment changes provenance without changing behavior.
            annotated = temporary / "EpochCodec_comment_only.ML"
            annotated.write_bytes(original + b"\n(* Isolated provenance control. *)\n")
            annotated_hash = digest(annotated.read_bytes())
            require(annotated_hash != original_hash,
                    "Comment-only copy unexpectedly equals the export")
            annotated_result = run_tester(annotated, args.timeout, args.polyml)
            require(annotated_result.returncode == 0
                    and "SMOKE:" in annotated_result.stdout
                    and annotated_hash in annotated_result.stdout,
                    "Comment-only copy did not pass the executable checks", annotated_result)
            print("PASS: comment-only copy passes behavior tests but has a different SHA256")
    finally:
        require(digest(CORE.read_bytes()) == original_hash,
                "The original Isabelle export changed during negative controls")
    print(f"PASS: original export unchanged, SHA256 {original_hash}")
    print("Scope: harness fault detection and provenance controls, not a proof of the test harness")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
