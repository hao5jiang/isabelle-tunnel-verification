"""Exercise the Isabelle-exported SML codec in a real Poly/ML process.

The expected answers use Python's standard-library byte conversions, not the
earlier Python protocol model. Passing these tests is executable evidence;
it does not certify Poly/ML, the handwritten text interface, or machine code.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import os
import shutil
from pathlib import Path
from queue import Empty, Queue
from random import Random
import subprocess
import sys
from threading import Thread
import time


HERE = Path(__file__).resolve().parent
DEFAULT_POLYML = Path(os.environ.get("POLYML", shutil.which("poly") or "poly"))
DEFAULT_CORE = HERE / "generated" / "EpochCodec.ML"
DEFAULT_WRAPPER = HERE / "generated_codec_cli.ML"
BANNER = "ISABELLE_EPOCH_CODEC_V1"


@dataclass(frozen=True, slots=True)
class Case:
    request: str
    expected: str
    group: str


def bytes_reply(payload: bytes | None) -> str:
    if payload is None:
        return "N"
    return "B" + (" " + " ".join(map(str, payload)) if payload else "")


def reference_encode(width: int, cap: int, value: int) -> str:
    if cap >= 1 << (8 * width) or value > cap:
        return "N"
    return bytes_reply(value.to_bytes(width, byteorder="little", signed=False))


def reference_value(width: int, cap: int, payload: tuple[int, ...]) -> int | None:
    if (cap >= 1 << (8 * width) or len(payload) != width
            or any(digit >= 256 for digit in payload)):
        return None
    value = int.from_bytes(bytes(payload), byteorder="little", signed=False)
    return value if value <= cap else None


def encode_case(width: int, cap: int, value: int, group: str) -> Case:
    return Case(f"E {width} {cap} {value}",
                reference_encode(width, cap, value), group)


def payload_case(operation: str, width: int, cap: int,
                 payload: tuple[int, ...], group: str) -> Case:
    suffix = " " + " ".join(map(str, payload)) if payload else ""
    request = f"{operation} {width} {cap}{suffix}"
    value = reference_value(width, cap, payload)
    if operation == "D":
        expected = "N" if value is None else f"V {value}"
    elif operation == "S":
        expected = ("N" if value is None or value == cap else
                    bytes_reply((value + 1).to_bytes(width, "little")))
    else:
        raise ValueError(f"Unsupported operation: {operation}")
    return Case(request, expected, group)


def add_triplet(cases: list[Case], width: int, cap: int, value: int,
                group: str) -> None:
    payload = tuple(value.to_bytes(width, "little"))
    cases.append(encode_case(width, cap, value, group))
    cases.append(payload_case("D", width, cap, payload, group))
    cases.append(payload_case("S", width, cap, payload, group))


def exhaustive_cases(cases: list[Case], smoke: bool) -> None:
    caps = (0, 1, 127, 255) if smoke else range(256)
    values = (0, 1, 127, 128, 254, 255) if smoke else range(256)
    for cap in caps:
        for value in values:
            add_triplet(cases, 1, cap, value, "one-byte exhaustive")
    values = ((0, 1, 255, 256, 32767, 32768, 65534, 65535)
              if smoke else range(65536))
    for value in values:
        add_triplet(cases, 2, 65535, value, "two-byte full domain")


def boundary_cases(cases: list[Case], smoke: bool) -> None:
    rng = Random(20261003)
    for width in (0, 1, 2, 4, 8, 16, 64):
        capacity = 1 << (8 * width)
        caps = {0, 1, 255, 256, 257, capacity // 2, capacity - 2, capacity - 1}
        for cap in sorted(c for c in caps if 0 <= c < capacity):
            candidates = {0, cap, capacity - 1}
            candidates.update(v for v in (1, 255, 256, 257, cap - 1, cap + 1)
                              if 0 <= v < capacity)
            candidates.update(rng.randrange(capacity)
                              for _ in range(3 if smoke else 80))
            for value in sorted(candidates):
                add_triplet(cases, width, cap, value, "boundaries and seeded")
            for value in (cap + 1, capacity, capacity + 1):
                cases.append(encode_case(width, cap, value, "rejected range"))
            zero = (0,) * width
            malformed = {zero + (0,), zero + (255,)}
            if width:
                malformed.update((zero[:-1], (256,) + zero[1:],
                                  (257,) + zero[1:], (65536,) + zero[1:]))
            else:
                malformed.update(((0,), (256,), (257,)))
            for payload in sorted(malformed):
                for op in ("D", "S"):
                    cases.append(payload_case(op, width, cap, payload,
                                              "rejected payload"))
        for invalid_cap in (capacity, capacity + 1):
            cases.append(encode_case(width, invalid_cap, 0,
                                     "rejected configuration"))
            for op in ("D", "S"):
                cases.append(payload_case(op, width, invalid_cap, (0,) * width,
                                          "rejected configuration"))


def interface_cases(cases: list[Case]) -> None:
    malformed = (
        "", " ", "unknown", "V extra", "E", "D", "S", "E 1", "D 1",
        "S 1", "E 1 255", "E 1 255 0 1", "E -1 0 0", "E 1 -1 0",
        "E 1 255 -1", "D -1 0", "D 1 -1 0", "D 1 255 -1",
        "S -1 0", "S 1 -1 0", "S 1 255 -1", "E one 255 0",
        "E 1 cap 0", "E 1 255 value", "D 1 255 byte", "S 1 255 byte",
        "E 1.0 255 0", "E 1 255 0.0", "D 1 255 0x00", "S 1 255 1e0",
        "E +1 255 0", "E 1 255 +0", "D 1 255 +0", "S 1 255 +0",
        "E 1 255 ~0", "D 1 255 42junk", "E 1 255 \u0660", "D 1 255 \uff10",
    )
    for request in malformed:
        cases.append(Case(request, "X", "invalid text"))
        # Each invalid request is followed by a valid one in the same process.
        cases.append(Case("V", BANNER, "post-error recovery"))
    cases.extend((
        Case("E 0 0 0", "B", "zero-width interface"),
        Case("D 0 0", "V 0", "zero-width interface"),
        Case("S 0 0", "N", "zero-width interface"),
        Case("  E\t1  255\t42  ", "B 42", "whitespace interface"),
        Case("D 1 255 00042", "V 42", "decimal interface"),
    ))


def policy_cases(cases: list[Case]) -> None:
    invalid = (
        "E 65 0 0", "D 65 0", "S 65 0",
        "E 1 255 " + "0" * 161,
        "E " + "9" * 160 + " 0 0",
        "D 64 0 " + " ".join(["0"] * 130),
        "V" + " " * 16384,
    )
    for request in invalid:
        cases.append(Case(request, "X", "interface resource policy"))
        cases.append(Case("V", BANNER, "policy recovery"))
    cases.extend((
        Case("E 1 255 " + "0" * 160, "B 0", "policy accepted boundary"),
        Case("E 1 " + "9" * 160 + " 0", "N", "policy accepted boundary"),
        Case("D 64 0 " + " ".join(["0"] * 129), "N", "policy accepted boundary"),
        Case("V" + " " * 16383, BANNER, "policy accepted boundary"),
    ))
    for operation in ("D", "S"):
        cases.append(payload_case(operation, 64, 0, (0,) * 65,
                                  "overlong bytes reach codec"))


def make_cases(smoke: bool) -> list[Case]:
    cases = [Case("V", BANNER, "banner")]
    interface_cases(cases)
    policy_cases(cases)
    exhaustive_cases(cases, smoke)
    boundary_cases(cases, smoke)
    cases.append(Case("V", BANNER, "final liveness"))
    return cases


def sha256(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def check_answers(cases: list[Case], stdout: str) -> None:
    lines = stdout.splitlines()
    if len(lines) != len(cases):
        preview = "\n".join(lines[:8])
        raise RuntimeError(
            f"Expected {len(cases):,} output lines; received {len(lines):,}. "
            f"First output lines: {preview!r}"
        )
    for number, (case, actual) in enumerate(zip(cases, lines), 1):
        if actual != case.expected:
            raise RuntimeError(
                f"Request {number:,} ({case.group}) failed: {case.request!r}; "
                f"expected {case.expected!r}, received {actual!r}"
            )


def checker_negative_controls() -> None:
    """Ensure the answer checker fails on wrong values and broken framing."""
    sample = [Case("E 1 255 42", "B 42", "checker control")]
    check_answers(sample, "B 42\n")
    for wrong in ("B 41\n", "N\n", "B 42 \n", "", "B 42\nB 42\n"):
        try:
            check_answers(sample, wrong)
        except RuntimeError:
            continue
        raise RuntimeError(f"Checker accepted its negative control: {wrong!r}")


def interactive_probe(polyml: Path, wrapper: Path,
                      environment: dict[str, str], timeout: float) -> None:
    """Require replies while stdin remains open, with bounded pipe reads."""
    process = subprocess.Popen(
        [str(polyml), "-q", "--error-exit", "--script", str(wrapper)],
        cwd=HERE, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="strict",
        shell=False, env=environment, bufsize=1,
    )
    replies: Queue[tuple[str, str]] = Queue()
    errors: list[str] = []

    def read_replies() -> None:
        try:
            for line in process.stdout:
                replies.put(("line", line))
        except (OSError, UnicodeError, ValueError) as error:
            replies.put(("error", repr(error)))
        finally:
            replies.put(("eof", ""))

    def read_errors() -> None:
        try:
            errors.append(process.stderr.read())
        except (OSError, UnicodeError, ValueError) as error:
            errors.append(f"stderr reader failed: {error!r}")

    output_reader = Thread(target=read_replies, daemon=True)
    error_reader = Thread(target=read_errors, daemon=True)
    output_reader.start()
    error_reader.start()
    try:
        for command, expected in (("V", BANNER), ("E 2 65535 513", "B 1 2")):
            process.stdin.write(command + "\n")
            process.stdin.flush()
            try:
                kind, reply = replies.get(timeout=timeout)
            except Empty as error:
                raise RuntimeError(
                    f"Interactive probe timed out after {timeout:g}s on {command!r}; "
                    "stdin was still open"
                ) from error
            if kind != "line" or reply != expected + "\n":
                raise RuntimeError(
                    f"Interactive probe {command!r}: expected {expected!r}; "
                    f"received {kind} {reply!r}"
                )
        process.stdin.close()
        try:
            result = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired as error:
            raise RuntimeError("Interactive probe did not exit after stdin closed") from error
        output_reader.join(timeout=timeout)
        error_reader.join(timeout=timeout)
        if output_reader.is_alive() or error_reader.is_alive():
            raise RuntimeError("Interactive probe output readers did not finish")
        if result != 0 or "".join(errors):
            raise RuntimeError(
                f"Interactive probe exited {result}; stderr={''.join(errors)!r}"
            )
        leftovers = []
        while not replies.empty():
            leftovers.append(replies.get_nowait())
        if leftovers != [("eof", "")]:
            raise RuntimeError(f"Interactive probe produced extra output: {leftovers!r}")
    finally:
        if process.poll() is None:
            process.kill()
        process.wait(timeout=timeout)
        output_reader.join(timeout=timeout)
        error_reader.join(timeout=timeout)
        for handle in (process.stdin, process.stdout, process.stderr):
            if handle is not None and not handle.closed:
                handle.close()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--polyml", type=Path, default=DEFAULT_POLYML)
    parser.add_argument("--wrapper", type=Path, default=DEFAULT_WRAPPER,
                        help="SML text interface; overrides enable isolated negative controls")
    parser.add_argument("--core", type=Path, default=DEFAULT_CORE,
                        help="Generated SML core, also supplied to the interface by environment")
    parser.add_argument("--smoke", action="store_true",
                        help="Run representative subsets instead of the two exhaustive domains")
    parser.add_argument("--timeout", type=float, default=180.0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.timeout <= 0:
        raise ValueError("Timeout must be positive")
    polyml = args.polyml.resolve()
    wrapper = args.wrapper.resolve()
    core = args.core.resolve()
    for path in (polyml, core, wrapper):
        if not path.is_file():
            raise FileNotFoundError(f"Required file is missing: {path}")
    hashes = {path: sha256(path) for path in (polyml, core, wrapper)}
    checker_negative_controls()
    cases = make_cases(args.smoke)
    # The final banner has no newline: exercise EOF after a complete command,
    # as well as newline-terminated requests and drained oversized lines.
    batch = "\n".join(case.request for case in cases)
    environment = os.environ.copy()
    environment["EPOCH_CODEC_CORE"] = str(core)
    interactive_probe(polyml, wrapper, environment, min(5.0, args.timeout))
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            [str(polyml), "-q", "--error-exit", "--script", str(wrapper)], cwd=HERE,
            input=batch, text=True, encoding="utf-8", errors="strict",
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=args.timeout, check=False, shell=False, env=environment,
        )
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"Poly/ML did not finish within {args.timeout:g}s") from error
    elapsed = time.perf_counter() - started
    if completed.returncode != 0:
        raise RuntimeError(
            f"Poly/ML exited with code {completed.returncode}; "
            f"stdout={completed.stdout[:3000]!r}; stderr={completed.stderr[:3000]!r}"
        )
    if completed.stderr:
        raise RuntimeError(f"Poly/ML wrote unexpected stderr: {completed.stderr[:3000]!r}")
    check_answers(cases, completed.stdout)
    for path, expected_hash in hashes.items():
        if sha256(path) != expected_hash:
            raise RuntimeError(f"Executable input changed during testing: {path}")
    mode = "SMOKE" if args.smoke else "FULL"
    print(f"{mode}: {len(cases):,} requests passed against real exported SML in {elapsed:.2f}s")
    print("  interactive pipe probe: 2 timely replies before closing stdin; clean exit")
    for group, count in Counter(case.group for case in cases).items():
        print(f"  {group}: {count:,}")
    print("  checker negative controls: 5 rejected")
    for path, digest in hashes.items():
        print(f"SHA256 {path}: {digest}")
    print("Scope: generated codec execution plus text-interface tests; not compiler certification")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
