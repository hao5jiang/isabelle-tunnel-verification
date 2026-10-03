"""Test the Isabelle-exported full frame codec in a real Poly/ML process.

Expected frames use struct and standard-library integer/byte conversions.
Neither the handwritten Python protocol model nor a codec round trip is the
oracle. This verifies executable behavior, not the compiler or machine code.
"""
from __future__ import annotations

import argparse
from collections import Counter
import os
from pathlib import Path
from queue import Empty, Queue
from random import Random
import struct
import subprocess
import sys
from threading import Thread
import time

from check_generated_codec import Case, DEFAULT_POLYML, check_answers, sha256


HERE = Path(__file__).resolve().parent
DEFAULT_CORE = HERE / "generated" / "FrameCodec.ML"
DEFAULT_WRAPPER = HERE / "generated_frame_cli.ML"
BANNER = "ISABELLE_TUNNEL_FRAME_V1"


def frame_bytes(width: int, tag: int, device: int, epoch: int) -> bytes:
    return struct.pack("6B", 84, 75, 1, tag, device, width) + epoch.to_bytes(width, "little")


def reference_encode(width: int, limit: int, tag: int, device: int, epoch: int) -> bytes | None:
    if (not 1 <= width <= 255 or not 0 <= limit < 256 ** width
            or tag not in (1, 2, 3) or device not in (0, 1)
            or not 0 <= epoch <= limit):
        return None
    return frame_bytes(width, tag, device, epoch)


def reference_decode(width: int, limit: int, payload: tuple[int, ...]) -> tuple[int, int, int] | None:
    if (not 1 <= width <= 255 or not 0 <= limit < 256 ** width
            or len(payload) != width + 6 or any(not 0 <= b < 256 for b in payload)):
        return None
    data = bytes(payload)
    first, second, version, tag, device, declared = struct.unpack("6B", data[:6])
    if ((first, second, version) != (84, 75, 1) or tag not in (1, 2, 3)
            or device not in (0, 1) or declared != width):
        return None
    epoch = int.from_bytes(data[6:], "little", signed=False)
    return (tag, device, epoch) if epoch <= limit else None


def bytes_reply(payload: bytes | None) -> str:
    return "N" if payload is None else "B " + " ".join(map(str, payload))


def encode_case(width: int, limit: int, tag: int, device: int, epoch: int, group: str) -> Case:
    return Case(f"E {width} {limit} {tag} {device} {epoch}",
                bytes_reply(reference_encode(width, limit, tag, device, epoch)), group)


def decode_case(width: int, limit: int, payload: tuple[int, ...], group: str) -> Case:
    suffix = " " + " ".join(map(str, payload)) if payload else ""
    message = reference_decode(width, limit, payload)
    expected = "N" if message is None else "P " + " ".join(map(str, message))
    return Case(f"D {width} {limit}{suffix}", expected, group)


def add_pair(cases: list[Case], width: int, limit: int, tag: int,
             device: int, epoch: int, group: str) -> None:
    cases.append(encode_case(width, limit, tag, device, epoch, group))
    cases.append(decode_case(width, limit, tuple(frame_bytes(width, tag, device, epoch)), group))


def exhaustive_cases(cases: list[Case], smoke: bool) -> None:
    values = (0, 1, 126, 127, 128, 254, 255) if smoke else range(256)
    for limit in (0, 1, 127, 255):
        for tag in (1, 2, 3):
            for device in (0, 1):
                for epoch in values:
                    add_pair(cases, 1, limit, tag, device, epoch, "one-byte selected caps exhaustive")
    values = ((0, 1, 255, 256, 257, 32767, 32768, 65534, 65535)
              if smoke else range(65536))
    for epoch in values:
        add_pair(cases, 2, 65535, 1, 0, epoch, "two-byte full domain")


def header_cases(cases: list[Case]) -> None:
    base = list(frame_bytes(2, 2, 1, 777))
    for index in range(6):
        for value in range(256):
            mutated = base.copy()
            mutated[index] = value
            cases.append(decode_case(2, 1000, tuple(mutated), "complete header-byte mutation"))
    for index in range(len(base)):
        for value in (256, 257, 65536):
            mutated = base.copy()
            mutated[index] = value
            cases.append(decode_case(2, 1000, tuple(mutated), "nonbyte rejection"))
    malformed = [tuple(base[:size]) for size in range(len(base))]
    malformed += [tuple(base + [0]), tuple(base + base), tuple([0] + base), tuple(base[1:]),
                  tuple(base[:5] + [1] + base[6:7]), tuple(base[:5] + [3] + base[6:] + [0])]
    for data in malformed:
        cases.append(decode_case(2, 1000, data, "length and datagram boundaries"))
    # A clear-ACK generation operation has no wire tag.
    for tag in (0, 4, 255, 256, 65536):
        cases.append(encode_case(1, 255, tag, 0, 1, "invalid kind identity"))
    for device in (2, 255, 256, 65536):
        cases.append(encode_case(1, 255, 1, device, 1, "invalid kind identity"))


def boundary_cases(cases: list[Case], smoke: bool) -> None:
    rng = Random(20261003)
    for width in (0, 1, 2, 3, 4, 8, 16, 64):
        capacity = 256 ** width
        limits = {0, 1, 255, 256, capacity // 2, capacity - 2, capacity - 1}
        for limit in sorted(value for value in limits if 0 <= value < capacity):
            candidates = {0, limit, capacity - 1}
            candidates.update(value for value in (1, 255, 256, 257, limit - 1, limit + 1)
                              if 0 <= value < capacity)
            candidates.update(rng.randrange(capacity) for _ in range(2 if smoke else 20))
            for epoch in sorted(candidates):
                for tag in (1, 2, 3):
                    for device in (0, 1):
                        add_pair(cases, width, limit, tag, device, epoch, "width boundaries and seeded")
            for epoch in (limit + 1, capacity, capacity + 1):
                cases.append(encode_case(width, limit, 1, 0, epoch, "epoch range rejection"))
            zero = tuple(frame_bytes(width, 1, 0, 0))
            for malformed in (zero[:-1], zero + (0,), zero + (255,), zero + zero):
                # The 64-byte concatenation exceeds the wrapper's token policy;
                # test that policy separately instead of expecting a core reply.
                if len(malformed) <= 129:
                    cases.append(decode_case(width, limit, malformed, "payload length rejection"))
        for limit in (capacity, capacity + 1):
            cases.append(encode_case(width, limit, 1, 0, 0, "configuration rejection"))
            cases.append(decode_case(width, limit, tuple(frame_bytes(width, 1, 0, 0)),
                                     "configuration rejection"))


def interface_cases(cases: list[Case]) -> None:
    malformed = ["", " ", "unknown", "V extra", "E", "D", "S", "E 1", "D 1",
                 "E 1 255", "E 1 255 1", "E 1 255 1 0", "E 1 255 1 0 0 0",
                 "S 1 255 84 75 1 1 0 1 0"]
    valid_tokens = ["E", "1", "255", "1", "0", "42"]
    for index in range(1, len(valid_tokens)):
        for bad in ("-1", "+1", "~1", "1.0", "1e0", "0x1", "one", "42junk", "\u0660", "\uff10"):
            tokens = valid_tokens.copy()
            tokens[index] = bad
            malformed.append(" ".join(tokens))
    for bad in ("-1", "+1", "~1", "1.0", "1e0", "0x1", "one", "42junk", "\u0660", "\uff10"):
        malformed.append("D 1 255 84 75 1 1 0 1 " + bad)
    for request in malformed:
        cases.append(Case(request, "X", "invalid ASCII decimal or command"))
        cases.append(Case("V", BANNER, "post-error recovery"))
    cases.extend((
        Case("E 0 0 1 0 0", "N", "zero-width core rejection"),
        Case("D 0 0", "N", "zero-width core rejection"),
        Case("D 0 0 84 75 1 1 0 0", "N", "zero-width core rejection"),
        Case("  E\t1  255\t1  0  42  ", "B 84 75 1 1 0 1 42", "whitespace interface"),
        Case("D 01 00255 084 075 01 01 00 01 00042", "P 1 0 42", "leading-zero decimal interface"),
    ))


def policy_cases(cases: list[Case]) -> None:
    invalid = ["E 65 0 1 0 0", "D 65 0", "E 255 0 1 0 0", "D 255 0",
               "E 1 255 1 0 " + "0" * 161,
               "E " + "9" * 160 + " 0 1 0 0",
               "D 64 0 " + " ".join(["0"] * 130),
               "V" + " " * 16384]
    for request in invalid:
        cases.append(Case(request, "X", "interface resource policy"))
        cases.append(Case("V", BANNER, "policy recovery"))
    cases.extend((
        Case("E 1 255 1 0 " + "0" * 160, "B 84 75 1 1 0 1 0", "policy accepted boundary"),
        Case("E 1 " + "9" * 160 + " 1 0 0", "N", "policy accepted boundary"),
        Case("D 64 0 " + " ".join(["0"] * 129), "N", "policy accepted boundary"),
        Case("V" + " " * 16383, BANNER, "policy accepted boundary"),
    ))


def make_cases(smoke: bool) -> list[Case]:
    cases = [Case("V", BANNER, "banner")]
    interface_cases(cases)
    policy_cases(cases)
    exhaustive_cases(cases, smoke)
    header_cases(cases)
    boundary_cases(cases, smoke)
    cases.append(Case("V", BANNER, "final EOF command"))
    return cases


def checker_negative_controls() -> None:
    sample = [Case("E 1 255 1 0 42", "B 84 75 1 1 0 1 42", "checker control")]
    check_answers(sample, "B 84 75 1 1 0 1 42\n")
    for wrong in ("B 84 75 1 1 0 1 41\n", "N\n", "B 84 75 1 1 0 1 42 \n", "", "B 84 75 1 1 0 1 42\nX\n"):
        try:
            check_answers(sample, wrong)
        except RuntimeError:
            continue
        raise RuntimeError(f"Checker accepted a negative control: {wrong!r}")


def interactive_probe(polyml: Path, wrapper: Path, environment: dict[str, str], timeout: float) -> None:
    """Demand two replies before closing stdin; reject diagnostics/extra lines."""
    process = subprocess.Popen(
        [str(polyml), "-q", "--error-exit", "--script", str(wrapper)],
        cwd=HERE, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, encoding="utf-8", errors="strict", shell=False, env=environment, bufsize=1)
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
            errors.append(repr(error))

    output_reader = Thread(target=read_replies, daemon=True)
    error_reader = Thread(target=read_errors, daemon=True)
    output_reader.start()
    error_reader.start()
    try:
        for command, expected in (("V", BANNER), ("E 2 65535 2 1 513", "B 84 75 1 2 1 2 1 2")):
            process.stdin.write(command + "\n")
            process.stdin.flush()
            try:
                kind, reply = replies.get(timeout=timeout)
            except Empty as error:
                raise RuntimeError(f"Interactive probe timed out on {command!r} while stdin remained open") from error
            if kind != "line" or reply != expected + "\n":
                raise RuntimeError(f"Interactive probe expected {expected!r}; received {kind} {reply!r}")
        process.stdin.close()
        result = process.wait(timeout=timeout)
        output_reader.join(timeout=timeout)
        error_reader.join(timeout=timeout)
        if output_reader.is_alive() or error_reader.is_alive():
            raise RuntimeError("Interactive probe output readers did not finish")
        if result != 0 or "".join(errors):
            raise RuntimeError(f"Interactive probe exited {result}; stderr={''.join(errors)!r}")
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
    parser.add_argument("--wrapper", type=Path, default=DEFAULT_WRAPPER)
    parser.add_argument("--core", type=Path, default=DEFAULT_CORE,
                        help="Supplied to the wrapper using FRAME_CODEC_CORE")
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--timeout", type=float, default=180.0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.timeout <= 0:
        raise ValueError("Timeout must be positive")
    polyml, wrapper, core = (value.resolve() for value in (args.polyml, args.wrapper, args.core))
    for path in (polyml, wrapper, core):
        if not path.is_file():
            raise FileNotFoundError(f"Required file is missing: {path}")
    hashes = {path: sha256(path) for path in (polyml, wrapper, core)}
    checker_negative_controls()
    cases = make_cases(args.smoke)
    # No newline after the final command checks EOF processing, independently
    # of the interactive test that deliberately leaves stdin open.
    batch = "\n".join(case.request for case in cases)
    environment = os.environ.copy()
    environment["FRAME_CODEC_CORE"] = str(core)
    interactive_probe(polyml, wrapper, environment, min(5.0, args.timeout))
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            [str(polyml), "-q", "--error-exit", "--script", str(wrapper)], cwd=HERE,
            input=batch, text=True, encoding="utf-8", errors="strict", stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=args.timeout, check=False, shell=False, env=environment)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"Poly/ML exceeded {args.timeout:g}s") from error
    elapsed = time.perf_counter() - started
    if completed.returncode != 0:
        raise RuntimeError(f"Poly/ML exited {completed.returncode}; stdout={completed.stdout[:3000]!r}; stderr={completed.stderr[:3000]!r}")
    if completed.stderr:
        raise RuntimeError(f"Unexpected Poly/ML stderr: {completed.stderr[:3000]!r}")
    check_answers(cases, completed.stdout)
    for path, expected in hashes.items():
        if sha256(path) != expected:
            raise RuntimeError(f"Executable input changed during tests: {path}")
    mode = "SMOKE" if args.smoke else "FULL"
    print(f"{mode}: {len(cases):,} full-frame requests passed against real exported SML in {elapsed:.2f}s")
    print("  interactive pipe probe: 2 replies before closing stdin; clean exit")
    for group, count in Counter(case.group for case in cases).items():
        print(f"  {group}: {count:,}")
    print("  checker negative controls: 5 rejected")
    for path, digest in hashes.items():
        print(f"SHA256 {path}: {digest}")
    print("Scope: complete datagram codec execution and text interface; not authentication, stream framing or compiler certification")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
