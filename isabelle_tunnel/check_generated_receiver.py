"""Exercise the Isabelle-exported receiver gate in a real Poly/ML process.

The frame oracle uses struct and Python integer/byte conversion. Receive
roles are checked against an explicit independent table. Successful tests
establish executable behavior, not authentication or compiler certification.
"""
from __future__ import annotations

import argparse
from collections import Counter
import os
from pathlib import Path
from queue import Empty, Queue
import subprocess
import sys
from threading import Thread
import time

from check_generated_codec import Case, DEFAULT_POLYML, check_answers, sha256
import check_generated_frame as frames


HERE = Path(__file__).resolve().parent
DEFAULT_CORE = HERE / "generated" / "ReceiverGate.ML"
DEFAULT_WRAPPER = HERE / "generated_receiver_cli.ML"
BANNER = "ISABELLE_RECEIVER_GATE_V1"
# The device label in kind 3 identifies the ACK sender, not its receiver.
EXPECTED_PORT = {(1, 0): 1, (1, 1): 2,
                 (2, 0): 1, (2, 1): 2,
                 (3, 0): 0, (3, 1): 0}


def reference_receive(width: int, limit: int, port: int,
                      payload: tuple[int, ...]) -> tuple[int, int, int] | None:
    message = frames.reference_decode(width, limit, payload)
    if message is None or port != EXPECTED_PORT[message[:2]]:
        return None
    return message


def receive_case(width: int, limit: int, port: int,
                 payload: tuple[int, ...], group: str) -> Case:
    suffix = " " + " ".join(map(str, payload)) if payload else ""
    message = reference_receive(width, limit, port, payload)
    expected = "N" if message is None else "P " + " ".join(map(str, message))
    return Case(f"R {width} {limit} {port}{suffix}", expected, group)


def binding_cases(cases: list[Case], smoke: bool) -> None:
    values = (0, 1, 126, 127, 128, 254, 255) if smoke else range(256)
    for limit in (0, 1, 127, 255):
        for tag in (1, 2, 3):
            for device in (0, 1):
                for epoch in values:
                    cases.append(frames.encode_case(1, limit, tag, device, epoch,
                                                     "one-byte encoder/receiver binding"))
                    payload = tuple(frames.frame_bytes(1, tag, device, epoch))
                    for port in (0, 1, 2):
                        cases.append(receive_case(1, limit, port, payload,
                                                  "one-byte encoder/receiver binding"))
    values = ((0, 1, 255, 256, 257, 32767, 32768, 65534, 65535)
              if smoke else range(65536))
    for epoch in values:
        for tag, device, correct, wrong in ((1, 0, 1, 2), (3, 1, 0, 2)):
            payload = tuple(frames.frame_bytes(2, tag, device, epoch))
            for port in (correct, wrong):
                cases.append(receive_case(2, 65535, port, payload,
                                          "two-byte full-domain accepted/wrong-port"))
    for tag in (1, 2, 3):
        for device in (0, 1):
            payload = tuple(frames.frame_bytes(1, tag, device, 42))
            for port in (3, 255, 65536, 10 ** 100):
                cases.append(receive_case(1, 255, port, payload, "invalid port core rejection"))


def add_frame_cases(cases: list[Case], smoke: bool) -> None:
    inherited: list[Case] = []
    frames.header_cases(inherited)
    frames.boundary_cases(inherited, smoke)
    for case in inherited:
        tokens = case.request.split()
        if tokens[0] == "E":
            cases.append(case)
            continue
        assert tokens[0] == "D"
        width, limit = map(int, tokens[1:3])
        payload = tuple(map(int, tokens[3:]))
        if len(payload) > 128:
            # R includes one more trusted-context field than the old D API.
            cases.append(Case(f"R {width} {limit} 0 " + " ".join(map(str, payload)),
                              "X", "receiver-specific token policy"))
        else:
            for port in (0, 1, 2):
                cases.append(receive_case(width, limit, port, payload, case.group))


def interface_cases(cases: list[Case]) -> None:
    malformed = ["", " ", "unknown", "V extra", "E", "R", "D", "S", "E 1",
                 "R 1", "R 1 255", "E 1 255", "E 1 255 1", "E 1 255 1 0",
                 "E 1 255 1 0 0 0", "D 1 255 84 75 1 1 0 1 42",
                 "S 1 255 84 75 1 1 0 1 42"]
    for valid in (["E", "1", "255", "1", "0", "42"],
                  ["R", "1", "255", "1", "84", "75", "1", "1", "0", "1", "42"]):
        for index in range(1, len(valid)):
            for bad in ("-1", "+1", "~1", "1.0", "1e0", "0x1", "one", "42junk", "\u0660", "\uff10"):
                tokens = valid.copy()
                tokens[index] = bad
                malformed.append(" ".join(tokens))
    for request in malformed:
        cases.append(Case(request, "X", "invalid ASCII decimal or unbound command"))
        cases.append(Case("V", BANNER, "post-error recovery"))
    cases.extend((
        Case("E 0 0 1 0 0", "N", "zero-width core rejection"),
        Case("R 0 0 0", "N", "zero-width core rejection"),
        Case("R 0 0 1 84 75 1 1 0 0", "N", "zero-width core rejection"),
        Case("R 1 255 1", "N", "empty datagram rejection"),
        Case("  E\t1  255\t1  0  42  ", "B 84 75 1 1 0 1 42", "whitespace interface"),
        Case(" R\t01  00255\t01 084 075 01 01 00 01 00042 ", "P 1 0 42", "leading-zero decimal interface"),
        Case("R 1 255 0 84 75 1 3 1 1 42", "P 3 1 42", "ACK sender is B, receiver is controller"),
        Case("R 1 255 2 84 75 1 3 1 1 42", "N", "ACK sender is not its receiver"),
    ))


def policy_cases(cases: list[Case]) -> None:
    invalid = ["E 65 0 1 0 0", "R 65 0 0", "E 255 0 1 0 0", "R 255 0 0",
               "E 1 255 1 0 " + "0" * 161,
               "R 1 255 " + "0" * 161 + " 84 75 1 1 0 1 42",
               "E " + "9" * 160 + " 0 1 0 0",
               "R 64 0 0 " + " ".join(["0"] * 129),
               "V" + " " * 16384]
    for request in invalid:
        cases.append(Case(request, "X", "interface resource policy"))
        cases.append(Case("V", BANNER, "policy recovery"))
    cases.extend((
        Case("E 1 255 1 0 " + "0" * 160, "B 84 75 1 1 0 1 0", "policy accepted boundary"),
        Case("R 1 255 " + "0" * 160 + " 84 75 1 3 1 1 42", "P 3 1 42", "policy accepted boundary"),
        Case("R 1 255 " + "9" * 160 + " 84 75 1 3 1 1 42", "N", "policy accepted boundary"),
        Case("E 1 " + "9" * 160 + " 1 0 0", "N", "policy accepted boundary"),
        Case("R 64 0 0 " + " ".join(["0"] * 128), "N", "policy accepted boundary"),
        Case("V" + " " * 16383, BANNER, "policy accepted boundary"),
    ))


def make_cases(smoke: bool) -> list[Case]:
    cases = [Case("V", BANNER, "banner")]
    # Wrong-port probes appear before large enumerations and policy tests.
    for tag in (1, 2, 3):
        for device in (0, 1):
            payload = tuple(frames.frame_bytes(1, tag, device, 42))
            for port in (0, 1, 2):
                cases.append(receive_case(1, 255, port, payload, "explicit accepted/wrong-port gate"))
    interface_cases(cases)
    policy_cases(cases)
    binding_cases(cases, smoke)
    add_frame_cases(cases, smoke)
    cases.append(Case("V", BANNER, "final EOF command"))
    return cases


def checker_negative_controls() -> None:
    sample = [Case("R 1 255 2 84 75 1 1 0 1 42", "N", "checker control")]
    check_answers(sample, "N\n")
    for wrong in ("P 1 0 42\n", "X\n", "N \n", "", "N\nX\n"):
        try:
            check_answers(sample, wrong)
        except RuntimeError:
            continue
        raise RuntimeError(f"Checker accepted a negative control: {wrong!r}")


def interactive_probe(polyml: Path, wrapper: Path, environment: dict[str, str], timeout: float) -> None:
    """Require two replies while stdin remains open, then a clean EOF exit."""
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
        probes = (("V", BANNER), ("R 2 65535 0 84 75 1 3 1 2 1 2", "P 3 1 513"))
        for command, expected in probes:
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
                        help="Supplied to the wrapper using RECEIVER_GATE_CORE")
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
    # The final command has no newline; the interactive test separately checks
    # that replies do not depend on closing stdin.
    batch = "\n".join(case.request for case in cases)
    environment = os.environ.copy()
    environment["RECEIVER_GATE_CORE"] = str(core)
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
    print(f"{mode}: {len(cases):,} receiver-gate requests passed against real exported SML in {elapsed:.2f}s")
    print("  interactive pipe probe: 2 replies before closing stdin; clean exit")
    for group, count in Counter(case.group for case in cases).items():
        print(f"  {group}: {count:,}")
    print("  checker negative controls: 5 rejected")
    for path, digest in hashes.items():
        print(f"SHA256 {path}: {digest}")
    print("Scope: receiver-bound datagram execution and text interface; not authentication, socket binding, physical delivery or compiler certification")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
