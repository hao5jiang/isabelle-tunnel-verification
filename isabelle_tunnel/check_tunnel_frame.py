"""Independent datagram-format and finite-protocol regression checks.

The format is [84, 75, 1, tag, device, width] followed by the little-endian
epoch field. Tags 1, 2, and 3 deliver entry, fence, and clear-ack messages.
Creating an acknowledgement is a local controller/device action, not a wire
tag. This Python model is not Isabelle extraction, transport authentication,
a stream reassembler, or a machine-code verification result.
"""
from collections import deque
from dataclasses import dataclass
from random import Random

import check_activation as activation
import check_finite_activation as finite


TAG_KIND = {1: "entry", 2: "fence", 3: "receive"}
KIND_TAG = {kind: tag for tag, kind in TAG_KIND.items()}
LOCAL_KINDS = frozenset({"begin", "flush", "commit", "send", "ack", "exit",
                         "crash"} | activation.LOCAL)
MAGIC_VERSION = [84, 75, 1]


def natural(value):
    return type(value) is int and value >= 0


def config_valid(width, limit):
    return (natural(width) and 1 <= width <= 255 and natural(limit)
            and limit < 256 ** width)


def encode(width, limit, tag, device, epoch):
    """Build a canonical datagram; reject bad inputs instead of truncating."""
    if not (config_valid(width, limit) and type(tag) is int and tag in TAG_KIND
            and type(device) is int and device in (0, 1)
            and natural(epoch) and epoch <= limit):
        return None
    payload = [(epoch >> (8 * index)) & 255 for index in range(width)]
    return MAGIC_VERSION + [tag, device, width] + payload


def decode(width, limit, data):
    """Decode one whole datagram; exact length excludes concatenated frames."""
    if not config_valid(width, limit):
        return None
    if not isinstance(data, (list, tuple, bytes, bytearray)):
        return None
    if len(data) != 6 + width:
        return None
    if any(type(value) is not int or not 0 <= value <= 255 for value in data):
        return None
    if list(data[:3]) != MAGIC_VERSION:
        return None
    tag, device, declared_width = data[3:6]
    if tag not in TAG_KIND or device not in (0, 1) or declared_width != width:
        return None
    epoch = sum(value << (8 * index) for index, value in enumerate(data[6:]))
    return (tag, device, epoch) if epoch <= limit else None


def oracle_decode(width, limit, data):
    """Separate conversion path using Python's byte conversion primitive."""
    if not config_valid(width, limit) or not isinstance(data, (list, tuple, bytes, bytearray)):
        return None
    if len(data) != width + 6 or any(type(value) is not int for value in data):
        return None
    try:
        octets = bytes(data)
    except (ValueError, TypeError):
        return None
    if (octets[:3] != b"TK\x01" or octets[3] not in (1, 2, 3)
            or octets[4] not in (0, 1) or octets[5] != width):
        return None
    value = int.from_bytes(octets[6:], "little", signed=False)
    return (octets[3], octets[4], value) if value <= limit else None


@dataclass(frozen=True)
class Local:
    kind: str
    epoch: int = 0
    device: int | None = 0

    def __post_init__(self):
        if self.kind not in LOCAL_KINDS or not natural(self.epoch):
            raise ValueError("Not a permitted local event")
        if self.kind == "begin" and self.device is None:
            return
        if type(self.device) is not int or self.device not in (0, 1):
            raise ValueError("Invalid local device identity")

    def event(self):
        return self.kind, self.epoch, self.device


def datagram_step(width, limit, state, data):
    message = decode(width, limit, data)
    if message is None:
        return state
    tag, device, epoch = message
    return finite.step(limit, state, (TAG_KIND[tag], epoch, device))


def local_step(width, limit, state, action):
    if not isinstance(action, Local):
        raise TypeError("The local interface requires a Local event")
    # Packet configuration governs parsing, not already typed local actions.
    return finite.step(limit, state, action.event())


def represent(width, limit, event):
    kind, epoch, device = event
    if kind in KIND_TAG:
        # The raw input can contain an out-of-cap epoch, so this test helper
        # serializes representable values without using the guarded encoder.
        assert 0 <= epoch < 256 ** width
        return MAGIC_VERSION + [KIND_TAG[kind], device, width] + list(epoch.to_bytes(width, "little"))
    return Local(kind, epoch, device)


def mixed_checked(width, limit, state, action):
    finite.invariant(limit, state)
    if isinstance(action, Local):
        result = local_step(width, limit, state, action)
        projected = finite.checked(limit, state, action.event())
    else:
        result = datagram_step(width, limit, state, action)
        message = oracle_decode(width, limit, action)
        if message is None:
            projected = state
        else:
            tag, device, epoch = message
            projected = finite.checked(limit, state, (TAG_KIND[tag], epoch, device))
    assert result == projected
    finite.invariant(limit, result)
    assert len(result.engine.inside) <= 1
    if finite.exhausted(limit, state):
        assert finite.exhausted(limit, result)
    return result


def full_one_byte_space():
    cases = accepted = 0
    for limit in range(256):
        for tag in TAG_KIND:
            for device in (0, 1):
                for epoch in range(256):
                    data = [84, 75, 1, tag, device, 1, epoch]
                    expected = (tag, device, epoch) if epoch <= limit else None
                    assert decode(1, limit, data) == expected
                    assert oracle_decode(1, limit, data) == expected
                    encoded = encode(1, limit, tag, device, epoch)
                    assert encoded == (data if expected is not None else None)
                    accepted += expected is not None
                    cases += 1
    print(f"One-byte exhaustive: {cases} cap/tag/device/epoch cases; {accepted} accepted, exact encode/decode agreement")


def header_and_structure_tests():
    width, limit = 2, 1000
    baseline = encode(width, limit, 2, 1, 777)
    cases = valid_mutations = 0
    for position in range(6):
        for replacement in range(256):
            mutated = baseline.copy()
            mutated[position] = replacement
            actual = decode(width, limit, mutated)
            assert actual == oracle_decode(width, limit, mutated)
            if position < 3:
                valid = replacement == baseline[position]
            elif position == 3:
                valid = replacement in TAG_KIND
            elif position == 4:
                valid = replacement in (0, 1)
            else:
                valid = replacement == width
            assert (actual is not None) == valid
            valid_mutations += valid
            cases += 1

    malformed = [None, 7, "TK", {}, [], baseline + [0], baseline + baseline]
    malformed += [baseline[:length] for length in range(len(baseline))]
    malformed += [[0] + baseline, baseline[1:], baseline + [0] * 1024]
    for position in range(len(baseline)):
        for bad in (-1, 256, 65536, None, "1", 1.0, True, False):
            mutated = baseline.copy()
            mutated[position] = bad
            malformed.append(mutated)
    # The indicated byte width is checked against the configured width,
    # independently of whether the datagram was padded to fit that declaration.
    malformed += [baseline[:5] + [1] + baseline[6:7],
                  baseline[:5] + [3] + baseline[6:] + [0]]
    for data in malformed:
        assert decode(width, limit, data) is None
        assert oracle_decode(width, limit, data) is None
    for container in (list, tuple, bytes, bytearray):
        assert decode(width, limit, container(baseline)) == (2, 1, 777)
    assert decode(width, limit, [84, 75, 1, 4, 1, width, 9, 3]) is None
    print(f"Header mutation: {cases} byte replacements, {valid_mutations} legal changes; {len(malformed)} malformed/type/length/concatenation cases rejected")
    return malformed


def width_and_range_tests():
    cases = 0
    for width in (1, 2, 4, 8, 64, 255):
        capacity = 256 ** width
        for limit in sorted({0, 1, capacity // 2, capacity - 2, capacity - 1}):
            values = sorted({0, 1, limit, limit + 1, capacity - 1, capacity})
            for tag in TAG_KIND:
                for device in (0, 1):
                    for epoch in values:
                        frame = encode(width, limit, tag, device, epoch)
                        if epoch <= limit:
                            oracle = MAGIC_VERSION + [tag, device, width] + list(epoch.to_bytes(width, "little"))
                            assert frame == oracle
                            assert decode(width, limit, frame) == (tag, device, epoch)
                            assert int.from_bytes(bytes(frame[6:]), "little") == epoch
                        else:
                            assert frame is None
                        if epoch < capacity:
                            raw = MAGIC_VERSION + [tag, device, width] + list(epoch.to_bytes(width, "little"))
                            assert decode(width, limit, raw) == oracle_decode(width, limit, raw)
                        cases += 1
    invalid_configs = [(0, 0), (256, 0), (-1, 0), (1, -1), (1, 256),
                       (2, 65536), (True, 0), (1.0, 0), (1, False), (1, None)]
    baseline = [84, 75, 1, 1, 0, 1, 0]
    for width, limit in invalid_configs:
        assert encode(width, limit, 1, 0, 0) is None
        assert decode(width, limit, baseline) is None
        assert datagram_step(width, limit, activation.boot(), baseline) == activation.boot()
    for width, limit in ((0, 2), (256, 2), (1, 256), (2, 65536)):
        assert not config_valid(width, limit)
        initial = activation.boot()
        action = Local("begin", 0, 0)
        actual = local_step(width, limit, initial, action)
        assert actual == finite.checked(limit, initial, action.event())
        assert actual != initial
        assert actual.engine.requests == {(1, 0), (1, 1)}
    for tag in (0, 4, 255, -1, True, 1.0, "1", None):
        assert encode(1, 255, tag, 0, 0) is None
    for device in (-1, 2, 255, True, 0.0, "0", None):
        assert encode(1, 255, 1, device, 0) is None
    for epoch in (-1, 256, True, 0.0, "0", None):
        assert encode(1, 255, 1, 0, epoch) is None
    print(f"Width boundaries: {cases} encode/decode cases for 1, 2, 4, 8, 64, 255 bytes; {len(invalid_configs)} invalid configurations; 4 invalid-config local-progress checks; no modular truncation")


def authority_boundary_tests():
    rejected = 0
    for kind in ("entry", "fence", "receive", "unknown"):
        try:
            Local(kind, 1, 0)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("A wire input bypassed the parser through Local")
    s = activation.boot()
    s = mixed_checked(1, 2, s, Local("begin", 0, 0))
    requested = s
    # A syntactically valid acknowledgement packet cannot create evidence.
    assert mixed_checked(1, 2, s, encode(1, 2, 3, 0, 1)) == s
    assert not s.engine.acknowledgements and not s.engine.received
    for event in activation.store_floor(1, 0) + [("activate", 0, 0)]:
        s = mixed_checked(1, 2, s, represent(1, 2, event))
    assert not s.engine.acknowledgements
    bad_tag = [84, 75, 1, 4, 0, 1, 1]
    assert mixed_checked(1, 2, s, bad_tag) == s
    assert mixed_checked(1, 2, s, encode(1, 2, 3, 0, 1)) == s
    s = mixed_checked(1, 2, s, Local("ack", 1, 0))
    assert s.engine.acknowledgements == {(1, 0)} and not s.engine.received
    s = mixed_checked(1, 2, s, encode(1, 2, 3, 0, 1))
    assert s.engine.received == {(1, 0)}
    # A different valid identity changes routing, but not established history.
    assert mixed_checked(1, 2, requested, encode(1, 2, 1, 1, 1)) == requested
    print(f"Authority boundaries: {rejected} local bypass kinds rejected; tag 4 rejected; tag 3 receives only established local ACK history")


def protocol_traces(malformed):
    edges = cuts = 0
    seeds = {}
    for limit in range(4):
        s = activation.boot()
        trace = []
        for epoch in range(1, limit + 1):
            owner = (epoch - 1) % 2
            trace += activation.handoff(epoch, owner)
            trace += [("send", 0, owner), ("entry", epoch, owner), ("exit", 0, owner)]
        trace += [("begin", 0, 1), ("crash", 0, 0), ("commit", 0, 0)]
        seed_states = [s]
        for event in trace:
            action = represent(1, limit, event)
            direct = finite.checked(limit, s, event)
            s = mixed_checked(1, limit, s, action)
            assert s == direct
            seed_states.append(s)
            edges += 1
        assert finite.exhausted(limit, s)
        for state in seed_states:
            for bad in malformed:
                assert mixed_checked(1, limit, state, bad) == state
                edges += 1
        seeds[limit] = (seed_states[0], seed_states[len(seed_states) // 2], s)
        for cut in range(len(trace) + 1):
            state = activation.boot()
            prefix = trace[:cut]
            suffix = [("power", 0, 0), ("crash", 0, 0), ("recover", 0, 0)] + trace[cut:]
            for event in prefix + suffix:
                state = mixed_checked(1, limit, state, represent(1, limit, event))
                edges += 1
            cuts += 1
    print(f"Protocol traces: {edges} mixed/local/raw checks and {cuts} crash cuts across caps 0..3; finite-model state equality, range and exclusion checked")
    return seeds


def bounded_protocol(seeds, depth_limit=2):
    count = edges = 0
    for limit, states in seeds.items():
        actions = [Local("begin", 0, owner) for owner in (None, 0, 1)]
        actions += [Local(kind, 0, 0) for kind in ("flush", "commit", "crash")]
        actions += [Local(kind, 0, i) for kind in sorted(activation.LOCAL | {"send", "exit"})
                    for i in (0, 1)]
        actions += [Local("ack", epoch, i) for epoch in range(limit + 2) for i in (0, 1)]
        actions += [represent(1, limit, (kind, epoch, i)) for kind in KIND_TAG
                    for epoch in range(limit + 2) for i in (0, 1)]
        actions += [[], [84, 75, 1, 4, 0, 1, 0], [84, 75, 1, 1, 2, 1, 0]]
        seen = {activation.canonical(s) for s in states}
        queue = deque((s, 0) for s in seen)
        while queue:
            s, depth = queue.popleft()
            if depth == depth_limit:
                continue
            for action in actions:
                nxt = activation.canonical(mixed_checked(1, limit, s, action))
                edges += 1
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append((nxt, depth + 1))
        count += len(seen)
    print(f"Depth-{depth_limit} mixed-input search: {count} states, {edges} transitions")


def randomized_tests():
    rng = Random(20261003)
    parser_cases = protocol_edges = 0
    for _ in range(20000):
        width = rng.choice((1, 2, 4, 8, 64, 255))
        limit = rng.randrange(256 ** width)
        value = rng.randrange(limit + 1)
        data = encode(width, limit, rng.choice((1, 2, 3)), rng.randrange(2), value)
        mode = rng.randrange(5)
        if mode == 0:
            data[rng.randrange(len(data))] = rng.randrange(-2, 258)
        elif mode == 1:
            data = data[:rng.randrange(len(data) + 1)]
        elif mode == 2:
            data += [rng.randrange(256)]
        actual = decode(width, limit, data)
        assert actual == oracle_decode(width, limit, data)
        if actual is not None:
            tag, device, epoch = actual
            assert encode(width, limit, tag, device, epoch) == data
        parser_cases += 1
    for limit in range(4):
        for _ in range(20):
            s = activation.boot()
            for _ in range(limit + 3):
                plan = activation.handoff(finite.epoch(s) + 1, rng.choice((None, 0, 1)))
                for event in plan:
                    for _ in range(2):
                        if rng.randrange(2):
                            noise = (rng.choice(tuple(KIND_TAG)), rng.randrange(limit + 2), rng.randrange(2))
                            action = represent(1, limit, noise)
                        else:
                            action = Local(rng.choice(sorted(LOCAL_KINDS)), rng.randrange(limit + 2), rng.randrange(2))
                        s = mixed_checked(1, limit, s, action)
                        protocol_edges += 1
                    s = mixed_checked(1, limit, s, represent(1, limit, event))
                    protocol_edges += 1
    print(f"Seeded tests: {parser_cases} parser/oracle cases and {protocol_edges} mixed protocol transitions")


def main():
    full_one_byte_space()
    malformed = header_and_structure_tests()
    width_and_range_tests()
    authority_boundary_tests()
    seeds = protocol_traces(malformed)
    bounded_protocol(seeds)
    randomized_tests()
    print("PASS: complete datagram syntax and finite-protocol adapter checks; not authentication or a stream-transport proof")


if __name__ == "__main__":
    main()
