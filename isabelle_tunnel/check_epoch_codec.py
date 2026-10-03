"""Independent byte-codec and finite-protocol adapter checks.

This is an executable mathematical model, not certified extraction, compiled
implementation verification, a transport test, or a firmware test. Epochs use
exact-length little-endian byte sequences. A zero-byte configuration with cap
zero is included as a mathematical degenerate case, not a deployment format.
The protocol retains its earlier authentication and atomic-actuation assumptions.
"""
from random import Random

import check_activation as activation
import check_finite_activation as finite


WIRE_KINDS = frozenset(("entry", "fence", "ack", "receive"))
TRUSTED_KINDS = frozenset(("begin", "flush", "commit", "send", "exit", "crash")) | activation.LOCAL


def natural(value):
    # Python bool is an int subclass, but is not accepted as a wire byte here.
    return type(value) is int and value >= 0


def configuration(width, limit):
    return (natural(width) and natural(limit)
            and limit < 256 ** width)


def encode(width, limit, value):
    if not configuration(width, limit) or not natural(value) or value > limit:
        return None
    result = []
    rest = value
    for _ in range(width):
        result.append(rest % 256)
        rest //= 256
    assert rest == 0
    return result


def decode(width, limit, payload):
    if (not configuration(width, limit)
            or not isinstance(payload, (list, tuple))
            or len(payload) != width
            or any(type(digit) is not int or not 0 <= digit < 256
                   for digit in payload)):
        return None
    value = 0
    place = 1
    for digit in payload:
        value += digit * place
        place *= 256
    return value if value <= limit else None


def successor(width, limit, payload):
    value = decode(width, limit, payload)
    if value is None or value >= limit:
        return None
    # Compare first: no overflowing increment is evaluated at the cap.
    return encode(width, limit, value + 1)


def wire_step(width, limit, state, event):
    kind, payload, device = event
    if kind not in WIRE_KINDS:
        raise ValueError("Raw wire input needs a supported epoch-bearing kind")
    value = decode(width, limit, payload)
    return state if value is None else finite.step(limit, state, (kind, value, device))


def trusted_step(width, limit, state, event):
    if event[0] not in TRUSTED_KINDS:
        raise ValueError("Epoch-bearing input must pass through the wire decoder")
    return finite.step(limit, state, event)


def expected_decode(width, limit, payload):
    """Separate stdlib oracle, deliberately not implemented with decode."""
    if type(width) is not int or width < 0 or type(limit) is not int or limit < 0:
        return None
    if limit >= (1 << (8 * width)):
        return None
    if not isinstance(payload, (list, tuple)) or len(payload) != width:
        return None
    if any(type(digit) is not int or not 0 <= digit <= 255 for digit in payload):
        return None
    value = int.from_bytes(bytes(payload), byteorder="little", signed=False)
    return value if value <= limit else None


def checked_payload(width, limit, payload):
    actual = decode(width, limit, payload)
    assert actual == expected_decode(width, limit, payload)
    if actual is not None:
        assert encode(width, limit, actual) == list(payload)
        assert list(actual.to_bytes(width, byteorder="little", signed=False)) == list(payload)
    expected_next = (None if actual is None or actual >= limit
                     else list((actual + 1).to_bytes(width, byteorder="little", signed=False)))
    assert successor(width, limit, payload) == expected_next
    return actual


def exhaustive_one_byte():
    decodes = encodes = successful = 0
    for limit in range(256):
        seen = {}
        for value in range(256):
            payload = [value]
            result = checked_payload(1, limit, payload)
            decodes += 1
            expected = [value] if value <= limit else None
            assert encode(1, limit, value) == expected
            encodes += 1
            if result is not None:
                successful += 1
                assert result not in seen
                seen[result] = tuple(payload)
                assert decode(1, limit, encode(1, limit, value)) == value
        assert len(seen) == limit + 1
        assert encode(1, limit, limit + 1) is None
        assert successor(1, limit, [limit]) is None
    print(f"One-byte exhaustive checks: {decodes} decodes, {encodes} encodes, {successful} accepted round trips; exact bytes and guarded successor match stdlib")


def boundary_and_malformed_checks():
    rng = Random(20261003)
    cases = 0
    for width in (0, 1, 2, 4, 8):
        capacity = 256 ** width
        limits = {0, capacity - 1, capacity // 2}
        limits.update(value for value in (1, 255, 256, 257) if value < capacity)
        for limit in sorted(limits):
            if limit >= capacity:
                continue
            candidates = {0, limit, capacity - 1}
            candidates.update(value for value in (1, limit - 1, limit + 1, 255, 256, 257)
                              if 0 <= value < capacity)
            candidates.update(rng.randrange(capacity) for _ in range(60))
            for value in candidates:
                payload = list(value.to_bytes(width, "little"))
                checked_payload(width, limit, payload)
                encoded = encode(width, limit, value)
                assert encoded == (payload if value <= limit else None)
                if encoded is not None:
                    assert decode(width, limit, encoded) == value
                cases += 1
            assert encode(width, limit, -1) is None
            assert encode(width, limit, limit + 1) is None
            zero = [0] * width
            malformed = [zero + [0], zero + [255], None, "0", 0]
            if width:
                malformed.append(zero[:-1])
                for digit in (-1, 256, 257, 1.0, True, None, "1"):
                    malformed.append([digit] + zero[1:])
            else:
                malformed.extend(([0], [1], [256]))
            for payload in malformed:
                assert checked_payload(width, limit, payload) is None
                cases += 1
            # A longer encoding is rejected even when its numeric value agrees.
            assert decode(width, limit, zero + [0]) is None
        for invalid_limit in (-1, capacity, capacity + 1, 1.0, True):
            assert not configuration(width, invalid_limit)
            assert encode(width, invalid_limit, 0) is None
            assert decode(width, invalid_limit, [0] * width) is None
    for invalid_width in (-1, 1.0, True, None):
        assert not configuration(invalid_width, 0)
        assert encode(invalid_width, 0, 0) is None
        assert decode(invalid_width, 0, []) is None
    assert encode(0, 0, 0) == [] and decode(0, 0, []) == 0
    assert successor(0, 0, []) is None
    assert decode(0, 1, []) is None
    # Exhaustively check the full two-byte domain at its maximum cap.
    representations = set()
    for value in range(65536):
        payload = encode(2, 65535, value)
        assert checked_payload(2, 65535, payload) == value
        representations.add(tuple(payload))
    assert len(representations) == 65536
    print(f"Boundary/malformed checks: {cases} cases at 0, 1, 2, 4, 8 bytes; full 65,536-value two-byte bijection; zero-byte cap-zero case explicitly covered")


def checked_wire(width, limit, state, event):
    kind, payload, device = event
    value = expected_decode(width, limit, payload)
    finite.invariant(limit, state)
    actual = wire_step(width, limit, state, event)
    if value is None:
        assert actual == state
    else:
        assert actual == finite.checked(limit, state, (kind, value, device))
    finite.invariant(limit, actual)
    return actual, None if value is None else (kind, value, device)


def checked_trusted(width, limit, state, event):
    actual = trusted_step(width, limit, state, event)
    assert actual == finite.checked(limit, state, event)
    finite.invariant(limit, actual)
    return actual


def protocol_adapter_checks():
    rng = Random(20261003)
    transitions = rejected = traces = 0
    configs = ((0, 0), (1, 0), (1, 1), (1, 3), (2, 3), (4, 3), (8, 3))
    for width, limit in configs:
        for _ in range(12):
            state = activation.boot()
            projected = []
            for _ in range(limit + 3):
                planned_epoch = finite.epoch(state) + 1
                planned = activation.handoff(planned_epoch, rng.choice((None, 0, 1)))
                planned += [("send", 0, rng.randrange(2)), ("exit", 0, rng.randrange(2))]
                for event in planned:
                    # Malformed and authentic-shaped replay packets are mixed.
                    for _ in range(2):
                        kind = rng.choice(sorted(WIRE_KINDS))
                        digit_value = rng.randrange(min(256 ** width, limit + 3))
                        payload = list(digit_value.to_bytes(width, "little"))
                        shape = rng.randrange(5)
                        if shape == 0:
                            payload.append(0)
                        elif shape == 1:
                            payload = [257] + payload[1:] if width else [257]
                        elif shape == 2 and width:
                            payload = payload[:-1]
                        state, projected_event = checked_wire(width, limit, state,
                                                              (kind, payload, rng.randrange(2)))
                        transitions += 1
                        if projected_event is None:
                            rejected += 1
                        else:
                            projected.append(projected_event)
                    if event[0] in WIRE_KINDS:
                        # A next-epoch attempt above the cap has a well-shaped
                        # packet when it fits the physical width; otherwise it
                        # is an overlong packet, which is also rejected.
                        wire_width = max(width, (event[1].bit_length() + 7) // 8)
                        payload = list(event[1].to_bytes(wire_width, "little"))
                        state, projected_event = checked_wire(width, limit, state,
                                                              (event[0], payload, event[2]))
                        if projected_event is None:
                            rejected += 1
                        else:
                            projected.append(projected_event)
                    else:
                        state = checked_trusted(width, limit, state, event)
                        projected.append(event)
                    transitions += 1
                # Persistent storage recovery remains a trusted protocol event.
                for local in (("power", 0, 0), ("recover", 0, 0), ("exit", 0, 0), ("exit", 0, 1)):
                    state = checked_trusted(width, limit, state, local)
                    projected.append(local)
                    transitions += 1
            assert state == finite.run(limit, projected)
            assert len(state.engine.inside) <= 1
            traces += 1
    # A queued final-epoch command can still enter after issuance stops.
    state = finite.reach_epoch(1, 1)
    state = checked_trusted(1, 1, state, ("send", 0, 0))
    state = checked_trusted(1, 1, state, ("begin", 0, 1))
    assert finite.exhausted(1, state)
    state, _ = checked_wire(1, 1, state, ("entry", [1], 0))
    assert state.engine.inside == {0}
    for invalid_config in ((1, 256), (0, 1)):
        assert wire_step(*invalid_config, state, ("entry", [1], 0)) == state
        live = finite.reach_epoch(1, 1)
        sent = trusted_step(*invalid_config, live, ("send", 0, 0))
        assert sent == finite.step(invalid_config[1], live, ("send", 0, 0))
        assert sent != live
    print(f"Protocol adapter: {traces} seeded traces, {transitions} transitions, {rejected} rejected packets; exact decoded-event projection and finite safety checked; old final-epoch entry remains possible")


def rejected_shortcuts():
    # These are serialization/range witnesses, not collision demonstrations.
    for width in (1, 2, 4, 8):
        limit = 256 ** width - 1
        too_large = limit + 1
        truncated = [0] * width
        assert too_large % (256 ** width) == 0
        assert encode(width, limit, too_large) is None
        assert decode(width, limit, truncated) == 0
        assert successor(width, limit, [255] * width) is None
    assert [digit & 255 for digit in [257]] == [1]
    assert decode(1, 255, [257]) is None
    assert decode(1, 255, [1]) == 1
    assert int.from_bytes(bytes([1, 0]), "little") == 1
    assert decode(1, 255, [1, 0]) is None
    assert decode(1, 255, [1]) == 1
    print("Negative witnesses: overflowing/truncating encoders wrap cap + 1 to zero; byte masking aliases [257] to [1]; high-zero length normalization aliases [1, 0] to [1]. Strict codec rejects the unsafe inputs")


def main():
    exhaustive_one_byte()
    boundary_and_malformed_checks()
    protocol_adapter_checks()
    rejected_shortcuts()


if __name__ == "__main__":
    main()
