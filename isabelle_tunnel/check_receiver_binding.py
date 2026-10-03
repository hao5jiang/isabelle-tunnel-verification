"""Independent receiver-port binding and protocol refinement checks.

Port 0 is the controller; ports 1 and 2 are devices A and B. In entry and
fence packets, the device field is the destination. In a clear-ACK packet,
that field labels the sender and the destination is the controller.
This is a model test, not Isabelle extraction, sender authentication, or a
verified socket implementation. Local operations do not pass through a port.
"""
from collections import deque
from dataclasses import dataclass
from random import Random

import check_activation as activation
import check_finite_activation as finite
import check_tunnel_frame as frame


PORTS = (0, 1, 2)
DELIVERY_PORTS = {(1, 0): 1, (1, 1): 2,
                  (2, 0): 1, (2, 1): 2,
                  (3, 0): 0, (3, 1): 0}


def receiver_decode(width, limit, port, data):
    """Bind decoding to trusted receive context, not a packet-provided port."""
    if type(port) is not int or port not in PORTS:
        return None
    packet = frame.decode(width, limit, data)
    if packet is None:
        return None
    tag, device, _ = packet
    if tag == 3:
        return packet if port == 0 else None
    return packet if port == device + 1 else None


def oracle_receiver(width, limit, port, data):
    packet = frame.oracle_decode(width, limit, data)
    if packet is None or type(port) is not int:
        return None
    return packet if port == DELIVERY_PORTS[packet[:2]] else None


@dataclass(frozen=True)
class Received:
    port: object
    data: object


def project(width, limit, action):
    if isinstance(action, frame.Local):
        return action.event()
    if not isinstance(action, Received):
        raise TypeError("The receive interface requires a Received or Local event")
    packet = receiver_decode(width, limit, action.port, action.data)
    if packet is None:
        return None
    tag, device, epoch = packet
    return frame.TAG_KIND[tag], epoch, device


def bound_step(width, limit, state, action):
    event = project(width, limit, action)
    return state if event is None else finite.step(limit, state, event)


def checked(width, limit, state, action):
    finite.invariant(limit, state)
    actual = bound_step(width, limit, state, action)
    if isinstance(action, frame.Local):
        expected = finite.checked(limit, state, action.event())
    else:
        packet = oracle_receiver(width, limit, action.port, action.data)
        if packet is None:
            expected = state
        else:
            tag, device, epoch = packet
            expected = finite.checked(limit, state, (frame.TAG_KIND[tag], epoch, device))
    assert actual == expected
    finite.invariant(limit, actual)
    assert len(actual.engine.inside) <= 1
    if finite.exhausted(limit, state):
        assert finite.exhausted(limit, actual)
    return actual


def represent(width, limit, event):
    action = frame.represent(width, limit, event)
    if isinstance(action, frame.Local):
        return action
    kind, _, device = event
    return Received(DELIVERY_PORTS[frame.KIND_TAG[kind], device], action)


def run(width, limit, actions, state=None):
    state = activation.boot() if state is None else state
    original = state
    projected = []
    for action in actions:
        event = project(width, limit, action)
        if event is not None:
            projected.append(event)
        state = checked(width, limit, state, action)
    assert state == finite.run(limit, projected, original)
    return state


def parser_binding_tests():
    checks = packets = 0
    for limit in (0, 1, 127, 255):
        for tag in (1, 2, 3):
            for device in (0, 1):
                for epoch in range(256):
                    raw = [84, 75, 1, tag, device, 1, epoch]
                    accepted = []
                    for port in PORTS:
                        actual = receiver_decode(1, limit, port, raw)
                        expected = ((tag, device, epoch)
                                    if epoch <= limit and port == DELIVERY_PORTS[tag, device]
                                    else None)
                        assert actual == expected == oracle_receiver(1, limit, port, raw)
                        if actual is not None:
                            accepted.append(port)
                        checks += 1
                    assert accepted == ([DELIVERY_PORTS[tag, device]] if epoch <= limit else [])
                    packets += 1
    # The entire two-byte epoch domain is exercised for both role classes.
    for tag, device in ((1, 0), (2, 1), (3, 0), (3, 1)):
        for epoch in range(65536):
            raw = [84, 75, 1, tag, device, 2, epoch & 255, epoch >> 8]
            for port in PORTS:
                expected = ((tag, device, epoch)
                            if port == DELIVERY_PORTS[tag, device] else None)
                assert receiver_decode(2, 65535, port, raw) == expected
                checks += 1
            packets += 1
    print(f"Receiver binding: {packets:,} packets, {checks:,} port checks; accepted packets have exactly one port")


def syntax_and_local_tests():
    base = frame.encode(2, 1000, 2, 1, 777)
    count = 0
    for index in range(6):
        for value in range(256):
            raw = base.copy()
            raw[index] = value
            for port in PORTS:
                assert receiver_decode(2, 1000, port, raw) == oracle_receiver(2, 1000, port, raw)
                count += 1
    malformed = [None, "TK", {}, [], base + [0], base + base, base[1:]]
    malformed += [base[:size] for size in range(len(base))]
    for index in range(len(base)):
        for value in (-1, 256, True, "1", 1.0):
            raw = base.copy()
            raw[index] = value
            malformed.append(raw)
    for raw in malformed:
        for port in PORTS:
            assert receiver_decode(2, 1000, port, raw) is None
            count += 1
    invalid_ports = (-1, 3, 255, True, False, 0.0, "0", None)
    for port in invalid_ports:
        assert receiver_decode(2, 1000, port, base) is None
        count += 1
    for width in (1, 2, 4, 8, 64, 255):
        limit = 256 ** width - 1
        for tag in (1, 2, 3):
            for device in (0, 1):
                raw = frame.encode(width, limit, tag, device, limit)
                assert receiver_decode(width, limit, DELIVERY_PORTS[tag, device], raw) == (tag, device, limit)
                count += 1
    # A rejected network configuration does not disable typed local actions.
    for width, limit in ((0, 2), (256, 2), (1, 256), (2, 65536)):
        initial = activation.boot()
        local = frame.Local("begin", 0, 0)
        advanced = checked(width, limit, initial, local)
        assert advanced != initial
        assert advanced == finite.checked(limit, initial, local.event())
        for port in PORTS + invalid_ports:
            assert checked(width, limit, initial, Received(port, base)) == initial
        count += 1
    print(f"Syntax/context boundaries: {count:,} checks; ACK sender labels are not receive ports; invalid configuration does not block local progress")
    return malformed


def protocol_traces(malformed):
    seeds = {}
    edges = cuts = wrong_ports = 0
    for limit in range(4):
        events = []
        for epoch in range(1, limit + 1):
            owner = (epoch - 1) % 2
            events += activation.handoff(epoch, owner)
            events += [("send", 0, owner), ("entry", epoch, owner), ("exit", 0, owner)]
        events += [("begin", 0, 1), ("crash", 0, 0), ("commit", 0, 0)]
        actions = [represent(1, limit, event) for event in events]
        state = activation.boot()
        saved = [state]
        for event, action in zip(events, actions):
            if isinstance(action, Received):
                for port in PORTS:
                    if port != action.port:
                        assert checked(1, limit, state, Received(port, action.data)) == state
                        wrong_ports += 1
            direct = finite.checked(limit, state, event)
            state = checked(1, limit, state, action)
            assert state == direct
            saved.append(state)
            edges += 1
        assert finite.exhausted(limit, state)
        assert run(1, limit, actions) == state
        for cut in range(len(actions) + 1):
            for device in (0, 1):
                fault = [frame.Local("power", 0, device), frame.Local("crash"),
                         frame.Local("recover", 0, device)]
                run(1, limit, actions[:cut] + fault + actions[cut:])
                edges += len(actions) + len(fault)
                cuts += 1
        selected = (saved[0], saved[len(saved) // 2], state)
        for before in selected:
            for raw in malformed:
                for port in PORTS:
                    assert checked(1, limit, before, Received(port, raw)) == before
                    edges += 1
        seeds[limit] = selected
    print(f"Protocol: {edges:,} full-state/projection checks, {wrong_ports} wrong-port stutters and {cuts} crash cuts; finite bounds/exclusion/exhaustion preserved")
    return seeds


def bounded_protocol(seeds, depth_limit=2):
    count = edges = 0
    for limit, states in seeds.items():
        actions = [frame.Local("begin", 0, owner) for owner in (None, 0, 1)]
        actions += [frame.Local(kind) for kind in ("flush", "commit", "crash")]
        actions += [frame.Local(kind, 0, device)
                    for kind in sorted(activation.LOCAL | {"send", "exit"}) for device in (0, 1)]
        actions += [frame.Local("ack", epoch, device)
                    for epoch in range(limit + 2) for device in (0, 1)]
        for kind in frame.KIND_TAG:
            for epoch in range(limit + 2):
                for device in (0, 1):
                    raw = frame.represent(1, limit, (kind, epoch, device))
                    actions += [Received(port, raw) for port in PORTS]
        actions += [Received(0, []), Received(3, [84, 75, 1, 3, 0, 1, 0])]
        seen = {activation.canonical(s) for s in states}
        queue = deque((s, 0) for s in seen)
        while queue:
            state, depth = queue.popleft()
            if depth == depth_limit:
                continue
            for action in actions:
                nxt = activation.canonical(checked(1, limit, state, action))
                edges += 1
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append((nxt, depth + 1))
        count += len(seen)
    print(f"Depth-{depth_limit} receiver search: {count} states, {edges:,} transitions")


def boundary_witnesses():
    # Unbound decoding loses receive context even when the syntax is valid.
    state = finite.reach_epoch(1, 1)
    state = finite.checked(1, state, ("send", 0, 0))
    state = finite.checked(1, state, ("begin", 0, 1))
    assert finite.exhausted(1, state)
    packet = frame.encode(1, 1, 1, 0, 1)
    assert frame.decode(1, 1, packet) == (1, 0, 1)
    assert checked(1, 1, state, Received(2, packet)) == state
    unbound = frame.datagram_step(1, 1, state, packet)
    assert unbound.engine.inside == {0}
    assert not state.engine.inside
    # This exhibits a routing-context failure, not simultaneous occupancy.
    assert len(unbound.engine.inside) == 1
    # A syntactically accepted ACK still cannot invent the sender's history.
    fresh = finite.checked(2, activation.boot(), ("begin", 0, 0))
    for device in (0, 1):
        ack = frame.encode(1, 2, 3, device, 1)
        assert receiver_decode(1, 2, 0, ack) == (3, device, 1)
        assert checked(1, 2, fresh, Received(0, ack)) == fresh
        for port in (1, 2):
            assert receiver_decode(1, 2, port, ack) is None
    print("Negative/boundary witnesses: unbound parser loses receive context; accepted ACK does not establish sender authenticity or create ACK history")


def seeded_tests():
    rng = Random(20261004)
    parser_cases = transitions = 0
    for _ in range(10000):
        width = rng.choice((1, 2, 4, 8, 64, 255))
        limit = rng.randrange(256 ** width)
        raw = frame.encode(width, limit, rng.choice((1, 2, 3)),
                           rng.randrange(2), rng.randrange(limit + 1))
        if rng.randrange(2):
            raw[rng.randrange(len(raw))] = rng.randrange(258)
        port = rng.randrange(5)
        assert receiver_decode(width, limit, port, raw) == oracle_receiver(width, limit, port, raw)
        parser_cases += 1
    for limit in range(4):
        for _ in range(12):
            actions = []
            for epoch in range(1, limit + 3):
                for event in activation.handoff(epoch, rng.choice((None, 0, 1))):
                    noise = frame.represent(1, limit, (rng.choice(tuple(frame.KIND_TAG)),
                                                      rng.randrange(limit + 2), rng.randrange(2)))
                    actions.append(Received(rng.randrange(4), noise))
                    if rng.randrange(4) == 0:
                        actions.append(frame.Local(rng.choice(("crash", "power", "recover")),
                                                   0, rng.randrange(2)))
                    actions.append(represent(1, limit, event))
            run(1, limit, actions)
            transitions += len(actions)
    print(f"Seeded tests: {parser_cases:,} parser/context cases and {transitions:,} exact projected transitions")


def main():
    parser_binding_tests()
    malformed = syntax_and_local_tests()
    seeds = protocol_traces(malformed)
    bounded_protocol(seeds)
    boundary_witnesses()
    seeded_tests()
    print("PASS: receiver-context binding and finite-protocol projection; not cryptographic authentication or real transport verification")


if __name__ == "__main__":
    main()
