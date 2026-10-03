"""Independent packet-layer tests, not Isabelle-certified code extraction."""
from dataclasses import dataclass, replace
from random import Random

from check_delayed import Controller, react, valid


@dataclass(frozen=True)
class Numbered:
    core: Controller = Controller()
    generation: int = 0


def decode(s, packet):
    kind, owner, number = packet
    if kind == "enqueue":
        return ("request", owner)
    if kind == "schedule":
        return ("poll", -1)
    if number == s.generation:
        if kind == "entry" and s.core.stage == ("entering", owner):
            return ("entry", owner)
        if kind == "exit" and s.core.stage == ("leaving", owner):
            return ("exit", owner)
    return None


def numbered_react(s, packet):
    event = decode(s, packet)
    if event is None:
        return s
    c = react(s.core, event)
    admitted = s.core.stage[0] == "ready" and c.stage[0] != "ready"
    return Numbered(c, s.generation + int(admitted))


def abstract_input(s, packet):
    event = decode(s, packet)
    if event is not None:
        return event
    stage, owner = s.core.stage
    return ("entry", 1-owner if stage == "entering" else 0)


def checked(s, p):
    nxt = numbered_react(s, p)
    valid(nxt.core)
    assert nxt.core == react(s.core, abstract_input(s, p))
    assert nxt.generation in (s.generation, s.generation+1)
    if p[0] in ("entry", "exit"):
        assert numbered_react(nxt, p) == nxt
        if p[2] != s.generation:
            assert nxt == s
    return nxt


def main():
    schedule = ("schedule", -1, -1)
    s = Numbered()
    # Two journeys of the same train expose a same-phase replay in the old model.
    for p in (("enqueue", 0, -1), schedule, ("entry", 0, 1),
              schedule, ("exit", 0, 1), ("enqueue", 0, -1), schedule):
        s = checked(s, p)
    assert s.core.stage == ("entering", 0) and s.generation == 2
    assert react(s.core, ("entry", 0)).served[0] == 2
    assert checked(s, ("entry", 0, 1)) == s
    assert checked(s, ("entry", 0, 3)) == s
    assert checked(s, ("entry", 1, 2)) == s
    assert checked(s, ("exit", 0, 2)) == s
    s = checked(s, ("entry", 0, 2))
    assert s.core.served == (2, 0)
    assert checked(s, ("entry", 0, 2)) == s
    s = checked(s, schedule)
    assert checked(s, ("exit", 0, 1)) == s
    s = checked(s, ("exit", 0, 2))
    assert s.core.stage[0] == "ready"
    print("PASS: old-model replay witness; stale, future, wrong-owner, wrong-kind rejection")
    print("PASS: entry/exit duplicates do not repeat their effects")

    # The controller cannot infer physical truth from a syntactically correct packet.
    s = checked(checked(s, ("enqueue", 0, -1)), schedule)
    forged = ("entry", 0, s.generation)
    assert checked(s, forged).core.served[0] == s.core.served[0]+1
    print("PASS: explicit boundary: current-ID packet is accepted without authentication")

    rng = Random(20261002)
    s = Numbered()
    for _ in range(20000):
        kind = rng.choice(("enqueue", "schedule", "entry", "exit"))
        p = (kind, rng.randrange(2), max(0, s.generation+rng.choice((-2, -1, 0, 0, 1))))
        s = checked(s, p)
    print("PASS: 20000 seeded packet transitions preserve refinement and invariants")

    # A responsive suffix drains the finite received batch despite stale noise.
    target = s.core.received
    steps = 0
    while s.core.served != target or s.core.stage[0] != "ready":
        stage, owner = s.core.stage
        p = {"entering": ("entry", owner, s.generation),
             "leaving": ("exit", owner, s.generation)}.get(stage, schedule)
        s = checked(s, p)
        if s.generation:
            for kind in ("entry", "exit"):
                stale = (kind, 0, s.generation-1)
                assert checked(s, stale) == s
        steps += 1
        assert steps < 100000
    assert s.core.pending == (0, 0)
    print(f"PASS: responsive suffix drains {sum(target)} requests; counters {s.core.served}")


if __name__ == "__main__":
    main()
