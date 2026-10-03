"""Independent finite-identifier fail-stop tests; not certified extraction.

The caps bound identifiers, not request counters or certificate storage. A lock
blocks controller processing, while previously authorized plant motion remains
possible. No recovery from a lock or unconditional service property is modeled.
"""
from dataclasses import dataclass, replace
from itertools import product
from random import Random

import check_physical as physical
from check_physical import Event, System


@dataclass(frozen=True)
class Bounded:
    system: System = System()
    locked: bool = False


def step(g_cap, e_cap, event, state):
    """Stop before identifier reuse without freezing the physical plant."""
    s = state.system
    if state.locked:
        if event.kind in ("enter", "leave"):
            return replace(state, system=physical.step(s, event))
        return state
    if event.kind == "restart" and s.era >= e_cap:
        return replace(state, locked=True)
    if (event.kind == "poll" and s.machine.core.stage[0] == "ready"
            and s.machine.generation >= g_cap):
        return replace(state, locked=True)
    return replace(state, system=physical.step(s, event))


def checked(g_cap, e_cap, state, event):
    physical.invariant(state.system)
    assert 0 <= state.system.machine.generation <= g_cap
    assert 0 <= state.system.era <= e_cap
    nxt = step(g_cap, e_cap, event, state)
    physical.invariant(nxt.system)
    assert state.system.machine.generation <= nxt.system.machine.generation <= g_cap
    assert state.system.era <= nxt.system.era <= e_cap
    assert not state.locked or nxt.locked
    if state.locked:
        assert nxt.system.machine == state.system.machine
        assert nxt.system.era == state.system.era
        assert nxt.system.certificates == state.system.certificates
        if event.kind not in ("enter", "leave"):
            assert nxt == state
    if not state.locked and nxt.locked:
        assert nxt.system == state.system
    if event.kind == "receive":
        if (event.era != state.system.era
                or (event.era, event.packet) not in state.system.certificates):
            assert nxt == state
    return nxt


def run(g_cap, e_cap, state, events):
    for event in events:
        state = checked(g_cap, e_cap, state, event)
    return state


def deliver(g_cap, e_cap, state, kind, owner):
    s = state.system
    return checked(g_cap, e_cap, state, Event(
        "receive", era=s.era, packet=(kind, owner, s.machine.generation)))


def finish_visit(g_cap, e_cap, state, owner):
    assert state.system.machine.core.stage == ("entering", owner)
    state = run(g_cap, e_cap, state, (Event("enter", owner), Event("sense_entry", owner)))
    state = deliver(g_cap, e_cap, state, "entry", owner)
    state = run(g_cap, e_cap, state, (Event("poll"), Event("leave", owner), Event("sense_exit", owner)))
    return deliver(g_cap, e_cap, state, "exit", owner)


def test_caps_and_retention():
    for g_cap, e_cap in product(range(4), repeat=2):
        state = Bounded()
        for journey in range(g_cap):
            owner = journey % 2
            state = run(g_cap, e_cap, state, (Event("request", owner), Event("poll")))
            assert not state.locked and state.system.machine.generation == journey + 1
            # Reaching the cap must not interrupt the current visit.
            state = checked(g_cap, e_cap, state, Event("poll"))
            assert not state.locked
            state = finish_visit(g_cap, e_cap, state, owner)
            assert not state.locked and state.system.machine.core.stage[0] == "ready"
        state = checked(g_cap, e_cap, state, Event("request", 0))
        checkpoint = state.system
        state = checked(g_cap, e_cap, state, Event("poll"))
        assert state.locked and state.system == checkpoint
        assert state.system.machine.core.pending[0] == 1
        for _ in range(100):
            state = checked(g_cap, e_cap, state, Event("poll"))
        assert state.system == checkpoint
        # Incoming requests after the lock are not accepted into this model.
        assert checked(g_cap, e_cap, state, Event("request", 1)) == state

        state = Bounded()
        for era in range(1, e_cap + 1):
            state = checked(g_cap, e_cap, state, Event("restart"))
            assert not state.locked and state.system.era == era
        checkpoint = state.system
        state = checked(g_cap, e_cap, state, Event("restart"))
        assert state.locked and state.system == checkpoint
    print("PASS: all 16 cap pairs from 0..3 stop before reuse; active visits finish at the generation cap")
    print("PASS: accepted requests remain recorded at lock; pending service can stall permanently")


def test_provenance_and_plant():
    state = run(3, 3, Bounded(), (Event("request", 0), Event("poll")))
    assert deliver(3, 3, state, "entry", 0) == state
    state = run(3, 3, state, (Event("enter", 0), Event("sense_entry", 0)))
    old = Event("receive", era=state.system.era, packet=("entry", 0, state.system.machine.generation))
    state = checked(3, 3, state, Event("restart"))
    assert checked(3, 3, state, old) == state
    assert deliver(3, 3, state, "entry", 0) == state
    state = checked(3, 3, state, Event("sense_entry", 0))
    state = deliver(3, 3, state, "entry", 0)
    assert state.system.machine.core.stage == ("occupied", 0)
    print("PASS: unissued and old-era packets remain rejected; fresh sensing restores accepted confirmation")

    state = run(1, 0, Bounded(), (Event("request", 0), Event("poll"), Event("restart")))
    assert state.locked and state.system.inside == (False, False)
    state = checked(1, 0, state, Event("enter", 0))
    assert state.system.inside == (True, False)
    assert checked(1, 0, state, Event("enter", 1)) == state
    assert checked(1, 0, state, Event("sense_entry", 0)) == state

    state = run(1, 0, Bounded(), (Event("request", 0), Event("poll"), Event("enter", 0), Event("sense_entry", 0)))
    state = deliver(1, 0, state, "entry", 0)
    state = run(1, 0, state, (Event("poll"), Event("restart")))
    assert state.locked and state.system.inside == (True, False)
    state = checked(1, 0, state, Event("leave", 0))
    assert state.system.inside == (False, False)
    assert state.system.machine.core.zone == (True, False)
    print("PASS: locked processing preserves reservation while authorized entry/exit motion remains possible")

    state = run(1, 0, Bounded(), (Event("request", 0), Event("poll"), Event("enter", 0), Event("sense_entry", 0)))
    state = deliver(1, 0, state, "entry", 0)
    state = checked(1, 0, state, Event("restart"))
    assert state.locked and state.system.machine.core.stage == ("occupied", 0)
    checkpoint = state
    state = run(1, 0, state, (Event("poll"), Event("leave", 0), Event("sense_exit", 0)))
    assert state == checkpoint and state.system.inside == (True, False)
    assert state.system.machine.core.zone == (True, False)
    print("PASS: era-cap lock during Occupied retains reservation but does not guarantee physical clearance")


def test_active_clearance_at_cap():
    for g_cap, e_cap in product(range(1, 4), range(4)):
        entering = Bounded()
        for _ in range(g_cap - 1):
            entering = run(g_cap, e_cap, entering, (Event("request", 0), Event("poll")))
            entering = finish_visit(g_cap, e_cap, entering, 0)
        entering = run(g_cap, e_cap, entering, (Event("request", 0), Event("poll")))
        occupied = run(g_cap, e_cap, entering, (Event("enter", 0), Event("sense_entry", 0)))
        occupied = deliver(g_cap, e_cap, occupied, "entry", 0)
        leaving = checked(g_cap, e_cap, occupied, Event("poll"))
        for state, phase in ((entering, "entering"), (occupied, "occupied"), (leaving, "leaving")):
            assert not state.locked and state.system.machine.generation == g_cap
            assert state.system.machine.core.stage == (phase, 0)
            if phase == "entering":
                state = finish_visit(g_cap, e_cap, state, 0)
            else:
                if phase == "occupied":
                    state = checked(g_cap, e_cap, state, Event("poll"))
                state = run(g_cap, e_cap, state, (Event("leave", 0), Event("sense_exit", 0)))
                state = deliver(g_cap, e_cap, state, "exit", 0)
            assert not state.locked and state.system.machine.generation == g_cap
            assert state.system.inside == (False, False)
            assert state.system.machine.core.stage[0] == "ready"
            assert checked(g_cap, e_cap, state, Event("poll")).locked
    print("PASS: unlocked Entering/Occupied/Leaving at the generation cap each clear without a restart; next Ready poll locks")


def test_random_traces():
    rng = Random(20261004)
    kinds = ("request", "poll", "poll", "enter", "leave", "sense_entry", "sense_exit", "receive", "receive", "restart")
    transitions = 0
    for g_cap, e_cap in product(range(4), repeat=2):
        # Fresh sessions prevent early fail-stop from dominating the sample.
        for _ in range(100):
            state = Bounded()
            for _ in range(100):
                kind = rng.choice(kinds)
                event = Event(kind, rng.randrange(2))
                s = state.system
                if kind == "receive":
                    if s.certificates and rng.randrange(2):
                        era, packet = rng.choice(sorted(s.certificates))
                    else:
                        era = max(0, s.era + rng.choice((-1, 0, 0, 1)))
                        packet = (rng.choice(("entry", "exit")), rng.randrange(2),
                                  max(0, s.machine.generation + rng.choice((-1, 0, 1))))
                    event = Event(kind, era=era, packet=packet)
                state = checked(g_cap, e_cap, state, event)
                transitions += 1
    print(f"PASS: {transitions} seeded transitions preserve physical invariants and bounded monotone identifiers")


def naive_wrap_step(cap, system, event):
    """Deliberately unsafe mutation: retain certificates and reuse identifiers."""
    nxt = physical.step(system, event)
    if nxt.machine.generation > cap:
        nxt = replace(nxt, machine=replace(
            nxt.machine, generation=1 + (nxt.machine.generation - 1) % cap))
    return nxt


def test_wrap_counterexample():
    safe = run(1, 0, Bounded(), (Event("request", 0), Event("poll")))
    safe = finish_visit(1, 0, safe, 0)
    old_exit = Event("receive", era=0, packet=("exit", 0, 1))
    assert (old_exit.era, old_exit.packet) in safe.system.certificates

    # The unchanged trusted gate sees a genuinely issued certificate, but the
    # mutated second visit has reused its identifier in the same era.
    unsafe = safe.system
    for event in (Event("request", 0), Event("poll"), Event("enter", 0),
                  Event("sense_entry", 0), Event("receive", era=0, packet=("entry", 0, 1)),
                  Event("poll")):
        unsafe = naive_wrap_step(1, unsafe, event)
    assert unsafe.machine.generation == 1
    assert unsafe.inside == (True, False) and unsafe.machine.core.stage == ("leaving", 0)
    assert (old_exit.era, old_exit.packet) in unsafe.certificates
    unsafe = naive_wrap_step(1, unsafe, old_exit)
    assert unsafe.inside == (True, False) and unsafe.machine.core.stage[0] == "ready"
    for event in (Event("request", 1), Event("poll"), Event("enter", 1)):
        unsafe = naive_wrap_step(1, unsafe, event)
    assert unsafe.inside == (True, True)

    # The real wrapper stops the second admission before an identifier repeats.
    safe = run(1, 0, safe, (Event("request", 0), Event("poll"), old_exit,
                           Event("enter", 0), Event("request", 1), Event("poll"), Event("enter", 1)))
    assert safe.locked and safe.system.inside == (False, False)
    assert safe.system.machine.core.pending == (1, 0)
    print("PASS: naive generation wrap replays an authentic old exit and causes collision; fail-stop prevents reuse")


def main():
    test_caps_and_retention()
    test_provenance_and_plant()
    test_active_clearance_at_cap()
    test_random_traces()
    test_wrap_counterexample()


if __name__ == "__main__":
    main()
