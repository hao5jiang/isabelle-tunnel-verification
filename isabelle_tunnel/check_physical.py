"""Independent physical/provenance/restart tests; not certified extraction."""
from dataclasses import dataclass, replace
from random import Random

from check_delayed import set_item, valid
from check_numbered import Numbered, numbered_react


@dataclass(frozen=True)
class System:
    machine: Numbered = Numbered()
    era: int = 0
    inside: tuple = (False, False)
    certificates: frozenset = frozenset()


@dataclass(frozen=True)
class Event:
    kind: str
    owner: int = -1
    era: int = -1
    packet: tuple = ()


def step(s, e):
    phase, owner = s.machine.core.stage
    g = s.machine.generation
    if e.kind == "request":
        return replace(s, machine=numbered_react(s.machine, ("enqueue", e.owner, -1)))
    if e.kind == "poll":
        return replace(s, machine=numbered_react(s.machine, ("schedule", -1, -1)))
    if e.kind == "enter" and (phase, owner) == ("entering", e.owner):
        return replace(s, inside=set_item(s.inside, owner, True))
    if e.kind == "leave" and (phase, owner) == ("leaving", e.owner):
        return replace(s, inside=set_item(s.inside, owner, False))
    if e.kind == "sense_entry" and (phase, owner) == ("entering", e.owner) and s.inside[owner]:
        return replace(s, certificates=s.certificates | {(s.era, ("entry", owner, g))})
    if e.kind == "sense_exit" and (phase, owner) == ("leaving", e.owner) and not s.inside[owner]:
        return replace(s, certificates=s.certificates | {(s.era, ("exit", owner, g))})
    if e.kind == "receive" and e.era == s.era and (e.era, e.packet) in s.certificates:
        return replace(s, machine=numbered_react(s.machine, e.packet))
    if e.kind == "restart":
        return replace(s, era=s.era+1)
    return s


def invariant(s):
    c, g = s.machine.core, s.machine.generation
    valid(c)
    assert not all(s.inside)
    for i in range(2):
        assert not s.inside[i] or c.zone[i]
        assert c.stage != ("occupied", i) or s.inside[i]
        if c.stage == ("entering", i) and (s.era, ("entry", i, g)) in s.certificates:
            assert s.inside[i]
        if c.stage == ("leaving", i) and (s.era, ("exit", i, g)) in s.certificates:
            assert not s.inside[i]
        if (s.era, ("exit", i, g)) in s.certificates:
            assert c.stage not in (("entering", i), ("occupied", i))
    for e, p in s.certificates:
        assert e <= s.era and p[0] in ("entry", "exit") and p[2] <= g


def checked(s, e):
    result = step(s, e)
    invariant(result)
    assert result.era >= s.era
    if e.kind == "receive" and (e.era != s.era or (e.era, e.packet) not in s.certificates):
        assert result == s
    if e.kind == "restart":
        assert result.machine == s.machine and result.inside == s.inside
    return result


def deliver(s, kind, owner):
    return checked(s, Event("receive", era=s.era, packet=(kind, owner, s.machine.generation)))


def active_a():
    s = System()
    for e in (Event("request", 0), Event("poll"), Event("enter", 0), Event("sense_entry", 0)):
        s = checked(s, e)
    s = deliver(s, "entry", 0)
    return checked(s, Event("poll"))


def main():
    s = checked(checked(System(), Event("request", 0)), Event("poll"))
    assert checked(s, Event("sense_entry", 0)) == s
    assert deliver(s, "entry", 0) == s
    s = active_a()
    assert checked(s, Event("sense_exit", 0)) == s
    assert deliver(s, "exit", 0) == s
    print("PASS: correct-number invented confirmations cannot enter trusted provenance")

    # The abstract authenticated gate is necessary: bypassing it can cause collision.
    forged = replace(s, machine=numbered_react(s.machine, ("exit", 0, s.machine.generation)))
    for e in (Event("request", 1), Event("poll"), Event("enter", 1)):
        forged = step(forged, e)
    assert forged.inside == (True, True)
    print("PASS: bypass mutation admits a second train while the first is physically inside")

    # Keep old traffic in the channel across a restart, then re-observe the plant.
    s = checked(s, Event("leave", 0))
    s = checked(s, Event("sense_exit", 0))
    old = Event("receive", era=s.era, packet=("exit", 0, s.machine.generation))
    saved = s.machine
    s = checked(s, Event("restart"))
    assert s.machine == saved and checked(s, old) == s
    assert deliver(s, "exit", 0) == s
    s = checked(s, Event("sense_exit", 0))
    s = deliver(s, "exit", 0)
    assert s.machine.core.stage[0] == "ready"
    print("PASS: active restart rejects old-era traffic; fresh observation resumes release")

    s = active_a()
    s = checked(s, Event("restart"))
    s = checked(s, Event("request", 1))
    s = checked(s, Event("poll"))
    assert s.inside == (True, False) and s.machine.core.zone == (True, False)
    assert s.machine.core.stage == ("leaving", 0)
    print("PASS: restart while physically occupied retains A's reservation and blocks B")

    # A checkpoint-erasing reboot is outside the safe restart model.
    s = active_a()
    erased = replace(s, machine=Numbered(), era=s.era+1)
    assert erased.inside[0] and not erased.machine.core.zone[0]
    print("PASS: checkpoint-erasing reboot exposes the lost-reservation counterexample")

    rng = Random(20261003)
    s = System()
    kinds = ("request", "poll", "poll", "enter", "leave", "sense_entry", "sense_exit",
             "receive", "receive", "restart")
    restarts = 0
    for _ in range(20000):
        kind = rng.choice(kinds)
        e = Event(kind, rng.randrange(2))
        if kind == "receive":
            if s.certificates and rng.randrange(2):
                era, packet = rng.choice(sorted(s.certificates))
            else:
                era = max(0, s.era+rng.choice((-1, 0, 0, 1)))
                packet = (rng.choice(("entry", "exit")), rng.randrange(2), s.machine.generation)
            e = Event(kind, era=era, packet=packet)
        if kind == "restart":
            restarts += 1
        s = checked(s, e)
    print(f"PASS: 20000 mixed system transitions including {restarts} state-preserving restarts")

    target = s.machine.core.received
    count = 0
    while s.machine.core.served != target or s.machine.core.stage[0] != "ready":
        phase, owner = s.machine.core.stage
        if phase == "entering":
            s = checked(s, Event("enter", owner))
            s = checked(s, Event("sense_entry", owner))
            s = deliver(s, "entry", owner)
        elif phase == "leaving":
            s = checked(s, Event("leave", owner))
            s = checked(s, Event("sense_exit", owner))
            s = deliver(s, "exit", owner)
        else:
            s = checked(s, Event("poll"))
        count += 1
        assert count < 100000
    assert not any(s.inside) and s.machine.core.pending == (0, 0)
    print(f"PASS: cooperative restart-free suffix drains {sum(target)} requests and leaves both outside")


if __name__ == "__main__":
    main()
