"""Independent asynchronous fencing tests, not certified code extraction.

Authentic packet histories permit replay and nondelivery; endpoint floors and
physical state survive controller crashes. Actuation checks the floor locally.
"""
from collections import deque
from dataclasses import dataclass, replace
from random import Random

import check_journal as journal

TRAINS = (0, 1)


@dataclass(frozen=True)
class System:
    log: journal.Journal
    stopped: bool = True
    floors: tuple = (0, 0)
    commands: frozenset = frozenset()
    requests: frozenset = frozenset()
    acknowledgements: frozenset = frozenset()
    received: frozenset = frozenset()
    inside: frozenset = frozenset()


def boot():
    return System(journal.boot((0, None)))


def step(s, event):
    kind, k, i = event
    epoch, owner = journal.restore(s.log)
    if kind == "begin":
        return replace(s, log=journal.step(s.log, ("prepare", (epoch + 1, i))),
                       stopped=True, requests=s.requests | {(epoch + 1, t) for t in TRAINS})
    if kind == "flush":
        return replace(s, log=journal.step(s.log, ("flush", None)))
    if kind == "commit":
        candidate = journal.inactive(s.log)
        if candidate.kind == "complete":
            new_epoch, _ = candidate.value
            if (s.log.pending and s.stopped and new_epoch == epoch + 1
                    and all((new_epoch, t) in s.received for t in TRAINS)):
                return replace(s, log=journal.step(s.log, ("commit", None)), stopped=False)
    if kind == "send" and not s.stopped and owner == i:
        return replace(s, commands=s.commands | {(epoch, i)})
    if kind == "entry" and (k, i) in s.commands and s.floors[i] <= k:
        return replace(s, inside=s.inside | {i})
    if kind == "fence" and (k, i) in s.requests:
        floors = list(s.floors)
        floors[i] = max(floors[i], k)
        return replace(s, floors=tuple(floors))
    if kind == "ack" and (k, i) in s.requests and k <= s.floors[i] and i not in s.inside:
        return replace(s, acknowledgements=s.acknowledgements | {(k, i)})
    if kind == "receive" and (k, i) in s.acknowledgements:
        return replace(s, received=s.received | {(k, i)})
    if kind == "exit":
        return replace(s, inside=s.inside - {i})
    if kind == "crash":
        return replace(s, log=journal.step(s.log, ("crash", None)), stopped=True, received=frozenset())
    return s


def effective(s):
    return {i for k, i in s.commands if s.floors[i] <= k}


def invariant(s):
    selected = journal.selected(s.log)
    assert selected.kind == "complete" and selected.value == s.log.committed[-1]
    epoch, owner = selected.value
    assert all(epoch <= floor for floor in s.floors)
    assert all(k <= epoch and (k != epoch or owner == i) for k, i in s.commands)
    assert all(owner == i for i in s.inside)
    assert all(k <= s.floors[i] and (k <= epoch or i not in s.inside)
               for k, i in s.acknowledgements)
    assert s.received <= s.acknowledgements
    assert len(s.inside) <= 1
    assert all(owner == i for i in effective(s))
    if all((epoch + 1, t) in s.received for t in TRAINS):
        assert not s.inside and not effective(s)


def checked(s, event):
    nxt = step(s, event)
    invariant(nxt)
    assert all(a <= b for a, b in zip(s.floors, nxt.floors))
    assert journal.restore(s.log)[0] <= journal.restore(nxt.log)[0]
    assert s.commands <= nxt.commands  # No proof by erasing delayed commands.
    if event[0] == "crash":
        assert nxt.floors == s.floors and nxt.inside == s.inside
        assert nxt.stopped and not nxt.received
    if journal.restore(nxt.log)[0] > journal.restore(s.log)[0]:
        assert not s.inside and not effective(s)
    return nxt


def canonical(s):
    return replace(s, log=replace(s.log, committed=(s.log.committed[-1],)))


def handoff(epoch, owner):
    return [("begin", 0, owner), ("flush", 0, 0)] + [
        (kind, epoch, t) for t in TRAINS for kind in ("fence", "ack", "receive")
    ] + [("commit", 0, 0)]


def run(events, s=None):
    s = boot() if s is None else s
    for event in events:
        s = checked(s, event)
    return s


def targeted():
    a = run(handoff(1, 0) + [("send", 0, 0)])
    assert a.commands == {(1, 0)} and not a.inside
    # A's delayed command survives; fencing prevents it from taking effect.
    b = run(handoff(2, 1), a)
    assert b.commands == a.commands
    assert step(b, ("entry", 1, 0)) == b
    b = run([("send", 0, 1), ("entry", 2, 1), ("entry", 1, 0)], b)
    assert b.inside == {1}
    restarted = run(handoff(2, 1) + [("crash", 0, 0), ("entry", 1, 0)]
                    + handoff(3, 1) + [("send", 0, 1), ("entry", 3, 1), ("entry", 1, 0)], a)
    assert restarted.inside == {1} and (1, 0) in restarted.commands
    assert journal.restore(restarted.log) == (3, 1)
    # Occupied endpoint cannot acknowledge until it actually exits.
    occupied = run([("entry", 1, 0)], a)
    busy = run(handoff(2, 1), occupied)
    assert journal.restore(busy.log) == (1, 0) and busy.inside == {0}
    cleared = run([("exit", 0, 0), ("ack", 2, 0), ("receive", 2, 0), ("commit", 0, 0)], busy)
    assert journal.restore(cleared.log) == (2, 1)
    # Crash aborts prepared data; repeated commit cannot activate the orphan.
    prep = run(handoff(2, 1)[:-1], a)
    crashed = run([("crash", 0, 0), ("receive", 2, 0), ("receive", 2, 1), ("commit", 0, 0)], prep)
    assert journal.restore(crashed.log) == (1, 0) and crashed.stopped
    # Retrying the uncommitted epoch may use its old genuine acknowledgements.
    retry = run([("begin", 0, None), ("flush", 0, 0), ("commit", 0, 0)], crashed)
    assert journal.restore(retry.log) == (2, None)
    # Once epoch 2 is committed, its acknowledgements do not authorize epoch 3.
    stale = run([("begin", 0, 0), ("flush", 0, 0), ("commit", 0, 0)], cleared)
    assert journal.restore(stale.log) == (2, 1)
    # Forge an acknowledgement at the transport boundary: normal delivery rejects it.
    initial = boot()
    assert step(initial, ("receive", 1, 0)) == initial
    # A floor reset is deliberately OUTSIDE the supported protocol.
    reset = replace(b, floors=(0, b.floors[1]))
    collision = step(reset, ("entry", 1, 0))
    assert collision.inside == {0, 1}
    # Bypass the local fence gate, also outside the supported protocol.
    assert b.commands >= {(1, 0), (2, 1)}
    collision = replace(b, inside=b.inside | {0})
    assert collision.inside == {0, 1}
    trace = handoff(1, 0) + [("send", 0, 0), ("entry", 1, 0), ("exit", 0, 0)] + handoff(2, 1)
    for cut in range(len(trace) + 1):
        run(trace[:cut] + [("crash", 0, 0)] + trace[cut:])
    print(f"Targeted: {len(trace)+1} crash cuts; delayed/replayed entry, busy exit, stale ack, retry, two unsafe mutations")
    return a, occupied, prep


def bounded_search(seeds, depth_limit=6):
    # Explicitly depth-bounded, seeded from three reachable active states.
    events = [("begin", 0, t) for t in (None, 0, 1)]
    events += [(kind, 0, 0) for kind in ("flush", "commit", "crash")]
    events += [(kind, 0, t) for kind in ("send", "exit") for t in TRAINS]
    events += [(kind, k, t) for kind in ("entry", "fence", "ack", "receive")
               for k in (1, 2, 3) for t in TRAINS]
    seen = {canonical(s) for s in seeds}
    todo = deque((s, 0) for s in seen)
    edges = 0
    while todo:
        s, depth = todo.popleft()
        if depth == depth_limit:
            continue
        for event in events:
            nxt = canonical(checked(s, event))
            edges += 1
            if nxt not in seen:
                seen.add(nxt)
                todo.append((nxt, depth + 1))
    print(f"Depth-{depth_limit} search from 3 reachable seeds: {len(seen)} states, {edges} transitions")


def seeded_runs():
    rng = Random(20261003)
    transitions = 0
    commits = 0
    for _ in range(100):
        s = boot()
        for cycle in range(20):
            epoch = journal.restore(s.log)[0] + 1
            for planned in handoff(epoch, rng.choice((None, 0, 1))):
                for _ in range(3):
                    g, _ = journal.restore(s.log)
                    packet_epoch = rng.choice((max(0, g-1), g, g+1))
                    event = (rng.choice(("crash", "entry", "send", "exit", "fence", "ack", "receive", "commit")),
                             packet_epoch, rng.choice(TRAINS))
                    before = journal.restore(s.log)[0]
                    s = canonical(checked(s, event))
                    commits += journal.restore(s.log)[0] > before
                    transitions += 1
                before = journal.restore(s.log)[0]
                s = canonical(checked(s, planned))
                commits += journal.restore(s.log)[0] > before
                transitions += 1
        # Cooperative suffix demonstrates recoverability without asserting fairness.
        s = run([("exit", 0, 0), ("exit", 0, 1)], s)
        target_epoch = journal.restore(s.log)[0] + 1
        s = run(handoff(target_epoch, 1) + [("send", 0, 1), ("entry", target_epoch, 1)], s)
        assert s.inside == {1}
    print(f"Seeded: {transitions} mixed transitions, {commits} commits, 100 cooperative recovery suffixes")


def main():
    seeds = targeted()
    bounded_search(seeds)
    seeded_runs()


if __name__ == "__main__":
    main()
