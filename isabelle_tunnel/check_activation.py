"""Independent tests for durable floor commit followed by local activation.

This is an executable model, not certified extraction or a hardware test.
While offline, the engine floor is an abstract shadow of the previous gate;
entry and acknowledgement processing are disabled until recovery reloads disk.
"""
from collections import deque
from dataclasses import dataclass, replace
from random import Random

import check_fenced as fenced
import check_journal as journal

TRAINS = (0, 1)
LOCAL = {"store_flush", "store_commit", "activate", "power", "recover"}


@dataclass(frozen=True)
class System:
    engine: fenced.System
    logs: tuple
    awake: tuple = (True, True)


def boot():
    return System(fenced.boot(), (journal.boot(0), journal.boot(0)))


def set_item(items, i, value):
    return items[:i] + (value,) + items[i + 1:]


def disk(s, i):
    return journal.restore(s.logs[i])


def activation_allowed(s, i):
    value = disk(s, i)
    if value is None:
        return False
    floor = s.engine.floors[i]
    return value >= floor and (value == floor or (value, i) in s.engine.requests)


def step(s, event):
    kind, k, i = event
    if kind == "fence":
        if s.awake[i] and (k, i) in s.engine.requests:
            log = journal.step(s.logs[i], ("prepare", max(k, disk(s, i))))
            return replace(s, logs=set_item(s.logs, i, log))
        return s
    if kind == "store_flush":
        if s.awake[i]:
            log = journal.step(s.logs[i], ("flush", None))
            return replace(s, logs=set_item(s.logs, i, log))
        return s
    if kind == "store_commit":
        record = journal.inactive(s.logs[i])
        if (s.awake[i] and s.logs[i].pending and record.kind == "complete"
                and disk(s, i) <= record.value
                and (record.value, i) in s.engine.requests):
            log = journal.step(s.logs[i], ("commit", None))
            return replace(s, logs=set_item(s.logs, i, log))
        return s
    if kind == "activate":
        if s.awake[i] and activation_allowed(s, i):
            engine = fenced.step(s.engine, ("fence", disk(s, i), i))
            return replace(s, engine=engine)
        return s
    if kind == "power":
        log = journal.step(s.logs[i], ("crash", None))
        return replace(s, logs=set_item(s.logs, i, log),
                       awake=set_item(s.awake, i, False))
    if kind == "recover":
        if activation_allowed(s, i):
            engine = fenced.step(s.engine, ("fence", disk(s, i), i))
            return replace(s, engine=engine, awake=set_item(s.awake, i, True))
        return s
    if kind in {"entry", "ack"} and not s.awake[i]:
        return s
    return replace(s, engine=fenced.step(s.engine, event))


def invariant(s):
    fenced.invariant(s.engine)
    for i in TRAINS:
        log = s.logs[i]
        assert log.committed
        assert journal.selected(log) == journal.Slot("complete", log.committed[-1])
        assert s.engine.floors[i] <= disk(s, i)
        assert disk(s, i) == 0 or (disk(s, i), i) in s.engine.requests


def abstract_step(s, event):
    """Projection to the earlier message model: a step or a stutter."""
    kind, k, i = event
    if kind in {"activate", "recover"}:
        enabled = kind == "recover" or s.awake[i]
        if enabled and activation_allowed(s, i):
            return fenced.step(s.engine, ("fence", disk(s, i), i))
        return s.engine
    if kind == "fence" or kind in LOCAL:
        return s.engine
    if kind in {"entry", "ack"} and not s.awake[i]:
        return s.engine
    return fenced.step(s.engine, event)


def checked(s, event):
    nxt = step(s, event)
    invariant(nxt)
    assert nxt.engine == abstract_step(s, event)
    assert all(s.engine.floors[i] <= nxt.engine.floors[i] for i in TRAINS)
    assert all(disk(s, i) <= disk(nxt, i) for i in TRAINS)
    assert s.engine.commands <= nxt.engine.commands
    kind, _, i = event
    if kind in {"fence", "store_flush", "store_commit", "power"}:
        assert nxt.engine == s.engine
    if kind in {"power", "recover"}:
        assert nxt.engine.inside == s.engine.inside
    if kind == "power":
        assert not nxt.awake[i] and not nxt.logs[i].pending
    if kind == "recover" and activation_allowed(s, i):
        assert nxt.awake[i] and nxt.engine.floors[i] == disk(s, i)
    if kind in {"entry", "ack", "fence"} and not s.awake[i]:
        assert nxt == s
    return nxt


def run(events, s=None):
    s = boot() if s is None else s
    for event in events:
        s = checked(s, event)
    return s


def store_floor(epoch, i):
    return [("fence", epoch, i), ("store_flush", 0, i), ("store_commit", 0, i)]


def handoff(epoch, owner):
    events = [("begin", 0, owner), ("flush", 0, 0)]
    for i in TRAINS:
        events += store_floor(epoch, i)
        events += [("activate", 0, i), ("ack", epoch, i), ("receive", epoch, i)]
    return events + [("commit", 0, 0)]


def canonical(s):
    logs = tuple(replace(log, committed=(log.committed[-1],)) for log in s.logs)
    return replace(s, engine=fenced.canonical(s.engine), logs=logs)


def targeted():
    a = run(handoff(1, 0) + [("send", 0, 0)])
    gap = run([("begin", 0, 1), ("flush", 0, 0)] + store_floor(2, 0), a)
    assert disk(gap, 0) == 2 and gap.engine.floors[0] == 1
    assert checked(gap, ("ack", 2, 0)) == gap
    occupied = checked(gap, ("entry", 1, 0))
    assert occupied.engine.inside == {0}
    active = checked(occupied, ("activate", 0, 0))
    assert active.engine.floors[0] == 2 and active.engine.inside == {0}
    assert checked(active, ("ack", 2, 0)) == active
    cleared = run([("exit", 0, 0), ("ack", 2, 0)], active)
    assert (2, 0) in cleared.engine.acknowledgements
    assert checked(cleared, ("entry", 1, 0)) == cleared

    offline = checked(gap, ("power", 0, 0))
    assert offline.engine.floors[0] == 1 and disk(offline, 0) == 2
    for event in [("entry", 1, 0), ("ack", 2, 0), ("fence", 2, 0),
                  ("store_flush", 0, 0), ("store_commit", 0, 0), ("activate", 0, 0)]:
        assert checked(offline, event) == offline
    recovered = checked(offline, ("recover", 0, 0))
    assert recovered.awake[0] and recovered.engine.floors[0] == 2
    assert checked(recovered, ("entry", 1, 0)) == recovered

    # Delayed requests cannot roll back disk, even before local activation.
    repeated = run(store_floor(1, 0), gap)
    assert disk(repeated, 0) == 2 and repeated.engine.floors[0] == 1
    assert checked(repeated, ("activate", 0, 0)).engine.floors[0] == 2
    # Several real commits occur while the gate remains at 1; activation loads 2.
    several = run(store_floor(1, 0) + store_floor(1, 0)
                  + [("begin", 0, 1)] + store_floor(2, 0), a)
    assert several.logs[0].committed[-3:] == (1, 1, 2)
    assert several.engine.floors[0] == 1
    assert checked(several, ("activate", 0, 0)).engine.floors[0] == 2

    # Power loss does not freeze other endpoints or the controller.
    ahead = run(store_floor(2, 1) + [("activate", 0, 1), ("ack", 2, 1),
                ("receive", 2, 1)], offline)
    assert not ahead.awake[0] and (2, 1) in ahead.engine.received
    assert checked(ahead, ("commit", 0, 0)) == ahead
    # An already acknowledged endpoint may go offline while handoff completes.
    prepared = run(handoff(2, 1)[:-1], a)
    progressed = run([("power", 0, 0), ("commit", 0, 0), ("send", 0, 1),
                      ("entry", 2, 1)], prepared)
    assert not progressed.awake[0] and progressed.engine.inside == {1}
    assert journal.restore(progressed.engine.log) == (2, 1)

    trace = handoff(2, 1) + [("send", 0, 1), ("entry", 2, 1)]
    cuts = 0
    for i in TRAINS:
        for cut in range(len(trace) + 1):
            prefix = run(trace[:cut], a)
            crashed = checked(prefix, ("power", 0, i))
            assert disk(crashed, i) == disk(prefix, i)
            run([("recover", 0, i)] + trace[cut:], crashed)
            cuts += 1
    print(f"Targeted: {cuts} endpoint power-loss cuts; commit/activation gap, busy exit, latest-disk reload, stale requests, offline progress")
    return gap, occupied, offline


def unsafe_disk_ack(s, event):
    """One intentional bug: acknowledge disk before activating the local gate."""
    kind, k, i = event
    if (kind == "ack" and s.awake[i] and (k, i) in s.engine.requests
            and k <= disk(s, i) and i not in s.engine.inside):
        engine = replace(s.engine, acknowledgements=s.engine.acknowledgements | {(k, i)})
        return replace(s, engine=engine)
    return step(s, event)


def negative_gap_ack():
    a = run(handoff(1, 0) + [("send", 0, 0)])
    gap = run([("begin", 0, 1), ("flush", 0, 0)] + store_floor(2, 0)
              + store_floor(2, 1) + [("activate", 0, 1), ("ack", 2, 1),
                                    ("receive", 2, 1)], a)
    assert checked(gap, ("ack", 2, 0)) == gap
    bad = unsafe_disk_ack(gap, ("ack", 2, 0))
    assert bad.engine.floors == (1, 2) and disk(bad, 0) == 2
    for event in [("receive", 2, 0), ("commit", 0, 0), ("send", 0, 1),
                  ("entry", 2, 1), ("entry", 1, 0)]:
        bad = step(bad, event)
    assert journal.restore(bad.engine.log) == (2, 1)
    assert bad.engine.inside == {0, 1}
    assert bad.engine.commands >= {(1, 0), (2, 1)}
    assert bad.engine.floors[0] <= 1  # The ordinary local gate admits old A.
    print("Negative: disk-only acknowledgement causes double occupancy via the unchanged ordinary entry gate")


def missing_record_boundary():
    # Storage corruption is outside the valid reachable-state invariant.
    # Check only fail-closed recovery here, without asserting that invariant.
    offline = step(boot(), ("power", 0, 0))
    damaged_log = replace(offline.logs[0], left=journal.Slot(), right=journal.Slot())
    damaged = replace(offline, logs=set_item(offline.logs, 0, damaged_log))
    assert disk(damaged, 0) is None
    assert not activation_allowed(damaged, 0)
    restored = step(damaged, ("recover", 0, 0))
    assert restored == damaged and not restored.awake[0]
    print("Boundary: missing committed record keeps endpoint offline; no invariant claim for corrupted storage")


def bounded_search(seeds, depth_limit=4):
    events = [("begin", 0, owner) for owner in (None, 0, 1)]
    events += [(kind, 0, 0) for kind in ("flush", "commit", "crash")]
    events += [(kind, 0, i) for kind in ("send", "exit") for i in TRAINS]
    events += [(kind, k, i) for kind in ("entry", "fence", "ack", "receive")
               for k in (1, 2) for i in TRAINS]
    events += [(kind, 0, i) for kind in sorted(LOCAL) for i in TRAINS]
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
    print(f"Depth-{depth_limit} search from {len(seeds)} reachable gap seeds: {len(seen)} states, {edges} transitions, projection checked on each transition")


def seeded_runs():
    rng = Random(20261003)
    transitions = commits = activations = 0
    noise_kinds = ("crash", "entry", "send", "exit", "fence", "ack", "receive", "commit",
                   "store_flush", "store_commit", "activate", "power", "recover")
    for _ in range(100):
        s = boot()
        for _ in range(20):
            epoch = journal.restore(s.engine.log)[0] + 1
            for planned in handoff(epoch, rng.choice((None, 0, 1))):
                g = journal.restore(s.engine.log)[0]
                noise = [(rng.choice(noise_kinds), rng.choice((max(0, g - 1), g, g + 1)),
                          rng.choice(TRAINS)) for _ in range(2)]
                for event in noise + [planned]:
                    before = tuple(disk(s, i) for i in TRAINS)
                    old_floors = s.engine.floors
                    s = canonical(checked(s, event))
                    commits += any(disk(s, i) > before[i] for i in TRAINS)
                    activations += s.engine.floors != old_floors
                    transitions += 1
        # A cooperative suffix, not an unconditional progress/fairness claim.
        s = run([("recover", 0, 0), ("recover", 0, 1),
                 ("exit", 0, 0), ("exit", 0, 1)], s)
        target_epoch = journal.restore(s.engine.log)[0] + 1
        s = run(handoff(target_epoch, 1) + [("send", 0, 1), ("entry", target_epoch, 1)], s)
        assert s.engine.inside == {1}
    print(f"Seeded: {transitions} mixed transitions, {commits} increasing disk commits, {activations} floor activations, 100 cooperative recovery suffixes")


def main():
    seeds = targeted()
    negative_gap_ack()
    missing_record_boundary()
    bounded_search(seeds)
    seeded_runs()


if __name__ == "__main__":
    main()
