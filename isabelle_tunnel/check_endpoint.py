"""Independent endpoint journal/power-loss tests; not certified extraction."""
from collections import deque
from dataclasses import dataclass, replace
from random import Random

import check_journal as journal
import check_fenced as fenced


@dataclass(frozen=True)
class Endpoint:
    platform: fenced.System
    logs: tuple
    online: tuple = (True, True)


def boot():
    return Endpoint(fenced.boot(), (journal.boot(0), journal.boot(0)))


def update_tuple(values, i, value):
    return values[:i] + (value,) + values[i+1:]


def net(kind, epoch=0, owner=0):
    return ("network", (kind, epoch, owner))


def step(s, event):
    kind, arg = event
    p = s.platform
    if kind == "network":
        message, k, i = arg
        if message == "fence":
            if s.online[i] and (k, i) in p.requests:
                record = journal.step(s.logs[i], ("prepare", max(k, p.floors[i])))
                return replace(s, logs=update_tuple(s.logs, i, record))
            return s
        if message in ("entry", "ack") and not s.online[i]:
            return s
        return replace(s, platform=fenced.step(p, arg))
    i = arg
    if kind == "flush" and s.online[i]:
        return replace(s, logs=update_tuple(s.logs, i, journal.step(s.logs[i], ("flush", None))))
    if kind == "commit":
        candidate = journal.inactive(s.logs[i])
        if (s.online[i] and s.logs[i].pending and candidate.kind == "complete"
                and p.floors[i] <= candidate.value and (candidate.value, i) in p.requests):
            return replace(s, logs=update_tuple(s.logs, i, journal.step(s.logs[i], ("commit", None))),
                           platform=fenced.step(p, ("fence", candidate.value, i)))
    if kind == "power":
        return replace(s, logs=update_tuple(s.logs, i, journal.step(s.logs[i], ("crash", None))),
                       online=update_tuple(s.online, i, False))
    if kind == "recover":
        selected = journal.selected(s.logs[i])
        if selected.kind == "complete":
            return replace(s, online=update_tuple(s.online, i, True),
                           platform=replace(p, floors=update_tuple(p.floors, i, selected.value)))
    return s


def invariant(s):
    fenced.invariant(s.platform)
    for i in fenced.TRAINS:
        selected = journal.selected(s.logs[i])
        assert selected.kind == "complete" and selected.value == s.logs[i].committed[-1]
        assert journal.restore(s.logs[i]) == s.platform.floors[i]


def checked(s, event):
    nxt = step(s, event)
    invariant(nxt)
    kind, arg = event
    if kind == "network" and arg[0] != "fence":
        assert nxt.platform in (s.platform, fenced.step(s.platform, arg))
    elif kind == "commit" and nxt.platform != s.platform:
        k = journal.restore(nxt.logs[arg])
        assert nxt.platform == fenced.step(s.platform, ("fence", k, arg))
    else:
        assert nxt.platform == s.platform  # Other concrete steps are abstract stutters.
    if kind == "power":
        assert not nxt.online[arg] and nxt.platform.inside == s.platform.inside
    if kind == "recover":
        assert nxt.platform.floors == s.platform.floors
    return nxt


def run(events, s=None, verify=True):
    s = boot() if s is None else s
    for event in events:
        s = checked(s, event) if verify else step(s, event)
    return s


def endpoint_fence(k, i):
    return [net("fence", k, i), ("flush", i), ("commit", i),
            net("ack", k, i), net("receive", k, i)]


def handoff(k, owner):
    return [net("begin", 0, owner), net("flush")] + endpoint_fence(k, 0) + endpoint_fence(k, 1) + [net("commit")]


def canonical(s):
    return replace(s, platform=fenced.canonical(s.platform),
                   logs=tuple(replace(j, committed=(j.committed[-1],)) for j in s.logs))


def targeted():
    a = run(handoff(1, 0) + [net("send", 0, 0)])
    assert a.platform.commands == {(1, 0)}
    prep = run([net("begin", 0, 1), net("flush"), net("fence", 2, 0)], a)
    assert prep.platform.floors[0] == 1
    flushed = run([("flush", 0)], prep)
    assert journal.inactive(flushed.logs[0]) == journal.Slot("complete", 2)
    assert step(flushed, net("ack", 2, 0)) == flushed
    crashed = run([("power", 0)], flushed)
    assert step(crashed, net("entry", 1, 0)) == crashed
    assert step(crashed, net("ack", 2, 0)) == crashed
    recovered = run([("recover", 0), ("commit", 0)], crashed)
    assert recovered.platform.floors[0] == 1  # Orphan Complete 2 cannot activate.
    committed = run([("commit", 0)], flushed)
    restarted = run([("power", 0), ("recover", 0), net("entry", 1, 0)], committed)
    assert restarted.platform.floors[0] == 2 and not restarted.platform.inside
    # A can go offline after sending a durable acknowledgement; handoff stays safe.
    offline = run([net("ack", 2, 0), ("power", 0), net("receive", 2, 0)]
                  + endpoint_fence(2, 1) + [net("commit"), net("send", 0, 1), net("entry", 2, 1)], committed)
    assert not offline.online[0] and offline.platform.inside == {1}
    final = run([("recover", 0), net("entry", 1, 0)], offline)
    assert final.platform.inside == {1} and (1, 0) in final.platform.commands
    # Power loss does not erase actual occupancy.
    occupied = run([net("entry", 1, 0), ("power", 0)], a)
    assert occupied.platform.inside == {0}
    # Fault: activate RAM's gate before the endpoint selector is committed.
    faulty = replace(flushed, platform=fenced.step(flushed.platform, ("fence", 2, 0)))
    collision = run([net("ack", 2, 0), net("receive", 2, 0)] + endpoint_fence(2, 1)
                    + [net("commit"), net("send", 0, 1), net("entry", 2, 1),
                       ("power", 0), ("recover", 0), net("entry", 1, 0)], faulty, verify=False)
    assert collision.platform.inside == {0, 1}
    # Both endpoints' failure cuts in a full handoff trace.
    trace = handoff(1, 0) + [net("send", 0, 0)] + handoff(2, 1)
    for i in fenced.TRAINS:
        for cut in range(len(trace) + 1):
            run(trace[:cut] + [("power", i), ("recover", i)] + trace[cut:])
    print(f"Targeted: {2*(len(trace)+1)} endpoint failure cuts; pre/post-commit recovery, offline gate, early-ack collision")
    return a, flushed, offline


def bounded_search(seeds, depth_limit=5):
    events = [net("begin", 0, i) for i in (None, 0, 1)]
    events += [net(kind) for kind in ("flush", "commit", "crash")]
    events += [net(kind, 0, i) for kind in ("send", "exit") for i in fenced.TRAINS]
    events += [net(kind, k, i) for kind in ("entry", "fence", "ack", "receive")
               for k in (1, 2, 3) for i in fenced.TRAINS]
    events += [(kind, i) for kind in ("flush", "commit", "power", "recover") for i in fenced.TRAINS]
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
    print(f"Depth-{depth_limit} from 3 reachable seeds: {len(seen)} states, {edges} transitions; abstract step/stutter checks")


def random_trials():
    rng = Random(20261003)
    count = 0
    for _ in range(100):
        s = boot()
        for _ in range(12):
            k = journal.restore(s.platform.log)[0] + 1
            for planned in handoff(k, rng.choice((None, 0, 1))):
                for _ in range(2):
                    i = rng.choice(fenced.TRAINS)
                    if rng.randrange(3) == 0:
                        event = (rng.choice(("power", "recover", "flush", "commit")), i)
                    else:
                        g = journal.restore(s.platform.log)[0]
                        event = net(rng.choice(("entry", "ack", "receive", "exit", "crash", "send")),
                                    rng.choice((max(0, g-1), g, g+1)), i)
                    s = canonical(checked(s, event))
                    count += 1
                s = canonical(checked(s, planned))
                count += 1
        s = run([("recover", 0), ("recover", 1), net("exit", 0, 0), net("exit", 0, 1)], s)
        k = journal.restore(s.platform.log)[0] + 1
        s = run(handoff(k, 1) + [net("send", 0, 1), net("entry", k, 1)], s)
        assert s.platform.inside == {1}
    print(f"Seeded: {count} transitions; 100 cooperative recovery suffixes")


if __name__ == "__main__":
    bounded_search(targeted())
    random_trials()
