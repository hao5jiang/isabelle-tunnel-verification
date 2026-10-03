"""Finite-epoch tests for the durable endpoint activation protocol.

This is an executable model, not certified extraction or a hardware test.
The wrapper uses the previous state without a new exhaustion flag. At the
configured cap, begin stops new issuance and controller commit cannot reopen it.
Previously sent commands, physical exits and endpoint recovery remain enabled.
The bound covers identifier payloads, not the length of histories or all memory.
"""
from collections import deque
from dataclasses import replace
from random import Random

import check_activation as activation
import check_journal as journal

TRAINS = (0, 1)
TOKEN_EVENTS = {"entry", "fence", "ack", "receive"}


def epoch(s):
    return journal.restore(s.engine.log)[0]


def step(limit, s, event):
    assert isinstance(limit, int) and limit >= 0
    kind, k, _ = event
    if kind in TOKEN_EVENTS and k > limit:
        return s
    if kind == "begin" and epoch(s) >= limit:
        return replace(s, engine=replace(s.engine, stopped=True))
    if kind == "commit" and epoch(s) >= limit:
        return s
    return activation.step(s, event)


def payload_epochs(log, controller=False):
    """Inspect both storage slots and the complete ghost commit history."""
    values = [slot.value for slot in (log.left, log.right)
              if slot.kind in {"partial", "complete"}]
    values.extend(log.committed)
    return [value[0] if controller else value for value in values]


def identifiers(s):
    result = payload_epochs(s.engine.log, controller=True)
    for log in s.logs:
        result.extend(payload_epochs(log))
    result.extend(s.engine.floors)
    result.extend(activation.disk(s, i) for i in TRAINS)
    for history in (s.engine.commands, s.engine.requests,
                    s.engine.acknowledgements, s.engine.received):
        result.extend(k for k, _ in history)
    result.append(epoch(s))
    return result


def invariant(limit, s):
    activation.invariant(s)
    assert all(isinstance(k, int) and 0 <= k <= limit for k in identifiers(s))


def exhausted(limit, s):
    return epoch(s) == limit and s.engine.stopped


def checked(limit, s, event):
    invariant(limit, s)
    nxt = step(limit, s, event)
    invariant(limit, nxt)
    kind, k, _ = event
    assert epoch(s) <= epoch(nxt)
    assert all(a <= b for a, b in zip(s.engine.floors, nxt.engine.floors))
    assert all(activation.disk(s, i) <= activation.disk(nxt, i) for i in TRAINS)
    assert s.engine.commands <= nxt.engine.commands
    if kind in TOKEN_EVENTS and k > limit:
        assert nxt == s
    elif kind == "begin" and epoch(s) >= limit:
        assert nxt.engine.stopped and nxt.engine.log == s.engine.log
        assert nxt.engine.requests == s.engine.requests
        assert nxt.logs == s.logs and nxt.awake == s.awake
        assert nxt.engine.inside == s.engine.inside
    elif kind == "commit" and epoch(s) >= limit:
        assert nxt == s
    else:
        assert nxt == activation.step(s, event)
        assert nxt.engine == activation.abstract_step(s, event)
    if exhausted(limit, s):
        assert exhausted(limit, nxt)
        assert nxt.engine.commands == s.engine.commands
        assert nxt.engine.requests == s.engine.requests
    if kind in {"crash", "power", "recover"}:
        assert nxt.engine.inside == s.engine.inside
    if kind == "crash":
        assert nxt.engine.stopped
    if epoch(nxt) != epoch(s):
        assert epoch(nxt) == epoch(s) + 1
    return nxt


def run(limit, events, s=None):
    s = activation.boot() if s is None else s
    invariant(limit, s)
    for event in events:
        s = checked(limit, s, event)
    return s


def reach_epoch(limit, target):
    assert 0 <= target <= limit
    s = activation.boot()
    for k in range(1, target + 1):
        s = run(limit, activation.handoff(k, (k - 1) % 2), s)
        assert epoch(s) == k
    return s


def targeted():
    seeds = {}
    crash_cuts = 0
    for limit in range(4):
        initial = activation.boot()
        at_cap = reach_epoch(limit, limit)
        assert epoch(at_cap) == limit
        if limit == 0:
            assert at_cap.engine.stopped
            for owner in (None, 0, 1):
                blocked = run(limit, activation.handoff(1, owner), initial)
                assert blocked == initial
            seeds[limit] = (initial,)
            continue

        owner = (limit - 1) % 2
        assert not at_cap.engine.stopped
        sent = checked(limit, at_cap, ("send", 0, owner))
        assert (limit, owner) in sent.engine.commands
        stopped = checked(limit, sent, ("begin", 0, 1 - owner))
        assert exhausted(limit, stopped)
        assert stopped.engine.log == sent.engine.log
        assert (limit + 1, owner) not in stopped.engine.requests
        assert checked(limit, stopped, ("send", 0, owner)) == stopped
        assert checked(limit, stopped, ("commit", 0, 0)) == stopped

        # Stop prohibits new sends, but does not erase an in-flight command.
        inside = checked(limit, stopped, ("entry", limit, owner))
        assert inside.engine.inside == {owner}
        outside = checked(limit, inside, ("exit", 0, owner))
        assert not outside.engine.inside
        # A replay can enter again: exhaustion is not permanent physical clearance.
        replayed = checked(limit, outside, ("entry", limit, owner))
        assert replayed.engine.inside == {owner}
        recovered = run(limit, [("crash", 0, 0), ("power", 0, owner),
                                ("recover", 0, owner), ("commit", 0, 0),
                                ("begin", 0, owner), ("send", 0, owner)], replayed)
        assert exhausted(limit, recovered)
        assert recovered.engine.inside == {owner}
        assert recovered.engine.commands == stopped.engine.commands

        # A final-epoch crash also leaves issuance stopped; there is no spare epoch.
        final_crash = run(limit, [("crash", 0, 0), ("commit", 0, 0)]
                          + activation.handoff(limit + 1, owner), sent)
        assert exhausted(limit, final_crash)
        assert final_crash.engine.commands == sent.engine.commands

        previous = reach_epoch(limit, limit - 1)
        # The tuple's second field is not an epoch for local/control events.
        dummy_fields = [(kind, k if kind in TOKEN_EVENTS else limit + 100, i)
                        for kind, k, i in activation.handoff(limit, owner)]
        with_dummy_fields = run(limit, dummy_fields, previous)
        assert epoch(with_dummy_fields) == limit and not with_dummy_fields.engine.stopped
        gap_events = [("begin", 0, owner), ("flush", 0, 0)]
        gap_events += activation.store_floor(limit, 0)
        gap = run(limit, gap_events, previous)
        assert epoch(gap) == limit - 1
        assert activation.disk(gap, 0) == limit
        assert gap.engine.floors[0] == limit - 1
        offline = checked(limit, gap, ("power", 0, 0))
        awakened = checked(limit, offline, ("recover", 0, 0))
        assert awakened.engine.floors[0] == limit
        seeds[limit] = (previous, gap, offline, stopped, inside)

        # Prefix/suffix tests include controller and endpoint crashes at each cut.
        trace = activation.handoff(limit, owner)
        trace += [("send", 0, owner), ("begin", 0, 1 - owner),
                  ("entry", limit, owner), ("exit", 0, owner)]
        for cut in range(len(trace) + 1):
            prefix = run(limit, trace[:cut], previous)
            for fault in (("crash", 0, 0), ("power", 0, 0), ("power", 0, 1)):
                suffix = [fault]
                if fault[0] == "power":
                    suffix.append(("recover", 0, fault[2]))
                run(limit, suffix + trace[cut:], prefix)
                crash_cuts += 1

        # Invalid epoch-bearing input must not mutate storage or any packet history.
        for state in seeds[limit]:
            for kind in TOKEN_EVENTS:
                for i in TRAINS:
                    for k in (limit + 1, limit + 100):
                        assert checked(limit, state, (kind, k, i)) == state

    print(f"Targeted caps 0..3: {crash_cuts} crash cuts; final epoch remains usable, exhaustion persists, in-flight entry/exit and replay remain possible")
    return seeds


def bounded_search(seeds_by_limit, depth_limit=3):
    states = edges = 0
    for limit, seeds in seeds_by_limit.items():
        events = [("begin", 0, i) for i in (None, 0, 1)]
        events += [(kind, 0, 0) for kind in ("flush", "commit", "crash")]
        events += [(kind, 0, i) for kind in ("send", "exit") for i in TRAINS]
        events += [(kind, k, i) for kind in sorted(TOKEN_EVENTS)
                   for k in range(limit + 2) for i in TRAINS]
        events += [(kind, 0, i) for kind in sorted(activation.LOCAL) for i in TRAINS]
        # Only duplicate ghost history is truncated for state-space comparison.
        # Targeted and seeded tests retain and check the full commit histories.
        seen = {activation.canonical(s) for s in seeds}
        todo = deque((s, 0) for s in seen)
        while todo:
            s, depth = todo.popleft()
            if depth == depth_limit:
                continue
            for event in events:
                nxt = activation.canonical(checked(limit, s, event))
                edges += 1
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append((nxt, depth + 1))
        states += len(seen)
    print(f"Depth-{depth_limit} bounded search across caps 0..3: {states} states, {edges} transitions; storage, packet and floor bounds checked")


def seeded_runs():
    rng = Random(20261003)
    transitions = increasing_commits = stopped_steps = 0
    noise_kinds = ("crash", "entry", "send", "exit", "fence", "ack", "receive",
                   "commit", "flush", "store_flush", "store_commit", "activate",
                   "power", "recover")
    for limit in range(4):
        for _ in range(40):
            s = activation.boot()
            for _ in range(limit + 5):
                proposal = epoch(s) + 1
                for planned in activation.handoff(proposal, rng.choice((None, 0, 1))):
                    noise = [(rng.choice(noise_kinds), rng.randrange(limit + 3),
                              rng.choice(TRAINS)) for _ in range(2)]
                    for event in noise + [planned]:
                        before = epoch(s)
                        s = checked(limit, s, event)
                        transitions += 1
                        increasing_commits += epoch(s) > before
                        stopped_steps += exhausted(limit, s)
            # Cooperative completion reaches the cap if spare epochs remain.
            s = run(limit, [("recover", 0, i) for i in TRAINS]
                    + [("exit", 0, i) for i in TRAINS], s)
            while epoch(s) < limit:
                s = run(limit, activation.handoff(epoch(s) + 1, 0), s)
            s = checked(limit, s, ("begin", 0, 1))
            assert exhausted(limit, s)
            for _ in range(100):
                event = (rng.choice(noise_kinds + ("begin",)),
                         rng.randrange(limit + 3), rng.choice(TRAINS))
                s = checked(limit, s, event)
                transitions += 1
                stopped_steps += 1
            assert exhausted(limit, s)
    print(f"Seeded caps 0..3: {transitions} mixed transitions, {increasing_commits} increasing controller commits, {stopped_steps} exhausted-state checks; full ghost histories retained")


def representation_checks():
    # Mathematical range checks only: no binary serialization or firmware claim.
    for width in range(1, 5):
        limit = 2 ** width - 1
        s = reach_epoch(limit, limit)
        owner = (limit - 1) % 2
        s = run(limit, [("send", 0, owner), ("begin", 0, 1 - owner),
                        ("entry", limit, owner)], s)
        for k in identifiers(s):
            assert k < 2 ** width and k % (2 ** width) == k
    print("Representation: widths 1..4 satisfy unsigned range and modulo identity for reachable identifier payloads; no machine-code claim")


def negative_unbounded_reference():
    # Removing the finite wrapper violates the bound, not necessarily exclusion.
    # This is a range witness, not a fabricated collision from token arithmetic.
    for limit in range(4):
        s = reach_epoch(limit, limit)
        for event in activation.handoff(limit + 1, 0):
            s = activation.checked(s, event)
        assert epoch(s) == limit + 1
        assert max(identifiers(s)) == limit + 1
        activation.invariant(s)
        try:
            invariant(limit, s)
        except AssertionError:
            pass
        else:
            raise AssertionError("Unbounded controller unexpectedly respected the cap")
    print("Negative: unwrapped protocol reaches cap + 1 for caps 0..3 while preserving exclusion; this establishes a range failure only")


def main():
    seeds = targeted()
    bounded_search(seeds)
    seeded_runs()
    representation_checks()
    negative_unbounded_reference()


if __name__ == "__main__":
    main()
