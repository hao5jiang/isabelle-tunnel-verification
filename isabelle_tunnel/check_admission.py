"""Independent executable admission model; not Isabelle code extraction.

Exhaustive search quotients away only ghost commit history. Operational slots,
pending flag, selector, entry commands, and occupants remain in the key.
The reference transaction model does not use slots or selector state.
"""
from collections import deque
from dataclasses import dataclass, replace
from random import Random

import check_journal as journal


@dataclass(frozen=True)
class Admission:
    durable: journal.Journal
    issued: frozenset = frozenset()
    occupants: frozenset = frozenset()


@dataclass(frozen=True)
class Reference:
    owner: str | None = None
    proposal: str | None = None
    pending: bool = False
    flushed: bool = False
    issued: frozenset = frozenset()
    occupants: frozenset = frozenset()


EVENTS = [("prepare", owner) for owner in (None, "A", "B")]
EVENTS += [(kind, None) for kind in ("flush", "commit", "crash")]
EVENTS += [(kind, owner) for kind in ("emit", "enter", "leave") for owner in ("A", "B")]


def boot():
    return Admission(journal.boot(None))


def step(s, event):
    kind, owner = event
    if kind in ("prepare", "flush", "crash"):
        return replace(s, durable=journal.step(s.durable, event))
    if kind == "commit":
        target = journal.inactive(s.durable)
        if target.kind == "complete" and (
                target.value == journal.restore(s.durable)
                or not (s.issued or s.occupants)):
            return replace(s, durable=journal.step(s.durable, event))
    if kind == "emit" and journal.restore(s.durable) == owner:
        return replace(s, issued=s.issued | {owner})
    if kind == "enter" and owner in s.issued:
        return replace(s, issued=s.issued - {owner}, occupants=s.occupants | {owner})
    if kind == "leave":
        return replace(s, occupants=s.occupants - {owner})
    return s


def reference_step(s, event):
    kind, owner = event
    if kind == "prepare":
        return replace(s, proposal=owner, pending=True, flushed=False)
    if kind == "flush" and s.pending:
        return replace(s, flushed=True)
    if kind == "commit" and s.pending and s.flushed:
        if s.proposal == s.owner or not (s.issued or s.occupants):
            return replace(s, owner=s.proposal, pending=False, flushed=False, proposal=None)
    if kind == "crash":
        return replace(s, pending=False, flushed=False, proposal=None)
    if kind == "emit" and s.owner == owner:
        return replace(s, issued=s.issued | {owner})
    if kind == "enter" and owner in s.issued:
        return replace(s, issued=s.issued - {owner}, occupants=s.occupants | {owner})
    if kind == "leave":
        return replace(s, occupants=s.occupants - {owner})
    return s


def invariant(s):
    selected = journal.selected(s.durable)
    return (selected.kind == "complete"
            and s.durable.committed
            and selected.value == s.durable.committed[-1]
            and all(owner == selected.value for owner in s.issued | s.occupants))


def checked(s, ref, event):
    nxt, expected = step(s, event), reference_step(ref, event)
    assert invariant(nxt), (s, event, nxt)
    assert len(nxt.occupants) <= 1
    assert journal.restore(nxt.durable) == expected.owner
    assert nxt.issued == expected.issued and nxt.occupants == expected.occupants
    assert nxt.durable.pending == expected.pending
    if expected.pending:
        inactive = journal.inactive(nxt.durable)
        assert inactive.value == expected.proposal
        assert inactive.kind == ("complete" if expected.flushed else "partial")
    if event[0] == "crash":
        assert nxt.issued == s.issued and nxt.occupants == s.occupants
    return nxt, expected


def canonical(s):
    """Discard only ghost history prefix, which no operational guard reads."""
    return replace(s, durable=replace(s.durable, committed=(s.durable.committed[-1],)))


def run(events, s=None):
    s = boot() if s is None else s
    for event in events:
        s = step(s, event)
    return s


def targeted_checks():
    grant_a = [("prepare", "A"), ("flush", None), ("commit", None), ("emit", "A")]
    queued = run(grant_a)
    assert queued.issued == {"A"} and not queued.occupants
    staged = run([("prepare", "B"), ("flush", None)], queued)
    assert step(staged, ("commit", None)) == staged  # Empty tunnel is not sufficient.
    after_crash = step(queued, ("crash", None))
    assert step(after_crash, ("enter", "A")).occupants == {"A"}

    handoff = [("crash", None), ("enter", "A"), ("prepare", "B"),
               ("flush", None), ("commit", None), ("leave", "A"),
               ("commit", None), ("emit", "B"), ("enter", "B")]
    final = run(handoff, queued)
    assert invariant(final) and final.occupants == {"B"} and not final.issued
    # Every crash cut in one service/handoff trace, then continue remaining events.
    # Some cuts abort a pending transaction, so completion is not asserted.
    trace = grant_a + handoff
    for cut in range(len(trace) + 1):
        s = boot()
        for event in trace[:cut] + [("crash", None)] + trace[cut:]:
            s = step(s, event)
            assert invariant(s)

    # Fault injection 1: bypass the durable-owner emission guard.
    premature = replace(run([("prepare", "A"), ("flush", None)]), issued=frozenset({"A"}))
    premature = run([("crash", None), ("enter", "A")], premature)
    assert premature.occupants == {"A"} and journal.restore(premature.durable) is None
    assert not invariant(premature)

    # Fault injection 2: commit B with an empty tunnel but an outstanding A command.
    assert not staged.occupants and staged.issued == {"A"}
    unsafe = replace(staged, durable=journal.step(staged.durable, ("commit", None)))
    collision = run([("emit", "B"), ("enter", "A"), ("enter", "B")], unsafe)
    assert collision.occupants == {"A", "B"}
    print("Targeted: delayed entry after crash, safe handoff, 14 crash cuts, two faulty-order witnesses passed")


def main():
    frontier = deque([(boot(), Reference())])
    seen = {boot()}
    transitions = 0
    while frontier:
        s, ref = frontier.popleft()
        for event in EVENTS:
            nxt, expected = checked(s, ref, event)
            nxt = canonical(nxt)
            transitions += 1
            if nxt not in seen:
                seen.add(nxt)
                frontier.append((nxt, expected))
    print(f"Exhaustive quotient: {len(seen)} reachable states, {transitions} transitions, reference agreement")
    random = Random(20261002)
    s, ref = boot(), Reference()
    for _ in range(100_000):
        s, ref = checked(s, ref, random.choice(EVENTS))
        s = canonical(s)
    print("Seeded: 100000 mixed events, safety and transaction reference agreement")
    targeted_checks()


if __name__ == "__main__":
    main()
