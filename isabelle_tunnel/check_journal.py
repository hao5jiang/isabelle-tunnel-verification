"""Independent two-slot crash-consistency tests; not certified extraction.

Assumptions: selector updates are atomic and durable, Flush makes a whole record
durable, and Crash preserves Complete records and the selector. This model has
no physical/controller linkage and no guarantee about real storage hardware.
The committed history is ghost test state; recovery reads only the selected slot.
"""
from dataclasses import dataclass, replace
from itertools import product
from random import Random


@dataclass(frozen=True)
class Slot:
    kind: str = "empty"
    value: object = 0


@dataclass(frozen=True)
class Journal:
    left: Slot
    right: Slot = Slot()
    active: bool = False
    pending: bool = False
    committed: tuple = ()


def boot(seed):
    return Journal(Slot("complete", seed), committed=(seed,))


def selected(s):
    return s.right if s.active else s.left


def inactive(s):
    return s.left if s.active else s.right


def write_inactive(s, record):
    return replace(s, **{"left" if s.active else "right": record})


def restore(s):
    record = selected(s)
    return record.value if record.kind == "complete" else None


def step(s, event):
    kind, value = event
    if kind == "prepare":
        return replace(write_inactive(s, Slot("partial", value)), pending=True)
    if kind == "flush" and s.pending:
        record = inactive(s)
        if record.kind == "partial":
            return write_inactive(s, Slot("complete", record.value))
    if kind == "commit" and s.pending and inactive(s).kind == "complete":
        return replace(s, active=not s.active, pending=False,
                       committed=s.committed + (inactive(s).value,))
    if kind == "crash":
        return replace(s, left=Slot() if s.left.kind == "partial" else s.left,
                       right=Slot() if s.right.kind == "partial" else s.right,
                       pending=False)
    return s


@dataclass(frozen=True)
class Oracle:
    history: tuple
    proposal: object | None = None
    flushed: bool = False


def oracle_step(oracle, event):
    """Transaction-only reference, independent of slots and active selector."""
    kind, value = event
    if kind == "prepare":
        return replace(oracle, proposal=value, flushed=False)
    if kind == "flush" and oracle.proposal is not None:
        return replace(oracle, flushed=True)
    if kind == "commit" and oracle.proposal is not None and oracle.flushed:
        return Oracle(oracle.history + (oracle.proposal,))
    if kind == "crash":
        return Oracle(oracle.history)
    return oracle


def checked(s, oracle, event):
    nxt = step(s, event)
    expected = oracle_step(oracle, event)
    assert selected(nxt).kind == "complete"
    assert nxt.committed == expected.history
    assert restore(nxt) == expected.history[-1]
    assert nxt.pending == (expected.proposal is not None)
    if nxt.pending:
        assert inactive(nxt).kind == ("complete" if expected.flushed else "partial")
        assert inactive(nxt).value == expected.proposal
    else:
        assert inactive(nxt).kind != "partial"
    if event[0] != "commit":
        assert nxt.committed == s.committed
        assert restore(nxt) == restore(s)
    if event[0] == "commit" and not s.pending:
        assert nxt == s
    if event[0] == "crash":
        assert nxt.active == s.active and not nxt.pending
        assert step(nxt, ("crash", 0)) == nxt
    return nxt, expected


def run(seed, events):
    state, oracle = boot(seed), Oracle((seed,))
    for event in events:
        state, oracle = checked(state, oracle, event)
    return state, oracle


FLUSH = ("flush", 0)
COMMIT = ("commit", 0)
CRASH = ("crash", 0)


def test_crash_boundaries():
    sequence = (("prepare", 1), FLUSH, COMMIT)
    for cut in range(4):
        state, oracle = run(0, sequence[:cut] + (CRASH,))
        assert restore(state) == (1 if cut == 3 else 0)
        assert not state.pending
        state, oracle = checked(state, oracle, COMMIT)
        assert restore(state) == (1 if cut == 3 else 0)
    print("PASS: crashes before selector commit restore the previous value; crashes after commit restore the new value")


def test_repeated_commit_and_orphans():
    state, oracle = run(0, (("prepare", 1), FLUSH, COMMIT))
    assert inactive(state) == Slot("complete", 0)
    snapshot = state
    for _ in range(100):
        state, oracle = checked(state, oracle, COMMIT)
        assert state == snapshot
    print("PASS: repeated Commit cannot toggle back to the previous complete slot")

    for flush_before_crash in (False, True):
        sequence = (("prepare", 1),) + ((FLUSH,) if flush_before_crash else ()) + (CRASH,)
        state, oracle = run(0, sequence)
        assert inactive(state).kind == ("complete" if flush_before_crash else "empty")
        snapshot = state
        for event in (COMMIT, FLUSH, COMMIT, CRASH, COMMIT):
            state, oracle = checked(state, oracle, event)
            assert state == snapshot
        for event in (("prepare", 2), FLUSH, COMMIT):
            state, oracle = checked(state, oracle, event)
        assert restore(state) == 2
    print("PASS: crash cancels the transaction; neither partial nor complete orphan data can commit without a new Prepare")

    state, oracle = run(0, (("prepare", 1), FLUSH, ("prepare", 2), COMMIT))
    assert restore(state) == 0 and state.pending
    state, oracle = checked(state, oracle, FLUSH)
    state, oracle = checked(state, oracle, COMMIT)
    assert restore(state) == 2 and state.committed == (0, 2)
    # This interface checks transaction order, not semantic freshness of values.
    for event in (("prepare", 0), FLUSH, COMMIT):
        state, oracle = checked(state, oracle, event)
    assert restore(state) == 0 and state.committed == (0, 2, 0)
    print("PASS: replacing a proposal requires a fresh Flush; explicitly preparing an older payload remains allowed")


def test_short_traces():
    events = (("prepare", 0), ("prepare", 1), ("prepare", 2), FLUSH, COMMIT, CRASH)
    count = 0
    for sequence in product(events, repeat=6):
        run(0, sequence)
        count += 1
    print(f"PASS: exhaustive {count} event sequences of length 6 over three payloads")


def test_seeded_traces():
    rng = Random(20261005)
    events = (("prepare", 0), ("prepare", 1), ("prepare", 2), FLUSH, COMMIT, CRASH)
    commits = 0
    for _ in range(100):
        seed = rng.randrange(3)
        state, oracle = boot(seed), Oracle((seed,))
        for _ in range(1000):
            state, oracle = checked(state, oracle, rng.choice(events))
        commits += len(state.committed) - 1
    print(f"PASS: 100000 seeded transitions; {commits} successful commits agree with the transaction-only oracle")


def test_uncoupled_controller_restore():
    """Integration counterexample, not a verified persistence protocol."""
    import check_physical as physical
    from check_numbered import Numbered

    plant = physical.active_a()
    physical.invariant(plant)
    assert plant.inside == (True, False)
    assert plant.machine.core.stage == ("leaving", 0)
    old_checkpoint = Numbered()

    interrupted, _ = run(old_checkpoint, (("prepare", plant.machine), FLUSH, CRASH))
    assert restore(interrupted) == old_checkpoint
    restored_old = replace(plant, machine=restore(interrupted))
    assert restored_old.inside == plant.inside
    assert restored_old.inside[0] and not restored_old.machine.core.zone[0]
    try:
        physical.invariant(restored_old)
    except AssertionError:
        pass
    else:
        raise AssertionError("Old-checkpoint restoration unexpectedly preserved physical coverage")

    committed, _ = run(old_checkpoint, (("prepare", plant.machine), FLUSH, COMMIT, CRASH))
    assert restore(committed) == plant.machine
    restored_current = replace(plant, machine=restore(committed))
    assert restored_current == plant
    physical.invariant(restored_current)
    print("PASS: uncoupled pre-commit crash restores a valid but physically stale checkpoint and loses zone coverage")
    print("PASS: this committed-current-checkpoint example preserves physical invariants; no general safe integration claim")


def main():
    test_crash_boundaries()
    test_repeated_commit_and_orphans()
    test_short_traces()
    test_seeded_traces()
    test_uncoupled_controller_restore()


if __name__ == "__main__":
    main()
