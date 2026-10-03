"""Independent tests of the delayed controller; not certified extraction."""
from collections import deque
from dataclasses import dataclass, replace


@dataclass(frozen=True)
class Controller:
    stage: tuple = ("ready", -1)
    priority: int = 0
    pending: tuple = (0, 0)
    received: tuple = (0, 0)
    served: tuple = (0, 0)
    zone: tuple = (False, False)


def set_item(xs, i, value):
    return tuple(value if j == i else xs[j] for j in range(2))


def react(c, event):
    kind, i = event
    stage, owner = c.stage
    if kind == "request":
        return replace(c, pending=set_item(c.pending, i, c.pending[i] + 1),
                       received=set_item(c.received, i, c.received[i] + 1))
    if kind == "poll":
        if stage == "ready":
            for j in (c.priority, 1 - c.priority):
                if c.pending[j]:
                    return replace(c, stage=("entering", j), priority=1-j,
                                   zone=set_item(c.zone, j, True))
        if stage == "occupied":
            return replace(c, stage=("leaving", owner))
    if kind == "entry" and c.stage == ("entering", i):
        return replace(c, stage=("occupied", i),
                       pending=set_item(c.pending, i, max(c.pending[i]-1, 0)),
                       served=set_item(c.served, i, c.served[i]+1))
    if kind == "exit" and c.stage == ("leaving", i):
        return replace(c, stage=("ready", -1), zone=set_item(c.zone, i, False))
    return c


def valid(c):
    stage, owner = c.stage
    assert all(c.received[i] == c.pending[i] + c.served[i] for i in range(2))
    assert c.zone == tuple(stage != "ready" and owner == i for i in range(2))
    assert sum(c.zone) <= 1
    if stage != "ready":
        assert c.priority == 1-owner
    if stage == "entering":
        assert c.pending[owner] > 0


def progress_event(c):
    stage, owner = c.stage
    return {"entering": ("entry", owner), "leaving": ("exit", owner)}.get(stage, ("poll", -1))


def main():
    events = [("poll", -1)] + [(kind, i) for kind in ("request", "entry", "exit") for i in range(2)]
    seen, queue, edges = {Controller()}, deque([Controller()]), 0
    while queue:
        c = queue.popleft()
        valid(c)
        for e in events:
            if e[0] == "request" and c.pending[e[1]] == 2:
                continue
            nxt = react(c, e)
            valid(nxt)
            assert all(nxt.served[i] >= c.served[i] for i in range(2))
            edges += 1
            # Quotient out cumulative counters for this bounded structural search.
            canon = replace(nxt, received=nxt.pending, served=(0, 0))
            if canon not in seen:
                seen.add(canon)
                queue.append(canon)
    print(f"PASS: bounded structural search: {len(seen)} states, {edges} transitions")
    c = Controller()
    for i in (0, 0, 1, 0, 1):
        c = react(c, ("request", i))
    target = c.received
    for _ in range(100):
        c = react(c, progress_event(c))
        valid(c)
        if c.served == target and c.stage[0] == "ready":
            break
    assert c.served == (3, 2) and c.pending == (0, 0)
    print("PASS: five separate requests retained and served")
    c = Controller()
    for e in (("request", 0), ("poll", -1), ("entry", 0), ("poll", -1), ("request", 1)):
        c = react(c, e)
    for _ in range(100):
        c = react(c, ("poll", -1))
        c = react(c, ("exit", 1))
        assert c.stage == ("leaving", 0) and c.zone == (True, False)
        assert c.pending[1] == 1
    c = react(c, ("exit", 0))
    c = react(c, ("poll", -1))
    assert c.stage == ("entering", 1)
    print("PASS: delayed exit and wrong-owner signal cannot release reservation")
    c = react(react(Controller(), ("request", 0)), ("poll", -1))
    for _ in range(100):
        c = react(c, ("poll", -1))
    assert c.pending == (1, 0) and c.served == (0, 0) and c.zone == (True, False)
    print("PASS: missing entry confirmation stalls service without losing request")


if __name__ == "__main__":
    main()
