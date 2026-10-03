"""Independent finite-state check; not Isabelle code extraction."""
from collections import deque

OUTSIDE, WAITING, INSIDE = range(3)
INITIAL = (OUTSIDE, OUTSIDE, False, False)


def successors(s, faulty=False):
    yield "idle", s
    for i, name in enumerate("AB"):
        actions = []
        if s[i] == OUTSIDE:
            actions.append(("request", {i: WAITING}))
        if s[i] == WAITING:
            if not any(s[2:]):
                actions.append(("grant", {i + 2: True}))
            if faulty and INSIDE not in s[:2]:
                actions.append(("premature_grant", {i + 2: True}))
            if s[i + 2]:
                actions.append(("enter", {i: INSIDE}))
        if s[i] == INSIDE:
            actions.append(("leave", {i: OUTSIDE, i + 2: False}))
        for action, updates in actions:
            t = list(s)
            for k, value in updates.items():
                t[k] = value
            yield f"{name}: {action}", tuple(t)


def explore(faulty=False):
    parents = {INITIAL: None}
    queue = deque([INITIAL])
    while queue:
        s = queue.popleft()
        for action, t in successors(s, faulty):
            if t not in parents:
                parents[t] = (s, action)
                queue.append(t)
    return parents


def safe(s):
    return s[:2] != (INSIDE, INSIDE)


def invariant(s):
    return sum(s[2:]) <= 1 and all(
        s[i] != INSIDE or s[i + 2] for i in range(2)
    )


def shortest_path(source, target, graph):
    parents = {source: None}
    queue = deque([source])
    while queue and target not in parents:
        s = queue.popleft()
        for t in graph[s]:
            if t not in parents:
                parents[t] = s
                queue.append(t)
    assert target in parents, "No connecting path in the reachable graph"
    path = [target]
    while path[-1] != source:
        path.append(parents[path[-1]])
    return list(reversed(path))


def check_fair_cycle(states):
    """A finite witness, separate from the Isabelle conditional theorem."""
    graph = {s: sorted({t for _, t in successors(s)}) for s in states}
    edges = {(s, t) for s in states for t in graph[s]}
    walk = [INITIAL]
    for s, t in sorted(edges):
        walk.extend(shortest_path(walk[-1], s, graph)[1:])
        walk.append(t)
    walk.extend(shortest_path(walk[-1], INITIAL, graph)[1:])
    walked = set(zip(walk, walk[1:]))
    assert walk[0] == walk[-1] == INITIAL
    assert walked == edges
    for i in range(2):
        assert any(s[i] == INSIDE for s in walk)
    # Repeating this closed walk traverses every reachable edge each period.
    print(f"PASS: fair periodic witness = {len(walk)-1} steps, {len(edges)} edges")


def dispatch(s, turn):
    result = list(s)
    if s[turn] == OUTSIDE:
        result[turn] = WAITING
    elif s[turn] == INSIDE:
        result[turn] = OUTSIDE
        result[turn + 2] = False
    elif s[turn + 2]:
        result[turn] = INSIDE
    elif not any(s[2:]):
        result[turn + 2] = True
    return tuple(result)


def check_round_robin(states):
    checks = 0
    worst = 0
    for start in states:
        for first_turn in range(2):
            for train in range(2):
                if start[train] != WAITING:
                    continue
                s, turn = start, first_turn
                first_entry = None
                for slot in range(1, 9):
                    t = dispatch(s, turn)
                    assert t in {u for _, u in successors(s)}
                    assert t in states and safe(t)
                    s, turn = t, 1 - turn
                    if s[train] == INSIDE and first_entry is None:
                        first_entry = slot
                assert first_entry is not None
                worst = max(worst, first_entry)
                checks += 1
    assert worst == 8
    s, turn = (WAITING, WAITING, False, False), 1
    print("Tight round-robin trace (A waits; B receives first slot):")
    print("0", s)
    for slot in range(1, 9):
        s, turn = dispatch(s, turn), 1 - turn
        assert (s[0] == INSIDE) == (slot == 8)
        print(slot, s)
    # Mutation check: removing alternation can starve B.
    mutant = (WAITING, WAITING, False, False)
    for _ in range(16):
        mutant = dispatch(mutant, 0)
        assert mutant[1] == WAITING
    print(f"PASS: round-robin {checks} waiting cases; tight maximum = {worst} slots")
    print("PASS: non-alternating mutation exposes starvation")


def check():
    good, bad = explore(), explore(True)
    assert all(invariant(s) and safe(s) for s in good)
    for s in good:
        for i in range(2):
            if s[i] == INSIDE:
                assert all(t[1 - i] != INSIDE for t in good if t[i] == s[i])
    collision = next(s for s in bad if not safe(s))
    trace = []
    current = collision
    while bad[current] is not None:
        previous, action = bad[current]
        trace.append((action, current))
        current = previous
    trace.reverse()
    assert len(trace) == 6
    print(f"PASS: safe reachable states = {len(good)}")
    print(f"PASS: faulty reachable states = {len(bad)}")
    print("PASS: safety, invariant and own-position knowledge (safe model)")
    print("Shortest faulty collision trace (position A, B; permit A, B):")
    print("initial", INITIAL)
    for action, state in trace:
        print(action, state)
    check_fair_cycle(good)
    check_round_robin(good)


if __name__ == "__main__":
    check()
