"""
Script 1: Ring-adjacent walk coverage analysis.

For n = 5, 7, 9, 11:
- Minimum walk length to visit every processor at least once
- With 3 non-consecutive binary processors: minimum walk length with all binary fire counts even >= 2
- Scaling analysis
"""

from itertools import product as iprod
from collections import Counter

def ring_dist(a, b, n):
    """Distance on ring of size n."""
    return min(abs(a - b), n - abs(a - b))

def is_ring_adjacent(a, b, n):
    """Check if a and b are ring-adjacent (distance <= 1)."""
    return ring_dist(a, b, n) <= 1

def min_walk_length_bfs(n):
    """
    Find minimum length ring-adjacent walk starting at 0 that visits all n processors.
    State: (current_position, frozenset_of_visited).
    Returns minimum walk length (number of steps, so sequence has length+1 elements).
    """
    from collections import deque
    all_visited = frozenset(range(n))
    start = (0, frozenset([0]))
    queue = deque([(start, 0)])
    visited = {start}

    while queue:
        (pos, vis), steps = queue.popleft()
        if vis == all_visited:
            return steps
        for delta in [-1, 0, 1]:
            npos = (pos + delta) % n
            nvis = vis | {npos}
            state = (npos, nvis)
            if state not in visited:
                visited.add(state)
                queue.append((state, steps + 1))
    return -1

def min_cycle_length_bfs(n):
    """
    Find minimum length ring-adjacent CYCLE (returns to start) that visits all n processors.
    Walk: m_0, m_1, ..., m_{CL-1} where m_0 = starting position.
    Cycle means the walk can repeat (m_{CL-1} is ring-adjacent to m_0).
    Returns CL (length of mover sequence).
    """
    from collections import deque
    all_visited = frozenset(range(n))
    # State: (current_pos, visited_set)
    # We want to visit all and return to start (ring-adjacent to 0)
    start_pos = 0
    start = (start_pos, frozenset([start_pos]))
    queue = deque([(start, 1)])  # CL=1 means just the start
    visited = {start}

    while queue:
        (pos, vis), cl = queue.popleft()
        # Check if we've visited all AND can close the cycle
        if vis == all_visited and is_ring_adjacent(pos, start_pos, n):
            return cl
        for delta in [-1, 0, 1]:
            npos = (pos + delta) % n
            nvis = vis | {npos}
            state = (npos, nvis)
            if state not in visited:
                visited.add(state)
                queue.append((state, cl + 1))
    return -1

def choose_binary_positions(n, num_binary=3):
    """Choose num_binary non-consecutive positions on ring of size n."""
    results = []
    from itertools import combinations
    for combo in combinations(range(n), num_binary):
        ok = True
        for i in range(len(combo)):
            for j in range(i+1, len(combo)):
                if ring_dist(combo[i], combo[j], n) <= 1:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            results.append(combo)
    return results

def enumerate_walks_with_binary(n, binary_pos, max_cl):
    """
    Find minimum CL for a ring-adjacent cycle visiting all processors
    where each binary processor has even fire count >= 2.

    Uses BFS over (position, visited_set, binary_parity_tuple).
    binary_parity_tuple: for each binary proc, (fire_count_mod_2, has_fired_at_least_twice).

    This is expensive, so we simplify: track (pos, visited, binary_fire_counts_mod2, binary_fired_ge2).
    """
    from collections import deque

    all_visited = frozenset(range(n))
    bp = sorted(binary_pos)
    nb = len(bp)
    bp_set = set(bp)

    # State: (pos, visited, parity_tuple, ge2_tuple)
    # parity_tuple: tuple of fire_count % 2 for each binary proc
    # ge2_tuple: tuple of booleans (fire_count >= 2) for each binary proc

    start_pos = 0
    init_parity = tuple(1 if 0 in bp_set and bp.index(0) == i else 0 for i in range(nb))
    # Actually: fire count of start_pos is 1 (it appears once at start)
    init_parity = tuple(0 for _ in range(nb))
    init_ge2 = tuple(False for _ in range(nb))

    # Account for starting position
    if start_pos in bp_set:
        idx = bp.index(start_pos)
        init_parity = list(init_parity)
        init_parity[idx] = 1
        init_parity = tuple(init_parity)

    start = (start_pos, frozenset([start_pos]), init_parity, init_ge2)
    queue = deque([(start, 1)])
    visited_states = {start}

    goal_parity = tuple(0 for _ in range(nb))
    goal_ge2 = tuple(True for _ in range(nb))

    while queue:
        (pos, vis, par, ge2), cl = queue.popleft()
        if cl > max_cl:
            return -1

        # Check goal
        if vis == all_visited and par == goal_parity and ge2 == goal_ge2 and is_ring_adjacent(pos, start_pos, n):
            return cl

        for delta in [-1, 0, 1]:
            npos = (pos + delta) % n
            nvis = vis | {npos}
            npar = list(par)
            nge2 = list(ge2)
            if npos in bp_set:
                idx = bp.index(npos)
                npar[idx] = 1 - npar[idx]
                if npar[idx] == 0:  # Just completed an even count
                    nge2[idx] = True
            npar = tuple(npar)
            nge2 = tuple(nge2)
            state = (npos, nvis, npar, nge2)
            if state not in visited_states:
                visited_states.add(state)
                queue.append((state, cl + 1))

    return -1

print("=" * 70)
print("SCRIPT 1: Ring-Adjacent Walk Coverage Analysis")
print("=" * 70)

# Part 1: Minimum walk lengths
print("\n--- Part 1: Minimum walk/cycle lengths to visit all processors ---")
print(f"{'n':>4} | {'min_walk':>10} | {'min_cycle':>10} | {'2(n-1)':>10}")
print("-" * 50)

for n in [5, 7, 9, 11]:
    mw = min_walk_length_bfs(n)
    mc = min_cycle_length_bfs(n)
    theoretical = 2 * (n - 1)
    print(f"{n:4d} | {mw:10d} | {mc:10d} | {theoretical:10d}")

# Part 2: With binary constraints
print("\n--- Part 2: Minimum cycle length with 3 non-consecutive binary (even fire counts >= 2) ---")
print(f"{'n':>4} | {'#placements':>12} | {'min_CL':>8} | {'max_CL':>8} | {'2(n-1)':>8}")
print("-" * 55)

for n in [5, 7, 9]:
    placements = choose_binary_positions(n, 3)
    if not placements:
        print(f"{n:4d} | {'0':>12} | {'N/A':>8} | {'N/A':>8} | {2*(n-1):>8}")
        continue

    max_cl_limit = 4 * n  # search up to 4n
    min_cls = []
    for bp in placements:
        cl = enumerate_walks_with_binary(n, bp, max_cl_limit)
        if cl > 0:
            min_cls.append(cl)

    if min_cls:
        print(f"{n:4d} | {len(placements):>12} | {min(min_cls):>8} | {max(min_cls):>8} | {2*(n-1):>8}")
    else:
        print(f"{n:4d} | {len(placements):>12} | {'>'+str(max_cl_limit):>8} | {'?':>8} | {2*(n-1):>8}")

# Part 3: Theoretical analysis
print("\n--- Part 3: Theoretical bounds ---")
print("""
Ring-adjacent walk analysis:
- To visit all n processors on a ring, a walk starting at 0 must reach
  distance floor(n/2) in both directions.
- Minimum walk (one-way): n-1 steps (go around one way).
- Minimum cycle (return to start): The walk must "turn around" at some point.
  Optimal: go CW to distance d, return, go CCW to distance n-d, return.
  Total = 2d + 2(n-d) = 2n. But can do better by starting in one direction
  and going all the way around: n steps to return, but visits all n.

- Key insight: a ring-adjacent CYCLE of length CL starting at 0 is a closed
  walk on the ring graph. Minimum to visit all n vertices in a closed walk
  on C_n = n (just go around the ring). But each step is ring-adjacent
  (can stay in place!), so minimum steps = n (go one direction all the way).

- With binary fire count constraints: each binary proc needs fire count
  that is even and >= 2. If the walk visits a binary proc just once
  (fire count 1), it needs to revisit. This adds overhead.
""")

# Part 4: Fire count distribution in minimal cycles
print("--- Part 4: Fire count distribution in optimal ring traversal ---")
for n in [5, 7, 9]:
    # Optimal pure traversal: go 0->1->2->...->n-1->0, length n
    walk = list(range(n))  # length n, cycle closes 0->...->n-1->0
    fc = Counter(walk)
    print(f"\nn={n}: Pure ring traversal (CL={n})")
    print(f"  Fire counts: {dict(fc)}")
    print(f"  All fire counts = 1 (odd!) => binary procs need revisiting")

    # Double traversal: go around twice
    walk2 = list(range(n)) * 2
    fc2 = Counter(walk2)
    print(f"  Double traversal (CL={2*n}): all fire counts = 2 (even, >= 2) -- works!")

    # Can we do better? Back-and-forth
    walk3 = list(range(n)) + list(range(n-2, 0, -1))  # 0,1,...,n-1,n-2,...,1
    fc3 = Counter(walk3)
    print(f"  Back-and-forth (CL={len(walk3)}): fire counts = {dict(fc3)}")
    even_all = all(v % 2 == 0 for v in fc3.values())
    ge2_all = all(v >= 2 for v in fc3.values())
    print(f"    All even: {even_all}, All >= 2: {ge2_all}")

print("\n" + "=" * 70)
print("KEY FINDINGS:")
print("=" * 70)
print("""
1. Minimum cycle visiting all n procs on ring: n steps (go around once).
2. But fire count = 1 for each proc (odd) => binary procs FAIL.
3. To get even fire counts >= 2: minimum CL ~ 2n (go around twice or back-and-forth).
4. With 3 non-consecutive binary: the binary constraint forces CL >= 2n roughly.
5. This CL must be <= product of state sizes = prod(m_i).
""")
