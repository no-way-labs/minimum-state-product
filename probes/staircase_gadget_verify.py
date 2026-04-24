#!/usr/bin/env python3
"""
Verify the bounded endpoint gadget acyclicity and check whether the
pure-mid rank ρ extends through the non-standard processors.

The non-standard processors are:
  P_0:   T_bot (binary, m_L=2, m_S=2, m_R=3)
  P_1:   T_low (ternary, m_L=2, m_S=3, m_R=3)
  P_{n-2}: T_high (ternary, m_L=3, m_S=3, m_R=2)
  P_{n-1}: T_top (ternary, m_L=3, m_S=3, m_R=2)

Question 1: Does T_low = T_mid restricted to L∈{0,1}?
Question 2: For mixed intervals (T_mid + gadget), is ρ still valid?
Question 3: Is the gadget DAG for small mixed systems?
"""

T_bot = {
    (0,0,0): 1,  (0,0,1): 1,  (0,0,2): 0,
    (0,1,0): 1,  (0,1,1): 1,  (0,1,2): 1,
    (1,0,0): 0,  (1,0,1): 1,  (1,0,2): 0,
    (1,1,0): 0,  (1,1,1): 1,  (1,1,2): 0,
}

T_low = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
}

T_mid = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
    (2,0,0): 0,  (2,0,1): 0,  (2,0,2): 2,
    (2,1,0): 1,  (2,1,1): 0,  (2,1,2): 2,
    (2,2,0): 0,  (2,2,1): 2,  (2,2,2): 2,
}

T_high = {
    (0,0,0): 0,  (0,0,1): 0,
    (0,1,0): 0,  (0,1,1): 0,
    (0,2,0): 0,  (0,2,1): 0,
    (1,0,0): 1,  (1,0,1): 1,
    (1,1,0): 1,  (1,1,1): 1,
    (1,2,0): 0,  (1,2,1): 1,
    (2,0,0): 0,  (2,0,1): 0,
    (2,1,0): 0,  (2,1,1): 0,
    (2,2,0): 0,  (2,2,1): 2,
}

T_top = {
    (0,0,0): 0,  (0,0,1): 0,
    (0,1,0): 0,  (0,1,1): 1,
    (0,2,0): 2,  (0,2,1): 2,
    (1,0,0): 0,  (1,0,1): 0,
    (1,1,0): 0,  (1,1,1): 1,
    (1,2,0): 2,  (1,2,1): 2,
    (2,0,0): 0,  (2,0,1): 0,
    (2,1,0): 0,  (2,1,1): 1,
    (2,2,0): 2,  (2,2,1): 2,
}

# Check Q1: T_low = T_mid|_{L in {0,1}}
print("=== Q1: T_low = T_mid restricted to L∈{0,1}? ===")
match = True
for L in [0, 1]:
    for S in range(3):
        for R in range(3):
            if T_low[(L,S,R)] != T_mid[(L,S,R)]:
                print(f"  MISMATCH at ({L},{S},{R}): T_low={T_low[(L,S,R)]}, T_mid={T_mid[(L,S,R)]}")
                match = False
if match:
    print("  YES — T_low is exactly T_mid restricted to L∈{0,1}")

# Check T_high vs T_mid
print("\n=== T_high vs T_mid restricted to R∈{0,1}? ===")
match = True
for L in range(3):
    for S in range(3):
        for R in [0, 1]:
            if T_high[(L,S,R)] != T_mid[(L,S,R)]:
                print(f"  MISMATCH at ({L},{S},{R}): T_high={T_high[(L,S,R)]}, T_mid={T_mid[(L,S,R)]}")
                match = False
if match:
    print("  YES — T_high is exactly T_mid restricted to R∈{0,1}")
else:
    print("  NO — T_high differs from T_mid|_{R∈{0,1}}")

# Enumerate all privileged T_high entries
print("\n=== T_high privileged entries ===")
for L in range(3):
    for S in range(3):
        for R in [0, 1]:
            if T_high[(L,S,R)] != S:
                print(f"  ({L},{S},{R})→{T_high[(L,S,R)]}")

# Now test mixed intervals: T_mid^ell + [T_high, T_top, T_bot, T_low] + T_mid^r
# For a ring of size n, the processors are:
#   P_0 (T_bot, binary {0,1}), P_1 (T_low), ..., P_{n-3} (T_mid), P_{n-2} (T_high), P_{n-1} (T_top)
#
# An active interval wrapping around P_0 would include:
#   ...T_mid, T_high, T_top, T_bot, T_low, T_mid...
# with fixed boundary values on both sides from frozen bad triples.
#
# For simplicity, test the 4-processor gadget [T_high, T_top, T_bot, T_low]
# with various T_mid extensions and boundary conditions.

from itertools import product as cart

def build_mixed_interval(mid_left, mid_right):
    """Build a mixed interval: mid_left T_mid procs + [T_high, T_top, T_bot, T_low] + mid_right T_mid procs.

    Returns list of (table, state_range) for each position.
    """
    tables = []
    state_ranges = []
    for _ in range(mid_left):
        tables.append(T_mid)
        state_ranges.append(range(3))
    tables.append(T_high)
    state_ranges.append(range(3))
    tables.append(T_top)
    state_ranges.append(range(3))
    tables.append(T_bot)
    state_ranges.append(range(2))  # binary
    tables.append(T_low)
    state_ranges.append(range(3))
    for _ in range(mid_right):
        tables.append(T_mid)
        state_ranges.append(range(3))
    return tables, state_ranges

def has_202_general(state, lb, rb):
    """Check (2,0,2)-free for general state with boundaries."""
    ext = [lb] + list(state) + [rb]
    for i in range(1, len(ext) - 1):
        if ext[i-1] == 2 and ext[i] == 0 and ext[i+1] == 2:
            return True
    return False

def check_mixed_acyclicity(mid_left, mid_right, lb, rb):
    """Check acyclicity of a mixed interval."""
    tables, state_ranges = build_mixed_interval(mid_left, mid_right)
    k = len(tables)

    # Enumerate valid states
    states = []
    for s in cart(*state_ranges):
        if not has_202_general(s, lb, rb):
            states.append(s)

    state_set = set(states)

    # Build adjacency
    adj = {s: [] for s in states}
    for s in states:
        ext = [lb] + list(s) + [rb]
        for i in range(k):
            L, S, R = ext[i], ext[i+1], ext[i+2]
            table = tables[i]
            if (L, S, R) in table and table[(L, S, R)] != S:
                new_s = list(s)
                new_s[i] = table[(L, S, R)]
                new_s = tuple(new_s)
                if new_s in state_set:
                    adj[s].append(new_s)

    # Cycle detection
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {s: WHITE for s in states}
    has_cycle = False

    import sys
    sys.setrecursionlimit(100000)

    def dfs(u):
        nonlocal has_cycle
        if has_cycle: return
        color[u] = GRAY
        for v in adj[u]:
            if color[v] == GRAY:
                has_cycle = True
                return
            if color[v] == WHITE:
                dfs(v)
        color[u] = BLACK

    for s in states:
        if color[s] == WHITE:
            dfs(s)

    edge_count = sum(len(v) for v in adj.values())
    return not has_cycle, len(states), edge_count

print("\n=== Q3: Mixed interval acyclicity ===")
for ml in range(4):
    for mr in range(4):
        all_ok = True
        total_states = 0
        total_edges = 0
        for lb in range(3):
            for rb in range(3):
                ok, ns, ne = check_mixed_acyclicity(ml, mr, lb, rb)
                total_states += ns
                total_edges += ne
                if not ok:
                    print(f"  CYCLE: mid_left={ml}, mid_right={mr}, lb={lb}, rb={rb}")
                    all_ok = False
        if all_ok:
            k = ml + 4 + mr
            print(f"  mid_left={ml}, mid_right={mr} (k={k}): ALL 9 boundaries acyclic ({total_states} states, {total_edges} edges)")

# Also check the pure-mid rank on the T_low restriction
print("\n=== Q2: ρ on T_low (left endpoint) ===")
# Since T_low = T_mid|_{L∈{0,1}}, every T_low transition is also a T_mid transition.
# Therefore the same rank ρ works. The edge word still has the same structure.
# The only difference is that the left boundary value is in {0,1} (from T_bot).
# This is already covered by the pure-mid verification (which tests all lb ∈ {0,1,2}).
print("  T_low = T_mid|_{L∈{0,1}} ⇒ ρ rank transfers directly")
print("  Already verified for all lb ∈ {0,1,2}, so lb ∈ {0,1} is a subcase")

print("\n=== Summary of T_high differences from T_mid ===")
diffs = []
for L in range(3):
    for S in range(3):
        for R in [0, 1]:
            if T_high[(L,S,R)] != T_mid[(L,S,R)]:
                diffs.append((L,S,R, T_mid[(L,S,R)], T_high[(L,S,R)]))
                print(f"  ({L},{S},{R}): T_mid→{T_mid[(L,S,R)]}, T_high→{T_high[(L,S,R)]}")
print(f"  Total differences: {len(diffs)}")
