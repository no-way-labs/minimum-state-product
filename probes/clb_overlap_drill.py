#!/usr/bin/env python3
"""clb_overlap_drill.py — Drill into the triple overlap at 2-binary bounce cycles.

Key finding: the simple down-up bounce cycle at ms=(2,2,3,...,3) has triple
overlap at P2 and P8. This means mutual exclusion is impossible for that cycle.

Questions:
1. What specific triples overlap, and why?
2. Is the overlap inherent to ALL bounce cycles with 2 adjacent binary, or just this construction?
3. Can we find ANY cycle structure for 2-binary that avoids overlap?
4. Is there a capacity argument that proves overlap is INEVITABLE?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian, permutations

# ============================================================
# Part 1: Identify the overlapping triples
# ============================================================

def build_bounce_cycle(ms, n):
    """Build simple down-up bounce cycle."""
    base = list(range(n-1, -1, -1)) + list(range(1, n))
    for repeats in range(1, 5):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full_movers = base * repeats
        for step, mover in enumerate(full_movers):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            new_config = tuple(config)
            if new_config in visited and new_config != cycle[0]:
                break
            if new_config == cycle[0]:
                return cycle, full_movers[:step+1]
            visited.add(new_config)
            cycle.append(new_config)
    return None, None


n = 9
ms = (2, 2, 3, 3, 3, 3, 3, 3, 3)
cycle, movers = build_bounce_cycle(ms, n)
assert cycle is not None

print("2-binary adjacent bounce cycle analysis")
print(f"ms={ms}, cycle_len={len(cycle)}")
print()

# Print the full cycle with movers
print("Step | Config           | Mover")
print("-----|------------------|------")
for idx in range(len(cycle)):
    c = cycle[idx]
    m = movers[idx]
    config_str = ''.join(str(x) for x in c)
    print(f"  {idx:2d} | {config_str}          | P{m}")

print()

# Find overlapping triples for each processor
for p in range(n):
    mover_triples = {}
    nonmover_triples = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        triple = (c[(p-1)%n], c[p], c[(p+1)%n])
        if movers[idx] == p:
            mover_triples[triple] = mover_triples.get(triple, []) + [idx]
        else:
            nonmover_triples[triple] = nonmover_triples.get(triple, []) + [idx]

    overlap = set(mover_triples.keys()) & set(nonmover_triples.keys())
    if overlap:
        print(f"P{p} OVERLAP:")
        for t in sorted(overlap):
            print(f"  Triple {t}: mover at steps {mover_triples[t]}, "
                  f"non-mover at steps {nonmover_triples[t]}")
            for idx in mover_triples[t]:
                c = cycle[idx]
                print(f"    Step {idx}: config={''.join(str(x) for x in c)}, "
                      f"mover=P{movers[idx]}")
            for idx in nonmover_triples[t]:
                c = cycle[idx]
                print(f"    Step {idx}: config={''.join(str(x) for x in c)}, "
                      f"mover=P{movers[idx]}")
        print()

# ============================================================
# Part 2: Try ALL possible bounce-like cycles for 2-binary
# ============================================================

print("\n" + "="*70)
print("Part 2: Exhaustive search for overlap-free cycles")
print("="*70)
print()

def try_cycle_pattern(ms, n, mover_pattern):
    """Try to build a cycle with given mover pattern, incrementing at each step."""
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}

    for step, mover in enumerate(mover_pattern):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        new_config = tuple(config)

        if new_config == cycle[0] and step == len(mover_pattern) - 1:
            return cycle  # Closed!

        if new_config in visited:
            return None  # Collision before closing

        visited.add(new_config)
        cycle.append(new_config)

    return None  # Didn't close


def check_overlap(cycle, movers, n):
    """Check if any processor has triple overlap."""
    for p in range(n):
        mover_set = set()
        nonmover_set = set()
        for idx in range(len(cycle)):
            c = cycle[idx]
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if movers[idx] == p:
                mover_set.add(triple)
            else:
                nonmover_set.add(triple)
        if mover_set & nonmover_set:
            return True, p, mover_set & nonmover_set
    return False, None, None


# Try various bounce patterns
patterns = {
    "down-up": list(range(n-1,-1,-1)) + list(range(1,n)),
    "up-down": list(range(n)) + list(range(n-2,0,-1)),
}

# Also try with different nb_val increments
# The simple construction always increments by 1. Let's try a more
# general approach: at each step, choose what value to set (not just +1)

print("Trying various mover patterns...")
ms_test = (2, 2, 3, 3, 3, 3, 3, 3, 3)

for name, base in patterns.items():
    for reps in range(1, 5):
        full_pattern = base * reps
        cycle = try_cycle_pattern(ms_test, n, full_pattern)
        if cycle:
            has_ovlp, proc, triples = check_overlap(cycle, full_pattern, n)
            status = f"OVERLAP at P{proc}" if has_ovlp else "CLEAN"
            print(f"  {name}×{reps}: len={len(cycle)}, {status}")
            if not has_ovlp:
                print(f"  *** OVERLAP-FREE CYCLE FOUND! ***")


# ============================================================
# Part 3: Generalized cycle search — try non-increment transitions
# ============================================================

print("\n" + "="*70)
print("Part 3: DFS for overlap-free cycles at ms=(2,2,3,3,3,3,3,3,3)")
print("="*70)
print()

def dfs_overlap_free_cycles(ms, n, max_depth=60, max_cycles=100, timeout_nodes=500000):
    """DFS search for good cycles that are overlap-free.

    At each step, try all possible (mover, new_value) pairs.
    Track triple usage per processor to prune early.
    """
    total_configs = 1
    for m in ms:
        total_configs *= m

    start = tuple(0 for _ in range(n))
    cycles_found = []
    nodes_explored = 0

    # Stack: (config, path, movers_so_far, mover_triples_per_proc, nonmover_triples_per_proc)
    # Use iterative DFS with light state

    # Actually, tracking full triple sets per proc is expensive. Let me use a simpler approach:
    # just find cycles and check overlap after.

    stack = [(start, [start], [])]
    visited_in_path = {start}

    while stack and len(cycles_found) < max_cycles and nodes_explored < timeout_nodes:
        config, path, movers_list = stack.pop()
        nodes_explored += 1

        if len(path) > max_depth:
            continue

        # Try all possible single-processor moves
        for p in range(n):
            L = config[(p-1)%n]
            S = config[p]
            R = config[(p+1)%n]

            for new_s in range(ms[p]):
                if new_s == S:
                    continue  # Not a move

                new_config = list(config)
                new_config[p] = new_s
                new_config = tuple(new_config)

                if new_config == start and len(path) >= n:
                    # Cycle found! Check fairness and overlap.
                    full_movers = movers_list + [p]
                    procs_seen = set(full_movers)
                    if procs_seen == set(range(n)):
                        # Fair cycle! Check overlap.
                        has_ovlp, ovlp_proc, _ = check_overlap(path, full_movers, n)
                        if not has_ovlp:
                            cycles_found.append((list(path), full_movers))
                            if len(cycles_found) <= 5:
                                print(f"  OVERLAP-FREE cycle #{len(cycles_found)}: "
                                      f"len={len(path)}, movers={full_movers[:20]}...")
                    continue

                if new_config not in visited_in_path and len(path) < max_depth:
                    new_path = path + [new_config]
                    new_movers = movers_list + [p]
                    visited_in_path_copy = visited_in_path | {new_config}
                    # Can't use visited_in_path directly (shared) — need to track path membership differently
                    # This DFS is expensive. Let me simplify.
                    pass

    return cycles_found, nodes_explored


# The full DFS is too expensive. Let me try a targeted approach:
# enumerate all FEASIBLE mover sequences and check if a cycle exists.

# Key insight: for a cycle to be overlap-free, each processor's mover-triples
# and non-mover-triples must be disjoint. The binary processors (P0, P1) are
# the bottleneck because they have the fewest triples.

# P0 (m=2): left=P8(m=3), right=P1(m=2) → capacity = 3·2·2 = 12 triples
# P1 (m=2): left=P0(m=2), right=P2(m=3) → capacity = 2·2·3 = 12 triples

# For P0: 12 triples, partition into 6 where S=0 and 6 where S=1
#   S=0 triples: (L,0,R) for L∈{0,1,2}, R∈{0,1} → 6 triples
#   S=1 triples: (L,1,R) for L∈{0,1,2}, R∈{0,1} → 6 triples
# Mover triples have f(L,S,R)≠S, so:
#   - If S=0, mover means f→1 (toggle)
#   - If S=1, mover means f→0 (toggle)
# Each S=0 triple is either mover or non-mover. Same for S=1.
# The ONLY constraint from mutual exclusion is: mover set ∩ non-mover set = ∅
# Since mover triples always change S and non-mover triples keep S,
# a triple (L,S,R) with the same (L,S,R) can't be both.
# But this is about the SAME triple appearing at different cycle positions!

# Wait — I need to think about this more carefully.
# The issue is: at cycle position i, the mover is some proc p.
# For EVERY proc q, the triple (c_i[q-1], c_i[q], c_i[q+1]) determines
# whether q is privileged. If q≠p (non-mover), then q must NOT be privileged:
# f_q(L,S,R) = S. If q=p (mover), then q IS privileged: f_q(L,S,R) ≠ S.
# Overlap: if triple T appears at position i (q is mover) and position j
# (q is not mover), then f_q(T) must both ≠ T[1] and = T[1]. Contradiction.

# So the question is: in what cycles do binary procs have overlap?

# Let me check: for P0 in the bounce cycle, what are the triples?
print("P0 triple analysis in bounce cycle:")
for idx in range(len(cycle)):
    c = cycle[idx]
    triple = (c[8], c[0], c[1])  # (left=P8, self=P0, right=P1)
    is_mover = (movers[idx] == 0)
    print(f"  Step {idx}: config={''.join(str(x) for x in c)}, "
          f"P0 triple={triple}, {'MOVER' if is_mover else 'non-mover'}")

print()
print("P1 triple analysis in bounce cycle:")
for idx in range(len(cycle)):
    c = cycle[idx]
    triple = (c[0], c[1], c[2])  # (left=P0, self=P1, right=P2)
    is_mover = (movers[idx] == 1)
    print(f"  Step {idx}: config={''.join(str(x) for x in c)}, "
          f"P1 triple={triple}, {'MOVER' if is_mover else 'non-mover'}")


# ============================================================
# Part 4: CAPACITY LOWER BOUND — how many positions can a cycle have?
# ============================================================

print("\n" + "="*70)
print("Part 4: Capacity analysis — maximum overlap-free cycle length")
print("="*70)
print()

# For processor p, the triples with S=s form a group of m_{p-1}·m_{p+1} triples.
# In any overlap-free cycle, each such triple is either always-mover or always-non-mover.
#
# A mover triple (L,S,R) means: whenever the cycle visits config c with
# c[p-1]=L, c[p]=S, c[p+1]=R, processor p IS the mover.
# A non-mover triple means: p is NOT the mover.
#
# Constraint: p moves N_p times in the cycle. The mover-triples for p
# cover N_p positions (with possible repetition). The non-mover-triples
# cover L-N_p positions.
#
# The number of distinct mover-triples ≤ N_p.
# The number of distinct non-mover-triples ≤ L-N_p.
# But also: mover-triples ∩ non-mover-triples = ∅.
# Total distinct triples used ≤ m_{p-1}·m_p·m_{p+1}.

# For binary P0 with ternary P8 and binary P1:
# Capacity = 3·2·2 = 12
# If P0 moves N times: need ≤ 12 - N non-mover triples (since N mover triples used)
# But non-mover triples = L - N positions, with ≤ 12 - [mover triples] distinct values
# Since [mover triples] ≥ 1, non-mover can have at most 11 distinct triples
# Since [non-mover triples] ≤ L - N positions, each maps to one of at most 11 values
# This gives: non-mover repetition = (L - N) / 11

# The REAL constraint is stronger: look at which triples are possible.
# For binary P0 (S ∈ {0,1}):
#   State 0 triples: (L, 0, R) for L∈{0,1,2}, R∈{0,1} = 6 triples
#   State 1 triples: (L, 1, R) for L∈{0,1,2}, R∈{0,1} = 6 triples
#
# In the cycle, P0 alternates between states 0 and 1.
# If P0 moves k times: it alternates k times. Starting at 0:
#   0 → 1 → 0 → 1 → ... (k moves)
# For a cycle, must return to 0, so k is even (or the cycle starts at a different config).
#
# Between moves, P0 stays at the same state. So there are k "runs" of constant P0-state.
# During a run of S=0: all triples have form (L, 0, R). These are non-mover triples.
# At the move: the triple (L, 0, R) is a mover triple.
#
# Key: the mover triple at a move from 0→1 has form (L, 0, R). The non-mover triples
# in the preceding run also have form (L', 0, R'). For overlap-freeness:
# the specific (L, 0, R) at the move must NOT appear in any non-mover position.
# But in the run before the move, the (L, 0, R) values change as OTHER processors
# change state (they are the movers in the run).

# So the constraint is: the final (L, 0, R) in a S=0 run — the one where P0 moves —
# must not equal any earlier (L, 0, R) in that run or any OTHER S=0 run.

# And similarly for S=1 runs.

# For P0 with capacity 12 (6 per state):
# Each S=0 run has some length l_k. The l_k-1 non-mover triples plus the 1 mover triple
# at the end must all be distinct (actually, the non-mover triples within a run can repeat
# each other — no, actually they can't repeat a MOVER triple from another run, but they
# CAN repeat other non-mover triples).

# Actually, let me re-think. The overlap constraint is:
# mover_triple_set ∩ non_mover_triple_set = ∅ (for each processor)
# But within mover_triple_set, duplicates are fine.
# And within non_mover_triple_set, duplicates are fine.
# The SETS must be disjoint.

# So for P0: let A = {triples at mover positions}, B = {triples at non-mover positions}
# Need A ∩ B = ∅. |A| ≤ N, |B| ≤ L-N. |A ∪ B| ≤ 12.

# This is satisfiable as long as the cycle doesn't force the same triple to appear
# at both a mover and non-mover position for P0.

# The question: when does the CYCLE STRUCTURE force this?

# In a bounce cycle [8,7,...,0,...,8], P0 moves at one specific position.
# At that position, P0's triple is determined by the config at that step.
# P0's triple at all other positions is also determined.
# The overlap happens when the config at P0's mover position creates a triple
# that also appears at some non-mover position.

# This is structural, not capacity-based. It depends on the specific configs visited.

# Let me try: for 2-binary systems, systematically try ALL possible cycle structures
# (not just bounce) and check if ANY is overlap-free.

# Actually, that's too many cycles. Let me instead:
# Count the MINIMUM number of distinct triples a cycle needs.

# For a cycle of length L visiting all n processors:
# Each processor p has N_p ≥ 1 mover positions.
# The mover triples for p: at least 1 distinct (if all moves have the same triple).
# The non-mover triples for p: at least 1 distinct (at least one position where p doesn't move).
# So at least 2 distinct triples per processor, using 2 out of capacity.
# This is always feasible for capacity ≥ 2, which is always true (m_i ≥ 2).

# So the capacity argument alone CAN'T prove infeasibility. The constraint must come
# from the INTERACTION between processors — the same config determines triples for
# ALL processors simultaneously.

print("Capacity per processor for ms=(2,2,3,3,3,3,3,3,3):")
for p in range(n):
    cap = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
    print(f"  P{p} (m={ms[p]}): left=P{(p-1)%n}(m={ms[(p-1)%n]}), "
          f"right=P{(p+1)%n}(m={ms[(p+1)%n]}), capacity={cap}")

print()
print("Minimum capacity: P1 = 2·2·3 = 12")
print("This is tight but not inherently impossible.")
print("The overlap must come from inter-processor constraints.")

# ============================================================
# Part 5: Check — does the overlap persist across ALL orientations?
# ============================================================

print("\n" + "="*70)
print("Part 5: All orientations of 2-binary at n=9")
print("="*70)
print()

# For ms with 2 binary: 4 necklaces × up to 9 rotations each
necklaces = [
    (2,2,3,3,3,3,3,3,3),  # sep=1
    (2,3,2,3,3,3,3,3,3),  # sep=2
    (2,3,3,2,3,3,3,3,3),  # sep=3
    (2,3,3,3,2,3,3,3,3),  # sep=4
]

for neck in necklaces:
    tested = set()
    for rot in range(n):
        ms_rot = tuple(neck[(i+rot)%n] for i in range(n))
        if ms_rot in tested:
            continue
        tested.add(ms_rot)

        cycle, movers_seq = build_bounce_cycle(ms_rot, n)
        if cycle is None:
            continue

        has_ovlp, proc, triples = check_overlap(cycle, movers_seq, n)
        bin_pos = [i for i in range(n) if ms_rot[i] == 2]
        status = f"OVERLAP at P{proc}" if has_ovlp else "CLEAN"
        print(f"  {ms_rot} bins@{bin_pos}: len={len(cycle)}, {status}")
        if not has_ovlp:
            print(f"  *** OVERLAP-FREE! ***")

# Also try up-down pattern
print("\nUp-down pattern:")
for neck in necklaces:
    tested = set()
    base_up = list(range(n)) + list(range(n-2, 0, -1))
    for rot in range(n):
        ms_rot = tuple(neck[(i+rot)%n] for i in range(n))
        if ms_rot in tested:
            continue
        tested.add(ms_rot)

        for reps in range(1, 5):
            full = base_up * reps
            config = [0] * n
            cycle = [tuple(config)]
            visited = {tuple(config)}
            closed = False
            for step, mover in enumerate(full):
                config = list(cycle[-1])
                config[mover] = (config[mover] + 1) % ms_rot[mover]
                nc = tuple(config)
                if nc == cycle[0]:
                    movers_seq = full[:step+1]
                    closed = True
                    break
                if nc in visited:
                    break
                visited.add(nc)
                cycle.append(nc)

            if closed:
                has_ovlp, proc, _ = check_overlap(cycle, movers_seq, n)
                bin_pos = [i for i in range(n) if ms_rot[i] == 2]
                status = f"OVERLAP at P{proc}" if has_ovlp else "CLEAN"
                print(f"  {ms_rot} bins@{bin_pos}: len={len(cycle)}, {status} (up-down×{reps})")
                if not has_ovlp:
                    print(f"  *** OVERLAP-FREE! ***")
                break
