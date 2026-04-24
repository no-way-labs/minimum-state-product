"""
Deep investigation: Do odd-winding mover words even exist for non-consecutive
binary at sub-threshold? And does UEC cover them?

Approach: Enumerate ALL possible mover words (not just for specific transition
functions) that are consistent with being a good cycle, and check winding.
"""

import itertools
from collections import defaultdict

def total_displacement(movers, n):
    cw = 0; ccw = 0
    for idx in range(len(movers)):
        curr = movers[idx]
        nxt = movers[(idx + 1) % len(movers)]
        diff = (nxt - curr) % n
        if diff == 1: cw += 1
        elif diff == n - 1: ccw += 1
    return cw - ccw

def fire_count(movers, p):
    return sum(1 for m in movers if m == p)

def edge_traversal_count(movers, n, edge_i):
    count = 0; CL = len(movers)
    a, b = edge_i, (edge_i + 1) % n
    for k in range(CL):
        curr = movers[k]; nxt = movers[(k + 1) % CL]
        if (curr == a and nxt == b) or (curr == b and nxt == a):
            count += 1
    return count

def edge_cross_steps(movers, n, edge_i):
    steps = []; CL = len(movers)
    a, b = edge_i, (edge_i + 1) % n
    for k in range(CL):
        curr = movers[k]; nxt = movers[(k + 1) % CL]
        if (curr == a and nxt == b) or (curr == b and nxt == a):
            steps.append(k)
    return steps

def is_valid_mover_walk(movers, n):
    """Check if movers form a valid walk on the ring (each step to neighbor or stay)."""
    CL = len(movers)
    for k in range(CL):
        curr = movers[k]; nxt = movers[(k + 1) % CL]
        diff = (nxt - curr) % n
        if diff != 0 and diff != 1 and diff != n - 1:
            return False
    return True

def check_entry_conflict_at_binary(movers, n, ms, binary_pos):
    """Check if a binary proc at binary_pos has entry conflict in this mover word.

    Entry conflict at proc p: there exist steps s1 (p is mover) and s2 (p is non-mover)
    where the left-self-right triple is the same, but p must change state at s1
    and keep state at s2.

    For a mover word, the "context" at step s for proc p is:
    (mover[s-1], mover[s], mover[s+1]) determines the position relative to p's neighbors.
    But actually, the context is the VALUES of (left_proc, self, right_proc) in the config.
    We can't check this without knowing the actual configs.

    For the MOVER WORD level analysis: if p fires at steps a1, a2 (binary → fc even ≥ 2),
    and between a1 and a2 the mover word doesn't return to p, then the config at p
    during the interval [a1+1, a2-1] is frozen (p doesn't fire). If some non-mover step
    in that interval has the same (L, S, R) context as a mover step: entry conflict.

    Actually this needs full config tracking. Let me use a different approach.
    """
    pass

# For n=6 with ms=(2,3,2,3,2,3), binary at {0,2,4}
# Enumerate ALL mover walks on C_6 of various lengths that:
# 1. Visit all 6 procs
# 2. Each binary fires even number of times
# 3. Have odd winding (|disp| = 6)

print("=" * 70)
print("Enumerating odd-winding mover walks for n=6, binary at {0,2,4}")
print("=" * 70)

n = 6
binary = {0, 2, 4}
ternary = {1, 3, 5}

# For odd winding: |displacement| = n = 6
# Minimum possible length: need to traverse each edge at least once (odd count).
# Sum of edge traversals = sum of (CW+CCW moves at each edge).
# Total CW + CCW moves ≤ CL (some steps may be "stay").
# If disp = 6: CW - CCW = 6, so CW = 6 + CCW.
# Total moves = CW + CCW = 6 + 2*CCW.
# Stay moves = CL - (6 + 2*CCW).
# Binary procs fire even: fc ≥ 2 each. 3 binary → ≥ 6 fires from binary.
# Ternary procs fire ≥ 1 each. 3 ternary → ≥ 3 fires from ternary.
# Total fires = CL ≥ 9.
# But also: binary fc must be even, ternary fc must allow return to start state.
# For ternary (m=3): fc can be anything ≥ 1 (not necessarily multiple of 3,
# since the transition function determines what values are visited).
# Actually for a VALID good cycle: each proc returns to its start state after
# fc firings. This constrains fc based on the transition function, but for
# mover word enumeration we just need fc ≥ 1 for each proc.

# With binary fc even ≥ 2 and ternary fc ≥ 1:
# min CL = 3*2 + 3*1 = 9

# For CL up to some bound, enumerate walks.
# But this is exponential. Let me use BFS/DFS with pruning.

def enumerate_odd_winding_walks(n, binary_set, max_cl=18):
    """Enumerate cyclic mover walks with |displacement|=n."""
    results = []

    # BFS: state = (current_position, displacement_so_far, fire_counts, length)
    # Start at each position
    for start in range(n):
        # Stack: (pos, word_so_far)
        stack = [(start, [start])]
        while stack:
            pos, word = stack.pop()
            cl = len(word)

            if cl > max_cl:
                continue

            # Check if we can close the cycle (return to start)
            if cl >= 9:  # minimum length
                # Can we close? Next step from pos must reach start
                diff = (start - pos) % n
                if diff == 0 or diff == 1 or diff == n - 1:
                    # Candidate cycle (close it)
                    full_word = word  # cyclic: word[CL] = word[0] = start
                    d = total_displacement(full_word, n)
                    if abs(d) == n:
                        # Check all procs visited
                        procs = set(full_word)
                        if procs == set(range(n)):
                            # Check binary fc even
                            ok = True
                            for b in binary_set:
                                fc = fire_count(full_word, b)
                                if fc % 2 != 0:
                                    ok = False
                                    break
                            if ok:
                                results.append((list(full_word), d))
                                if len(results) % 100 == 0:
                                    print(f"  Found {len(results)} so far (cl={cl})...")
                                if len(results) >= 5000:
                                    return results

            if cl < max_cl:
                for nxt in [(pos - 1) % n, pos, (pos + 1) % n]:
                    stack.append((nxt, word + [nxt]))

    return results

# This is still too slow for large max_cl. Let me limit to small lengths.
print("Searching for odd-winding walks at n=6 with CL=9..14...")

# Actually let me be smarter. For displacement = +6 or -6:
# Pure CW sweep: 0→1→2→3→4→5→0 gives displacement +6 in 6 steps.
# But we need CL ≥ 9 (binary fc ≥ 2).
# So we need at least 3 extra steps (stay or back-and-forth).

# Key insight: displacement +6 means exactly one net CW traversal of the ring.
# The walk goes around once CW (net). The minimum odd-winding walk with
# binary fc even is:
# 6 CW steps + extra steps to get binary fc to even.
# In 6 CW steps, each proc fires once. Binary need fc=2 (even).
# So 3 more fires at binary procs = 3 more steps → CL=9.
# But to fire a binary proc again, we need to "revisit" it.
# A revisit requires going back and forth, adding ≥2 to displacement (net 0).

# Example: 0,1,2,1,2,3,4,3,4,5,0,5,0 — no, this has CL=12 not cyclic.
# Let me think differently.

# For a mover walk of length CL with disp=+6:
# CW steps - CCW steps = 6
# CW + CCW + STAY = CL
# So CW = (6 + CW + CCW - STAY)/... let me just parameterize.
# Let c = CW, w = CCW, s = STAY. c - w = 6, c + w + s = CL.
# c = (CL - s + 6)/2, w = (CL - s - 6)/2.
# Need w ≥ 0: CL - s ≥ 6, i.e., c + w ≥ 6.
# Need c, w integers: CL - s must be even, i.e., CL and s have same parity.

# For CL=9, s must be odd (9-s even → s odd).
# s=1: c=7, w=1. 7 CW + 1 CCW + 1 STAY = 9.
# s=3: c=6, w=0. Pure CW + 3 stays.

# CL=9, s=3, c=6, w=0: pure sweep with 3 stays.
# The walk goes CW always but stays 3 times.
# E.g.: 0,0,1,2,2,3,4,4,5 → displacement:
# Step 0→1: 0→0 (stay, disp 0)
# Step 1→2: 0→1 (CW, disp +1)
# ... this gets complicated. Let me just enumerate short walks.

# More efficient: generate walks recursively with memoization of
# (position, fire_count_per_binary, displacement_so_far, length)

from functools import lru_cache

def count_odd_winding_walks_dp(n, binary_set, target_disp, max_cl):
    """Count walks using DP. State: (pos, disp, fc_b0, fc_b1, fc_b2, length)."""
    binary_list = sorted(binary_set)
    nb = len(binary_list)

    results = []

    # State: (pos, length, disp, fc_tuple_for_binary, visited_set_bitmask)
    # Too many states for general case. Let me just do BFS up to CL=12.

    # Actually, let me just enumerate short walks by DFS with strong pruning.

    found = []

    def dfs(pos, word, disp, fc, visited):
        cl = len(word)

        # Pruning: remaining length
        remaining = max_cl - cl

        # Can we still achieve target displacement?
        # Each remaining step changes disp by at most ±1
        if abs(target_disp - disp) > remaining + 1:  # +1 for closing step
            return

        # Can we still visit all procs?
        unvisited = set(range(n)) - visited
        if len(unvisited) > remaining + 1:
            return

        if cl >= max(9, n):
            # Try to close
            diff = (word[0] - pos) % n
            close_disp = disp
            if diff == 1:
                close_disp += 1
            elif diff == n - 1:
                close_disp -= 1
            elif diff != 0:
                pass  # can't close
            else:
                pass  # stay (disp unchanged)

            if diff in (0, 1, n - 1) and abs(close_disp) == n:
                # Check all visited
                if visited == set(range(n)):
                    # Check binary fc even
                    ok = True
                    for b in binary_set:
                        if fc[b] % 2 != 0:
                            ok = False
                            break
                    if ok:
                        found.append((list(word), close_disp))
                        if len(found) % 500 == 0:
                            print(f"    Found {len(found)} walks (cl={cl})...")
                        if len(found) >= 2000:
                            return

        if cl >= max_cl or len(found) >= 2000:
            return

        # Extend
        for nxt in [(pos + 1) % n, pos, (pos - 1) % n]:
            step_disp = 0
            if (nxt - pos) % n == 1:
                step_disp = 1
            elif (nxt - pos) % n == n - 1:
                step_disp = -1

            new_fc = dict(fc)
            new_fc[nxt] = new_fc.get(nxt, 0) + 1
            new_visited = visited | {nxt}

            dfs(nxt, word + [nxt], disp + step_disp, new_fc, new_visited)

    # Start from position 0 (by symmetry, multiply count by n / equivalence)
    for start in range(1):  # just start=0
        dfs(start, [start], 0, {start: 1}, {start})

    return found

print("\nDFS enumeration of odd-winding walks at n=6, starting at 0, CL ≤ 14...")
walks = count_odd_winding_walks_dp(6, {0, 2, 4}, 6, 14)
print(f"Found {len(walks)} walks with displacement +6")

# Also check displacement -6
walks_neg = count_odd_winding_walks_dp(6, {0, 2, 4}, -6, 14)
print(f"Found {len(walks_neg)} walks with displacement -6")

total_walks = walks + walks_neg
print(f"Total odd-winding walks: {len(total_walks)}")

if total_walks:
    print("\nFirst 5 examples:")
    for w, d in total_walks[:5]:
        fcs = {p: fire_count(w, p) for p in range(6)}
        print(f"  word={w}, len={len(w)}, disp={d}, fc={fcs}")
        # Check singleton edges
        for e in range(6):
            tc = edge_traversal_count(w, 6, e)
            if tc == 1:
                steps = edge_cross_steps(w, 6, e)
                print(f"    SINGLETON edge {e}-{(e+1)%6}: step {steps[0]}, terminal={steps[0]+1==len(w)}")

    # Analyze all walks
    print(f"\nAnalyzing all {len(total_walks)} walks:")
    has_singleton = 0
    has_terminal_singleton = 0
    for w, d in total_walks:
        singletons = []
        for e in range(6):
            tc = edge_traversal_count(w, 6, e)
            if tc == 1:
                steps = edge_cross_steps(w, 6, e)
                singletons.append((e, steps[0]))
        if singletons:
            has_singleton += 1
            for e, s in singletons:
                if s + 1 == len(w):
                    has_terminal_singleton += 1
                    break
    print(f"  Walks with ≥1 singleton edge: {has_singleton}/{len(total_walks)}")
    print(f"  Walks with terminal singleton: {has_terminal_singleton}/{len(total_walks)}")
else:
    print("\nNO odd-winding walks exist for n=6 with binary at {0,2,4} up to CL=14!")
    print("This suggests odd-winding may be impossible for non-consec binary.")

# Now check n=9
print("\n" + "=" * 70)
print("Checking n=9, binary at {0,3,6}, CL ≤ 16...")
print("=" * 70)

# n=9 is too large for full DFS. Let me check a smaller case first.
# At n=7, binary at {0,2,4}:
print("\nFirst: n=7, binary at {0,2,4}, CL ≤ 16...")
walks7 = count_odd_winding_walks_dp(7, {0, 2, 4}, 7, 16)
print(f"Found {len(walks7)} walks with displacement +7")
walks7_neg = count_odd_winding_walks_dp(7, {0, 2, 4}, -7, 16)
print(f"Found {len(walks7_neg)} walks with displacement -7")

total7 = walks7 + walks7_neg
print(f"Total odd-winding walks at n=7: {len(total7)}")

if total7:
    print("First 3 examples:")
    for w, d in total7[:3]:
        fcs = {p: fire_count(w, p) for p in range(7)}
        print(f"  len={len(w)}, disp={d}, fc={fcs}")
else:
    print("NO odd-winding walks at n=7 with non-consec binary up to CL=16!")
