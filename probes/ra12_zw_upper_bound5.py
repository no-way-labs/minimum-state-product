#!/usr/bin/env python3
"""
RA12 Part 5: Definitive proof of CL ≤ 2n.

The approach: prove that in a ZW good cycle with fc ≥ 2, the number of
non-binary stays is bounded by 2*cwSteps - 2*(n-1), which combined with
CL = 2*cwSteps + staySteps ≥ 2n forces CL = 2n.

Actually, let me try to find the RIGHT proof via a systematic analysis of
what constraints we have and what they imply.

CONSTRAINTS:
C1: Closed walk on C_n (steps ±1, 0)
C2: Zero winding (cwSteps = ccwSteps)
C3: fc(p) ≥ 2 for all p
C4: Binary procs: max run length 1 (no consecutive firing)
C5: Ternary procs: max run length 2
C6: Distinct configs
C7: At most 1 uncrossed edge (from C3 + connectivity)
C8: Edge balance: cwMoveCountAt(e) = ccwMoveCountAt(e) for all e (from C2)

FROM THESE:
CL = 2*cwSteps + staySteps (C1 + C2)
CL = sum fc(p) ≥ 2n (C3)
staySteps = sum_{non-binary} stayMoveCountAt(p) (C4)

QUESTION: Do C1-C8 + sub-threshold + ≥3 binary + n≥9 imply CL ≤ 2n?

Let me try to find abstract walks satisfying C1-C5 with CL > 2n and check
whether C6 (distinct configs) can be satisfied.
"""

from itertools import product as cprod
from collections import Counter, defaultdict

def enumerate_closed_walks(n, target_len, require_zw=True, require_fc2=True,
                           binary_positions=None, max_ternary_run=2):
    """
    Enumerate closed walks on C_n of given length satisfying constraints.
    binary_positions: set of positions that are binary (max run 1).
    Other positions are ternary (max run 2).
    """
    if binary_positions is None:
        binary_positions = set()

    results = []

    def dfs(pos_seq, step_idx):
        if len(results) > 10000:
            return

        curr = pos_seq[-1]

        if step_idx == target_len:
            # Check closure
            if curr != pos_seq[0]:
                return
            # Check zero winding
            if require_zw:
                cw = sum(1 for i in range(target_len)
                         if (pos_seq[i+1] - pos_seq[i]) % n == 1)
                ccw = sum(1 for i in range(target_len)
                          if (pos_seq[i+1] - pos_seq[i]) % n == n-1)
                if cw != ccw:
                    return
            # Check fc ≥ 2
            if require_fc2:
                fc = Counter(pos_seq[:-1])  # exclude duplicate last
                if any(fc[p] < 2 for p in range(n)):
                    return
            results.append(list(pos_seq[:-1]))
            return

        # Try next position: left, same, right
        for delta in [-1, 0, 1]:
            nxt = (curr + delta) % n

            # Check run length constraint
            new_seq = pos_seq + [nxt]

            # Count current run length at nxt
            run_len = 1
            for j in range(len(new_seq) - 2, -1, -1):
                if new_seq[j] == nxt:
                    run_len += 1
                else:
                    break

            if nxt in binary_positions and run_len > 1:
                continue
            if nxt not in binary_positions and run_len > max_ternary_run:
                continue

            # Also check: if this is a stay at binary, skip
            if delta == 0 and curr in binary_positions:
                continue

            dfs(new_seq, step_idx + 1)

    # Start from position 0
    dfs([0], 0)
    return results

# Test: n=5, 3 binary at 0,1,2, all ternary at 3,4
print("="*70)
print("Walks on C_5 with binary at {0,1,2}, ZW, fc≥2")
print("="*70)

binary_pos = {0, 1, 2}
n = 5

for L in range(10, 16):
    walks = enumerate_closed_walks(n, L, require_zw=True, require_fc2=True,
                                    binary_positions=binary_pos, max_ternary_run=2)
    if walks:
        fc_dist = Counter(tuple(sorted(Counter(w).values())) for w in walks)
        stay_counts = []
        for w in walks:
            stays = sum(1 for i in range(L) if w[i] == w[(i+1) % L])
            stay_counts.append(stays)
        stay_dist = Counter(stay_counts)
        print(f"  L={L}: {len(walks)} walks, fc_dist={dict(fc_dist)}, stay_dist={dict(stay_dist)}")
    else:
        print(f"  L={L}: 0 walks")

print()
print("="*70)
print("Walks on C_9 with binary at {0,1,2}, ZW, fc≥2")
print("="*70)

# n=9 is the target. But enumeration at n=9 with L=18+ is exponential.
# Let me try n=7 instead.

n = 7
binary_pos = {0, 1, 2}

for L in range(14, 18):
    walks = enumerate_closed_walks(n, L, require_zw=True, require_fc2=True,
                                    binary_positions=binary_pos, max_ternary_run=2)
    if walks:
        stay_dist = Counter(sum(1 for i in range(L) if w[i] == w[(i+1) % L]) for w in walks)
        print(f"  L={L}: {len(walks)} walks, stay_dist={dict(sorted(stay_dist.items()))}")
        if L > 2*n:
            # Show examples
            for w in walks[:3]:
                fc = [0]*n
                for p in w:
                    fc[p] += 1
                print(f"    walk={w}, fc={fc}")
    else:
        print(f"  L={L}: 0 walks")

# KEY TEST: at n=5, are there walks with L=11 (= 2*5+1) satisfying all constraints?
# If yes: CL ≤ 2n is FALSE for abstract walks with the run-length constraint.
# If no: CL ≤ 2n follows from run-length constraints alone.

print()
print("="*70)
print("CRITICAL TEST: Can L > 2n with all walk constraints?")
print("="*70)

n = 5
binary_pos = {0, 1, 2}

for L in [10, 11, 12]:
    walks = enumerate_closed_walks(n, L, require_zw=True, require_fc2=True,
                                    binary_positions=binary_pos, max_ternary_run=2)
    print(f"  n={n}, L={L}: {len(walks)} walks")
    if walks and L > 2*n:
        for w in walks[:5]:
            fc = [0]*n
            for p in w:
                fc[p] += 1
            stays = sum(1 for i in range(L) if w[i] == w[(i+1) % L])
            cw = sum(1 for i in range(L) if (w[(i+1)%L] - w[i]) % n == 1)
            print(f"    walk={w}, fc={fc}, stays={stays}, cw={cw}")

# Now try with 4 binary
print()
binary_pos = {0, 1, 2, 3}  # 4 binary
for L in [10, 11, 12]:
    walks = enumerate_closed_walks(n, L, require_zw=True, require_fc2=True,
                                    binary_positions=binary_pos, max_ternary_run=2)
    print(f"  n={n}, L={L} (4 binary): {len(walks)} walks")
    if walks and L > 2*n:
        for w in walks[:5]:
            fc = [0]*n
            for p in w:
                fc[p] += 1
            stays = sum(1 for i in range(L) if w[i] == w[(i+1) % L])
            print(f"    walk={w}, fc={fc}, stays={stays}")

# Try with non-consecutive binary
print()
binary_pos = {0, 2, 4}  # non-consecutive binary
for L in [10, 11, 12]:
    walks = enumerate_closed_walks(n, L, require_zw=True, require_fc2=True,
                                    binary_positions=binary_pos, max_ternary_run=2)
    print(f"  n={n}, L={L} (non-consec binary): {len(walks)} walks")
    if walks and L > 2*n:
        for w in walks[:5]:
            fc = [0]*n
            for p in w:
                fc[p] += 1
            stays = sum(1 for i in range(L) if w[i] == w[(i+1) % L])
            print(f"    walk={w}, fc={fc}, stays={stays}")
