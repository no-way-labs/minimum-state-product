#!/usr/bin/env python3
"""
RA12 Part 3: Investigate the gap cases where boundary ternary's
binary neighbor has fc >= 4.

Key question: In these gap cases, does ANOTHER ternary proc
(possibly non-boundary) provide the needed condition?

Also: can we use fc_bin >= 4 with fc_ter >= 6 to get zero-sided?
If fc_ter = 6 (double ternary) and fc_bin = 4: 4 across 6 phases ->
  pigeonhole: some phase has 0 bin-fires. YES! 4 < 6.

General: zero-sided exists if fc_bin < fc_ter (strict).
  fc_bin fires across fc_ter phases -> some phase has 0 fires.

So the condition weakens to: ternary t with fc_t >= 3, binary nbr b
with fc_b < fc_t.

Check: is fc_b < fc_t always satisfied for some (t, b) pair?
"""
import sys, os, time
from collections import Counter

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


print("=" * 70)
print("RA12 GAP: WEAKER CONDITION fc_bin < fc_ter")
print("=" * 70)

# The weakest pigeonhole condition for zero-sided:
# fc_bin fires distributed across fc_ter phases.
# If fc_bin < fc_ter: some phase has 0 fires. Guaranteed.

cases = [
    ([3, 3, 3, 2, 2, 2, 3], 7),
    ([2, 3, 3, 2, 3, 3, 2], 7),
    ([2, 2, 2, 2, 3, 3, 3], 7),
    ([2, 2, 2, 2, 2, 3, 3], 7),
]

for ms, n in cases:
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    max_cl = sum(ms) + 4
    words = enumerate_mover_words(ms, n, max_cl)

    print(f"\nms={ms}, {len(words)} words")
    print(f"  binary={binary_pos}, ternary={ternary_pos}")

    # For each word: check weakest condition
    # Condition A: some ternary t has binary nbr b with fc_b < fc_t
    # Condition B: some ternary t has binary nbr b with fc_b = 2 and fc_t >= 3
    # Condition C: some ternary t has both binary nbrs (pivot) and fc_t >= 3

    n_total = 0
    n_condA = 0
    n_condB = 0
    n_condC = 0
    n_gap = 0
    gap_examples = []

    for word in words:
        fc = Counter(word)
        has_fc3 = any(fc[p] >= 3 for p in range(n))
        if not has_fc3:
            continue
        n_total += 1

        # Check conditions
        satisfies_A = False
        satisfies_B = False
        satisfies_C = False

        for t in ternary_pos:
            if fc[t] < 3:
                continue
            L = (t - 1) % n
            R = (t + 1) % n
            bin_nbrs = [x for x in [L, R] if ms[x] == 2]

            for b in bin_nbrs:
                if fc[b] < fc[t]:
                    satisfies_A = True
                if fc[b] == 2:
                    satisfies_B = True
                if ms[L] == 2 and ms[R] == 2:
                    satisfies_C = True

        if satisfies_A:
            n_condA += 1
        if satisfies_B:
            n_condB += 1
        if satisfies_C:
            n_condC += 1
        if not satisfies_A:
            n_gap += 1
            if len(gap_examples) < 5:
                gap_examples.append({p: fc[p] for p in range(n)})

    print(f"  Total fc≥3 words: {n_total}")
    print(f"  Cond C (pivot, both binary): {n_condC} ({100*n_condC/n_total:.1f}%)")
    print(f"  Cond B (1 binary nbr, fc=2): {n_condB} ({100*n_condB/n_total:.1f}%)")
    print(f"  Cond A (1 binary nbr, fc<fc_t): {n_condA} ({100*n_condA/n_total:.1f}%)")
    print(f"  Gap (no condition satisfied): {n_gap}")

    if gap_examples:
        print(f"  Gap examples:")
        for ex in gap_examples:
            print(f"    fc={ex}")
            # For each gap example, show the ternary fc and their binary nbr fc
            for t in ternary_pos:
                if ex[t] >= 3:
                    L = (t - 1) % n
                    R = (t + 1) % n
                    bin_nbrs = [(x, ex[x]) for x in [L, R] if ms[x] == 2]
                    print(f"      ter t={t} fc={ex[t]}, bin nbrs: {bin_nbrs}")

print("\n" + "=" * 70)
print("ADDITIONAL CHECK: ALL PROCS, NOT JUST TERNARY")
print("=" * 70)
print("""
What if we use a BINARY proc as the target instead?
Binary proc b has fc_b >= 2 (even). If fc_b >= 4, it has 4 fires across
at least 2 phases. Not enough for pigeonhole.

But wait: the phase structure for binary is different.
Binary proc fires fc_b/2 "full cycles" of its 2 states.
Phases at binary proc: fc_b/2 phases? Or fc_b phases?

Actually, phases are defined by the ternary TernaryPhase structure:
each "phase" of a ternary proc t is one full 3-cycle (0→1→2→0).
The number of phases = fc_t / 3.

For binary: each "phase" would be one full 2-cycle (0→1→0).
Number of phases = fc_b / 2.

The phase_dispatch_ec machinery is specific to ternary procs.
So using binary as target doesn't help directly.
""")

# Final check: among gap cases, what's the relationship?
print("=" * 70)
print("CONDITION A GAP ANALYSIS")
print("=" * 70)

# For gap cases (cond A fails): fc_bin >= fc_ter for ALL (ter, bin_nbr) pairs
# Since fc_ter >= 3 (ternary minimum) and fc_bin >= 2 (binary minimum):
# Gap means fc_bin >= fc_ter >= 3 for all pairs.
# But fc_bin is even and >= fc_ter >= 3, so fc_bin >= 4.
# And fc_ter = 3 or 6 or 9...
# fc_bin >= 3 and even -> fc_bin >= 4.
# If fc_ter = 3 and fc_bin >= 4: cond A fails (4 >= 3).
# If fc_ter = 6 and fc_bin >= 6: cond A fails (6 >= 6).

# So the gap has: for every boundary ternary t,
#   fc_t = 3 and all binary nbrs have fc >= 4, OR
#   fc_t = 6 and all binary nbrs have fc >= 6, etc.

# The critical sub-case: fc_t = 3, fc_bin = 4 (minimum gap).
# 4 fires across 3 phases: can have (2,1,1) or (2,2,0) or (1,1,2) etc.
# Pigeonhole says max phase has >= ceil(4/3) = 2 fires.
# But min phase could be 0 or 1.
# NOT guaranteed to have a zero phase.

# However: there are 3 phases and 4 fires.
# Average = 4/3 > 1. So all phases could have >= 1 fire.
# Distribution (2,1,1) has no zero phase.
# Distribution (4,0,0) has two zero phases.
# So it depends on the actual firing pattern.

print("Gap case: fc_ter = 3, fc_bin = 4")
print("4 binary fires across 3 ternary phases.")
print("Possible distributions: (2,1,1), (3,1,0), (2,2,0), (4,0,0)")
print("Zero phase exists in 3 of 4 distributions, NOT in (2,1,1) or (1,2,1) or (1,1,2).")
print()
print("So pigeonhole ALONE doesn't give zero-sided when fc_bin >= fc_ter.")
print("Need additional structural argument for these cases.")
print()

# But how common is the gap?
total_gap = 0
total_all = 0
for ms, n in cases:
    max_cl = sum(ms) + 4
    words = enumerate_mover_words(ms, n, max_cl)
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    for word in words:
        fc = Counter(word)
        if not any(fc[p] >= 3 for p in range(n)):
            continue
        total_all += 1

        satisfies_A = any(
            fc[t] >= 3 and ms[(t-1)%n] == 2 and fc[(t-1)%n] < fc[t]
            or fc[t] >= 3 and ms[(t+1)%n] == 2 and fc[(t+1)%n] < fc[t]
            for t in ternary_pos
        )
        if not satisfies_A:
            total_gap += 1

print(f"TOTAL: {total_gap}/{total_all} words in gap = {100*total_gap/total_all:.2f}%")
print("These are the words where NO ternary has a binary nbr with strictly lower fc.")
