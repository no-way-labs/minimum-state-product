#!/usr/bin/env python3
"""
RA12 Part 2: Deep investigation of the one-binary-neighbor case.

Key questions:
1. In pivot-free placements, does every fc≥3 ternary have a binary neighbor
   with fc_bin = 2 (not 4, 6, ...)?
2. For the n=7 counterexamples (no pivot but fc≥3): what does the
   fc distribution look like at boundary ternary?
3. Can we compute: for every word, the number of ternary procs that have
   (a) fc≥3, (b) ≥1 binary neighbor, (c) that binary neighbor has fc=2?
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
print("RA12 DEEP: ONE-BINARY-NEIGHBOR ANALYSIS")
print("=" * 70)

# Focus on the counterexample placements from Part C
counterexamples = [
    # n=7, pivot-free placements with no_fc3_pivot > 0
    ([3, 3, 3, 2, 2, 2, 3], 7),
    ([2, 3, 3, 2, 3, 3, 2], 7),
    ([2, 2, 2, 2, 3, 3, 3], 7),
    ([2, 2, 2, 2, 2, 3, 3], 7),
]

for ms, n in counterexamples:
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]
    pivots = [t for t in ternary_pos
              if ms[(t-1) % n] == 2 and ms[(t+1) % n] == 2]
    boundary_ter = [t for t in ternary_pos
                    if ms[(t-1) % n] == 2 or ms[(t+1) % n] == 2]
    interior_ter = [t for t in ternary_pos
                    if ms[(t-1) % n] != 2 and ms[(t+1) % n] != 2]

    print(f"\n{'='*60}")
    print(f"ms={ms}")
    print(f"  binary={binary_pos}, ternary={ternary_pos}")
    print(f"  pivots={pivots}, boundary_ter={boundary_ter}, interior_ter={interior_ter}")

    max_cl = sum(ms) + 4
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_cl)
    print(f"  {len(words)} words ({time.time()-t0:.1f}s)")

    # For each word: find the no-pivot-fc3 counterexample words
    # and check the weaker condition
    n_total = 0
    n_has_pivot_fc3 = 0         # some fc≥3 ternary has BOTH binary nbrs
    n_has_boundary_fc3 = 0       # some fc≥3 ternary has ≥1 binary nbr
    n_has_boundary_fc3_binfc2 = 0  # ... and that binary nbr has fc=2
    n_no_hope = 0                # fc≥3 ternary with no binary nbr at all
    n_boundary_binfc4 = 0        # boundary ternary but all binary nbrs have fc≥4

    # Detailed: for the no-pivot cases, what IS the fc at binary neighbors?
    binary_nbr_fc_when_no_pivot = Counter()

    for word in words:
        fc = Counter(word)
        has_fc3 = any(fc[p] >= 3 for p in range(n))
        if not has_fc3:
            continue
        n_total += 1

        # Check pivot condition (both binary nbrs)
        has_pivot = any(fc[p] >= 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2
                       for p in range(n))
        if has_pivot:
            n_has_pivot_fc3 += 1
            continue

        # No pivot. Check boundary condition (≥1 binary nbr)
        found_boundary = False
        found_boundary_fc2 = False
        for t in ternary_pos:
            if fc[t] < 3:
                continue
            # Check neighbors
            L = (t - 1) % n
            R = (t + 1) % n
            bin_nbrs = []
            if ms[L] == 2:
                bin_nbrs.append(L)
            if ms[R] == 2:
                bin_nbrs.append(R)
            if not bin_nbrs:
                continue  # interior ternary
            found_boundary = True
            for b in bin_nbrs:
                binary_nbr_fc_when_no_pivot[fc[b]] += 1
                if fc[b] == 2:
                    found_boundary_fc2 = True

        if found_boundary:
            n_has_boundary_fc3 += 1
            if found_boundary_fc2:
                n_has_boundary_fc3_binfc2 += 1
            else:
                n_boundary_binfc4 += 1
        else:
            n_no_hope += 1

    print(f"  Words with fc≥3: {n_total}")
    print(f"  Has pivot (both-binary-nbr fc≥3): {n_has_pivot_fc3}")
    print(f"  No pivot, has boundary fc≥3: {n_has_boundary_fc3}")
    print(f"    ... with binary nbr fc=2: {n_has_boundary_fc3_binfc2}")
    print(f"    ... with all binary nbrs fc≥4: {n_boundary_binfc4}")
    print(f"  No hope (fc≥3 only at interior ternary): {n_no_hope}")
    print(f"  Binary nbr fc distribution (no-pivot cases): {dict(sorted(binary_nbr_fc_when_no_pivot.items()))}")

    coverage = n_has_pivot_fc3 + n_has_boundary_fc3_binfc2
    print(f"\n  COVERAGE: {coverage}/{n_total} = {100*coverage/n_total:.1f}%")
    if n_boundary_binfc4 > 0:
        print(f"  GAP: {n_boundary_binfc4} words where boundary ternary exists but binary nbr fc≥4")
    if n_no_hope > 0:
        print(f"  GAP: {n_no_hope} words where fc≥3 only at interior ternary")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
The key condition is: find ternary t with fc≥3 and ONE binary neighbor
whose fc = 2 (the minimum for binary).

If binary fc can be 4 or higher, pigeonhole fails:
  4 fires across 3 phases doesn't guarantee a zero phase.

Need to check: does fc_bin = 2 ALWAYS hold for the binary neighbor,
or can it be 4?

Note: at minimum cycle length, every proc fires exactly m_p times.
  So binary fires exactly 2, ternary exactly 3.
  fc_bin = 2 always at minimum CL.

At CL > min: some proc fires extra. If a binary fires 4 instead of 2,
  CL increases by 2. This is possible but means a longer cycle.

For sub-threshold analysis: the question is whether we need to handle
  cycles where binary procs fire more than minimum.
""")

# Check: at minimum CL, do all binary have fc=2?
print("CHECK: fc distribution at minimum cycle length")
for ms, n in counterexamples[:1]:  # just first
    min_cl = sum(ms)
    words_min = [w for w in enumerate_mover_words(ms, n, min_cl) if len(w) == min_cl]
    print(f"\nms={ms}, min_cl={min_cl}, {len(words_min)} min-length words")
    for word in words_min[:5]:
        fc = {p: Counter(word)[p] for p in range(n)}
        print(f"  fc={fc}")
    if words_min:
        all_binary_fc2 = all(
            all(Counter(w)[b] == 2 for b in range(n) if ms[b] == 2)
            for w in words_min
        )
        print(f"  All binary fc=2 at min CL: {all_binary_fc2}")
