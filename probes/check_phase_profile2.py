#!/usr/bin/env python3
"""
Fixed phase profile check — per-CYCLE coverage (not per-phase).
A cycle is covered if ANY phase at ANY sandwiched ternary proc triggers a mechanism.
Also fix n=6 wrap adjacency issue.
"""
from itertools import product as iproduct
from collections import Counter
import time

def temporal_order(steps, ell):
    if len(steps) <= 1:
        return steps
    max_gap = 0
    start_after = 0
    for i in range(len(steps)):
        nxt = (i + 1) % len(steps)
        gap = (steps[nxt] - steps[i]) % ell
        if gap > max_gap:
            max_gap = gap
            start_after = i
    start_idx = (start_after + 1) % len(steps)
    return [steps[(start_idx + i) % len(steps)] for i in range(len(steps))]

def analyze_profiles(n, ms, max_len):
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    start = tuple(0 for _ in range(n))

    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
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

    print(f"\nn={n}, ms={ms}, sandwiched={sandwiched}")
    print(f"Found {len(results)} mover words")

    # Per-cycle coverage check
    total_cycles = 0
    covered_cycles = 0
    uncovered_examples = []
    profile_set = set()
    M_values = set()

    for word in results:
        ell = len(word)
        configs = [list(start)]
        for i in range(ell):
            c = list(configs[-1])
            c[word[i]] = (c[word[i]] + 1) % ms[word[i]]
            configs.append(c)

        total_cycles += 1
        cycle_covered = False

        for t in sandwiched:
            bL = (t-1) % n
            bR = (t+1) % n

            for k in range(3):
                raw = sorted(s for s in range(ell) if configs[s][t] == k)
                steps = temporal_order(raw, ell)
                M = sum(1 for s in steps if word[s] == t)
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                M_values.add(M)
                profile_set.add((M, J, K))

                # Check mechanisms
                M_per = M  # M per phase
                if M_per == 1 and J % 2 == 0 and K % 2 == 0:
                    cycle_covered = True; break
                if (J >= 3 and K == 0) or (J == 0 and K >= 3):
                    cycle_covered = True; break
                if M_per == 1 and ((J >= 2 and K == 0) or (J == 0 and K >= 2)):
                    cycle_covered = True; break
                if M_per == 1 and (J, K) in [(2, 1), (1, 2)]:
                    # Check singleton-first
                    for s in steps:
                        if word[s] in (bL, bR):
                            single = bR if J == 2 else bL
                            if word[s] == single:
                                cycle_covered = True
                            break
                    if cycle_covered: break
            if cycle_covered: break

        if cycle_covered:
            covered_cycles += 1
        else:
            if len(uncovered_examples) < 5:
                uncovered_examples.append(word)

    print(f"\nTotal cycles: {total_cycles}")
    print(f"Covered: {covered_cycles} ({100*covered_cycles/max(1,total_cycles):.1f}%)")
    print(f"Uncovered: {total_cycles - covered_cycles}")
    print(f"M values seen: {sorted(M_values)}")
    print(f"Distinct profiles (M,J,K): {len(profile_set)}")
    for p in sorted(profile_set):
        print(f"  {p}")

    if uncovered_examples:
        print(f"\nUncovered example words:")
        for w in uncovered_examples[:3]:
            print(f"  {w}")
    else:
        print(f"\n*** ALL CYCLES COVERED ***")

# Run
for n, ms, ml in [(5, [2,3,2,3,2], 16), (6, [2,3,2,3,2,3], 24)]:
    t0 = time.time()
    analyze_profiles(n, ms, ml)
    print(f"Time: {time.time()-t0:.1f}s")
