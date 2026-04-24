#!/usr/bin/env python3
"""
Prototype the PhaseProfile finite check for non-consecutive EC.

For a ternary proc t sandwiched between binary bL and bR:
- Each phase k (c[t] = 0,1,2) has counts M, J, K
- M = number of times t fires while c[t]=k
- J = number of times bL fires while c[t]=k
- K = number of times bR fires while c[t]=k

The 4 mechanisms check (M, J, K, parities, singleton order).

QUESTION 1: How many distinct (M, J, K) profiles exist across all cycles?
QUESTION 2: Does every profile trigger at least one mechanism?
QUESTION 3: What is the maximum M, J, K value? (determines finite type size)
QUESTION 4: Can we bound M, J, K independent of n?

Extract from n=5,6 cycles and tabulate.
"""
from itertools import product as iproduct
from collections import Counter
import time

def analyze_profiles(n, ms, max_len):
    binary_procs = [p for p in range(n) if ms[p] == 2]
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    all_configs = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(all_configs)}
    total = len(all_configs)

    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    # Enumerate mover words (nearest-neighbor walks that return to start)
    results = []
    start = tuple(0 for _ in range(n))

    def dfs(word, fc, config):
        if len(word) > max_len:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
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

    print(f"\nn={n}, ms={ms}, sandwiched={sandwiched}")
    print(f"Found {len(results)} mover words")

    # Build cycles and extract phase profiles
    all_profiles = Counter()  # (M, J, K) per phase
    all_profiles_full = Counter()  # (M, J, K, J%2, K%2)
    max_M, max_J, max_K = 0, 0, 0

    mechanism_coverage = Counter()
    uncovered_profiles = set()

    for word in results:
        ell = len(word)
        configs = [list(start)]
        for i in range(ell):
            c = list(configs[-1])
            c[word[i]] = (c[word[i]] + 1) % ms[word[i]]
            configs.append(c)

        # Check wrap adjacency
        if abs(word[-1] - word[0]) % n not in (1, n-1):
            continue

        for t in sandwiched:
            bL = (t-1) % n
            bR = (t+1) % n
            fc_t = sum(1 for s in range(ell) if word[s] == t)
            M_per_phase = fc_t // 3

            for k in range(3):
                # Steps where c[t] = k
                steps_in_phase = [s for s in range(ell) if configs[s][t] == k]
                M = sum(1 for s in steps_in_phase if word[s] == t)
                J = sum(1 for s in steps_in_phase if word[s] == bL)
                K = sum(1 for s in steps_in_phase if word[s] == bR)

                max_M = max(max_M, M)
                max_J = max(max_J, J)
                max_K = max(max_K, K)

                all_profiles[(M, J, K)] += 1
                all_profiles_full[(M, J, K, J%2, K%2)] += 1

                # Check which mechanism covers this
                covered = False
                if M == 1 and J % 2 == 0 and K % 2 == 0:
                    mechanism_coverage['both-even'] += 1
                    covered = True
                elif (J >= 3 and K == 0) or (J == 0 and K >= 3):
                    mechanism_coverage['toggle-FR'] += 1
                    covered = True
                elif M == 1 and ((J >= 2 and K == 0) or (J == 0 and K >= 2)):
                    mechanism_coverage['zero-side'] += 1
                    covered = True
                elif M == 1 and (J, K) in [(2, 1), (1, 2)]:
                    mechanism_coverage['traversal-return'] += 1
                    covered = True

                if not covered:
                    uncovered_profiles.add((M, J, K, J%2, K%2))

    print(f"\nMax M={max_M}, J={max_J}, K={max_K}")
    print(f"\nDistinct (M, J, K) profiles: {len(all_profiles)}")
    for k in sorted(all_profiles):
        print(f"  {k}: {all_profiles[k]}")

    print(f"\nMechanism coverage:")
    total_phases = sum(all_profiles.values())
    for mech in sorted(mechanism_coverage):
        print(f"  {mech}: {mechanism_coverage[mech]} ({100*mechanism_coverage[mech]/total_phases:.1f}%)")

    covered_count = sum(mechanism_coverage.values())
    print(f"\nTotal phases: {total_phases}")
    print(f"Covered: {covered_count} ({100*covered_count/total_phases:.1f}%)")
    print(f"Uncovered: {total_phases - covered_count}")

    if uncovered_profiles:
        print(f"\nUncovered (M,J,K,J%2,K%2):")
        for p in sorted(uncovered_profiles):
            print(f"  {p}")
    else:
        print(f"\n*** ALL PHASES COVERED BY 4 MECHANISMS ***")

    return all_profiles

# Test
t0 = time.time()
analyze_profiles(5, [2,3,2,3,2], 16)
print(f"\nTime: {time.time()-t0:.1f}s")

t0 = time.time()
analyze_profiles(6, [2,3,2,3,2,3], 20)
print(f"\nTime: {time.time()-t0:.1f}s")
