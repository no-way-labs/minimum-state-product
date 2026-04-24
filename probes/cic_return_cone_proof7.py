#!/usr/bin/env python3
"""
CIC Exploration 11g: Classify the kill mechanism precisely.

From proof3.py: 0 survivors. Every word killed by:
  - Tool 2 (>= 2 singletons or return cone): 53076
  - Shadow (pure sweep): 571142
  Total: 624218

But proof6.py shows: 40782 fair words with max_L=20, only 2 sweeps.
So proof3.py found 624218 with max_L=24, including many more sweeps.

Key question: of the non-sweep words, are they killed by:
(a) >= 2 singleton edges alone, or
(b) return cones, or
(c) both?

If (a) suffices for all: the Two-Singleton-Edge Theorem is universal
for non-sweeps, and the proof is:
  Shadow kills sweeps + Two-Singleton kills non-sweeps.
"""

from collections import Counter


def is_pure_sweep(word, n):
    L = len(word)
    return (all((word[(i+1)%L]-word[i]) % n == 1 for i in range(L)) or
            all((word[i]-word[(i+1)%L]) % n == 1 for i in range(L)))


def count_singletons(word, n):
    edge_counts = Counter()
    L = len(word)
    for i in range(L):
        a, b = word[i], word[(i+1) % L]
        if abs(a - b) == 1:
            e = (min(a, b), max(a, b))
        else:
            e = (0, n - 1)
        edge_counts[e] += 1
    return sum(1 for c in edge_counts.values() if c == 1)


def check_return_cone(word, n):
    L = len(word)
    proc_pos = {p: set() for p in range(n)}
    for t in range(L):
        proc_pos[word[t]].add(t)

    for start in range(n):
        for length in range(1, n):
            S = set((start + i) % n for i in range(length))
            all_pos = set()
            for p in S:
                all_pos |= proc_pos[p]
            if not all_pos or len(all_pos) == L:
                continue
            sorted_pos = sorted(all_pos)
            max_gap = 0
            for i in range(len(sorted_pos)):
                if i + 1 < len(sorted_pos):
                    gap = sorted_pos[i+1] - sorted_pos[i] - 1
                else:
                    gap = (sorted_pos[0] + L) - sorted_pos[-1] - 1
                max_gap = max(max_gap, gap)
            if max_gap > 0 and max_gap == L - len(all_pos):
                return True
    return False


def classify_kills(n, binary_positions, max_L):
    """Classify how each fair word is killed."""
    binary_set = set(binary_positions)
    k = len(binary_positions)

    total = 0
    kill_sweep = 0
    kill_singleton_only = 0  # >= 2 singletons, no cone
    kill_cone_only = 0       # cone, < 2 singletons
    kill_both = 0            # both >= 2 singletons and cone
    survivors = []

    # Track singleton distribution for non-sweeps
    singleton_dist = Counter()

    def dfs(word, mc):
        nonlocal total, kill_sweep
        nonlocal kill_singleton_only, kill_cone_only, kill_both

        L = len(word)
        if L > max_L:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            d = abs(current - first)
            if d == 1 or d == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0
                           for b in binary_positions):
                        total += 1

                        if is_pure_sweep(word, n):
                            kill_sweep += 1
                            return

                        s = count_singletons(word, n)
                        singleton_dist[s] += 1
                        has_s = s >= 2
                        has_c = check_return_cone(word, n)

                        if has_s and has_c:
                            kill_both += 1
                        elif has_s:
                            kill_singleton_only += 1
                        elif has_c:
                            kill_cone_only += 1
                        else:
                            survivors.append(
                                (list(word), s))

        for np_ in [(current-1) % n, (current+1) % n]:
            mc[np_] += 1
            word.append(np_)
            dfs(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs([0], mc)

    ns = total - kill_sweep
    print(f"\nn={n} k={k} bin={binary_positions} maxL={max_L}")
    print(f"  Total: {total}")
    print(f"  Sweeps: {kill_sweep}")
    print(f"  Non-sweep: {ns}")
    print(f"    Killed by >=2 singletons only: "
          f"{kill_singleton_only}")
    print(f"    Killed by cone only: {kill_cone_only}")
    print(f"    Killed by both: {kill_both}")
    print(f"    Survivors: {len(survivors)}")
    print(f"  Non-sweep singleton dist: "
          f"{dict(sorted(singleton_dist.items()))}")

    if survivors:
        print(f"  *** SURVIVORS ***")
        for w, s in survivors[:5]:
            print(f"    {w} S={s}")
    else:
        if ns > 0:
            s_pct = 100 * (kill_singleton_only + kill_both)
            s_pct /= ns
            c_pct = 100 * (kill_cone_only + kill_both) / ns
            print(f"  Singletons suffice for: {s_pct:.1f}%")
            print(f"  Cones suffice for: {c_pct:.1f}%")

    return len(survivors)


def main():
    print("CIC Exploration 11g: Kill mechanism classification")
    print("=" * 60)

    total_surv = 0

    # n=6, k=3
    total_surv += classify_kills(6, [0, 2, 4], max_L=18)

    # n=7, k=3
    total_surv += classify_kills(7, [0, 2, 4], max_L=18)
    total_surv += classify_kills(7, [0, 2, 5], max_L=18)

    # n=8, k=3
    total_surv += classify_kills(8, [0, 2, 5], max_L=18)
    total_surv += classify_kills(8, [0, 3, 6], max_L=18)

    # n=9, k=3
    total_surv += classify_kills(9, [0, 3, 6], max_L=18)

    # k=4
    total_surv += classify_kills(8, [0, 2, 4, 6], max_L=18)

    print(f"\n{'='*60}")
    print(f"TOTAL SURVIVORS: {total_surv}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()
