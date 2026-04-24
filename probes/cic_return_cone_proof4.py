#!/usr/bin/env python3
"""
CIC Exploration 11d: The real theorem is simpler than expected.

Discovery from 11c: Tool 3 (binary-bounce) is NEVER needed.
ALL non-sweep fair words are killed by Tool 2 (>= 2 singletons OR return cone).

Hypothesis: Every non-sweep fair adjacent cyclic mover word on C_n with
k >= 3 non-adjacent binary processors has EITHER >= 2 singleton edges OR
a return cone.

This would give a 1-tool proof: Shadow kills sweeps, Tool 2 kills everything else.

Let's verify this and understand WHY it holds.
"""

from collections import Counter
import sys


def is_pure_sweep(word, n):
    """All steps in same direction."""
    for i in range(len(word)):
        diff = (word[(i+1) % len(word)] - word[i]) % n
        if diff != 1 and diff != n - 1:
            return False
    return True


def count_singletons(word, n):
    """Count edges with traversal count = 1."""
    edge_counts = Counter()
    L = len(word)
    for i in range(L):
        a, b = word[i], word[(i+1) % L]
        if abs(a - b) == 1:
            e = (min(a, b), max(a, b))
        else:
            e = (0, n-1)
        edge_counts[e] += 1
    return sum(1 for c in edge_counts.values() if c == 1), edge_counts


def check_return_cone(word, n):
    """Check for nontrivial return cone."""
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
                return True, S
    return False, None


def get_winding(word, n):
    """Get winding number."""
    L = len(word)
    fwd = sum(1 for i in range(L) if (word[(i+1)%L] - word[i]) % n == 1)
    bwd = L - fwd
    return fwd - bwd


def verify_nonsweep_tool2(n, gap_sizes, max_L):
    """Verify ALL non-sweep fair words have >= 2 singletons or return cone."""
    k = len(gap_sizes)
    binary_positions = []
    pos = 0
    for i in range(k):
        binary_positions.append(pos)
        pos += 1 + gap_sizes[i]
    assert pos == n

    binary_set = set(binary_positions)
    ring = ''.join('B' if i in binary_set else 'T' for i in range(n))
    print(f"\nn={n}, k={k}, gaps={gap_sizes}, ring={ring}, max_L={max_L}")

    total = 0
    sweeps = 0
    singleton_kills = 0
    cone_kills = 0
    both_kills = 0
    survivors = []

    # Track distribution
    winding_dist = Counter()
    singleton_dist = Counter()

    def dfs(word, move_counts):
        nonlocal total, sweeps, singleton_kills, cone_kills, both_kills

        L = len(word)
        if L > max_L:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in move_counts):
                    if all(move_counts[b] % 2 == 0 for b in binary_positions):
                        total += 1

                        if is_pure_sweep(word, n):
                            sweeps += 1
                            return

                        s_count, ec = count_singletons(word, n)
                        W = get_winding(word, n)
                        winding_dist[W] += 1
                        singleton_dist[s_count] += 1

                        has_cone, cone_S = check_return_cone(word, n)

                        if s_count >= 2 and has_cone:
                            both_kills += 1
                        elif s_count >= 2:
                            singleton_kills += 1
                        elif has_cone:
                            cone_kills += 1
                        else:
                            survivors.append((list(word), s_count, W, ec))
                            if len(survivors) <= 3:
                                print(f"  SURVIVOR: {word} S={s_count} W={W}")

        for next_p in [(current - 1) % n, (current + 1) % n]:
            move_counts[next_p] += 1
            word.append(next_p)
            dfs(word, move_counts)
            word.pop()
            move_counts[next_p] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs([0], mc)

    nonsweep = total - sweeps
    print(f"  Total fair: {total}, Sweeps: {sweeps}, Non-sweep: {nonsweep}")
    print(f"  Non-sweep kills: singleton≥2={singleton_kills}, cone={cone_kills}, both={both_kills}")
    print(f"  Survivors: {len(survivors)}")
    if nonsweep > 0:
        print(f"  Winding dist (non-sweep): {dict(sorted(winding_dist.items()))}")
        print(f"  Singleton dist (non-sweep): {dict(sorted(singleton_dist.items()))}")

    if survivors:
        print(f"  *** SURVIVORS ***")
        for w, s, W, ec in survivors[:5]:
            print(f"    {w} S={s} W={W} edges={dict(sorted(ec.items()))}")
    else:
        print(f"  ✓ ALL non-sweep words killed by Tool 2")

    return len(survivors)


def main():
    total = 0

    # n=6
    total += verify_nonsweep_tool2(6, [1, 1, 1], max_L=24)

    # n=7, all gap patterns
    total += verify_nonsweep_tool2(7, [1, 1, 2], max_L=24)
    total += verify_nonsweep_tool2(7, [1, 2, 1], max_L=24)

    # n=8, representative gap patterns
    total += verify_nonsweep_tool2(8, [1, 1, 3], max_L=22)
    total += verify_nonsweep_tool2(8, [1, 2, 2], max_L=22)
    total += verify_nonsweep_tool2(8, [2, 1, 2], max_L=22)
    total += verify_nonsweep_tool2(8, [2, 2, 1], max_L=22)

    # n=9 with small max_L
    total += verify_nonsweep_tool2(9, [1, 1, 4], max_L=22)
    total += verify_nonsweep_tool2(9, [1, 2, 3], max_L=22)
    total += verify_nonsweep_tool2(9, [2, 2, 2], max_L=22)

    # k=4 binary
    total += verify_nonsweep_tool2(8, [1, 1, 1, 1], max_L=20)
    total += verify_nonsweep_tool2(9, [1, 1, 1, 2], max_L=20)

    print(f"\n{'='*70}")
    print(f"GRAND TOTAL SURVIVORS: {total}")
    if total == 0:
        print(f"THEOREM VERIFIED: Shadow + Tool 2 kill everything.")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
