#!/usr/bin/env python3
"""
CIC Exploration 11c: Clean verification — Tool 2 + Tool 3 kill all non-sweep words.

Fix the fairness bug from proof1.py and verify the theorem.
"""

from collections import Counter
import sys

def check_return_cone(word, n):
    """Check if cyclic word has a nontrivial return cone."""
    L = len(word)
    proc_positions = {p: set() for p in range(n)}
    for t in range(L):
        proc_positions[word[t]].add(t)

    for start in range(n):
        for length in range(1, n):
            S = set((start + i) % n for i in range(length))
            all_pos = set()
            for p in S:
                all_pos |= proc_positions[p]
            if not all_pos or len(all_pos) == L:
                continue

            # Check contiguity: all positions in all_pos form a single cyclic interval
            sorted_pos = sorted(all_pos)
            # Find largest gap
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


def check_binary_bounce(word, n, binary_set):
    """
    Check Tool 3: binary-bounce context lemma.

    For each non-binary proc p adjacent to binary b:
    Find interval ending at a p-move where p and q (other neighbor) are frozen,
    and b moves exactly twice.
    """
    L = len(word)

    for b in range(n):
        if b not in binary_set:
            continue
        for p in [(b-1) % n, (b+1) % n]:
            if p in binary_set:
                continue
            q = (2*p - b) % n  # other neighbor of p (p + (p-b))

            p_positions = [i for i in range(L) if word[i] == p]
            if not p_positions:
                continue

            for u in p_positions:
                # Scan backward from u to find interval where p and q are frozen
                t = (u - 1) % L
                b_count = 0
                steps = 0
                valid = True

                while steps < L - 1:
                    mover = word[t]
                    if mover == p or mover == q:
                        valid = False
                        break
                    if mover == b:
                        b_count += 1
                        if b_count > 2:
                            valid = False
                            break
                    t = (t - 1) % L
                    steps += 1

                if valid and b_count == 2:
                    return True

                # Also try scanning forward and looking for sub-intervals
                # where both p and q are frozen and b moves exactly twice.
                # More granular approach:
                # Walk backward from u, tracking b-moves and stopping at p/q moves.

    # More thorough: check ALL sub-intervals where p, q frozen and b moves exactly 2
    for b in range(n):
        if b not in binary_set:
            continue
        for p in [(b-1) % n, (b+1) % n]:
            if p in binary_set:
                continue
            q = (2*p - b) % n

            p_positions = [i for i in range(L) if word[i] == p]
            q_positions = set(i for i in range(L) if word[i] == q)

            for u_idx in range(len(p_positions)):
                u = p_positions[u_idx]
                # Previous p-move (or wrap around)
                prev_p = p_positions[u_idx - 1]

                # The interval (prev_p, u) is where p is frozen.
                # Within this interval, find sub-intervals where q is also frozen
                # and b moves exactly twice.

                # Collect all q-positions in (prev_p, u)
                interval_len = (u - prev_p - 1) % L
                if interval_len == 0:
                    continue

                # Build list of movers in this interval
                interval_movers = []
                for step in range(1, interval_len + 1):
                    pos = (prev_p + step) % L
                    interval_movers.append(word[pos])

                # Split by q-positions
                q_indices = [i for i, m in enumerate(interval_movers) if m == q]

                # Check segments between q-positions (and before first / after last)
                boundaries = [-1] + q_indices + [len(interval_movers)]
                for seg_idx in range(len(boundaries) - 1):
                    seg_start = boundaries[seg_idx] + 1
                    seg_end = boundaries[seg_idx + 1]
                    segment = interval_movers[seg_start:seg_end]

                    b_count = segment.count(b)

                    # For Tool 3: need b_count == 2, and this segment must end
                    # at the point where p fires (i.e., seg_end == len(interval_movers))
                    # because p fires at time u which is right after the interval.
                    if b_count == 2 and seg_end == len(interval_movers):
                        return True

    return False


def is_pure_sweep(word, n):
    """Check if word is a pure sweep (all steps same direction)."""
    for i in range(len(word)):
        diff = (word[(i+1) % len(word)] - word[i]) % n
        if diff != 1 and diff != n-1:
            return False
    return True


def verify_case3c(n, gap_sizes, max_L):
    """
    Verify that all fair adjacent cyclic mover words for Case 3c
    are killed by Tool 2, Tool 3, or are pure sweeps (killed by Shadow).
    """
    k = len(gap_sizes)
    binary_positions = []
    pos = 0
    for i in range(k):
        binary_positions.append(pos)
        pos += 1 + gap_sizes[i]
    assert pos == n, f"pos={pos} != n={n}"

    binary_set = set(binary_positions)

    print(f"\n{'='*70}")
    print(f"n={n}, k={k}, gaps={gap_sizes}, binary={binary_positions}")
    print(f"Ring: {''.join('B' if i in binary_set else 'T' for i in range(n))}")
    print(f"Max L: {max_L}")
    print(f"{'='*70}")

    total_words = 0
    killed_tool2 = 0
    killed_tool3 = 0
    killed_sweep = 0
    survivors = []

    def count_singletons(word):
        edge_counts = Counter()
        for i in range(len(word)):
            a, b_val = word[i], word[(i+1) % len(word)]
            if abs(a - b_val) == 1:
                e = (min(a, b_val), max(a, b_val))
            else:
                e = (0, n-1)
            edge_counts[e] += 1
        return sum(1 for c in edge_counts.values() if c == 1)

    def dfs(word, move_counts):
        nonlocal total_words, killed_tool2, killed_tool3, killed_sweep

        L = len(word)
        if L > max_L:
            return

        current = word[-1]

        # Try to close cycle
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                # Check fairness: all procs move >= 2
                if all(c >= 2 for c in move_counts):
                    # Check binary parity
                    if all(move_counts[b] % 2 == 0 for b in binary_positions):
                        total_words += 1

                        # Check Tool 2
                        if count_singletons(word) >= 2:
                            killed_tool2 += 1
                            return

                        # Check pure sweep (killed by Shadow)
                        if is_pure_sweep(word, n):
                            killed_sweep += 1
                            return

                        # Check Tool 3
                        if check_binary_bounce(word, n, binary_set):
                            killed_tool3 += 1
                            return

                        # Check return cone (as backup)
                        if check_return_cone(word, n):
                            killed_tool2 += 1  # cones kill like tool 2
                            return

                        survivors.append(list(word))
                        if len(survivors) <= 3:
                            mc = Counter(word)
                            print(f"  SURVIVOR: {word}")
                            print(f"    moves={dict(sorted(mc.items()))}")
                            print(f"    singletons={count_singletons(word)}")

        # Extend
        for next_p in [(current - 1) % n, (current + 1) % n]:
            move_counts[next_p] += 1
            word.append(next_p)
            dfs(word, move_counts)
            word.pop()
            move_counts[next_p] -= 1

    move_counts = [0] * n
    move_counts[0] = 1
    dfs([0], move_counts)

    print(f"\nResults:")
    print(f"  Total fair words: {total_words}")
    print(f"  Killed by Tool 2 (>= 2 singletons or return cone): {killed_tool2}")
    print(f"  Killed by Tool 3 (binary-bounce): {killed_tool3}")
    print(f"  Killed by Shadow (pure sweep): {killed_sweep}")
    print(f"  Survivors: {len(survivors)}")

    if survivors:
        print(f"\n  *** {len(survivors)} SURVIVORS ***")
        for w in survivors[:10]:
            mc = Counter(w)
            winding = sum(1 if (w[(i+1)%len(w)]-w[i])%n == 1 else -1 for i in range(len(w)))
            print(f"    {w} W={winding} moves={dict(sorted(mc.items()))}")
    else:
        print(f"\n  ALL KILLED! ✓")

    return len(survivors)


def main():
    print("CIC Exploration 11c: Clean Tool 2 + Tool 3 verification")
    print("=" * 70)

    total_survivors = 0

    # n=6, k=3
    total_survivors += verify_case3c(6, [1, 1, 1], max_L=24)

    # n=7, k=3
    total_survivors += verify_case3c(7, [1, 1, 2], max_L=24)
    total_survivors += verify_case3c(7, [1, 2, 1], max_L=24)

    # n=8, k=3 (smaller max_L for speed)
    total_survivors += verify_case3c(8, [1, 1, 3], max_L=22)
    total_survivors += verify_case3c(8, [1, 2, 2], max_L=22)
    total_survivors += verify_case3c(8, [2, 1, 2], max_L=22)

    print(f"\n{'='*70}")
    print(f"GRAND TOTAL SURVIVORS: {total_survivors}")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
