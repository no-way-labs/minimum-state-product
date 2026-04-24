#!/usr/bin/env python3
"""
RA13 Part 4: Which binary pair is the provider? Structural characterization.

Key question: (1,1) splits exist at some binary pairs, but not ALL.
For the theorem: we need to show there EXISTS a pair with (0,2) pattern.

Strategy: For each word, look at ALL pairs of adjacent binary procs.
Classify each pair as (0,2)/(2,0) or (1,1). What determines which?

HYPOTHESIS: The pair where (0,2) holds is determined by the walk's
"turnaround" structure — where the walk reverses direction on the ring.
"""

import time
from itertools import permutations
from collections import Counter


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1:
            cw += 1
        elif diff == n - 1:
            ccw += 1
    return cw, ccw


def _enumerate_walks_dfs(n, length, ms):
    results = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == length:
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1:
                return
            if any(f < 2 for f in fc):
                return
            if all(f <= 2 for f in fc):
                return
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw:
                return
            results.append(tuple(path))
            return
        remaining = length - step
        unfired = sum(1 for f in fc if f < 2)
        if unfired > remaining:
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2:
                continue
            if fc[nxt] >= 2 * ms[nxt]:
                continue
            fc[nxt] += 1
            path.append(nxt)
            dfs(path, fc)
            path.pop()
            fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    unique = set()
    result = []
    for w in results:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def generate_subthreshold_multisets(n, threshold):
    results = []
    max_state = min(threshold // (2 ** (n - 1)) + 1, 10)
    def gen(pos, min_val, current, prod):
        if pos == n:
            if prod < threshold:
                num_bin = sum(1 for m in current if m == 2)
                if num_bin >= 3:
                    results.append(tuple(current))
            return
        remaining = n - pos
        for m in range(max(2, min_val), max_state + 1):
            new_prod = prod * m
            if new_prod >= threshold:
                break
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2:
                    break
            gen(pos + 1, m, current + [m], new_prod)
    gen(0, 2, [], 1)
    return results


def get_all_ring_placements(sorted_ms, n):
    seen = set()
    results = []
    for perm in set(permutations(sorted_ms)):
        best = perm
        for i in range(n):
            rot = perm[i:] + perm[:i]
            if rot < best:
                best = rot
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best:
                best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def classify_binary_pairs(word, n, ms):
    """For each pair of adjacent binary procs (t, b=t+1), classify interleaving."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    pairs = []
    for t in range(n):
        b = (t + 1) % n
        if ms[t] != 2 or ms[b] != 2 or fc[t] != 2 or fc[b] != 2:
            continue
        # Count b-fires in each of t's phases
        t_fires = [i for i, x in enumerate(word) if x == t]
        b_fires = [i for i, x in enumerate(word) if x == b]
        # Phase 0: between t_fires[0] and t_fires[1]
        gap = (t_fires[1] - t_fires[0]) % L
        b_in_phase0 = sum(1 for bf in b_fires if 0 < (bf - t_fires[0]) % L < gap)
        b_in_phase1 = len(b_fires) - b_in_phase0
        pairs.append((t, b, b_in_phase0, b_in_phase1))
    return pairs


def get_turnarounds(word, n):
    """Find turnaround points where the walk reverses direction."""
    L = len(word)
    turns = []
    for i in range(L):
        prev_dir = (word[i] - word[(i-1) % L]) % n
        next_dir = (word[(i+1) % L] - word[i]) % n
        if prev_dir == 1 and next_dir == n - 1:
            turns.append((i, word[i], 'CW_to_CCW'))
        elif prev_dir == n - 1 and next_dir == 1:
            turns.append((i, word[i], 'CCW_to_CW'))
    return turns


def main():
    print("RA13 Part 4: Pair Selection and Turnaround Analysis")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        # For words with both (0,2) and (1,1) pairs: what distinguishes them?
        mixed_words = 0
        all_02_words = 0
        all_11_words = 0  # should be 0 (provider always exists)

        # How many binary pairs per word?
        num_pairs_dist = Counter()
        num_02_pairs_dist = Counter()

        # Turnaround analysis
        turn_near_02 = 0
        turn_near_11 = 0

        # For mixed words: is the (0,2) pair at the END of a binary run?
        end_of_run = 0
        not_end_of_run = 0

        # Detailed examples
        examples = []

        for sorted_ms in sorted_multisets:
            placements = get_all_ring_placements(sorted_ms, n)
            for ms in placements:
                max_len = min(sum(ms), 4 * n)
                min_len = 2 * n + 1
                for cycle_len in range(min_len, max_len + 1):
                    walks = _enumerate_walks_dfs(n, cycle_len, ms)
                    for w in walks:
                        fc = [0] * n
                        for p in w:
                            fc[p] += 1

                        pairs = classify_binary_pairs(w, n, ms)
                        num_pairs_dist[len(pairs)] += 1
                        if not pairs:
                            continue

                        pairs_02 = [(t, b) for t, b, p0, p1 in pairs
                                    if p0 == 0 or p0 == 2]
                        pairs_11 = [(t, b) for t, b, p0, p1 in pairs
                                    if p0 == 1]
                        num_02_pairs_dist[len(pairs_02)] += 1

                        if pairs_02 and pairs_11:
                            mixed_words += 1
                        elif pairs_02 and not pairs_11:
                            all_02_words += 1
                        elif not pairs_02 and pairs_11:
                            all_11_words += 1

                        # Turnaround analysis
                        turns = get_turnarounds(w, n)
                        turn_procs = set(tp for _, tp, _ in turns)

                        for t, b, p0, p1 in pairs:
                            is_02 = (p0 == 0 or p0 == 2)
                            # Is t or b a turnaround point?
                            near_turn = (t in turn_procs or b in turn_procs)
                            # Or: is t or b ADJACENT to a turnaround?
                            adj_turn = any(abs((t - tp) % n) <= 1 or abs((tp - t) % n) <= 1
                                          for tp in turn_procs)
                            if is_02:
                                if near_turn:
                                    turn_near_02 += 1
                            else:
                                if near_turn:
                                    turn_near_11 += 1

                        # Binary run analysis
                        for t, b, p0, p1 in pairs:
                            if p0 == 0 or p0 == 2:
                                # Is (t, b) at the end of a binary run?
                                # i.e., is (b+1) % n non-binary?
                                beyond_b = (b + 1) % n
                                before_t = (t - 1) % n
                                at_end = (ms[beyond_b] != 2 or ms[before_t] != 2)
                                if at_end:
                                    end_of_run += 1
                                else:
                                    not_end_of_run += 1

                        if len(examples) < 8 and pairs_11:
                            examples.append({
                                'ms': list(ms), 'word': list(w), 'fc': list(fc),
                                'pairs': pairs,
                                'turns': [(tp, d) for _, tp, d in turns]
                            })

        elapsed = time.time() - t0
        print(f"  ({elapsed:.1f}s)")
        print(f"\n  Word categories:")
        print(f"    All (0,2) pairs: {all_02_words}")
        print(f"    Mixed (0,2)+(1,1): {mixed_words}")
        print(f"    All (1,1) pairs: {all_11_words}  [should be 0!]")

        print(f"\n  Number of adjacent binary pairs per word:")
        for np, cnt in sorted(num_pairs_dist.items()):
            print(f"    {np} pairs: {cnt}")

        print(f"\n  Number of (0,2) pairs per word:")
        for np, cnt in sorted(num_02_pairs_dist.items()):
            print(f"    {np} (0,2) pairs: {cnt}")

        print(f"\n  Turnaround near (0,2) pair: {turn_near_02}")
        print(f"  Turnaround near (1,1) pair: {turn_near_11}")

        print(f"\n  (0,2) pair at end of binary run: {end_of_run}")
        print(f"  (0,2) pair NOT at end: {not_end_of_run}")

        print(f"\n  Examples with (1,1) pairs:")
        for ex in examples[:4]:
            print(f"    ms={ex['ms']}, word={ex['word']}")
            print(f"    fc={ex['fc']}")
            for t, b, p0, p1 in ex['pairs']:
                tag = "(0,2)" if (p0 == 0 or p0 == 2) else "(1,1)"
                print(f"    pair ({t},{b}): b_in_phases=({p0},{p1}) {tag}")
            print(f"    turns: {ex['turns']}")


if __name__ == "__main__":
    main()
