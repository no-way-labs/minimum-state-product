#!/usr/bin/env python3
"""
RA12: Quick word-level provider check.

For ZW words with fc>=3, does EVERY word have a proc with binary-neighbor
one-sided >=2 phase?

This is word-level only (no state sequences needed), so fast.
We check ALL rotations of the multiset too.
"""

from collections import Counter
from itertools import permutations
import time


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


def analyze_phases(word, n, q):
    L = len(word)
    left_q = (q - 1) % n
    right_q = (q + 1) % n
    fire_steps = [t for t in range(L) if word[t] == q]
    fc_q = len(fire_steps)
    if fc_q == 0:
        return []
    phases = []
    for idx in range(fc_q):
        s = fire_steps[idx]
        a = fire_steps[(idx - 1) % fc_q]
        J = K = 0
        t = (a + 1) % L
        while t != s:
            if word[t] == left_q:
                J += 1
            if word[t] == right_q:
                K += 1
            t = (t + 1) % L
        phases.append((J, K))
    return phases


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


def find_provider(word, n, ms, fc):
    """Find proc with binary-neighbor one-sided >=2 phase."""
    for p in range(n):
        if fc[p] < 2:
            continue
        left_p = (p - 1) % n
        right_p = (p + 1) % n
        phases = analyze_phases(word, n, p)
        for J, K in phases:
            if J == 0 and K >= 2 and ms[right_p] == 2:
                return p
            if K == 0 and J >= 2 and ms[left_p] == 2:
                return p
    return None


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
    """Get all distinct ring placements of a sorted multiset."""
    # Generate all distinct permutations, then take canonical rotation
    seen = set()
    results = []
    for perm in set(permutations(sorted_ms)):
        # Canonical: smallest rotation
        best = perm
        for i in range(n):
            rot = perm[i:] + perm[:i]
            if rot < best:
                best = rot
        # Also check reverse
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best:
                best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def main():
    print("RA12: Word-Level Provider Check (All Ring Placements)")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)
        print(f"  Threshold: {threshold}")
        print(f"  Sorted multisets: {len(sorted_multisets)}")

        total_words = 0
        has_provider = 0
        no_provider = 0
        no_provider_examples = []

        for sorted_ms in sorted_multisets:
            if time.time() - t0 > 120:
                print("  TIME LIMIT")
                break

            # Get all distinct ring placements
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

                        total_words += 1
                        prov = find_provider(w, n, ms, fc)
                        if prov is not None:
                            has_provider += 1
                        else:
                            no_provider += 1
                            if len(no_provider_examples) < 10:
                                no_provider_examples.append({
                                    'ms': list(ms), 'word': list(w), 'fc': list(fc)
                                })

        elapsed = time.time() - t0
        print(f"  Elapsed: {elapsed:.1f}s")
        print(f"  Total ZW words: {total_words}")
        print(f"  Has provider: {has_provider}")
        print(f"  No provider:  {no_provider}")

        if no_provider > 0:
            print(f"\n  *** PROVIDER NOT UNIVERSAL ***")
            for ex in no_provider_examples[:5]:
                print(f"    ms={ex['ms']}, word={ex['word']}")
                print(f"    fc={ex['fc']}")
                # Show all phases for all procs
                n_ex = len(ex['ms'])
                for p in range(n_ex):
                    if ex['fc'][p] >= 2:
                        phases = analyze_phases(ex['word'], n_ex, p)
                        lp = (p - 1) % n_ex
                        rp = (p + 1) % n_ex
                        print(f"      p={p}(m={ex['ms'][p]},fc={ex['fc'][p]}) "
                              f"L={lp}(m={ex['ms'][lp]}) R={rp}(m={ex['ms'][rp]}): "
                              f"phases={phases}")
        else:
            print(f"  PROVIDER IS UNIVERSAL at word level!")


if __name__ == "__main__":
    main()
