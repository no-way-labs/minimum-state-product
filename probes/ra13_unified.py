#!/usr/bin/env python3
"""
RA13 Unified: Test the simplest possible selection rule.

CONJECTURE: For >=3 binary, sub-threshold, ZW, all fc>=2, some fc>=3:
  There exists binary b (fc=2) and neighbor t such that:
  (a) Both b-fires are in one phase of t
  (b) The other neighbor of t fires 0 in that phase

We know (a)+(b) holds 100%. The question for the proof is WHY.

Alternative approach: Don't prove (a)+(b) directly. Instead:

LEMMA: For any binary b (fc=2), ANY neighbor t (fc>=2):
  b's fires distribute across t's phases as either [2,0,...,0] or [0,...,0,2,0,...].
  I.e., BOTH b-fires always land in the SAME phase of t.

If this lemma holds, then we just need to find a (t,b) pair where the other
side fires 0.

Let me test this lemma: for every binary b, every neighbor t with fc>=2,
are b's fires always in one phase of t?
"""

from itertools import permutations
from collections import Counter


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1: cw += 1
        elif diff == n - 1: ccw += 1
    return cw, ccw


def _enumerate_walks_dfs(n, length, ms):
    results = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == length:
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1: return
            if any(f < 2 for f in fc): return
            if all(f <= 2 for f in fc): return
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw: return
            results.append(tuple(path))
            return
        remaining = length - step
        unfired = sum(1 for f in fc if f < 2)
        if unfired > remaining: return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2: continue
            if fc[nxt] >= 2 * ms[nxt]: continue
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
            if rot < best: best = rot
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
            if new_prod >= threshold: break
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2: break
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
            if rot < best: best = rot
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best: best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def main():
    print("RA13 Unified: Binary fire clustering lemma test")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n  n = {n}")
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        total_pairs = 0  # (b, t) pairs
        all_in_one = 0   # both b-fires in one phase of t
        split = 0         # b-fires split across phases

        split_examples = []

        for sorted_ms in sorted_multisets:
            placements = get_all_ring_placements(sorted_ms, n)
            for ms in placements:
                max_len = min(sum(ms), 4 * n)
                min_len = 2 * n + 1
                for cycle_len in range(min_len, max_len + 1):
                    walks = _enumerate_walks_dfs(n, cycle_len, ms)
                    for w in walks:
                        fc = [0] * n
                        for p in w: fc[p] += 1
                        L = len(w)

                        for b in range(n):
                            if ms[b] != 2 or fc[b] != 2: continue
                            b_fires = [i for i, x in enumerate(w) if x == b]
                            for t in [(b-1)%n, (b+1)%n]:
                                if fc[t] < 2: continue
                                t_fires = [i for i, x in enumerate(w) if x == t]
                                fc_t = len(t_fires)
                                # Check distribution
                                dist = []
                                for idx in range(fc_t):
                                    start = t_fires[(idx-1)%fc_t]
                                    end = t_fires[idx]
                                    gap = (end - start) % L
                                    cnt = sum(1 for bf in b_fires if 0 < (bf - start) % L < gap)
                                    dist.append(cnt)
                                total_pairs += 1
                                if max(dist) == 2:
                                    all_in_one += 1
                                else:
                                    split += 1
                                    if len(split_examples) < 5:
                                        split_examples.append({
                                            'ms': list(ms), 'word': list(w),
                                            'b': b, 't': t, 'dist': dist,
                                            'm_t': ms[t], 'fc_t': fc[t]
                                        })

        print(f"  Total (b,t) pairs: {total_pairs}")
        print(f"  Both b-fires in one phase: {all_in_one} ({100*all_in_one/max(1,total_pairs):.1f}%)")
        print(f"  Split: {split} ({100*split/max(1,total_pairs):.1f}%)")

        if split_examples:
            print(f"\n  SPLIT examples:")
            for ex in split_examples:
                print(f"    ms={ex['ms']}, word={ex['word']}")
                print(f"    b={ex['b']}, t={ex['t']}(m={ex['m_t']},fc={ex['fc_t']}), dist={ex['dist']}")


if __name__ == "__main__":
    main()
