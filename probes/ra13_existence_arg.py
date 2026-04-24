#!/usr/bin/env python3
"""
RA13 Existence Argument: Why does at least one (b,t) pair always work?

Approach: Double counting / pigeonhole on the walk graph.

Consider the walk as a sequence of ring positions. Each binary proc b is visited
exactly twice (fc=2). The two visits divide the walk into two segments (arcs).

For adjacent procs b and t: both b-fires in one phase of t iff both b-visits
occur in the same arc of t.

Let's think about this as a COLORING problem:
- The walk visits n procs, each at least twice.
- For each binary b: its 2 visits split the walk into 2 arcs.
- For each neighbor t: t's visits are in one or both arcs of b.
  If t has fc=2: t's visits split into (0,2), (1,1), or (2,0) across b's arcs.
  If (0,2) or (2,0): b's fires cluster into one phase of t.

OBSERVATION: When both b and t are binary (fc=2), the interleaving on the walk
circle is either "nested" (one pair inside the other) or "crossing" (alternating).
- Nested: b1, b2, t1, t2 or b1, t1, t2, b2 => (0,2)/(2,0)
- Crossing: b1, t1, b2, t2 => (1,1)

So the question reduces to: do there exist non-crossing adjacent binary pairs?

For >=3 binary procs on a ring, each with fc=2, consider the 2-element sets of
visit times. If ALL adjacent pairs cross, what happens?

KEY: crossing means the visits alternate around the cycle.
If b1,b2 are the visits of b and t1,t2 of t, crossing means they alternate:
b1, t1, b2, t2 or b1, t2, b2, t1 (cyclically on the walk).

This is like a linking/nesting structure on intervals on a circle.

With 3 binary procs a, b, c (each with 2 visit-times on the walk-circle),
can all 3 pairs of adjacent ones be "crossing"?

For the ring 0-1-2-...: if 0,1,2 are binary and adjacent:
(0,1) crossing, (1,2) crossing. Is (0,2) also crossing?

Actually (0,2) might not be adjacent on the ring. Depends on arrangement.

Let me check: for the walk-circle, can we have 3 mutually crossing pairs of
2-element sets? Answer: yes, with 6 points on a circle, we can have 3 pairs
of "linked" intervals. E.g., a1,b1,c1,a2,b2,c2 cyclically: a crosses b,
b crosses c, a crosses c.

So crossing is NOT the obstruction. The theorem must use something else.

Let me check: for the PROVIDER, we need BOTH:
(a) b's fires cluster in one phase of t (non-crossing)
(b) other side of t fires 0 in that phase

Maybe (b) provides additional constraints that make the theorem work.

Let me count: for each word, how many (b,t) pairs satisfy (a) but not (b)?
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
    print("RA13 Existence: Clustering + Silent decomposition")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n  n = {n}")
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        total_words = 0
        # For each word, count:
        words_stats = []

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
                        total_words += 1

                        cluster_only = 0  # (a) but not (b)
                        cluster_and_silent = 0  # (a) and (b)
                        neither = 0

                        for b in range(n):
                            if ms[b] != 2 or fc[b] != 2: continue
                            b_fires = [i for i, x in enumerate(w) if x == b]
                            for t in [(b-1)%n, (b+1)%n]:
                                if fc[t] < 2: continue
                                t_fires = [i for i, x in enumerate(w) if x == t]
                                fc_t = len(t_fires)
                                other = (t-1)%n if b == (t+1)%n else (t+1)%n
                                o_fires = [i for i, x in enumerate(w) if x == other]
                                for idx in range(fc_t):
                                    start = t_fires[(idx-1)%fc_t]
                                    end = t_fires[idx]
                                    gap = (end - start) % L
                                    b_in = sum(1 for bf in b_fires if 0 < (bf - start) % L < gap)
                                    if b_in == 2:
                                        o_in = sum(1 for of_ in o_fires if 0 < (of_ - start) % L < gap)
                                        if o_in == 0:
                                            cluster_and_silent += 1
                                        else:
                                            cluster_only += 1

                        words_stats.append((cluster_and_silent, cluster_only))

        # Distribution
        cas_dist = Counter(s[0] for s in words_stats)
        co_dist = Counter(s[1] for s in words_stats)
        print(f"  Total words: {total_words}")
        print(f"\n  cluster_and_silent count per word:")
        for k in sorted(cas_dist.keys()):
            print(f"    {k}: {cas_dist[k]} words")
        print(f"\n  cluster_only count per word:")
        for k in sorted(co_dist.keys()):
            print(f"    {k}: {co_dist[k]} words")

        # Words with 0 cluster_and_silent should be 0
        zero_cas = sum(1 for s in words_stats if s[0] == 0)
        print(f"\n  Words with 0 cluster_and_silent: {zero_cas} (should be 0)")

main()
