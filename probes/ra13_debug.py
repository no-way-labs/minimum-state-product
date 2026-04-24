#!/usr/bin/env python3
"""RA13 Debug: Why does Strategy A fail but general search succeeds?"""
import time
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

def main():
    n = 5
    ms = [2, 2, 2, 3, 3]
    walks = _enumerate_walks_dfs(n, 12, ms)
    print(f"n={n}, ms={ms}, {len(walks)} walks")

    for w in walks[:3]:
        fc = [0] * n
        for p in w: fc[p] += 1
        L = len(w)
        print(f"\n  word={list(w)}, fc={fc}")

        # General search
        for p in range(n):
            if fc[p] < 2: continue
            left_p = (p - 1) % n
            right_p = (p + 1) % n
            fire_steps = [i for i, x in enumerate(w) if x == p]
            for idx in range(len(fire_steps)):
                s = fire_steps[idx]
                a = fire_steps[(idx - 1) % len(fire_steps)]
                J = K = 0
                t_step = (a + 1) % L
                while t_step != s:
                    if w[t_step] == left_p: J += 1
                    if w[t_step] == right_p: K += 1
                    t_step = (t_step + 1) % L
                if (J == 0 and K >= 2 and ms[right_p] == 2) or \
                   (K == 0 and J >= 2 and ms[left_p] == 2):
                    active = right_p if (J == 0 and K >= 2 and ms[right_p] == 2) else left_p
                    silent = left_p if active == right_p else right_p
                    af = K if active == right_p else J
                    print(f"  PROVIDER: t={p}(m={ms[p]},fc={fc[p]}), "
                          f"active={active}(m={ms[active]},fc={fc[active]}), "
                          f"silent={silent}(m={ms[silent]},fc={fc[silent]}), "
                          f"active_fires={af}, phase ({J},{K})")

        # Strategy A
        print(f"  Strategy A:")
        binary_procs = [p for p in range(n) if ms[p] == 2]
        for b in binary_procs:
            b_fires = [i for i, x in enumerate(w) if x == b]
            for t in [(b-1)%n, (b+1)%n]:
                if fc[t] < 2: continue
                t_fires = [i for i, x in enumerate(w) if x == t]
                for idx in range(len(t_fires)):
                    start = t_fires[(idx-1)%len(t_fires)]
                    end = t_fires[idx]
                    gap = (end - start) % L
                    b_in = sum(1 for bf in b_fires if 0 < (bf - start) % L < gap)
                    other = (t-1)%n if b == (t+1)%n else (t+1)%n
                    o_fires = [i for i, x in enumerate(w) if x == other]
                    o_in = sum(1 for of_ in o_fires if 0 < (of_ - start) % L < gap)
                    if b_in == fc[b] and o_in == 0:
                        print(f"    MATCH: b={b},t={t},phase={idx}, b_in={b_in}, o({other})_in={o_in}")
                    elif b_in == fc[b]:
                        print(f"    NEAR: b={b},t={t},phase={idx}, b_in={b_in}, o({other})_in={o_in}")

main()
