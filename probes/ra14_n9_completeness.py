#!/usr/bin/env python3
"""
RA14 v6: Completeness check.

For 3-binary at n=9, the word-based enumeration only found sweep cycles.
Question: are there non-sweep good cycles that we're missing?

Approach: for small n (n=5), compare DFS-exhaustive vs word-constructed
to check if word construction misses important cycle families.
Then extrapolate to n=9.
"""

import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, permutations
from math import prod

def check_ec(good, word, n):
    L = len(word)
    mt = defaultdict(set)
    nt = defaultdict(set)
    for t in range(L):
        c = good[t]
        m = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == m:
                mt[j].add(triple)
            else:
                nt[j].add(triple)
    for j in range(n):
        if mt[j] & nt[j]:
            return True
    return False

def is_uniform_sweep(word, n):
    L = len(word)
    if L % n != 0:
        return False
    reps = L // n
    doubled = word + word
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            full = sweep * reps
            for off in range(L):
                if doubled[off:off+L] == full:
                    return True
    return False

def build_cycle_trans(word, ms, n, tm):
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + tm[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    cs = set(tuple(c) for c in configs[:L])
    if len(cs) != L:
        return None
    return [tuple(c) for c in configs[:L]]

def enumerate_dfs(ms, n, max_cycles=10000, max_time=60.0):
    t0 = time.time()
    if prod(ms) > 5000:
        return []
    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4*n, prod(ms))

    def dfs(config, path, word, det):
        if time.time() - t0 > max_time or len(results) >= max_cycles:
            return
        for p in range(n):
            for nv in range(ms[p]):
                if nv == config[p]:
                    continue
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue
                Lv = config[(p-1)%n]
                Sv = config[p]
                Rv = config[(p+1)%n]
                km = (p, Lv, Sv, Rv)
                nd = dict(det)
                if km in nd:
                    if nd[km] != nv:
                        continue
                else:
                    nd[km] = nv
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    ki = (i, config[(i-1)%n], config[i], config[(i+1)%n])
                    if ki in nd:
                        if nd[ki] != config[i]:
                            ok = False
                            break
                    else:
                        nd[ki] = config[i]
                if not ok:
                    continue
                nc = list(config)
                nc[p] = nv
                nc = tuple(nc)
                nw = word + [p]
                if nc == start and len(path) >= 2*n:
                    fc = Counter(nw)
                    if len(fc) == n:
                        ck = frozenset(path)
                        if ck not in seen:
                            seen.add(ck)
                            results.append((list(path), nw))
                    continue
                if nc not in set(path) and len(path) < max_len:
                    path.append(nc)
                    dfs(nc, path, nw, nd)
                    path.pop()
    dfs(start, [start], [], {})
    return results


# =============================================================================
# Test 1: n=5, 3-binary exhaustive
# =============================================================================

print("=" * 70)
print("TEST 1: n=5, 3-binary, DFS-exhaustive vs word-constructed")
print("=" * 70)

n = 5
threshold = 4 * 3**(n-2)
print(f"n={n}, threshold={threshold}")

# 3-binary at n=5: ms=(2,2,2,3,3)=72 or (2,2,2,3,4)=96
test_systems = [
    [2, 2, 2, 3, 3],   # product 72
]

for ms_base in test_systems:
    # All placements
    seen = set()
    placements = []
    for perm in set(permutations(ms_base)):
        canonical = min(
            min(tuple(perm[i:] + perm[:i]) for i in range(n)),
            min(tuple(perm[::-1][i:] + perm[::-1][:i]) for i in range(n))
        )
        if canonical not in seen:
            seen.add(canonical)
            placements.append(list(perm))

    for ms in placements:
        bp = [i for i in range(n) if ms[i] == 2]
        if len(bp) != 3:
            continue
        bp_s = sorted(bp)
        gaps = [(bp_s[(i+1)%3] - bp_s[i]) % n for i in range(3)]

        p_val = prod(ms)
        print(f"\nms={ms}, product={p_val}, gaps={gaps}")

        # DFS exhaustive
        t0 = time.time()
        dfs_cycles = enumerate_dfs(ms, n, max_cycles=10000, max_time=60.0)
        t1 = time.time()
        print(f"  DFS: {len(dfs_cycles)} cycles ({t1-t0:.1f}s)")

        sweep_count = 0
        nonsweep_ec = 0
        nonsweep_noec = 0

        for cyc, w in dfs_cycles:
            if is_uniform_sweep(w, n):
                sweep_count += 1
            elif check_ec(cyc, w, n):
                nonsweep_ec += 1
            else:
                nonsweep_noec += 1
                fc = Counter(w)
                print(f"    NO-EC non-sweep: CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}")

        print(f"  sweep={sweep_count}, nswp_EC={nonsweep_ec}, nswp_noEC={nonsweep_noec}")


# =============================================================================
# Test 2: n=7, 3-binary exhaustive (product may be too large for some)
# =============================================================================

print()
print("=" * 70)
print("TEST 2: n=7, 3-binary")
print("=" * 70)

n = 7
threshold = 4 * 3**(n-2)
print(f"n={n}, threshold={threshold}")

test_systems_n7 = [
    [2, 2, 2, 3, 3, 3, 3],   # product 648
]

for ms_base in test_systems_n7:
    seen = set()
    placements = []
    for perm in set(permutations(ms_base)):
        canonical = min(
            min(tuple(perm[i:] + perm[:i]) for i in range(n)),
            min(tuple(perm[::-1][i:] + perm[::-1][:i]) for i in range(n))
        )
        if canonical not in seen:
            seen.add(canonical)
            placements.append(list(perm))

    total_sw = 0
    total_nec = 0
    total_nnoec = 0

    for ms in placements:
        bp = [i for i in range(n) if ms[i] == 2]
        if len(bp) != 3:
            continue
        bp_s = sorted(bp)
        gaps = [(bp_s[(i+1)%3] - bp_s[i]) % n for i in range(3)]
        p_val = prod(ms)

        dfs_cycles = enumerate_dfs(ms, n, max_cycles=5000, max_time=30.0)

        sw = nec = nnoec = 0
        for cyc, w in dfs_cycles:
            if is_uniform_sweep(w, n):
                sw += 1
            elif check_ec(cyc, w, n):
                nec += 1
            else:
                nnoec += 1
                fc = Counter(w)
                if nnoec <= 3:
                    print(f"    NO-EC non-sweep: ms={ms}, CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}")

        if dfs_cycles:
            print(f"  ms={ms}, gaps={gaps}: {len(dfs_cycles)} cycles, sweep={sw}, nswp_EC={nec}, nswp_noEC={nnoec}")
        total_sw += sw
        total_nec += nec
        total_nnoec += nnoec

    print(f"\nn=7, 3-binary totals: sweep={total_sw}, nswp_EC={total_nec}, nswp_noEC={total_nnoec}")


# =============================================================================
# Test 3: n=5, 5-binary (all binary) — this is where non-EC appeared
# =============================================================================

print()
print("=" * 70)
print("TEST 3: n=5, all-binary ms=(2,2,2,2,2), product=32")
print("=" * 70)

n = 5
ms = [2, 2, 2, 2, 2]
dfs_cycles = enumerate_dfs(ms, n, max_cycles=10000, max_time=60.0)
print(f"DFS: {len(dfs_cycles)} cycles")

sw = nec = nnoec = 0
for cyc, w in dfs_cycles:
    if is_uniform_sweep(w, n):
        sw += 1
    elif check_ec(cyc, w, n):
        nec += 1
    else:
        nnoec += 1
        fc = Counter(w)
        print(f"  NO-EC non-sweep: CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}")

print(f"sweep={sw}, nswp_EC={nec}, nswp_noEC={nnoec}")


# =============================================================================
# Test 4: Check the KEY QUESTION more carefully
# =============================================================================

print()
print("=" * 70)
print("TEST 4: The boundary — at what binary count does non-EC non-sweep appear?")
print("=" * 70)

for n in [5, 7, 9]:
    print(f"\n--- n={n} ---")
    threshold = 4 * 3**(n-2)

    for nb in range(3, n+1):
        nn = n - nb
        if nn == 0:
            ms_base = [2]*n
            p_val = prod(ms_base)
            if p_val >= threshold:
                continue
        else:
            ms_base = [2]*nb + [3]*nn
            p_val = prod(ms_base)
            if p_val >= threshold:
                continue

        # Just test one canonical placement (the sorted one)
        ms = ms_base
        bp = [i for i in range(n) if ms[i] == 2]

        if p_val <= 3000:
            dfs_cycles = enumerate_dfs(ms, n, max_cycles=3000, max_time=15.0)
            sw = nec = nnoec = 0
            for cyc, w in dfs_cycles:
                if is_uniform_sweep(w, n):
                    sw += 1
                elif check_ec(cyc, w, n):
                    nec += 1
                else:
                    nnoec += 1
            print(f"  {nb} binary, ms={ms}, p={p_val}: {len(dfs_cycles)} cycles, sweep={sw}, nswp_EC={nec}, nswp_noEC={nnoec}")
        else:
            print(f"  {nb} binary, ms={ms}, p={p_val}: (product too large for DFS)")
