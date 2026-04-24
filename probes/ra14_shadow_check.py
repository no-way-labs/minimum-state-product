#!/usr/bin/env python3
"""
RA14 v7: Shadow check for non-sweep non-EC cycles at n=5 and n=7.

Key question: do the non-sweep non-EC cycles at 3-binary have shadows?
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

def enumerate_dfs(ms, n, max_cycles=5000, max_time=30.0):
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

def check_shadow_full(good, word, n, ms):
    """Full shadow check: try all possible transition functions for shadow cycle."""
    L = len(word)
    orig_set = set(good)
    p_val = prod(ms)
    if p_val > 5000:
        return None

    # Try all configs as shadow starts, with inc transition
    for s in iproduct(*(range(m) for m in ms)):
        s = tuple(s)
        if s in orig_set:
            continue
        configs = [list(s)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if configs[-1] != list(configs[0]):
            continue
        cs = set(tuple(c) for c in configs[:L])
        if len(cs) != L or cs & orig_set:
            continue
        return True

    # Try dec transition
    for s in iproduct(*(range(m) for m in ms)):
        s = tuple(s)
        if s in orig_set:
            continue
        configs = [list(s)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] - 1) % ms[p]
            configs.append(c)
        if configs[-1] != list(configs[0]):
            continue
        cs = set(tuple(c) for c in configs[:L])
        if len(cs) != L or cs & orig_set:
            continue
        return True

    return False

# =============================================================================
# n=5, 3-binary: ms=[2,2,2,3,3], consecutive binary at [0,1,2]
# =============================================================================

print("=" * 70)
print("SHADOW CHECK: n=5, 3-binary, ms=[3,3,2,2,2]")
print("=" * 70)

n = 5
ms = [3, 3, 2, 2, 2]

cycles = enumerate_dfs(ms, n, max_cycles=5000, max_time=60.0)
print(f"Found {len(cycles)} cycles")

noec_nonsweep = []
for cyc, w in cycles:
    if not is_uniform_sweep(w, n) and not check_ec(cyc, w, n):
        noec_nonsweep.append((cyc, w))

print(f"Non-sweep non-EC: {len(noec_nonsweep)}")

shadow_yes = 0
shadow_no = 0
for i, (cyc, w) in enumerate(noec_nonsweep[:200]):
    sh = check_shadow_full(cyc, w, n, ms)
    if sh:
        shadow_yes += 1
    else:
        shadow_no += 1
    if i < 5 or (not sh and shadow_no <= 5):
        fc = Counter(w)
        print(f"  [{i}] CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}, shadow={sh}")

print(f"\nShadow: YES={shadow_yes}, NO={shadow_no} (of {min(200, len(noec_nonsweep))} checked)")

# =============================================================================
# n=5, 3-binary: ms=[2,3,3,2,2], non-consecutive binary
# =============================================================================

print()
print("=" * 70)
print("SHADOW CHECK: n=5, 3-binary, ms=[2,3,3,2,2]")
print("=" * 70)

ms2 = [2, 3, 3, 2, 2]
cycles2 = enumerate_dfs(ms2, n, max_cycles=5000, max_time=60.0)
print(f"Found {len(cycles2)} cycles")

noec_nonsweep2 = []
for cyc, w in cycles2:
    if not is_uniform_sweep(w, n) and not check_ec(cyc, w, n):
        noec_nonsweep2.append((cyc, w))

print(f"Non-sweep non-EC: {len(noec_nonsweep2)}")

shadow_yes2 = 0
shadow_no2 = 0
for i, (cyc, w) in enumerate(noec_nonsweep2[:200]):
    sh = check_shadow_full(cyc, w, n, ms2)
    if sh:
        shadow_yes2 += 1
    else:
        shadow_no2 += 1
    if i < 5 or (not sh and shadow_no2 <= 5):
        fc = Counter(w)
        print(f"  [{i}] CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}, shadow={sh}")

print(f"\nShadow: YES={shadow_yes2}, NO={shadow_no2} (of {min(200, len(noec_nonsweep2))} checked)")

# =============================================================================
# n=7, 3-binary
# =============================================================================

print()
print("=" * 70)
print("SHADOW CHECK: n=7, 3-binary")
print("=" * 70)

n = 7
for ms in [[3, 3, 3, 2, 2, 2, 3], [2, 3, 3, 2, 3, 3, 2]]:
    bp = [i for i in range(n) if ms[i] == 2]
    bp_s = sorted(bp)
    gaps = [(bp_s[(i+1)%len(bp_s)] - bp_s[i]) % n for i in range(len(bp_s))]
    print(f"\nms={ms}, gaps={gaps}")

    cycles = enumerate_dfs(ms, n, max_cycles=2000, max_time=30.0)
    print(f"Found {len(cycles)} cycles")

    noec_ns = []
    for cyc, w in cycles:
        if not is_uniform_sweep(w, n) and not check_ec(cyc, w, n):
            noec_ns.append((cyc, w))

    print(f"Non-sweep non-EC: {len(noec_ns)}")

    if noec_ns:
        sy = sn = 0
        for i, (cyc, w) in enumerate(noec_ns[:50]):
            sh = check_shadow_full(cyc, w, n, ms)
            if sh:
                sy += 1
            else:
                sn += 1
            if i < 3 or (not sh and sn <= 3):
                fc = Counter(w)
                print(f"  [{i}] CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}, shadow={sh}")
        print(f"Shadow: YES={sy}, NO={sn} (of {min(50, len(noec_ns))} checked)")


# =============================================================================
# Critical: what DOES block these cycles?
# =============================================================================

print()
print("=" * 70)
print("WHAT BLOCKS NON-EC NON-SHADOW CYCLES?")
print("=" * 70)
print("If a cycle has no EC and no shadow, what prevents a valid system?")
print("Answer: the cycle's determinism constraints may conflict with OTHER")
print("cycles' constraints. A single good cycle without EC is necessary but")
print("not sufficient for a valid system — the TRANSITION FUNCTION must be")
print("globally consistent, and good-targeting completion may fail.")
print()
print("The existing proof handles this via:")
print("  1. WaterfallCycle (sweep) → shadow trap (proved)")
print("  2. Non-sweep → entry conflict (DISPROVED: fails at all n>=5)")
print()
print("The correct characterization must be different. Options:")
print("  A. Every good cycle has EC OR shadow (different from sweep-only)")
print("  B. The proof structure needs to handle non-EC non-shadow cycles")
print("     differently (e.g., completion failure, SCC obstruction)")
