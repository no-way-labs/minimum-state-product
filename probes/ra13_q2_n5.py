#!/usr/bin/env python3
"""
RA13 Q2 at n=5: For ALL no-EC cycles, does shadow exist?

At n=5, the DFS finds thousands of no-EC cycles with arbitrary transitions.
Check: does every one have a shadow cycle?

Shadow check: under INCREMENTING, does there exist a disjoint companion
cycle with the same mover word?

Also check: under the cycle's OWN transition function, does a shadow exist?
"""

import time
from collections import defaultdict, Counter
from itertools import product as iproduct, combinations
from math import prod

def check_ec(good, word, n):
    L = len(word)
    mt = defaultdict(set)
    nmt = defaultdict(set)
    for t in range(L):
        c = good[t]
        m = word[t]
        for j in range(n):
            tr = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == m: mt[j].add(tr)
            else: nmt[j].add(tr)
    conflicts = {}
    for j in range(n):
        ov = mt[j] & nmt[j]
        if ov: conflicts[j] = ov
    return conflicts


def check_shadow_inc(good, word, n, ms):
    """Check shadow under incrementing."""
    L = len(word)
    orig_set = set(good)
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if tuple(configs[-1]) != tuple(configs[0]):
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) == L and not (cycle_set & orig_set):
            return True
    return False


def check_shadow_det(good, word, n, ms, det):
    """Check shadow under the cycle's own transition function."""
    L = len(word)
    orig_set = set(good)
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in det:
                c[p] = det[key]
            else:
                c[p] = (c[p] + 1) % ms[p]  # default
            configs.append(c)
        if tuple(configs[-1]) != tuple(configs[0]):
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) == L and not (cycle_set & orig_set):
            return True
    return False


def enumerate_good_cycles_dfs(ms, n, max_cycles=5000, max_time=60.0):
    t0 = time.time()
    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4*n, prod(ms))

    def dfs(config, path, word, det):
        if time.time() - t0 > max_time or len(results) >= max_cycles:
            return
        for p in range(n):
            for nv in range(ms[p]):
                if nv == config[p]: continue
                if word:
                    d = min(abs(p - word[-1]), n - abs(p - word[-1]))
                    if d > 1: continue
                L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
                km = (p, L, S, R)
                nd = dict(det); ok = True
                if km in nd:
                    if nd[km] != nv: ok = False
                else: nd[km] = nv
                if not ok: continue
                for i in range(n):
                    if i == p: continue
                    ki = (i, config[(i-1)%n], config[i], config[(i+1)%n])
                    if ki in nd:
                        if nd[ki] != config[i]: ok = False; break
                    else: nd[ki] = config[i]
                if not ok: continue
                nc = list(config); nc[p] = nv; nc = tuple(nc)
                nw = word + [p]
                if nc == start and len(path) >= 2*n:
                    c = list(path); me = True
                    for idx in range(len(c)):
                        priv = [i for i in range(n) if (i, c[idx][(i-1)%n], c[idx][i], c[idx][(i+1)%n]) in nd and nd[(i, c[idx][(i-1)%n], c[idx][i], c[idx][(i+1)%n])] != c[idx][i]]
                        if len(priv) != 1: me = False; break
                    if me:
                        ck = frozenset(c)
                        if ck not in seen:
                            seen.add(ck); results.append((c, nw, dict(nd)))
                    continue
                if nc not in set(path) and len(path) < max_len:
                    path.append(nc)
                    dfs(nc, path, nw, nd)
                    path.pop()
    dfs(start, [start], [], {})
    return results


if __name__ == "__main__":
    n = 5
    threshold = 4 * 3**(n-2)

    print(f"n={n}, threshold={threshold}")
    print(f"Testing EC ∨ Shadow for ALL no-EC cycles\n")

    grand_total = 0
    grand_ec = 0
    grand_noec = 0
    grand_noec_shadow_inc = 0
    grand_noec_shadow_det = 0
    grand_noec_noshadow = 0
    noshadow_examples = []

    for bp in combinations(range(n), 3):
        ms = [3]*n
        for p in bp: ms[p] = 2
        if prod(ms) >= threshold:
            continue

        print(f"bp={bp}, ms={ms}, product={prod(ms)}", end="")
        t0 = time.time()
        cycles = enumerate_good_cycles_dfs(ms, n, max_cycles=1000, max_time=15.0)
        print(f"  -> {len(cycles)} cycles ({time.time()-t0:.1f}s)")

        for cyc, w, det in cycles:
            grand_total += 1
            ec = check_ec(cyc, w, n)
            if ec:
                grand_ec += 1
                continue

            grand_noec += 1

            # Check shadow under incrementing
            sh_inc = check_shadow_inc(cyc, w, n, ms)
            if sh_inc:
                grand_noec_shadow_inc += 1
                continue

            # Check shadow under cycle's own det
            sh_det = check_shadow_det(cyc, w, n, ms, det)
            if sh_det:
                grand_noec_shadow_det += 1
                continue

            grand_noec_noshadow += 1
            if len(noshadow_examples) < 5:
                fc = Counter(w)
                noshadow_examples.append({
                    'bp': bp, 'ms': ms, 'CL': len(w), 'word': w,
                    'fc': dict(sorted(fc.items()))
                })

    print(f"\n{'='*60}")
    print(f"RESULTS at n={n}")
    print(f"{'='*60}")
    print(f"Total cycles: {grand_total}")
    print(f"With EC (Mode A): {grand_ec}")
    print(f"Without EC: {grand_noec}")
    print(f"  Shadow (inc): {grand_noec_shadow_inc}")
    print(f"  Shadow (det): {grand_noec_shadow_det}")
    print(f"  No shadow:    {grand_noec_noshadow}")

    if grand_noec_noshadow == 0:
        print(f"\n*** EC ∨ SHADOW HOLDS at n={n} ***")
        print("Every cycle has either entry conflict or a shadow companion!")
    else:
        print(f"\n*** EC ∨ SHADOW STATUS at n={n} ***")
        print(f"{grand_noec_noshadow} cycles have neither EC nor shadow")
        for ex in noshadow_examples:
            print(f"  bp={ex['bp']}, CL={ex['CL']}, fc={ex['fc']}")
            print(f"    word={ex['word']}")

    # =========================================================
    # Also test n=7
    # =========================================================
    n = 7
    threshold = 4 * 3**(n-2)
    print(f"\n\nn={n}, threshold={threshold}")

    grand_total = 0
    grand_ec = 0
    grand_noec_shadow = 0
    grand_noec_noshadow = 0

    for bp in combinations(range(n), 3):
        ms = [3]*n
        for p in bp: ms[p] = 2
        if prod(ms) >= threshold:
            continue

        t0 = time.time()
        cycles = enumerate_good_cycles_dfs(ms, n, max_cycles=200, max_time=10.0)
        print(f"bp={bp}, ms={ms} -> {len(cycles)} cycles ({time.time()-t0:.1f}s)")

        for cyc, w, det in cycles:
            grand_total += 1
            ec = check_ec(cyc, w, n)
            if ec:
                grand_ec += 1
                continue

            sh = check_shadow_inc(cyc, w, n, ms)
            if sh:
                grand_noec_shadow += 1
            else:
                sh2 = check_shadow_det(cyc, w, n, ms, det)
                if sh2:
                    grand_noec_shadow += 1
                else:
                    grand_noec_noshadow += 1

    print(f"\nResults n={n}: total={grand_total}, EC={grand_ec}, "
          f"noEC+shadow={grand_noec_shadow}, noEC+noShadow={grand_noec_noshadow}")
    if grand_noec_noshadow == 0:
        print(f"*** EC ∨ SHADOW HOLDS at n={n} ***")
    else:
        print(f"*** {grand_noec_noshadow} cycles lack both EC and shadow ***")
