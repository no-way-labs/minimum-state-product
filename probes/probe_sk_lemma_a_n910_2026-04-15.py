#!/usr/bin/env python3
"""Lemma A generalized at n=9, 10 — verify  |SK|(n, L=2n) = 2^n - 2n - 2*[n odd]
and  |SK|(n, L=2n+1) = 2^n - 2n - 2*[n odd] + 2^(n-3) - 1 hold beyond M_n classical range.

Targeted: only test a few multisets per n (mostly binary + lightly mixed)
to keep runtime low. Cap cycles per multiset at 200, time budget 8s.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys

sys.setrecursionlimit(20000)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def sk_size(ms, n, cycle, det):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    remaining = set(non_good)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    return len(remaining)


def lemma_a(n):
    return 2**n - 2*n - (2 if n % 2 == 1 else 0)


def lemma_b(n):
    return lemma_a(n) + 2**(n - 3) - 1


def main():
    print("=" * 80, flush=True)
    print("Lemma A generalized at n=9, 10", flush=True)
    print("=" * 80, flush=True)

    plan = [
        # (n, multisets to test)
        (9, [
            (2,)*9,
            (2,)*8 + (3,),
            (2,)*7 + (3, 3),
            (2,)*8 + (4,),
        ]),
        (10, [
            (2,)*10,
            (2,)*9 + (3,),
            (2,)*8 + (3, 3),
        ]),
    ]

    for n, multisets in plan:
        print(f"\n=== n={n}  expected_lemma_a={lemma_a(n)}  expected_lemma_b={lemma_b(n)} ===", flush=True)
        for ms in multisets:
            M = 1
            for m in ms: M *= m
            print(f"  ms={ms}  M={M}", flush=True)
            t0 = time.time()
            cycles = enumerate_all_cycles(ms, n, L_max=2*n+2, time_budget=10.0, max_cycles=300)
            elapsed = time.time() - t0
            if not cycles:
                print(f"    ({elapsed:.0f}s)  no cycles found", flush=True)
                continue
            by_L = defaultdict(list)
            for cycle, movers, det in cycles:
                L = len(movers)
                sk = sk_size(ms, n, cycle, det)
                by_L[L].append(sk)
            for L in sorted(by_L.keys()):
                vs = by_L[L]
                mn, mx = min(vs), max(vs)
                lemA_str = ""
                if L == 2 * n:
                    expected = lemma_a(n)
                    status = "MATCH" if mn == expected == mx else "MISMATCH"
                    lemA_str = f"  (expected {expected}: {status})"
                elif L == 2 * n + 1:
                    expected = lemma_b(n)
                    status = "MATCH" if mn == expected == mx else "MISMATCH"
                    lemA_str = f"  (Lemma B {expected}: {status})"
                print(f"    L={L:2d}  count={len(vs):4d}  |SK|=[{mn},{mx}]{lemA_str}", flush=True)


if __name__ == "__main__":
    main()
