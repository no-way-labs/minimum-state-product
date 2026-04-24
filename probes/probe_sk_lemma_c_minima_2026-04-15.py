#!/usr/bin/env python3
"""Lemma C investigation: find the minimum |SK| at each (n, L) for L >= 2n+2.

Strategy: enumerate cycles at sub-M_n multisets, group by (n, L), record only
the minimum |SK| (and the multiset/movers achieving it). Try several closed
forms against the minimum:

  - 2^n - L - c
  - 2^n - 2n - 2*[n odd] - 2*(L - 2n - 1)   (linear decay)
  - 2^(n-1) - n
  - max(1, 2^n - 2n - 4*(L - 2n))

Report the actual minimum-by-(n,L) table and which closed forms fit.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys

sys.setrecursionlimit(20000)


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


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


def main():
    print("=" * 80, flush=True)
    print("Lemma C minima investigation: |SK|_min at (n, L >= 2n+2)", flush=True)
    print("=" * 80, flush=True)

    minima = {}  # (n, L) -> (min_sk, ms, movers)

    plan = [
        (5, 1,  3000, 12.0, 16),
        (6, 2,  1500,  8.0, 18),
        (7, 8,   500,  6.0, 20),
        (8, 60,  150,  5.0, 22),
    ]

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue  # only care about L >= 2n+2 here
                sk = sk_size(ms, n, cycle, det)
                key = (n, L)
                if key not in minima or sk < minima[key][0]:
                    minima[key] = (sk, ms, list(movers))
            if (idx + 1) % 20 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s", flush=True)

    print(f"\n  === minima by (n, L) ===", flush=True)
    print(f"    n  L   |SK|_min   ms                              movers", flush=True)
    for (n, L) in sorted(minima.keys()):
        sk, ms, movers = minima[(n, L)]
        ms_str = str(ms)[:32]
        print(f"    {n}  {L:2d}  {sk:5d}     {ms_str:<32}  {movers}", flush=True)

    # Try several closed-form floors against the actual minima
    print(f"\n  === floor candidates vs minima (only L >= 2n+2) ===", flush=True)
    candidates = {
        "2^n - 2n - 2*[n odd]":           lambda n, L: 2**n - 2*n - (2 if n % 2 == 1 else 0),
        "2^n - 2n - 2*(L-2n)":            lambda n, L: 2**n - 2*n - 2*(L - 2*n),
        "2^n - 2n - 4*(L-2n-1)":          lambda n, L: 2**n - 2*n - 4*max(L - 2*n - 1, 0),
        "2^n - L - 2":                    lambda n, L: 2**n - L - 2,
        "2^n - L - 4":                    lambda n, L: 2**n - L - 4,
        "2^(n-1)":                        lambda n, L: 2**(n - 1),
        "2^n - 2L":                       lambda n, L: 2**n - 2*L,
        "2^n - 3*(L-2n) - 2n":            lambda n, L: 2**n - 3*(L - 2*n) - 2*n,
    }
    for name, f in candidates.items():
        ok = 0; total = 0; min_slack = float('inf'); worst = None
        for (n, L), (sk, ms, mv) in minima.items():
            lb = f(n, L)
            total += 1
            if lb <= sk:
                ok += 1
                if sk - lb < min_slack:
                    min_slack = sk - lb
                    worst = (n, L, sk, lb)
        rate = ok / total * 100 if total else 0
        gives_one = sum(1 for (n, L) in minima if f(n, L) >= 1)
        print(f"    {name:<28}  holds {rate:5.1f}%  ({ok}/{total})  min_slack={min_slack}  "
              f"|SK|>=1: {gives_one}/{total}", flush=True)
        if worst:
            n, L, sk, lb = worst
            print(f"      tightest: n={n} L={L} SK_min={sk} lb={lb}", flush=True)


if __name__ == "__main__":
    main()
