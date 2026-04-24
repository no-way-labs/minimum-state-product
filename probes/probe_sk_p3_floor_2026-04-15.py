#!/usr/bin/env python3
"""Verify the (P3) information-theoretic floor candidates against all data.

Hypotheses:
  H_P3a: |SK(C)| >= |M| - 2*|C|
  H_P3b: |SK(C)| >= |M| - |C| - |C| * 2^(n-3)         (edge counting)
  H_P3c: |SK(C)| >= 1 whenever |C| * 2^(n-3) > |M| - |C|  (cycle-existence)
  H_P3d: |SK(C)| >= 2^(n-1)                            (strong form)

For each hypothesis, report:
  - holds-rate
  - tightest example
  - whether implies |SK| >= 1
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
    edges = 0
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
                    edges += 1
    remaining = set(non_good)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    return len(remaining), edges


def main():
    print("=" * 80, flush=True)
    print("(P3) information-theoretic floor verification", flush=True)
    print("=" * 80, flush=True)

    records = []  # (n, M, L, NG, SK, edges)
    plan = [
        (5, 1,  2000, 10.0, 16),
        (6, 3,  1000,  6.0, 18),
        (7, 12,  300,  5.0, 20),
    ]
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            M = 1
            for m in ms: M *= m
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                sk, edges = sk_size(ms, n, cycle, det)
                records.append((n, M, L, M - L, sk, edges))
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s  records={len(records)}", flush=True)

    print(f"\n  total records: {len(records)}", flush=True)

    # H_P3a: |SK| >= |M| - 2|C|
    a_holds = sum(1 for n, M, L, NG, sk, e in records if M - 2*L <= sk)
    a_implies = sum(1 for n, M, L, NG, sk, e in records if M - 2*L >= 1)
    a_min_slack = min((sk - (M - 2*L)) for n, M, L, NG, sk, e in records if M - 2*L <= sk) if a_holds else None
    print(f"\n  H_P3a: |SK| >= M - 2L", flush=True)
    print(f"    holds: {a_holds}/{len(records)} ({a_holds/len(records)*100:.2f}%)", flush=True)
    print(f"    implies |SK|>=1: {a_implies}/{len(records)} ({a_implies/len(records)*100:.2f}%)", flush=True)
    print(f"    min slack: {a_min_slack}", flush=True)

    # H_P3b: |SK| >= |M| - |C| - |C| * 2^(n-3)  (negative, ignore)
    b_holds = sum(1 for n, M, L, NG, sk, e in records if M - L - L * 2**(n - 3) <= sk)
    print(f"\n  H_P3b: |SK| >= M - L - L * 2^(n-3)", flush=True)
    print(f"    holds: {b_holds}/{len(records)} ({b_holds/len(records)*100:.2f}%)", flush=True)

    # H_P3c: |SK| >= 1 whenever L * 2^(n-3) > M - L
    c_eligible = [(n, M, L, NG, sk) for n, M, L, NG, sk, e in records if L * 2**(n - 3) > M - L]
    c_holds = sum(1 for n, M, L, NG, sk in c_eligible if sk >= 1)
    print(f"\n  H_P3c: |SK|>=1 when L*2^(n-3) > NG", flush=True)
    print(f"    eligible records: {len(c_eligible)}/{len(records)}", flush=True)
    print(f"    of those, |SK|>=1: {c_holds}/{len(c_eligible)}", flush=True)

    # H_P3d: |SK| >= 2^(n-1)
    d_holds = sum(1 for n, M, L, NG, sk, e in records if 2**(n - 1) <= sk)
    print(f"\n  H_P3d: |SK| >= 2^(n-1)", flush=True)
    print(f"    holds: {d_holds}/{len(records)} ({d_holds/len(records)*100:.2f}%)", flush=True)

    # Edge stats
    edges_all = [e for n, M, L, NG, sk, e in records]
    print(f"\n  Edge counts: min={min(edges_all)}  max={max(edges_all)}  mean={sum(edges_all)/len(edges_all):.0f}", flush=True)

    # Compare edges to L*2^(n-3)
    edge_vs_bound = []
    for n, M, L, NG, sk, e in records:
        bound = L * 2**(n - 3)
        edge_vs_bound.append((e, bound, e / max(bound, 1)))
    ratios = [r[2] for r in edge_vs_bound]
    print(f"  Actual edges / (L*2^(n-3)):  min={min(ratios):.3f}  max={max(ratios):.3f}  mean={sum(ratios)/len(ratios):.3f}", flush=True)


if __name__ == "__main__":
    main()
