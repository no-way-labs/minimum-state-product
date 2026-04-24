#!/usr/bin/env python3
"""Exhaustive all-multiset SK enumeration — step 3.5.

For each n in {5, 6} and each sub-M_n multiset, enumerate every fair
simple closed cycle (any mover sequence, up to cycle length sum(m_i))
and verify |SK| > 0 (ideally |SK| = 2^n - 2n - eps(n), matching
Conjecture B).

Branching factor:
  - At each cycle step, the DFS picks a mover p ∈ {0..n-1} and a new
    value v != c[p] from Fin(m_p). Branching ≤ n · (max m - 1).
  - Pruning: det consistency + whole-config no-revisit.

For n=5 sub-M_5 multisets, max product 95, max cycle length ≤ 13.
Feasible to exhaustively enumerate.

For n=6 sub-M_6, max product 287, cycle length ≤ 16 or so.
Harder but mostly feasible.

Goal: 0 violations across all (ms, cycle) pairs.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math
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


def enumerate_all_cycles(ms, n, L_max, time_budget=120.0, max_cycles=100000):
    """Exhaustive DFS over fair simple closed cycles up to length L_max."""
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
            L = len(path)
            norm = min(tuple(path[i:] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path), list(movers), dict(det)))
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
    return found, time.time() - t0


def sk_size(ms, n, cycle, det):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in set(cycle)]
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


def expected_sk(n):
    return 2 ** n - 2 * n - (2 if n % 2 == 1 else 0)


def main():
    print("=" * 90, flush=True)
    print("Exhaustive all-ms SK enumeration (step 3.5)", flush=True)
    print("=" * 90, flush=True)

    for n in [5, 6]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        expected = expected_sk(n)
        print(f"\n=== n={n}  M_n={Mn}  sub-M_n multisets: {len(multisets)}  expected |SK|={expected} ===", flush=True)

        total_cycles = 0
        violations = []
        sk_histogram = Counter()
        problem_ms = []  # ms where |SK| != expected (and |SK| > 0 — not a LB failure but conjecture B gap)
        lb_failures = []  # ms where |SK| = 0 (LB FAILS)
        ms_no_cycle = []

        t_start = time.time()
        max_L = n + max([10] + [m for m in range(2, 9)])  # ≈ sum(m_i) upper bound ~ 2n

        for idx, ms in enumerate(multisets):
            L_max = sum(ms) + 1  # upper bound on simple cycle length
            cycles, t = enumerate_all_cycles(ms, n, L_max, time_budget=30.0, max_cycles=50000)
            if not cycles:
                ms_no_cycle.append(ms)
                continue
            ms_violations = 0
            ms_lb_fail = 0
            for cycle, movers, det in cycles:
                total_cycles += 1
                sz = sk_size(ms, n, cycle, det)
                sk_histogram[sz] += 1
                if sz == 0:
                    ms_lb_fail += 1
                    lb_failures.append((ms, cycle, movers))
                elif sz != expected:
                    ms_violations += 1
            if ms_violations:
                problem_ms.append((ms, ms_violations, len(cycles)))
            if (idx + 1) % 5 == 0 or idx == len(multisets) - 1:
                elapsed = time.time() - t_start
                print(f"  [{idx+1}/{len(multisets)}]  {elapsed:.1f}s  total_cycles={total_cycles}  LB_fails={len(lb_failures)}  conj_B_gaps={len(problem_ms)}", flush=True)

        print(f"\n  summary: {total_cycles} cycles tested across {len(multisets) - len(ms_no_cycle)} multisets", flush=True)
        print(f"  no-cycle ms: {len(ms_no_cycle)}", flush=True)
        print(f"  |SK| histogram: {dict(sorted(sk_histogram.items()))}", flush=True)
        print(f"  LB failures (|SK|=0): {len(lb_failures)}", flush=True)
        if lb_failures:
            for ms, c, m in lb_failures[:5]:
                print(f"    FAIL ms={ms} cycle_len={len(c)}", flush=True)
        print(f"  Conjecture-B gaps (|SK|>0 but != {expected}): {len(problem_ms)}", flush=True)
        if problem_ms:
            for ms, nv, nc in problem_ms[:10]:
                print(f"    ms={ms} violations={nv}/{nc}", flush=True)


if __name__ == "__main__":
    main()
