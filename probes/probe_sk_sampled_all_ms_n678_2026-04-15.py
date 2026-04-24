#!/usr/bin/env python3
"""Sampled all-ms SK enumeration at n=6,7,8 — step 3.5 continuation.

The exhaustive enumerator (probe_sk_exhaustive_all_ms) hit 599K cycles
at n=5 in ~8 min with 50k/multiset cap. At n=6 (147 multisets) it'd
take ~45 min; at n=7 (820) ~4 hours; at n=8 (4555) infeasible.

This script drops the per-multiset cap dramatically (2000 cycles, 10s
budget) to push through n=6, 7, 8 at rough completeness. The goal is
to FIND LB violations (cycles with |SK|=0), not to exhaustively
characterize the |SK| distribution. A partial sample suffices to
detect failure — finding 0 failures in a big sample is strong
evidence for the weak-Conjecture-B statement.
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


def enumerate_cycles_sample(ms, n, L_max, time_budget=10.0, max_cycles=2000):
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
    return found


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


def main():
    print("=" * 90, flush=True)
    print("Sampled all-ms SK enumeration at n=6,7,8 (step 3.5 continuation)", flush=True)
    print("=" * 90, flush=True)

    for n, max_cycles_per_ms, time_budget, L_max in [
        (6, 2000, 10.0, 16),
        (7, 1000, 8.0, 18),
        (8, 500, 6.0, 20),
    ]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        print(f"\n=== n={n}  M_n={Mn}  multisets: {len(multisets)}  cap: {max_cycles_per_ms} cycles @ {time_budget}s each ===", flush=True)

        total_cycles = 0
        lb_failures = []
        sk_values_seen = Counter()
        ms_no_cycle = 0
        ms_checked = 0

        t_start = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_cycles_sample(ms, n, L_max, time_budget=time_budget, max_cycles=max_cycles_per_ms)
            if not cycles:
                ms_no_cycle += 1
                continue
            ms_checked += 1
            for cycle, movers, det in cycles:
                total_cycles += 1
                sz = sk_size(ms, n, cycle, det)
                sk_values_seen[sz] += 1
                if sz == 0:
                    lb_failures.append((ms, cycle, movers))
                    print(f"  !!! LB FAIL at ms={ms} cycle_len={len(cycle)}  movers={movers}", flush=True)
            if (idx + 1) % 20 == 0 or idx == len(multisets) - 1:
                elapsed = time.time() - t_start
                print(f"  [{idx+1}/{len(multisets)}]  {elapsed:.0f}s  total_cycles={total_cycles}  LB_fails={len(lb_failures)}  ms_with_cycles={ms_checked}  ms_no_cycle={ms_no_cycle}", flush=True)

        print(f"\n  === n={n} summary ===", flush=True)
        print(f"  total cycles tested: {total_cycles}", flush=True)
        print(f"  multisets covered: {ms_checked} / {len(multisets)} (no-cycle: {ms_no_cycle})", flush=True)
        print(f"  LB failures: {len(lb_failures)}", flush=True)
        print(f"  distinct |SK| values observed: {sorted(sk_values_seen.keys())[:15]}", flush=True)
        print(f"  min |SK|: {min(sk_values_seen.keys()) if sk_values_seen else 'N/A'}", flush=True)


if __name__ == "__main__":
    main()
