#!/usr/bin/env python3
"""Test clouds-proof candidates for |SK(C)| >= 1 via counting inequalities.

Strategy: for every fair simple closed cycle C on every sub-M_n multiset
at n=5 (exhaustive) and n=6 (sampled), record the tuple:

  (n, ms, |M|, L=|C|, |NG|=|M|-L, |SK|, binary_count, max_fc)

Then test candidate inequalities of shape  |SK| >= f(n, |M|, L, binary)
across all cycles. Report:
  - tightest linear-form inequality that holds on 100% of cycles
  - tightest ratio |SK|/|NG| that holds
  - any inequality that holds but implies |SK| >= 1 at sub-M_n

Goal: find a single closed-form invariant that replaces the 4-case split.
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


def enumerate_all_cycles(ms, n, L_max, time_budget=15.0, max_cycles=3000):
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
    print("=" * 90, flush=True)
    print("Counting-inequality clouds-proof probe", flush=True)
    print("=" * 90, flush=True)

    records = []  # (n, ms, M, L, NG, SK, binary_count, max_fc)

    for n in [5, 6]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        if n == 6:
            multisets = multisets[::3]  # stride sample
        print(f"\n=== n={n}  {len(multisets)} multisets ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            M = 1
            for m in ms: M *= m
            binary = sum(1 for m in ms if m == 2)
            cycles = enumerate_all_cycles(ms, n, L_max=2*n+4, time_budget=10.0, max_cycles=2000)
            for cycle, movers, det in cycles:
                L = len(movers)
                sk = sk_size(ms, n, cycle, det)
                fc = Counter(movers)
                max_fc = max(fc.values())
                records.append((n, ms, M, L, M - L, sk, binary, max_fc))
            if (idx + 1) % 10 == 0 or idx == len(multisets) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(multisets)}]  {elapsed:.0f}s  records={len(records)}", flush=True)

    print(f"\n  total records: {len(records)}", flush=True)
    if not records:
        return

    # Diagnostic: any record with SK=0? That would be an LB failure.
    failures = [r for r in records if r[5] == 0]
    print(f"  LB failures (|SK|=0): {len(failures)}", flush=True)

    # Candidate inequalities to test
    # Each is a lambda taking (n, M, L, NG, binary) and returning a lower bound
    # for |SK| that we want to be <= actual |SK|. A perfect candidate returns
    # at least 1 always and never exceeds actual |SK|.
    candidates = {
        "M - 2n - n*binary":        lambda n, M, L, NG, b: M - 2*n - n*b,
        "NG - 2n":                  lambda n, M, L, NG, b: NG - 2*n,
        "NG - 4n":                  lambda n, M, L, NG, b: NG - 4*n,
        "NG - (L + 2n)":            lambda n, M, L, NG, b: NG - (L + 2*n),
        "NG - 2L":                  lambda n, M, L, NG, b: NG - 2*L,
        "M - 3L":                   lambda n, M, L, NG, b: M - 3*L,
        "M - 2L - 2n":              lambda n, M, L, NG, b: M - 2*L - 2*n,
        "M/2 - n":                  lambda n, M, L, NG, b: M // 2 - n,
        "M - L - 2^binary":         lambda n, M, L, NG, b: M - L - (2**b),
        "NG - 2^binary":            lambda n, M, L, NG, b: NG - (2**b),
        "NG - (L - 2n) - 2n":       lambda n, M, L, NG, b: NG - max(L - 2*n, 0) - 2*n,
        # Lemma A-inspired: at binary ms |SK| = NG - 2[n odd], so slack = 2
        "NG - 4":                   lambda n, M, L, NG, b: NG - 4,
        "NG - 2*(L - 2n + 1)":      lambda n, M, L, NG, b: NG - 2*(L - 2*n + 1) if L >= 2*n else NG,
        "NG/2":                     lambda n, M, L, NG, b: NG // 2,
        "NG - n":                   lambda n, M, L, NG, b: NG - n,
    }

    print(f"\n  === candidate inequality test ===", flush=True)
    for name, f in candidates.items():
        ok_count = 0
        min_slack = float('inf')
        worst_example = None
        gives_one_count = 0  # count of records where f(...) >= 1
        for (n, ms, M, L, NG, sk, b, mfc) in records:
            lb = f(n, M, L, NG, b)
            if lb <= sk:
                ok_count += 1
                slack = sk - lb
                if slack < min_slack:
                    min_slack = slack
                    worst_example = (n, ms, M, L, NG, sk, lb)
            if lb >= 1:
                gives_one_count += 1
        ok_rate = ok_count / len(records) * 100
        implies_rate = gives_one_count / len(records) * 100
        print(f"    {name:<32}  holds: {ok_rate:5.1f}%  implies|SK|>=1: {implies_rate:5.1f}%  min_slack: {min_slack}", flush=True)
        if name in {"NG - 2n", "NG - 4n", "NG - 4", "NG - n"}:
            if worst_example and min_slack < float('inf'):
                n,ms,M,L,NG,sk,lb = worst_example
                print(f"      worst: n={n} ms={ms} L={L} NG={NG} SK={sk} lb={lb}", flush=True)

    # Also compute |SK| / |NG| ratio distribution
    ratios = [r[5] / r[4] if r[4] > 0 else 0 for r in records]
    if ratios:
        ratios_sorted = sorted(ratios)
        print(f"\n  |SK|/|NG| distribution:", flush=True)
        print(f"    min:    {ratios_sorted[0]:.4f}", flush=True)
        print(f"    p1:     {ratios_sorted[len(ratios_sorted)//100]:.4f}", flush=True)
        print(f"    median: {ratios_sorted[len(ratios_sorted)//2]:.4f}", flush=True)
        print(f"    max:    {ratios_sorted[-1]:.4f}", flush=True)

    # Constant lower bound
    sks = [r[5] for r in records]
    print(f"\n  |SK| range: [{min(sks)}, {max(sks)}]", flush=True)
    print(f"  |SK| = 0 count: {sum(1 for s in sks if s == 0)}", flush=True)
    print(f"  |SK| = 1 count: {sum(1 for s in sks if s == 1)}", flush=True)
    print(f"  |SK| <= 5 count: {sum(1 for s in sks if s <= 5)}", flush=True)

    # |SK| vs L: is there a correlation?
    by_L = defaultdict(list)
    for r in records:
        by_L[r[3]].append(r[5])
    print(f"\n  |SK| by cycle length L:", flush=True)
    for L in sorted(by_L.keys()):
        vs = by_L[L]
        print(f"    L={L:3d}  count={len(vs):6d}  min={min(vs):4d}  max={max(vs):4d}  mean={sum(vs)/len(vs):.1f}", flush=True)


if __name__ == "__main__":
    main()
