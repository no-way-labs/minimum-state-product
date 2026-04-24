#!/usr/bin/env python3
"""Floor-formula probe for |SK|: test Lemma A generalized to arbitrary
cycle length and multiset.

Goal: identify the exact closed-form floor for |SK|(n, L) across all
fair simple closed cycles on sub-M_n multisets at n ∈ {5,6,7,8}.

Hypotheses to test:
  H1: |SK|(n, L=2n)   = 2^n - 2n - 2*[n odd]    (Lemma A)
  H2: |SK|(n, L=2n+1) = 2^n - 2n + 1            (n=5 prior data)
  H3: |SK|(n, L=2n+k) = 2^n - 2n - g(k, n)      (unknown g)

Outputs:
  - (n, L) → (min, max, mean, count) of |SK|, grouped
  - for each (n, L), report whether |SK| is CONSTANT
  - fit a closed-form floor: a·2^n + b·n + c·L + d
  - report any (n, L) bucket where the floor hypothesis fails
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
    print("=" * 90, flush=True)
    print("Floor-formula probe for |SK|(n, L)", flush=True)
    print("=" * 90, flush=True)

    # (n, L) -> list of |SK| values
    by_nL = defaultdict(list)
    # (n, L) -> list of (ms, |SK|) for later inspection
    examples = defaultdict(list)
    total_records = 0
    lb_failures = []

    plan = [
        # (n, stride, max_cycles, time_budget, L_max)
        (5, 1,  3000, 12.0, 14),   # exhaustive 26 multisets
        (6, 2,  1500,  8.0, 16),   # stride 2 over 74
        (7, 8,   500,  6.0, 18),   # stride 8 over ~103
        (8, 48,  200,  5.0, 20),   # aggressive stride over 4555 → ~95
    ]
    for n, stride, max_cycles, time_budget, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  sampled {len(sampled)} of {len(multisets)} multisets  "
              f"cap={max_cycles}  L_max={L_max} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                sk = sk_size(ms, n, cycle, det)
                total_records += 1
                by_nL[(n, L)].append(sk)
                if len(examples[(n, L)]) < 3:
                    examples[(n, L)].append((ms, sk))
                if sk == 0:
                    lb_failures.append((n, ms, cycle, movers))
            if (idx + 1) % 20 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s  records={total_records}", flush=True)

    print(f"\n  total records: {total_records}", flush=True)
    print(f"  LB failures: {len(lb_failures)}", flush=True)

    # === Report (n, L) -> |SK| distribution ===
    print(f"\n  === (n, L) -> |SK| distribution ===", flush=True)
    print(f"    n  L   count       min   max  mean   Lemma-A?  const?", flush=True)
    for n in sorted(set(k[0] for k in by_nL)):
        ls = sorted(L for (nn, L) in by_nL if nn == n)
        for L in ls:
            vs = by_nL[(n, L)]
            mn = min(vs); mx = max(vs); mean = sum(vs) / len(vs)
            # Lemma A prediction at L=2n: 2^n - 2n - 2*[n odd]
            lemA = None
            if L == 2 * n:
                lemA = 2**n - 2*n - (2 if n % 2 == 1 else 0)
            lemA_match = "match" if lemA is not None and mn == lemA == mx else ""
            const = "YES" if mn == mx else ""
            lemA_str = f"{lemA}" if lemA is not None else ""
            print(f"    {n}  {L:2d}  {len(vs):7d}  {mn:5d}  {mx:4d}  {mean:6.1f}  "
                  f"{lemA_str:>4} {lemA_match:>6}  {const}", flush=True)

    # === Lemma A check at L = 2n ===
    print(f"\n  === Lemma A generalization check (L = 2n) ===", flush=True)
    for n in sorted(set(k[0] for k in by_nL)):
        if (n, 2*n) in by_nL:
            vs = by_nL[(n, 2*n)]
            expected = 2**n - 2*n - (2 if n % 2 == 1 else 0)
            mn, mx = min(vs), max(vs)
            status = "CONFIRMED" if mn == expected == mx else "VIOLATION"
            print(f"    n={n}  L=2n={2*n}  |SK| range=[{mn},{mx}]  "
                  f"expected={expected}  [{status}]  count={len(vs)}", flush=True)

    # === Closed-form floor search ===
    # Hypothesis: |SK|(n, L) >= 2^n - 2n - g(L - 2n, n) for some g ≥ 0
    # g(0, n) = 2*[n odd]
    # Fit g(k, n) for k = 0, 1, 2, 3, 4 from observed minima
    print(f"\n  === inferred floor function g(k, n) where |SK|_min = 2^n - 2n - g ===", flush=True)
    print(f"    n   k=0  k=1  k=2  k=3  k=4", flush=True)
    for n in sorted(set(k[0] for k in by_nL)):
        row = [f"    {n}"]
        for k in range(5):
            L = 2 * n + k
            if (n, L) in by_nL:
                mn = min(by_nL[(n, L)])
                g = (2**n - 2*n) - mn
                row.append(f"  {g:4d}")
            else:
                row.append("    - ")
        print("".join(row), flush=True)

    # === Universal floor candidates (must hold across ALL records) ===
    print(f"\n  === universal floor tests ===", flush=True)
    candidates = {
        "2^n - 2n":            lambda n, L: 2**n - 2*n,
        "2^n - 2n - 2":        lambda n, L: 2**n - 2*n - 2,
        "2^n - 2n - 4":        lambda n, L: 2**n - 2*n - 4,
        "2^n - L":             lambda n, L: 2**n - L,
        "2^n - L - 2":         lambda n, L: 2**n - L - 2,
        "2^n - L - 4":         lambda n, L: 2**n - L - 4,
        "2^n - 2L + 2n":       lambda n, L: 2**n - 2*L + 2*n,
        "2^n - 2n - 2*(L-2n)": lambda n, L: 2**n - 2*n - 2*max(L - 2*n, 0),
        "2^n - 2n - (L-2n+2)": lambda n, L: 2**n - 2*n - max(L - 2*n + 2, 0),
    }
    for name, f in candidates.items():
        holds = 0
        fails = 0
        gives_one = 0
        min_slack = float('inf')
        worst = None
        for (n, L), vs in by_nL.items():
            lb = f(n, L)
            if lb >= 1:
                gives_one += len(vs)
            for sk in vs:
                if lb <= sk:
                    holds += 1
                    slack = sk - lb
                    if slack < min_slack:
                        min_slack = slack
                        worst = (n, L, sk, lb)
                else:
                    fails += 1
        total = holds + fails
        rate = holds / total * 100 if total else 0
        implies_rate = gives_one / total * 100 if total else 0
        print(f"    {name:<26}  holds: {rate:6.2f}%  implies|SK|>=1: {implies_rate:5.1f}%  "
              f"min_slack: {min_slack}", flush=True)
        if worst and rate < 100:
            n, L, sk, lb = worst
            print(f"      tightest: n={n} L={L} SK={sk} lb={lb}", flush=True)

    if lb_failures:
        print(f"\n  !!! LB FAILURES:", flush=True)
        for n, ms, c, m in lb_failures[:5]:
            print(f"    n={n} ms={ms} len={len(c)} movers={m}", flush=True)


if __name__ == "__main__":
    main()
