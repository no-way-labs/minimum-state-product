#!/usr/bin/env python3
"""Build bounce good cycles at n=10, 11, 12 using CLB pattern; verify (F), (A).

CLB bounce cycle: ms=(2,3,...,3,2), mover pattern [0,1,...,n-1, n-2,...,1] × repeat.
Cycle length = 3n-2 (for n≥5).
"""
from itertools import product as iproduct, combinations
from collections import defaultdict
import time, sys
sys.setrecursionlimit(100000)


def build_bounce_cycle(n):
    """Return (ms, cycle, det) for CLB bounce at n."""
    ms = tuple([2] + [3]*(n-2) + [2])
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    movers = []
    full = up_down * 4
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            raise RuntimeError(f"Cycle didn't close at n={n}")
        visited.add(nc)
        cycle.append(nc)

    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S
    return ms, cycle, det, movers


def compute_sk(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)
    remaining = set(non_good)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        remaining -= sinks
    return remaining, V_sorted, cycle_set


def f_probe(n, ms, cycle, det, bound):
    sk, V_sorted, cycle_set = compute_sk(ms, n, cycle, det)
    if not sk: return None
    skuc = sk | cycle_set
    F_sizes, A_sizes = [], []
    for p in range(n):
        F_sizes.append(len({tuple(c[i] for i in range(n) if i != p) for c in skuc}))
        A_sizes.append(len({tuple(c[i] for i in range(n) if i != p) for c in sk}))
    # Binary lift
    bin_covs = []
    for p in range(n):
        labels_per_pos = []
        skip = False
        for i in range(n):
            if i == p: continue
            if len(V_sorted[i]) < 2: skip = True; break
            labels_per_pos.append(list(combinations(V_sorted[i], 2)))
        if skip: bin_covs.append(None); continue
        total = 1
        for lc in labels_per_pos: total *= len(lc)
        proj_skuc = {tuple(c[i] for i in range(n) if i != p) for c in skuc}
        proj_sk = {tuple(c[i] for i in range(n) if i != p) for c in sk}
        if total > 30000:
            label = tuple(pairs[0] for pairs in labels_per_pos)
            B = set(iproduct(*label))
            cov_skuc = sum(1 for b in B if b in proj_skuc)
            cov_sk = sum(1 for b in B if b in proj_sk)
            bin_covs.append((cov_skuc, cov_sk))
            continue
        best_skuc, best_sk = 0, 0
        for label in iproduct(*labels_per_pos):
            B = set(iproduct(*label))
            cs = sum(1 for b in B if b in proj_skuc)
            ck = sum(1 for b in B if b in proj_sk)
            if cs > best_skuc: best_skuc = cs
            if ck > best_sk: best_sk = ck
            if best_skuc == 2**(n-1) and best_sk == 2**(n-1): break
        bin_covs.append((best_skuc, best_sk))
    return {
        '|SK|': len(sk), 'L': len(cycle_set),
        'F_sizes': F_sizes, 'A_sizes': A_sizes, 'bin_covs': bin_covs,
        'V_sizes': [len(v) for v in V_sorted],
    }


def main():
    print("=" * 100)
    print("BOUNCE cycles at n=10, 11, 12; (F), (A), binary lift")
    print("=" * 100)
    for n in [9, 10, 11, 12]:
        bound = 2**(n-1)
        print(f"\n=== n={n} bound={bound} ===")
        t0 = time.time()
        ms, cycle, det, movers = build_bounce_cycle(n)
        print(f"  ms={ms}  L={len(cycle)}  (build {time.time()-t0:.1f}s)")
        t1 = time.time()
        r = f_probe(n, ms, cycle, det, bound)
        dt = time.time() - t1
        if r is None:
            print(f"  SK empty"); continue
        print(f"  |SK|={r['|SK|']} V_sizes={r['V_sizes']} probe {dt:.1f}s")
        F_min, F_max = min(r['F_sizes']), max(r['F_sizes'])
        A_min, A_max = min(r['A_sizes']), max(r['A_sizes'])
        print(f"  (F) ∀p |π_p(SK∪C)|: min={F_min} max={F_max} vs {bound}  "
              f"({'OK' if F_min>=bound else 'FAIL'})")
        print(f"  (A) max|π_p(SK)|={A_max} min={A_min} vs {bound}  "
              f"({'OK' if A_max>=bound else 'FAIL'})")
        bcs = [c for c in r['bin_covs'] if c is not None]
        if bcs:
            max_skuc = max(c[0] for c in bcs); max_sk = max(c[1] for c in bcs)
            full_skuc = sum(1 for c in bcs if c[0] == 2**(n-1))
            full_sk = sum(1 for c in bcs if c[1] == 2**(n-1))
            print(f"  bin lift SK∪C: max={max_skuc} full@ {full_skuc}/{len(bcs)}")
            print(f"  bin lift SK:   max={max_sk} full@ {full_sk}/{len(bcs)}")


if __name__ == "__main__":
    main()
