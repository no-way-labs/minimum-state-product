#!/usr/bin/env python3
"""Exploration 4: Large-L boundary test for the clouds theorem.

Critical observation: at ms=(2,...,2) on {0,1}^n, the game graph is the
hypercube Q_n (bipartite, only even-length cycles). With L configs in the
cycle, |VC-NG| = 2^n - L. For |SK| >= 2^(n-1), we need L <= 2^(n-1).

But does |SK| actually reach 2^(n-1) for L close to 2^(n-1)?

This probe:
1. Enumerates longer cycles (up to L=2^n) at n=5,6
2. Finds the MAXIMUM L with a valid fair cycle
3. Checks |SK| at all L values, especially large ones
4. Identifies the L boundary where |SK| < 2^(n-1)
"""
from itertools import product as iproduct
from collections import defaultdict
import time


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def compute_sk(ms, n, cycle, movers, det):
    """Compute |SK| for the VC forced graph."""
    cycle_set = set(cycle)
    V = value_sets(cycle, n)

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    out_edges = defaultdict(list)
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in vc_ng:
                    out_edges[c].append(nc)

    remaining = set(vc_ng)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in out_edges.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks

    return len(remaining), len(vc_ng)


def enumerate_cycles_deep(ms, n, L_max, time_budget, max_cycles):
    """Enumerate fair cycles with longer L."""
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) == set(range(n)):
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


def main():
    print("=" * 72)
    print("Exploration 4: Large-L boundary for clouds theorem")
    print("=" * 72)

    # Test at n=5 with all-binary ms and extended L range
    n = 5
    ms = (2, 2, 2, 2, 2)
    L_max = 32  # maximum possible on {0,1}^5

    print(f"\n=== n={n}, ms={ms}, L_max={L_max} ===")
    print(f"  Config space: {2**n}")
    print(f"  2^(n-1) = {2**(n-1)}")
    print(f"  Searching for cycles up to L={L_max}...")

    cycles = enumerate_cycles_deep(ms, n, L_max, 60.0, 5000)
    print(f"  Found {len(cycles)} cycles")

    by_L = defaultdict(list)
    for cycle, movers, det in cycles:
        L = len(movers)
        sk, ng = compute_sk(ms, n, cycle, movers, det)
        by_L[L].append({'sk': sk, 'ng': ng, 'L': L})

    target = 2 ** (n - 1)
    print(f"\n  L   count  |NG|  min_SK  max_SK  2^(n-1)  slack  violation?")
    for L in sorted(by_L.keys()):
        rs = by_L[L]
        min_sk = min(r['sk'] for r in rs)
        max_sk = max(r['sk'] for r in rs)
        ng = rs[0]['ng']  # same for all at this L and ms
        slack = min_sk - target
        flag = " VIOLATION!" if min_sk < target else ""
        print(f"  {L:3d}  {len(rs):5d}  {ng:4d}  {min_sk:6d}  {max_sk:6d}  "
              f"{target:6d}  {slack:+5d}{flag}")

    # Also test at ms=(2,2,2,3,3) with extended range
    print(f"\n=== n={n}, ms=(2,2,2,3,3), extended L ===")
    ms2 = (2, 2, 2, 3, 3)
    cycles2 = enumerate_cycles_deep(ms2, n, 40, 60.0, 3000)
    print(f"  Found {len(cycles2)} cycles")

    by_L2 = defaultdict(list)
    for cycle, movers, det in cycles2:
        L = len(movers)
        sk, ng = compute_sk(ms2, n, cycle, movers, det)
        by_L2[L].append({'sk': sk, 'ng': ng, 'L': L})

    print(f"\n  L   count  |NG|  min_SK  max_SK  2^(n-1)  slack  violation?")
    for L in sorted(by_L2.keys()):
        rs = by_L2[L]
        min_sk = min(r['sk'] for r in rs)
        max_sk = max(r['sk'] for r in rs)
        ng = rs[0]['ng']
        slack = min_sk - target
        flag = " VIOLATION!" if min_sk < target else ""
        print(f"  {L:3d}  {len(rs):5d}  {ng:4d}  {min_sk:6d}  {max_sk:6d}  "
              f"{target:6d}  {slack:+5d}{flag}")

    # Summary
    all_violations = 0
    max_L_no_violation = 0
    for L in sorted(by_L.keys()):
        rs = by_L[L]
        if min(r['sk'] for r in rs) >= target:
            max_L_no_violation = max(max_L_no_violation, L)
        else:
            all_violations += sum(1 for r in rs if r['sk'] < target)

    print(f"\n=== Summary for ms=(2,2,2,2,2) ===")
    print(f"  Total violations: {all_violations}")
    print(f"  Max L with no violation: {max_L_no_violation}")
    print(f"  L threshold: appears to be L <= {max_L_no_violation}")


if __name__ == "__main__":
    main()
