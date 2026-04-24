#!/usr/bin/env python3
"""Verify structural invariants of the greedy endpoint-binary construction.

Goal: Establish properties that hold for ALL n, supporting a meta-theorem
that the greedy construction always produces a valid system.

Properties to verify:
1. Bounce cycle structure: length 3n-2, all procs visited, single privilege
2. Determined entries: exactly 9n-6
3. Free entries: exactly 18n-42
4. Greedy completion: produces no bad cycles
5. Liveness fixes needed: exactly n-3
6. Total good configs: n^2 - 2n + 8
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, deque
from verifier import verify_system


def build_bounce_cycle(ms, n):
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (3 * n)
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step + 1]
        if nc in visited:
            raise RuntimeError(f"Revisited {nc}")
        visited.add(nc)
        cycle.append(nc)
    raise RuntimeError("Cycle didn't close")


def build_system_fixed(n):
    """CLB construction with corrected tiebreaker (best_ng=0)."""
    ms = tuple([2] + [3] * (n - 2) + [2])
    cycle, movers = build_bounce_cycle(ms, n)
    good_set = set(cycle)

    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Determined entries
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

    # Free entries
    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Greedy completion with corrected tiebreaker
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = 0  # FIXED: was float('inf')
        for out in range(ms[p]):
            ng = 0
            good_count = 0
            if out != S:
                for c in non_good:
                    if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                        new_c = tuple(c[j] if j != p else out for j in range(n))
                        if new_c in good_set:
                            good_count += 1
                        elif new_c in non_good_set:
                            ng += 1
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    # Count privileges before liveness fix
    priv_before = sum(1 for key in comp if comp[key] != key[2])

    # Liveness fix
    liveness_fixes = 0
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n)
        )
        if not has_priv:
            liveness_fixes += 1
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = sum(
                                1 for c2 in non_good
                                if c2[(p - 1) % n] == L2 and c2[p] == S2 and c2[(p + 1) % n] == R2
                                and tuple(c2[j] if j != p else out for j in range(n)) in non_good_set
                            )
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    return ms, fs, comp, cycle, movers, det, free_entries, liveness_fixes


def analyze_bad_graph(ms, fs, good_set, n):
    """Analyze the bad-config transition graph."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(all_configs) - good_set

    # Build bad→bad adjacency and count direct-to-good edges
    bad_adj = defaultdict(list)
    to_good_count = 0
    total_bad_edges = 0
    for c in bad_set:
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        for p in priv:
            lst = list(c)
            lst[p] = fs[p](c[(p - 1) % n], c[p], c[(p + 1) % n])
            succ = tuple(lst)
            if succ in bad_set:
                bad_adj[c].append(succ)
                total_bad_edges += 1
            elif succ in good_set:
                to_good_count += 1

    # DAG check via Kahn's algorithm
    in_deg = {c: 0 for c in bad_set}
    for c in bad_set:
        for s in bad_adj[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_set if in_deg[c] == 0)
    processed = 0
    topo = []
    while q:
        c = q.popleft()
        processed += 1
        topo.append(c)
        for s in bad_adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    is_dag = (processed == len(bad_set))

    # DAG depth
    max_depth = 0
    if is_dag:
        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in bad_adj[c]), default=0)
        max_depth = max(rank.values()) if rank else 0

    return {
        'bad_count': len(bad_set),
        'bad_edges': total_bad_edges,
        'to_good_edges': to_good_count,
        'is_dag': is_dag,
        'max_depth': max_depth,
    }


def main():
    print("STRUCTURAL INVARIANTS OF GREEDY ENDPOINT-BINARY CONSTRUCTION")
    print("=" * 90)
    header = (f"{'n':>3} {'cyc':>4} {'good':>5} {'det':>5} {'free':>5} "
              f"{'lfx':>4} {'bad':>6} {'b→b':>6} {'b→g':>5} "
              f"{'DAG':>4} {'depth':>5} {'valid':>5} {'t':>5}")
    print(header)
    print("-" * 90)

    formulas_match = True
    for nv in range(4, 14):
        ms_tuple = tuple([2] + [3] * (nv - 2) + [2])
        prod = 4 * 3 ** (nv - 2)
        if prod > 200000:
            print(f"{nv:>3} SKIP (prod={prod})")
            continue

        t0 = time.time()
        ms, fs, comp, cycle, movers, det, free_entries, liveness_fixes = build_system_fixed(nv)
        result = verify_system(ms, fs)

        good_set = set(cycle)
        # Extend good set from verifier if available
        if result['valid'] and 'good_configs' in result:
            good_set = result['good_configs']

        bad_info = analyze_bad_graph(ms, fs, good_set, nv)
        elapsed = time.time() - t0

        cyc_len = len(cycle)
        n_good = len(good_set)
        n_det = len(det)
        n_free = len(free_entries)
        valid = "Y" if result['valid'] else "N"

        print(f"{nv:>3} {cyc_len:>4} {n_good:>5} {n_det:>5} {n_free:>5} "
              f"{liveness_fixes:>4} {bad_info['bad_count']:>6} "
              f"{bad_info['bad_edges']:>6} {bad_info['to_good_edges']:>5} "
              f"{'Y' if bad_info['is_dag'] else 'N':>4} {bad_info['max_depth']:>5} "
              f"{valid:>5} {elapsed:>5.1f}")

        # Check formulas
        exp_cyc = 3 * nv - 2
        exp_good = nv * nv - 2 * nv + 8
        exp_det = 9 * nv - 6
        exp_free = 18 * nv - 42
        exp_lfx = nv - 3

        if cyc_len != exp_cyc:
            print(f"    FORMULA MISMATCH: cycle {cyc_len} vs expected {exp_cyc}")
            formulas_match = False
        if n_good != exp_good:
            print(f"    FORMULA MISMATCH: good {n_good} vs expected {exp_good}")
            formulas_match = False
        if n_det != exp_det:
            print(f"    FORMULA MISMATCH: det {n_det} vs expected {exp_det}")
            formulas_match = False
        if n_free != exp_free:
            print(f"    FORMULA MISMATCH: free {n_free} vs expected {exp_free}")
            formulas_match = False
        if liveness_fixes != exp_lfx:
            print(f"    FORMULA MISMATCH: lfx {liveness_fixes} vs expected {exp_lfx}")
            formulas_match = False

    print()
    if formulas_match:
        print("ALL FORMULAS MATCH for tested n values")
    else:
        print("SOME FORMULAS DO NOT MATCH")

    print("\nExpected formulas:")
    print("  Cycle length:    3n - 2")
    print("  Good configs:    n² - 2n + 8")
    print("  Determined:      9n - 6")
    print("  Free entries:    18n - 42")
    print("  Liveness fixes:  n - 3")


if __name__ == "__main__":
    main()
