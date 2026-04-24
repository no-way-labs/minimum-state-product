#!/usr/bin/env python3
"""clb_witness_8748.py — M_9 ≤ 8748 witness.

VALID self-stabilizing system at ms=(2,3,3,3,3,3,3,3,2), product=4·3^7=8748.
Verified: liveness, mutual_exclusion (71 good configs), closure,
convergence (8677 bad configs, no cycles), fairness (cycle len=25, all 9 procs).

Construction:
1. Good cycle: bounce cycle with mover pattern [0,1,...,8,7,...,1]
2. Free entries: good-targeting completion (prefer outputs reaching good cycle,
   break ties by minimizing non-good→non-good edges)
3. Liveness fix: for remaining dead configs, activate cheapest free entry
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system


def build_system():
    n = 9
    ms = (2, 3, 3, 3, 3, 3, 3, 3, 2)

    # Build bounce cycle
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * 3
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            raise RuntimeError("Cycle didn't close")
        visited.add(nc)
        cycle.append(nc)

    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Extract determined entries
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

    # Find free entries
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

    # Compute edge costs
    edge_costs = {}
    for key in free_entries:
        p, L, S, R = key
        for out in range(ms[p]):
            if out == S:
                edge_costs[(key, out)] = 0
            else:
                edges = sum(
                    1 for c in non_good
                    if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R
                    and tuple(c[j] if j != p else out for j in range(n)) in non_good_set
                )
                edge_costs[(key, out)] = edges

    # Good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = float('inf')
        for out in range(ms[p]):
            ng = edge_costs.get((key, out), 0)
            good_count = 0
            if out != S:
                good_count = sum(
                    1 for c in non_good
                    if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R
                    and tuple(c[j] if j != p else out for j in range(n)) in good_set
                )
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    # Liveness fix
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n)
        )
        if not has_priv:
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
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    # Build transition functions
    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    return list(ms), fs, comp


if __name__ == "__main__":
    ms, fs, comp = build_system()
    n = len(ms)

    print("=" * 70)
    print(f"M_9 witness: ms={tuple(ms)}, product={8748}")
    print("=" * 70)

    result = verify_system(ms, fs, verbose=True)
    print(f"\nValid: {result['valid']}")
    for prop, (ok, msg) in result['properties'].items():
        print(f"  {prop}: {ok} — {msg}")

    # Print transition tables
    print("\nTransition tables:")
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        print(f"\n  P{p} (m={m_S}):")
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    out = fs[p](L, S, R)
                    priv = "←" if out != S else ""
                    print(f"    f({L},{S},{R}) = {out} {priv}")
