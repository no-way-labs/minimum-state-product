#!/usr/bin/env python3
"""clb_verify_8748.py — Verify the good-targeting completion at product 8748.

If valid, this would give M_9 ≤ 8748, disproving the two-phase conjecture!
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system


def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    if base_pattern is None:
        base_pattern = list(range(n-1, -1, -1)) + list(range(1, n))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = base_pattern * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle, full[:step+1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


n = 9
ms_tuple = (2, 3, 3, 3, 3, 3, 3, 3, 2)
up_down = list(range(n)) + list(range(n-2, 0, -1))
cycle, movers = build_bounce_cycle(ms_tuple, n, up_down)
good_set = set(cycle)
all_configs = list(cartesian(*(range(m) for m in ms_tuple)))
non_good = [c for c in all_configs if c not in good_set]
non_good_set = set(non_good)

# Extract determined entries
det = {}
for idx in range(len(cycle)):
    c = cycle[idx]
    c_next = cycle[(idx + 1) % len(cycle)]
    mover = movers[idx]
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        key = (p, L, S, R)
        if p == mover:
            det[key] = c_next[p]
        else:
            det[key] = S

free_entries = []
for p in range(n):
    m_L = ms_tuple[(p - 1) % n]
    m_S = ms_tuple[p]
    m_R = ms_tuple[(p + 1) % n]
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                key = (p, L, S, R)
                if key not in det:
                    free_entries.append(key)

# Compute edge costs (same as clb_inherent_cycles.py)
edge_costs = {}
for key in free_entries:
    p, L, S, R = key
    for out in range(ms_tuple[p]):
        if out == S:
            edge_costs[(key, out)] = 0
        else:
            edges = 0
            for c in non_good:
                if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                    new_c = list(c)
                    new_c[p] = out
                    if tuple(new_c) in non_good_set:
                        edges += 1
            edge_costs[(key, out)] = edges

# Build good-targeting completion
comp = dict(det)
for key in free_entries:
    p, L, S, R = key
    best_out = S
    best_good = 0
    best_ng = float('inf')
    for out in range(ms_tuple[p]):
        ng = edge_costs.get((key, out), 0)
        good_count = 0
        if out != S:
            for c in non_good:
                if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                    new_c = list(c)
                    new_c[p] = out
                    if tuple(new_c) in good_set:
                        good_count += 1
        if good_count > best_good or (good_count == best_good and ng < best_ng):
            best_out = out
            best_good = good_count
            best_ng = ng
    comp[key] = best_out

# Fix liveness
for c in all_configs:
    has_priv = any(
        comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
        for p in range(n))
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
                for out in range(ms_tuple[p]):
                    if out != S2:
                        cost = edge_costs.get((key, out), 0)
                        if cost < best_cost:
                            best_cost = cost
                            best_key = key
                            best_out_val = out
        if best_key:
            comp[best_key] = best_out_val

# Convert to transition functions
def make_f(p_idx, completion):
    def f(L, S, R):
        key = (p_idx, L, S, R)
        return completion.get(key, S)
    return f

fs = [make_f(p, comp) for p in range(n)]
ms_list = list(ms_tuple)

print("=" * 70)
print("VERIFICATION: ms=(2,3,3,3,3,3,3,3,2), product=8748")
print("=" * 70)

# Quick pre-check
dead = 0
multi_priv_good = 0
for c in all_configs:
    priv = []
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if fs[p](L, S, R) != S:
            priv.append(p)
    if not priv:
        dead += 1
    if c in good_set and len(priv) != 1:
        multi_priv_good += 1

print(f"Pre-check:")
print(f"  Dead configs: {dead}")
print(f"  Good configs with != 1 privilege: {multi_priv_good}")

# Full verification
result = verify_system(ms_list, fs, verbose=True)
print(f"\nFull verification: valid = {result['valid']}")
for prop, (ok, msg) in result['properties'].items():
    print(f"  {prop}: {ok} — {msg}")

if result['valid']:
    print("\n*** VALID SYSTEM FOUND AT PRODUCT 8748! ***")
    print("This gives M_9 ≤ 8748.")
    print("The two-phase conjecture (M_n = 2·3^(n-1) for n≥9) is DISPROVED!")

    # Extract the transition tables for documentation
    print("\nTransition tables:")
    for p in range(n):
        m_L = ms_tuple[(p-1)%n]
        m_S = ms_tuple[p]
        m_R = ms_tuple[(p+1)%n]
        priv_count = 0
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    if fs[p](L, S, R) != S:
                        priv_count += 1
        print(f"  P{p} (m={m_S}): {priv_count}/{m_L*m_S*m_R} privileged triples")
else:
    print("\nSystem is NOT valid. Checking what went wrong...")

    # Additional diagnostics
    # Check for SCCs manually
    bad_adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            new_S = fs[p](L, S, R)
            if new_S != S:
                new_c = list(c)
                new_c[p] = new_S
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    bad_adj[c].append(new_c)

    from clb_inherent_cycles import find_sccs
    sccs = find_sccs(dict(bad_adj))
    trapped = sum(len(s) for s in sccs)
    print(f"  Non-good SCCs: {len(sccs)}, trapped: {trapped}")
    if sccs:
        sizes = sorted([len(s) for s in sccs], reverse=True)
        print(f"  SCC sizes: {sizes[:10]}")
