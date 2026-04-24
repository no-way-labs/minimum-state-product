#!/usr/bin/env python3
"""clb_clean_completion.py — Why does the clean bounce cycle fail at completion?

The (2,3,3,3,3,3,3,3,2) orientation has an overlap-free bounce cycle (len 25).
But M_9 > 8748, so completion into a valid system must fail.

Questions:
1. What do the determined entries look like?
2. What fraction of the rule table is determined?
3. Is there a specific config subspace where convergence fails?
4. Can we find the obstruction analytically?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import time


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


def find_sccs(adj):
    """Iterative Tarjan SCC."""
    idx_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []

    def strongconnect(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = idx_counter[0]
        idx_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        while work:
            node, si = work[-1]
            succs = adj.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = idx_counter[0]
                    idx_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1 or (scc[0] in adj and scc[0] in adj[scc[0]]):
                        sccs.append(scc)
                work.pop()
                if work:
                    lowlink[work[-1][0]] = min(lowlink[work[-1][0]], lowlink[node])

    for v in adj:
        if v not in index_map:
            strongconnect(v)
    return sccs


# ============================================================
# Build the clean bounce cycle
# ============================================================

n = 9
ms = (2, 3, 3, 3, 3, 3, 3, 3, 2)
up_down = list(range(n)) + list(range(n-2, 0, -1))
cycle, movers = build_bounce_cycle(ms, n, up_down)

assert cycle is not None, "Clean cycle should exist!"
print(f"Clean bounce cycle: ms={ms}, product=8748")
print(f"Cycle length: {len(cycle)}")
print(f"Movers: {movers}")
print()

# Print cycle
print("Step | Config    | Mover")
print("-----|-----------|------")
for idx in range(len(cycle)):
    c = cycle[idx]
    print(f"  {idx:2d} | {''.join(str(x) for x in c)} | P{movers[idx]}")

# ============================================================
# Extract determined entries
# ============================================================

det = {}  # (proc, L, S, R) -> new_S
for idx in range(len(cycle)):
    c = cycle[idx]
    c_next = cycle[(idx + 1) % len(cycle)]
    mover = movers[idx]
    for p in range(n):
        L = c[(p-1)%n]
        S = c[p]
        R = c[(p+1)%n]
        key = (p, L, S, R)
        if p == mover:
            det[key] = c_next[p]
        else:
            det[key] = S  # stays

# Count determined entries per processor
total_entries = 0
det_entries = 0
for p in range(n):
    m_L = ms[(p-1)%n]
    m_S = ms[p]
    m_R = ms[(p+1)%n]
    total_p = m_L * m_S * m_R
    det_p = sum(1 for L in range(m_L) for S in range(m_S) for R in range(m_R)
                if (p, L, S, R) in det)
    total_entries += total_p
    det_entries += det_p
    print(f"P{p}: {det_p}/{total_p} entries determined ({100*det_p/total_p:.0f}%)")

print(f"\nTotal: {det_entries}/{total_entries} determined ({100*det_entries/total_entries:.0f}%)")

# ============================================================
# Analyze the forced-entry graph (from determined entries only)
# ============================================================

print("\n" + "="*70)
print("Forced-entry SCC analysis (from determined entries only)")
print("="*70)

good_set = set(cycle)
all_configs = list(cartesian(*(range(m) for m in ms)))
non_good = [c for c in all_configs if c not in good_set]
non_good_set = set(non_good)

forced_adj = defaultdict(list)
for c in non_good:
    for p in range(n):
        L = c[(p-1)%n]
        S = c[p]
        R = c[(p+1)%n]
        key = (p, L, S, R)
        if key in det and det[key] != S:
            new_c = list(c)
            new_c[p] = det[key]
            new_c = tuple(new_c)
            if new_c in non_good_set:
                forced_adj[c].append(new_c)

sccs = find_sccs(dict(forced_adj))
print(f"Forced-entry SCCs: {len(sccs)}")
if sccs:
    sizes = sorted([len(s) for s in sccs], reverse=True)
    print(f"SCC sizes: {sizes[:20]}")
    print(f"Total configs in SCCs: {sum(sizes)}")

    # Analyze {0,1}^n content
    for scc in sccs[:3]:
        max_val = max(max(c) for c in scc)
        in_01 = sum(1 for c in scc if all(x <= 1 for x in c))
        print(f"  SCC size {len(scc)}: max state val={max_val}, "
              f"configs in {{0,1}}^9: {in_01}/{len(scc)}")
else:
    print("NO forced-entry SCCs — the clean cycle passes the forced-entry screen!")

# ============================================================
# Analyze liveness constraints
# ============================================================

print("\n" + "="*70)
print("Liveness analysis — configs with no forced privilege")
print("="*70)

# A non-good config c has "forced privilege" at proc p if (p,L,S,R) is a
# determined entry with det[key] != S.
# Configs with NO forced privilege need FREE entries to provide privilege.

no_forced_priv = []
for c in non_good:
    has_priv = False
    for p in range(n):
        L = c[(p-1)%n]
        S = c[p]
        R = c[(p+1)%n]
        key = (p, L, S, R)
        if key in det and det[key] != S:
            has_priv = True
            break
    if not has_priv:
        no_forced_priv.append(c)

print(f"Non-good configs: {len(non_good)}")
print(f"Configs with forced privilege: {len(non_good) - len(no_forced_priv)}")
print(f"Configs with NO forced privilege: {len(no_forced_priv)} "
      f"({100*len(no_forced_priv)/len(non_good):.1f}%)")

# How many of these are in {0,1}^n?
no_priv_01 = [c for c in no_forced_priv if all(x <= 1 for x in c)]
print(f"  Of which in {{0,1}}^9: {len(no_priv_01)}")
print(f"  Total {{0,1}}^9 configs: {2**n} (minus good: {2**n - sum(1 for c in cycle if all(x<=1 for x in c))})")

# For each no-privilege config, count how many free entries exist
print("\nFree entries for no-privilege configs (first 10):")
for c in no_forced_priv[:10]:
    free = []
    for p in range(n):
        L = c[(p-1)%n]
        S = c[p]
        R = c[(p+1)%n]
        key = (p, L, S, R)
        if key not in det:
            free.append(p)
    print(f"  {''.join(str(x) for x in c)}: free at procs {free}")

# ============================================================
# Analyze the {0,1}^n subspace behavior
# ============================================================

print("\n" + "="*70)
print("{0,1}^9 subspace analysis")
print("="*70)

configs_01 = [c for c in all_configs if all(x <= 1 for x in c)]
good_in_01 = [c for c in configs_01 if c in good_set]
bad_in_01 = [c for c in configs_01 if c not in good_set]

print(f"Total {0,1}^9: {len(configs_01)}")
print(f"Good in {{0,1}}^9: {len(good_in_01)}")
print(f"Bad in {{0,1}}^9: {len(bad_in_01)}")

# For bad {0,1}^9 configs, what transitions are determined?
# Key question: do the determined transitions keep configs WITHIN {0,1}^9?
stays_in_01 = 0
leaves_01 = 0
no_det_move = 0

for c in bad_in_01:
    for p in range(n):
        L = c[(p-1)%n]
        S = c[p]
        R = c[(p+1)%n]
        key = (p, L, S, R)
        if key in det and det[key] != S:
            new_c = list(c)
            new_c[p] = det[key]
            if all(x <= 1 for x in new_c):
                stays_in_01 += 1
            else:
                leaves_01 += 1
        elif key not in det:
            no_det_move += 1

print(f"Forced moves from bad {{0,1}}^9 configs:")
print(f"  Stay in {{0,1}}^9: {stays_in_01}")
print(f"  Leave {{0,1}}^9: {leaves_01}")
print(f"  Free (undetermined) entries: {no_det_move}")

# ============================================================
# Try Sol3 v1 completion and see what fails
# ============================================================

print("\n" + "="*70)
print("Sol3 v1 completion attempt at ms=(2,3,3,3,3,3,3,3,2)")
print("="*70)

from verifier import verify_system

def sol3_v1_rules(ms, n):
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f
    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f
    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f
    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n-1]))
    return fs

fs_v1 = sol3_v1_rules(list(ms), n)
result = verify_system(list(ms), fs_v1)
print(f"Sol3 v1: valid={result.get('valid')}")
if not result['valid']:
    for k, v in result.get('properties', {}).items():
        print(f"  {k}: {v}")

# Try other Sol3 variants
def sol3_v4_rules(ms, n):
    def make_bottom(m0, m1):
        def f(L, S, R):
            if m0 == 2:
                if S != R % 2:
                    return 1 - S
                return S
            else:
                if (S + 1) % 3 == R % 3:
                    return (S - 1) % 3
                return S
        return f
    def make_top(m_top, m_prev, m0):
        def f(L, S, R):
            if m_top == 2:
                if L % 2 == R % 2 and L % 2 != S:
                    return L % 2
                return S
            else:
                if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
                    return (L % 3 + 1) % 3
                return S
        return f
    def make_middle(m_i, m_prev, m_next):
        def f(L, S, R):
            if m_i == 2:
                if S != L % 2:
                    return L % 2
                if S != R % 2:
                    return R % 2
                return S
            else:
                if (S + 1) % 3 == L % 3:
                    return L % 3
                if (S + 1) % 3 == R % 3:
                    return R % 3
                return S
        return f
    fs = [make_bottom(ms[0], ms[1])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i], ms[i-1], ms[i+1]))
    fs.append(make_top(ms[n-1], ms[n-2], ms[0]))
    return fs

fs_v4 = sol3_v4_rules(list(ms), n)
result4 = verify_system(list(ms), fs_v4)
print(f"Sol3 v4: valid={result4.get('valid')}")
if not result4['valid']:
    for k, v in result4.get('properties', {}).items():
        print(f"  {k}: {v}")

# Try all rotations of the necklace (2,2,3,3,3,3,3,3,3)
print("\n--- All rotations of {2²,3⁷} with Sol3 v1 ---")
base_neck = (2,2,3,3,3,3,3,3,3)
tested = set()
for rot in range(n):
    ms_rot = tuple(base_neck[(i+rot)%n] for i in range(n))
    if ms_rot in tested:
        continue
    tested.add(ms_rot)

    fs = sol3_v1_rules(list(ms_rot), n)
    result = verify_system(list(ms_rot), fs)
    bin_pos = [i for i in range(n) if ms_rot[i] == 2]
    print(f"  {ms_rot} bins@{bin_pos}: valid={result.get('valid')}", end="")
    if result.get('valid'):
        print(f" cycle_len={result.get('cycle_length')}")
    else:
        props = result.get('properties', {})
        fail = next((f"{k}" for k, v in props.items()
                     if isinstance(v, tuple) and not v[0]), "?")
        print(f" FAIL at {fail}")

# ============================================================
# Deep analysis: what specifically causes convergence failure?
# ============================================================

print("\n" + "="*70)
print("Deep analysis: convergence failure mechanism at (2,3,3,3,3,3,3,3,2)")
print("="*70)

# Use Sol3 v1 rules and find the bad SCCs
if not result.get('valid'):
    # Build full transition graph for Sol3 v1
    fs = sol3_v1_rules(list(ms), n)

    # Find all privileged procs per config
    priv_map = {}
    for c in all_configs:
        priv = []
        for p in range(n):
            L = c[(p-1)%n]
            S = c[p]
            R = c[(p+1)%n]
            if fs[p](L, S, R) != S:
                priv.append(p)
        priv_map[c] = priv

    # Find good candidates (single-privilege, closed)
    single_priv = {c for c in all_configs if len(priv_map[c]) == 1}
    print(f"Single-privilege configs: {len(single_priv)}")

    # Check liveness
    dead = [c for c in all_configs if len(priv_map[c]) == 0]
    print(f"Dead configs: {len(dead)}")
    if dead:
        print("  First 5 dead configs:")
        for c in dead[:5]:
            print(f"    {''.join(str(x) for x in c)}")

    # Find closed subset
    succ_map = {}
    for c in single_priv:
        p = priv_map[c][0]
        new_c = list(c)
        new_c[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
        succ_map[c] = (tuple(new_c), p)

    closed = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in closed:
            s, _ = succ_map[c]
            if s not in closed:
                to_remove.add(c)
        if to_remove:
            closed -= to_remove
            changed = True

    print(f"Closed single-privilege configs: {len(closed)}")

    if closed:
        # Find cycles
        visited = set()
        cycles_found = []
        for c in closed:
            if c in visited:
                continue
            path = []
            node = c
            path_set = set()
            while node not in visited and node not in path_set:
                path.append(node)
                path_set.add(node)
                node = succ_map[node][0]
            if node in path_set:
                cycle_start = path.index(node)
                cyc = path[cycle_start:]
                cycles_found.append(cyc)
            visited.update(path)

        print(f"Cycles in closed set: {len(cycles_found)}")
        for i, cyc in enumerate(cycles_found[:5]):
            procs_in_cyc = set()
            for c in cyc:
                _, p = succ_map[c]
                procs_in_cyc.add(p)
            fair = procs_in_cyc == set(range(n))
            print(f"  Cycle {i}: len={len(cyc)}, procs={sorted(procs_in_cyc)}, fair={fair}")

        # Check convergence for each fair cycle
        for cyc in cycles_found:
            procs_in_cyc = set()
            for c in cyc:
                _, p = succ_map[c]
                procs_in_cyc.add(p)
            if procs_in_cyc != set(range(n)):
                continue

            cyc_set = set(cyc)
            # Build bad config graph
            bad = set(all_configs) - cyc_set
            bad_adj = defaultdict(list)
            for c in bad:
                for p in priv_map[c]:
                    new_c = list(c)
                    new_c[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                    new_c = tuple(new_c)
                    if new_c in bad:
                        bad_adj[c].append(new_c)

            # Find SCCs
            bad_sccs = find_sccs(dict(bad_adj))
            if bad_sccs:
                sizes = sorted([len(s) for s in bad_sccs], reverse=True)
                print(f"  Fair cycle len={len(cyc)}: {len(bad_sccs)} bad SCCs, "
                      f"sizes={sizes[:10]}")
                # Analyze largest SCC
                largest = max(bad_sccs, key=len)
                max_val = max(max(c) for c in largest)
                in_01 = sum(1 for c in largest if all(x <= 1 for x in c))
                print(f"    Largest SCC: {len(largest)} configs, max_val={max_val}, "
                      f"in {{0,1}}^9: {in_01}")
            else:
                print(f"  Fair cycle len={len(cyc)}: 0 bad SCCs — CONVERGES!")
