#!/usr/bin/env python3
"""clb_convergence_obstruction.py — Find the convergence obstruction for endpoint binary.

The bounce cycle at ms=(2,3,3,3,3,3,3,3,2) is overlap-free and has 0 forced SCCs.
But M_9 > 8748 so no valid system exists. What's the obstruction?

Strategy: Build the bounce cycle, then try RANDOM completions of free entries.
For each completion, check liveness and find bad SCCs. Classify the obstructions.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import random
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


n = 9
ms = (2, 3, 3, 3, 3, 3, 3, 3, 2)
up_down = list(range(n)) + list(range(n-2, 0, -1))
cycle, movers = build_bounce_cycle(ms, n, up_down)
good_set = set(cycle)

print(f"Bounce cycle: ms={ms}, product=8748, len={len(cycle)}")

# Extract determined entries
det = {}
for idx in range(len(cycle)):
    c = cycle[idx]
    c_next = cycle[(idx + 1) % len(cycle)]
    mover = movers[idx]
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        key = (p, L, S, R)
        if p == mover:
            det[key] = c_next[p]
        else:
            det[key] = S

# Identify free entries
free_entries = []
for p in range(n):
    m_L = ms[(p-1)%n]; m_S = ms[p]; m_R = ms[(p+1)%n]
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                key = (p, L, S, R)
                if key not in det:
                    free_entries.append(key)

print(f"Determined entries: {len(det)}")
print(f"Free entries: {len(free_entries)}")

# Pre-compute all configs
all_configs = list(cartesian(*(range(m) for m in ms)))
non_good = [c for c in all_configs if c not in good_set]
non_good_set = set(non_good)

# ============================================================
# Random completion search
# ============================================================

print("\n" + "="*70)
print("Random completion search (100 trials)")
print("="*70)

random.seed(42)
results = {'dead': 0, 'scc': 0, 'both': 0, 'valid': 0}
scc_sizes_all = []

for trial in range(100):
    # Random completion: for each free entry, choose output
    completion = dict(det)
    for key in free_entries:
        p, L, S, R = key
        # Choose random output
        choices = list(range(ms[p]))
        completion[key] = random.choice(choices)

    # Build transition functions
    def make_f(p_idx, comp):
        def f(L, S, R):
            key = (p_idx, L, S, R)
            return comp.get(key, S)
        return f

    fs = [make_f(p, completion) for p in range(n)]

    # Check liveness
    dead_count = 0
    for c in all_configs:
        has_priv = False
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            if fs[p](L, S, R) != S:
                has_priv = True
                break
        if not has_priv:
            dead_count += 1

    if dead_count > 0:
        results['dead'] += 1
        continue

    # Check for bad SCCs
    bad_adj = defaultdict(list)
    for c in non_good:
        priv = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            if fs[p](L, S, R) != S:
                priv.append(p)

        for p in priv:
            new_c = list(c)
            new_c[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            new_c = tuple(new_c)
            if new_c in non_good_set:
                bad_adj[c].append(new_c)

    sccs = find_sccs(dict(bad_adj))
    if sccs:
        sizes = sorted([len(s) for s in sccs], reverse=True)
        scc_sizes_all.append(sizes)
        results['scc'] += 1
    else:
        # Check mutual exclusion + fairness
        # ... actually if we got here with 0 dead and 0 SCCs, check if the good
        # cycle is indeed the good cycle of this system
        results['valid'] += 1
        print(f"  Trial {trial}: POTENTIAL VALID SYSTEM!")

print(f"\nResults: {results}")
if scc_sizes_all:
    # Statistics on SCCs
    min_sccs = min(len(s) for s in scc_sizes_all)
    max_sccs = max(len(s) for s in scc_sizes_all)
    avg_sccs = sum(len(s) for s in scc_sizes_all) / len(scc_sizes_all)
    largest_sizes = [s[0] for s in scc_sizes_all]
    print(f"SCC count: min={min_sccs}, max={max_sccs}, avg={avg_sccs:.1f}")
    print(f"Largest SCC: min={min(largest_sizes)}, max={max(largest_sizes)}, "
          f"avg={sum(largest_sizes)/len(largest_sizes):.0f}")

# ============================================================
# Smarter completion: maximize liveness first, then check convergence
# ============================================================

print("\n" + "="*70)
print("Smart completion: liveness-first strategy")
print("="*70)

# Strategy: for each free entry, set it to be privileged (f ≠ S) if possible
# This maximizes liveness at the cost of potentially creating SCCs.

completion_live = dict(det)
for key in free_entries:
    p, L, S, R = key
    # Make it privileged: choose output ≠ S
    choices = [v for v in range(ms[p]) if v != S]
    if choices:
        completion_live[key] = choices[0]  # deterministic: first non-S value
    else:
        completion_live[key] = S  # can't make privileged (shouldn't happen for m≥2)

fs_live = [make_f(p, completion_live) for p in range(n)]

# Check liveness
dead_count = 0
for c in all_configs:
    has_priv = False
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if fs_live[p](L, S, R) != S:
            has_priv = True
            break
    if not has_priv:
        dead_count += 1
print(f"Liveness-first: {dead_count} dead configs")

# Check SCCs
if dead_count == 0:
    bad_adj = defaultdict(list)
    for c in non_good:
        priv = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            if fs_live[p](L, S, R) != S:
                priv.append(p)
        for p in priv:
            new_c = list(c)
            new_c[p] = fs_live[p](c[(p-1)%n], c[p], c[(p+1)%n])
            new_c = tuple(new_c)
            if new_c in non_good_set:
                bad_adj[c].append(new_c)

    sccs = find_sccs(dict(bad_adj))
    print(f"Bad SCCs: {len(sccs)}")
    if sccs:
        sizes = sorted([len(s) for s in sccs], reverse=True)
        print(f"SCC sizes: {sizes[:20]}")
        total_in_sccs = sum(sizes)
        print(f"Total configs in SCCs: {total_in_sccs}")

        # Analyze SCC content
        for i, scc in enumerate(sccs[:3]):
            max_val = max(max(c) for c in scc)
            in_01 = sum(1 for c in scc if all(x <= 1 for x in c))
            # Check: what fraction of the SCC involves free entries?
            free_moves = 0
            det_moves = 0
            for c in scc:
                for p in range(n):
                    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                    key = (p, L, S, R)
                    if fs_live[p](L, S, R) != S:
                        if key in det:
                            det_moves += 1
                        else:
                            free_moves += 1
            print(f"  SCC[{i}]: size={len(scc)}, max_val={max_val}, "
                  f"in_01={in_01}, det_moves={det_moves}, free_moves={free_moves}")

# ============================================================
# Minimal liveness completion + convergence check
# ============================================================

print("\n" + "="*70)
print("Minimal liveness: only add privilege where needed")
print("="*70)

# Strategy: keep free entries as non-privileged (f = S) by default.
# Only make entries privileged where liveness requires it.

completion_min = dict(det)
for key in free_entries:
    p, L, S, R = key
    completion_min[key] = S  # non-privileged by default

fs_min = [make_f(p, completion_min) for p in range(n)]

# Find configs that are dead under minimal completion
dead_configs = []
for c in all_configs:
    has_priv = False
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if fs_min[p](L, S, R) != S:
            has_priv = True
            break
    if not has_priv:
        dead_configs.append(c)

print(f"Dead configs under minimal (all-non-privileged free): {len(dead_configs)}")
if dead_configs:
    in_01 = sum(1 for c in dead_configs if all(x <= 1 for x in c))
    print(f"  In {{0,1}}^9: {in_01}")
    print(f"  First 10:")
    for c in dead_configs[:10]:
        # What free entries could save this config?
        saviors = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            key = (p, L, S, R)
            if key not in det:  # free entry
                saviors.append(p)
        print(f"    {''.join(str(x) for x in c)}: saviors at P{saviors}")

# Check: how many dead configs share the SAME free entry as their only savior?
# If many share the same entry, making that entry privileged creates many
# new transitions, potentially forming SCCs.

savior_entry_count = defaultdict(int)
for c in dead_configs:
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        key = (p, L, S, R)
        if key not in det:
            savior_entry_count[key] += 1

print(f"\nMost popular savior entries:")
top_saviors = sorted(savior_entry_count.items(), key=lambda x: -x[1])[:15]
for key, count in top_saviors:
    p, L, S, R = key
    print(f"  P{p}({L},{S},{R}): saves {count} dead configs")

# ============================================================
# Analyze the STRUCTURE of dead configs
# ============================================================

print("\n" + "="*70)
print("Dead config structure analysis")
print("="*70)

# What states do the binary procs have at dead configs?
parity_count = defaultdict(int)
for c in dead_configs:
    parity_count[(c[0], c[8])] += 1

print("Binary state distribution in dead configs:")
for (b0, b8), count in sorted(parity_count.items()):
    print(f"  P0={b0}, P8={b8}: {count} dead configs")

# What about the middle ternary procs?
print("\nMiddle proc state distribution in dead configs:")
for p in range(1, 8):
    state_count = defaultdict(int)
    for c in dead_configs:
        state_count[c[p]] += 1
    print(f"  P{p}: {dict(state_count)}")

# Distribution of number of saviors per dead config
savior_count_dist = defaultdict(int)
for c in dead_configs:
    count = sum(1 for p in range(n)
                if (p, c[(p-1)%n], c[p], c[(p+1)%n]) not in det)
    savior_count_dist[count] += 1

print("\nSaviors per dead config:")
for k in sorted(savior_count_dist):
    print(f"  {k} saviors: {savior_count_dist[k]} configs")
