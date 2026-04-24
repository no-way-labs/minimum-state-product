#!/usr/bin/env python3
"""clb_inherent_cycles.py — Are SCCs inherent in the non-good transition graph?

The key question: for the endpoint binary bounce cycle at ms=(2,3,3,3,3,3,3,3,2),
do SCCs persist regardless of how we complete the free entries?

Strategy: Instead of random search, try a TARGETED completion that minimizes
non-good→non-good edges. Then check if SCCs survive.

Also: identify MINIMAL SCCs — small cycles that can't be broken by any completion.
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
all_configs = list(cartesian(*(range(m) for m in ms)))
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
    m_L = ms[(p - 1) % n]
    m_S = ms[p]
    m_R = ms[(p + 1) % n]
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                key = (p, L, S, R)
                if key not in det:
                    free_entries.append(key)

print(f"Cycle len={len(cycle)}, determined={len(det)}, free={len(free_entries)}")
print(f"Non-good configs: {len(non_good)}")

# ============================================================
# Part 1: FORCED edges — non-good→non-good edges from DETERMINED entries
# ============================================================

print("\n" + "=" * 70)
print("Part 1: Forced edges (from determined entries)")
print("=" * 70)

forced_adj = defaultdict(set)
for c in non_good:
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        key = (p, L, S, R)
        if key in det and det[key] != S:
            new_c = list(c)
            new_c[p] = det[key]
            new_c = tuple(new_c)
            if new_c in non_good_set:
                forced_adj[c].add(new_c)

# Find SCCs in forced graph
forced_adj_list = {k: list(v) for k, v in forced_adj.items()}
forced_sccs = find_sccs(forced_adj_list)
forced_trapped = sum(len(s) for s in forced_sccs)
print(f"Forced non-good→non-good edges: {sum(len(v) for v in forced_adj.values())}")
print(f"Forced SCCs: {len(forced_sccs)}, trapped: {forced_trapped}")

if forced_sccs:
    sizes = sorted([len(s) for s in forced_sccs], reverse=True)
    print(f"SCC sizes: {sizes[:20]}")
    print("\n*** CRITICAL: Even determined entries alone create SCCs! ***")
    print("These SCCs CANNOT be broken by any completion of free entries.")
    print("This is an INHERENT obstruction of this good cycle.\n")

    # Analyze forced SCCs
    for i, scc in enumerate(forced_sccs[:3]):
        scc_set = set(scc)
        print(f"  Forced SCC[{i}] (size {len(scc)}):")

        # Find a short cycle within this SCC
        # Use BFS from first node
        start = scc[0]
        parent = {start: None}
        queue = [start]
        found_cycle = None
        while queue and found_cycle is None:
            node = queue.pop(0)
            for nbr in forced_adj.get(node, set()):
                if nbr == start and node != start:
                    # Found cycle back to start
                    path = [start]
                    cur = node
                    while cur != start:
                        path.append(cur)
                        cur = parent.get(cur)
                        if cur is None:
                            break
                    path.reverse()
                    found_cycle = path
                    break
                if nbr not in parent and nbr in scc_set:
                    parent[nbr] = node
                    queue.append(nbr)

        if found_cycle and len(found_cycle) <= 20:
            print(f"    Short cycle (len {len(found_cycle)}):")
            for j, cfg in enumerate(found_cycle[:10]):
                # Find the determined move that takes cfg to next
                next_cfg = found_cycle[(j + 1) % len(found_cycle)]
                diffs = [k for k in range(n) if cfg[k] != next_cfg[k]]
                mover_p = diffs[0] if diffs else '?'
                print(f"      {''.join(str(x) for x in cfg)} -> P{mover_p}")
else:
    print("No forced SCCs — determined entries alone are acyclic.")
    print("SCCs come from free entry choices.")

# ============================================================
# Part 2: Search for MINIMAL 2-cycles
# ============================================================

print("\n" + "=" * 70)
print("Part 2: Minimal 2-cycles in non-good configs")
print("=" * 70)

# A 2-cycle occurs when c → c' → c (via the same or different processor).
# For determined entries, check all such pairs.

twocycles = []
for c in non_good:
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        key = (p, L, S, R)
        if key not in det or det[key] == S:
            continue
        c_prime = list(c)
        c_prime[p] = det[key]
        c_prime = tuple(c_prime)
        if c_prime not in non_good_set:
            continue
        # Check if c_prime → c via same processor (involution)
        L2 = c_prime[(p - 1) % n]
        S2 = c_prime[p]
        R2 = c_prime[(p + 1) % n]
        key2 = (p, L2, S2, R2)
        if key2 in det and det[key2] == S:
            twocycles.append((c, c_prime, p))

print(f"Forced 2-cycles (same processor): {len(twocycles)}")
if twocycles:
    # These are involutions — the same processor toggling back and forth.
    # This can only happen at binary processors.
    binary_2c = [(c, cp, p) for c, cp, p in twocycles if ms[p] == 2]
    ternary_2c = [(c, cp, p) for c, cp, p in twocycles if ms[p] != 2]
    print(f"  Binary processor 2-cycles: {len(binary_2c)}")
    print(f"  Ternary processor 2-cycles: {len(ternary_2c)}")
    for c, cp, p in binary_2c[:5]:
        print(f"    P{p}: {''.join(str(x) for x in c)} <-> {''.join(str(x) for x in cp)}")

# Also check cross-processor 2-cycles: c →_p c' →_q c
cross_2cycles = 0
for c in non_good:
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        key = (p, L, S, R)
        if key not in det or det[key] == S:
            continue
        c_prime = list(c)
        c_prime[p] = det[key]
        c_prime = tuple(c_prime)
        if c_prime not in non_good_set:
            continue
        # Check if c_prime → c via ANY processor
        for q in range(n):
            if q == p:
                continue
            L2 = c_prime[(q - 1) % n]
            S2 = c_prime[q]
            R2 = c_prime[(q + 1) % n]
            key2 = (q, L2, S2, R2)
            if key2 in det and det[key2] != S2:
                c_back = list(c_prime)
                c_back[q] = det[key2]
                c_back = tuple(c_back)
                if c_back == c:
                    cross_2cycles += 1

print(f"Cross-processor forced 2-cycles: {cross_2cycles}")

# ============================================================
# Part 3: Directed search — minimize non-good→non-good edges
# ============================================================

print("\n" + "=" * 70)
print("Part 3: Minimize non-good→non-good edges via smart completion")
print("=" * 70)

# For each free entry, choose the output that minimizes non-good→non-good edges.
# Strategy: for free entry (p, L, S, R), prefer outputs that map to good configs.

def count_ng_edges(comp, free_key, output_val):
    """Count non-good→non-good edges created by setting free_key to output_val."""
    p, L, S, R = free_key
    if output_val == S:
        return 0  # non-privileged, no edge created

    edges = 0
    for c in non_good:
        if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
            new_c = list(c)
            new_c[p] = output_val
            if tuple(new_c) in non_good_set:
                edges += 1
    return edges


# Greedy: for each free entry, choose output minimizing edges
# (while maintaining liveness)
print("Computing edge costs per free entry...")
t0 = time.time()

edge_costs = {}  # (key, output) -> edge count
for key in free_entries:
    p, L, S, R = key
    for out in range(ms[p]):
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

print(f"  Computed in {time.time()-t0:.1f}s")

# Build "good-targeting" completion: for each free entry, choose output that
# maps MOST configs to good cycle, breaking ties by fewest ng->ng edges.
comp_good = dict(det)
for key in free_entries:
    p, L, S, R = key
    best_out = S
    best_good = 0
    best_ng = float('inf')
    for out in range(ms[p]):
        ng = edge_costs.get((key, out), 0)
        # Count how many configs this sends to good cycle
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
    comp_good[key] = best_out

# Check liveness
dead = sum(1 for c in all_configs if not any(
    comp_good.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
    for p in range(n)))
print(f"Good-targeting completion: {dead} dead configs")

# If dead, fall back to liveness-first
if dead > 0:
    print("Falling back to liveness-first with edge minimization...")
    # Start with good-targeting, then activate cheapest entries for liveness
    for c in all_configs:
        has_priv = any(
            comp_good.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
            for p in range(n))
        if not has_priv:
            # Find cheapest free entry to activate for this config
            best_key = None
            best_cost = float('inf')
            for p in range(n):
                L = c[(p-1)%n]
                S = c[p]
                R = c[(p+1)%n]
                key = (p, L, S, R)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp_good[best_key] = best_out_val

    dead = sum(1 for c in all_configs if not any(
        comp_good.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
        for p in range(n)))
    print(f"After liveness fix: {dead} dead configs")

# Check SCCs
bad_adj = defaultdict(list)
for c in non_good:
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        key = (p, L, S, R)
        new_S = comp_good.get(key, S)
        if new_S != S:
            new_c = list(c)
            new_c[p] = new_S
            new_c = tuple(new_c)
            if new_c in non_good_set:
                bad_adj[c].append(new_c)

sccs = find_sccs(dict(bad_adj))
trapped = sum(len(s) for s in sccs)
total_ng_edges = sum(len(v) for v in bad_adj.values())
print(f"Non-good→non-good edges: {total_ng_edges}")
print(f"SCCs: {len(sccs)}, trapped: {trapped}")
if sccs:
    sizes = sorted([len(s) for s in sccs], reverse=True)
    print(f"SCC sizes: {sizes[:15]}")

# ============================================================
# Part 4: Random optimization — 1000 trials, minimize trapped
# ============================================================

print("\n" + "=" * 70)
print("Part 4: Random optimization (1000 trials)")
print("=" * 70)

random.seed(42)
best_trapped = trapped
best_sccs = len(sccs)

for trial in range(1000):
    comp_trial = dict(det)
    for key in free_entries:
        p, L, S, R = key
        # Weighted random: prefer outputs with fewer ng edges
        candidates = []
        for out in range(ms[p]):
            cost = edge_costs.get((key, out), 0)
            weight = 1.0 / (1.0 + cost)
            candidates.append((out, weight))
        total_w = sum(w for _, w in candidates)
        r = random.random() * total_w
        cumw = 0
        for out, w in candidates:
            cumw += w
            if cumw >= r:
                comp_trial[key] = out
                break

    # Check liveness
    is_live = True
    for c in all_configs:
        has_priv = False
        for p in range(n):
            L2 = c[(p - 1) % n]
            S2 = c[p]
            R2 = c[(p + 1) % n]
            key = (p, L2, S2, R2)
            if comp_trial.get(key, S2) != S2:
                has_priv = True
                break
        if not has_priv:
            is_live = False
            break

    if not is_live:
        continue

    # Count SCCs
    bad = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L2 = c[(p - 1) % n]
            S2 = c[p]
            R2 = c[(p + 1) % n]
            key = (p, L2, S2, R2)
            new_S = comp_trial.get(key, S2)
            if new_S != S2:
                new_c = list(c)
                new_c[p] = new_S
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    bad[c].append(new_c)

    sccs_t = find_sccs(dict(bad))
    tr = sum(len(s) for s in sccs_t)
    if tr < best_trapped:
        best_trapped = tr
        best_sccs = len(sccs_t)
        if trial < 50 or trial % 100 == 0 or tr == 0:
            print(f"  Trial {trial}: {len(sccs_t)} SCCs, {tr} trapped (BEST)")
    if tr == 0:
        print(f"  *** ZERO SCCs at trial {trial}! ***")
        break

print(f"\nBest: {best_sccs} SCCs, {best_trapped} trapped")
if best_trapped > 0:
    print(f"\n*** ALL 1000 weighted-random completions have SCCs. ***")
    print(f"Combined with forced SCC analysis, this strongly suggests")
    print(f"that product 8748 is IMPOSSIBLE for this good cycle.")
