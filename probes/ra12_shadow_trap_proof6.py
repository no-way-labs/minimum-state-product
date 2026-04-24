"""
Shadow Trap Proof — Part 6: Build and analyze shadow cycle from first principles.

Setup: n=7, ms=[2,2,2,3,3,3,3], CL=18.
Movers: [0,1,2,3,4,5,6, 6,5,4,3,2,1,0, 3,4,5,6]

Strategy:
1. Build the mover context table from the good cycle
2. Enumerate ALL non-good configs (feasible for small n)
3. Build the forced graph (non-good config -> successors via forced transitions)
4. Find ALL cycles in the forced graph
5. Analyze their structure to understand the mechanism
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

n = 7
ms = [2, 2, 2, 3, 3, 3, 3]
CL = sum(ms)

# Build good cycle
movers = list(range(7)) + list(range(6, -1, -1)) + [3, 4, 5, 6]
cfg = [0] * n
configs = [tuple(cfg)]
for p in movers:
    cfg = list(configs[-1])
    cfg[p] = (cfg[p] + 1) % ms[p]
    configs.append(tuple(cfg))
configs = configs[:-1]  # Remove duplicate end

assert len(configs) == CL
good_set = set(configs)
print(f"n={n}, ms={ms}, CL={CL}")
print(f"Distinct good configs: {len(good_set)}")

# Build mover context table
table = []
cmap = {}
for k in range(CL):
    p = movers[k]
    g = configs[k]
    L, S, R = get_context(g, p, n)
    Sp = configs[(k+1) % CL][p]
    table.append((p, L, S, R, Sp))
    key = (p, L, S, R)
    if key in cmap:
        print(f"  DUPLICATE CONTEXT at step {k}: {key} (prev at step {cmap[key][1]})")
    cmap[key] = (Sp, k)

print(f"Unique mover contexts: {len(cmap)}")
print(f"\nMover table:")
for k, (p, L, S, R, Sp) in enumerate(table):
    print(f"  Step {k:2d}: proc {p}, ({L},{S},{R})->{Sp}")

# Enumerate all configs
all_configs = list(itertools.product(*[range(m) for m in ms]))
non_good = [c for c in all_configs if c not in good_set]
print(f"\nTotal configs: {len(all_configs)}")
print(f"Non-good configs: {len(non_good)}")

# Build forced graph: for each non-good config, find all forced procs
# A proc p is forced if its context matches a mover table entry
forced_graph = {}  # cfg -> [(p, new_cfg, step)]
for c in non_good:
    forced = []
    for p in range(n):
        ctx = get_context(c, p, n)
        key = (p,) + ctx
        if key in cmap:
            Sp, step = cmap[key]
            new_cfg = list(c)
            new_cfg[p] = Sp
            forced.append((p, tuple(new_cfg), step))
    forced_graph[c] = forced

# Statistics
force_counts = defaultdict(int)
for c in non_good:
    force_counts[len(forced_graph[c])] += 1
print(f"\nForced proc count distribution:")
for cnt, num in sorted(force_counts.items()):
    print(f"  {cnt} forced procs: {num} configs")

# Find SCCs using Tarjan's
def tarjan_sccs(nodes, graph):
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        for p, w, step in graph.get(v, []):
            if w in good_set:
                continue  # Skip transitions to good configs
            if w not in index:
                if w in set(nodes):
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in nodes:
        if v not in index:
            strongconnect(v)

    return sccs

sccs = tarjan_sccs(non_good, forced_graph)
nontrivial = [s for s in sccs if len(s) > 1]
print(f"\nSCCs in forced graph:")
print(f"  Total: {len(sccs)}")
print(f"  Nontrivial (size > 1): {len(nontrivial)}")
for i, scc in enumerate(nontrivial):
    print(f"  SCC {i}: size {len(scc)}")

# Also find simple cycles: follow forced transitions with a specific
# scheduler (lowest proc index, then lowest step) and see if we get cycles
print("\n=== Finding cycles via orbit following ===")
visited = set()
cycles_found = []

for start in non_good:
    if start in visited:
        continue

    orbit = [start]
    orbit_set = {start}
    current = start

    while True:
        forced = forced_graph.get(current, [])
        # Filter out transitions to good configs
        forced = [(p, nc, s) for p, nc, s in forced if nc not in good_set]
        if not forced:
            break

        # Deterministic: pick lowest proc, then lowest step
        forced.sort(key=lambda x: (x[0], x[2]))
        p, next_cfg, step = forced[0]

        if next_cfg == start:
            # Found a cycle!
            cycles_found.append(list(orbit))
            for c in orbit:
                visited.add(c)
            break
        elif next_cfg in orbit_set:
            # Found a cycle, but not back to start
            idx = orbit.index(next_cfg)
            cycle = orbit[idx:]
            cycles_found.append(cycle)
            for c in cycle:
                visited.add(c)
            break
        else:
            orbit.append(next_cfg)
            orbit_set.add(next_cfg)
            current = next_cfg

print(f"Cycles found: {len(cycles_found)}")
for i, cycle in enumerate(cycles_found[:10]):
    print(f"  Cycle {i}: length {len(cycle)}")

# THE KEY ANALYSIS: For each nontrivial SCC, extract a cycle and
# analyze its relationship to the good cycle.
print("\n=== Detailed cycle analysis ===")
if nontrivial:
    scc = nontrivial[0]
    scc_set = set(scc)
    print(f"Analyzing SCC of size {len(scc)}")

    # Find a cycle within this SCC
    start = scc[0]
    orbit = [start]
    current = start
    for _ in range(len(scc) + 10):
        forced = forced_graph.get(current, [])
        forced = [(p, nc, s) for p, nc, s in forced if nc in scc_set]
        if not forced:
            print(f"  Dead end at {current}")
            break
        # Pick lowest proc
        forced.sort()
        p, next_cfg, step = forced[0]
        if next_cfg == start and len(orbit) > 1:
            print(f"  Found cycle of length {len(orbit)}")
            break
        orbit.append(next_cfg)
        current = next_cfg

    # Analyze: at each step, which proc fires and which good-cycle step is matched?
    print(f"\n  Step-by-step cycle analysis:")
    for k in range(min(len(orbit), CL + 2)):
        c = orbit[k % len(orbit)]
        forced = [(p, nc, s) for p, nc, s in forced_graph[c] if nc in scc_set]
        forced.sort()
        if forced:
            p, nc, step = forced[0]
            # Hamming distance to closest good config
            min_dist = min(sum(1 for a, b in zip(c, g) if a != b) for g in configs)
            print(f"  k={k:2d}: {c} -> fire proc {p} (matches good step {step}), Hamming={min_dist}")

    # KEY: What's the mover SEQUENCE in the cycle?
    print(f"\n  Mover sequence in the cycle:")
    cycle_movers = []
    cycle_steps = []
    for k in range(len(orbit)):
        c = orbit[k]
        forced = [(p, nc, s) for p, nc, s in forced_graph[c] if nc in scc_set]
        forced.sort()
        if forced:
            p, nc, step = forced[0]
            cycle_movers.append(p)
            cycle_steps.append(step)

    print(f"  Good cycle movers:  {movers}")
    print(f"  Shadow cycle movers: {cycle_movers}")
    print(f"  Good steps matched:  {cycle_steps}")

    # Is cycle_steps a permutation of range(CL)?
    if sorted(cycle_steps) == list(range(CL)):
        print(f"  *** PERMUTATION! Each good step matched exactly once! ***")
        # What's the permutation?
        perm = cycle_steps
        print(f"  σ: shadow step k -> good step σ(k) = {perm}")
    else:
        print(f"  Not a permutation. Step counts: {defaultdict(int, {s: cycle_steps.count(s) for s in set(cycle_steps)})}")
