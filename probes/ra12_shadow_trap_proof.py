"""
Shadow Trap Proof — Research Agent 12
Goal: Prove that for sub-threshold product with >=3 binary, non-consecutive,
a sweep good cycle with isolated binary firings always has a ShadowTrap.

Strategy: Start from n=5 all-binary (simplest case), understand the mechanism,
then generalize.
"""

import itertools
from collections import defaultdict

def get_privileged(config, ms):
    """Return list of (proc, L, S, R) where proc is privileged (can fire)."""
    n = len(ms)
    result = []
    for p in range(n):
        L = config[(p - 1) % n]
        S = config[p]
        R = config[(p + 1) % n]
        result.append((p, L, S, R))
    return result

def build_good_cycle_sweep(n, ms):
    """Build a sweep good cycle for all-binary ring.
    For ms=(2,...,2), a sweep is: move right n times, then move left n times.
    """
    # For all-binary: start from (0,0,...,0)
    # Sweep right: proc 0,1,...,n-1 each fires once going right
    # Sweep left: proc n-1,n-2,...,0 each fires once going left

    configs = []
    movers = []

    # Start config
    cfg = [0] * n
    configs.append(tuple(cfg))

    # Right sweep: proc 0, 1, ..., n-1
    for p in range(n):
        movers.append(p)
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    # Left sweep: proc n-1, n-2, ..., 0
    for p in range(n - 1, -1, -1):
        movers.append(p)
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    # Check: should return to start
    if configs[-1] != configs[0]:
        return None, None, None
    configs = configs[:-1]  # remove duplicate end

    return configs, movers, ms

def extract_mover_table(configs, movers, ms):
    """Extract the mover context table from a good cycle."""
    n = len(ms)
    CL = len(configs)
    table = []
    for k in range(CL):
        p = movers[k]
        cfg = configs[k]
        L = cfg[(p - 1) % n]
        S = cfg[p]
        R = cfg[(p + 1) % n]
        next_cfg = configs[(k + 1) % CL]
        S_prime = next_cfg[p]
        table.append((p, L, S, R, S_prime))
    return table

def find_forced_proc(cfg, mover_table, ms):
    """Find a proc in cfg whose context matches a mover table entry.
    Returns (proc, successor_value, matching_step) or None.
    """
    n = len(ms)
    for step, (p, L, S, R, S_prime) in enumerate(mover_table):
        # Check if proc p in cfg has context (L, S, R)
        if cfg[(p - 1) % n] == L and cfg[p] == S and cfg[(p + 1) % n] == R:
            return (p, S_prime, step)
    return None

def follow_forced_orbit(start_cfg, mover_table, ms, max_steps=200):
    """Follow forced transitions from start_cfg."""
    n = len(ms)
    orbit = [start_cfg]
    current = start_cfg
    for _ in range(max_steps):
        forced = find_forced_proc(current, mover_table, ms)
        if forced is None:
            return orbit, "stuck"
        p, s_prime, step = forced
        new_cfg = list(current)
        new_cfg[p] = s_prime
        new_cfg = tuple(new_cfg)
        if new_cfg == start_cfg:
            return orbit, "cycle"
        if new_cfg in orbit:
            idx = orbit.index(new_cfg)
            return orbit, f"cycle_at_{idx}"
        orbit.append(new_cfg)
        current = new_cfg
    return orbit, "max_steps"

def analyze_forced_graph(configs, movers, ms):
    """Full analysis of forced graph structure."""
    n = len(ms)
    CL = len(configs)
    good_set = set(configs)
    mover_table = extract_mover_table(configs, movers, ms)

    print(f"\n=== n={n}, ms={ms}, CL={CL} ===")
    print(f"Good configs: {len(good_set)}")

    # Build context→step lookup
    context_map = {}  # (proc, L, S, R) -> (step, S')
    for step, (p, L, S, R, S_prime) in enumerate(mover_table):
        key = (p, L, S, R)
        if key in context_map:
            print(f"  WARNING: duplicate context at step {step}: {key}")
        context_map[key] = (step, S_prime)

    print(f"Unique mover contexts: {len(context_map)}")

    # Generate ALL non-good configs and build forced graph
    all_configs = list(itertools.product(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    print(f"Non-good configs: {len(non_good)}")

    # For each non-good config, find all forced procs
    forced_graph = {}  # cfg -> list of (proc, new_cfg, step)
    for cfg in non_good:
        forced = []
        for p in range(n):
            L = cfg[(p - 1) % n]
            S = cfg[p]
            R = cfg[(p + 1) % n]
            key = (p, L, S, R)
            if key in context_map:
                step, S_prime = context_map[key]
                new_cfg = list(cfg)
                new_cfg[p] = S_prime
                new_cfg = tuple(new_cfg)
                forced.append((p, new_cfg, step))
        forced_graph[cfg] = forced

    # Count forced procs per non-good config
    force_counts = [len(forced_graph[c]) for c in non_good]
    print(f"Forced proc counts: min={min(force_counts)}, max={max(force_counts)}, avg={sum(force_counts)/len(force_counts):.1f}")
    zero_forced = [c for c in non_good if len(forced_graph[c]) == 0]
    print(f"Configs with 0 forced procs: {len(zero_forced)}")

    return good_set, non_good, forced_graph, mover_table, context_map

def find_sccs(non_good, forced_graph):
    """Find SCCs in forced graph using Tarjan's."""
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

        for p, w, step in forced_graph.get(v, []):
            if w not in index:
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

    for v in non_good:
        if v not in index:
            strongconnect(v)

    return sccs

# ============================================================
# PART 1: Understand n=5 all-binary
# ============================================================
print("=" * 60)
print("PART 1: n=5 all-binary, ms=(2,2,2,2,2)")
print("=" * 60)

n = 5
ms = [2] * n
configs, movers, _ = build_good_cycle_sweep(n, ms)
print(f"Good cycle length: {len(configs)}")
print(f"Movers: {movers}")
print(f"Configs:")
for i, (cfg, m) in enumerate(zip(configs, movers)):
    print(f"  Step {i:2d}: {cfg} -> proc {m} fires")

mover_table = extract_mover_table(configs, movers, ms)
print(f"\nMover context table:")
for i, (p, L, S, R, Sp) in enumerate(mover_table):
    print(f"  Step {i:2d}: proc {p}, ctx=({L},{S},{R}) -> {Sp}")

good_set, non_good, forced_graph, mover_table, context_map = analyze_forced_graph(configs, movers, ms)

# Find SCCs
sccs = find_sccs(non_good, forced_graph)
nontrivial = [s for s in sccs if len(s) > 1]
print(f"\nSCCs: {len(sccs)} total, {len(nontrivial)} nontrivial")
for i, scc in enumerate(nontrivial):
    print(f"  SCC {i}: {len(scc)} configs")
    for c in sorted(scc)[:5]:
        print(f"    {c}")
    if len(scc) > 5:
        print(f"    ... ({len(scc)} total)")
