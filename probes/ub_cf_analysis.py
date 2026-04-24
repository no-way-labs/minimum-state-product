#!/usr/bin/env python3
"""
CUP-2 CF boundary transition analysis for n=9.
Uses the ACTUAL 5-table CUP-2 system from cup2_final_verify.py.

Analyzes constant-FutureFc 6-tuple transitions for Lean convergence proof.
"""

import itertools
from collections import defaultdict, deque
import sys

N = 9
MS = [2, 3, 3, 3, 3, 3, 3, 3, 2]

# ================================================================
# THE 5 UNIVERSAL LOOKUP TABLES (from cup2_final_verify.py)
# ================================================================

# T_bot: P0, bottom binary (m_L=2, m_S=2, m_R=3)
T_bot = {
    (0,0,0): 1, (0,0,1): 1, (0,0,2): 0,
    (0,1,0): 1, (0,1,1): 1, (0,1,2): 1,
    (1,0,0): 0, (1,0,1): 1, (1,0,2): 0,
    (1,1,0): 0, (1,1,1): 1, (1,1,2): 0,
}

# T_low: P1, lower boundary ternary (m_L=2, m_S=3, m_R=3)
T_low = {
    (0,0,0): 0, (0,0,1): 0, (0,0,2): 0,
    (0,1,0): 0, (0,1,1): 1, (0,1,2): 0,
    (0,2,0): 0, (0,2,1): 2, (0,2,2): 0,
    (1,0,0): 1, (1,0,1): 1, (1,0,2): 1,
    (1,1,0): 1, (1,1,1): 1, (1,1,2): 2,
    (1,2,0): 0, (1,2,1): 1, (1,2,2): 2,
}

# T_mid: interior ternary (m_L=3, m_S=3, m_R=3)
T_mid = {
    (0,0,0): 0, (0,0,1): 0, (0,0,2): 0,
    (0,1,0): 0, (0,1,1): 1, (0,1,2): 0,
    (0,2,0): 0, (0,2,1): 2, (0,2,2): 0,
    (1,0,0): 1, (1,0,1): 1, (1,0,2): 1,
    (1,1,0): 1, (1,1,1): 1, (1,1,2): 2,
    (1,2,0): 0, (1,2,1): 1, (1,2,2): 2,
    (2,0,0): 0, (2,0,1): 0, (2,0,2): 2,
    (2,1,0): 1, (2,1,1): 0, (2,1,2): 2,
    (2,2,0): 0, (2,2,1): 2, (2,2,2): 2,
}

# T_high: P_{n-2}, upper boundary ternary (m_L=3, m_S=3, m_R=2)
T_high = {
    (0,0,0): 0, (0,0,1): 0,
    (0,1,0): 0, (0,1,1): 0,
    (0,2,0): 0, (0,2,1): 0,
    (1,0,0): 1, (1,0,1): 1,
    (1,1,0): 1, (1,1,1): 2,
    (1,2,0): 0, (1,2,1): 2,
    (2,0,0): 0, (2,0,1): 2,
    (2,1,0): 0, (2,1,1): 2,
    (2,2,0): 2, (2,2,1): 2,
}

# T_top: P_{n-1}, top binary (m_L=3, m_S=2, m_R=2)
# Note: R = c[0] (ring wraps), m_R = m_0 = 2
T_top = {
    (0,0,0): 0, (0,0,1): 0,
    (0,1,0): 0, (0,1,1): 0,
    (1,0,0): 0, (1,0,1): 1,
    (1,1,0): 1, (1,1,1): 1,
    (2,0,0): 1, (2,0,1): 1,
    (2,1,0): 1, (2,1,1): 1,
}

def get_table(j):
    if j == 0:
        return T_bot
    elif j == 1:
        return T_low
    elif j == N - 2:
        return T_high
    elif j == N - 1:
        return T_top
    else:
        return T_mid

def output(c, j):
    """Transition output for processor j at config c."""
    L = c[(j - 1) % N]
    S = c[j]
    R = c[(j + 1) % N]
    return get_table(j)[(L, S, R)]

def frontier_bit(c, j):
    return 1 if output(c, j) == c[j] else 0

def fc(c):
    return sum(frontier_bit(c, j) for j in range(N))

def privileged(c):
    return [j for j in range(N) if output(c, j) != c[j]]

def fire(c, j):
    c2 = list(c)
    c2[j] = output(c, j)
    return tuple(c2)

def sixtuple(c):
    """6-tuple: (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])"""
    return (c[0], c[1], c[2], c[N-3], c[N-2], c[N-1])

# ---- Step 1: Enumerate all configs ----
print("=" * 70)
print(f"CUP-2 CF Boundary Transition Analysis, n={N}")
print(f"ms={MS}, product={eval('*'.join(map(str, MS)))}")
print("=" * 70)

all_configs = list(itertools.product(*[range(m) for m in MS]))
print(f"\nTotal configs: {len(all_configs)}")

# ---- Step 2: Find good cycle ----
# Good configs have exactly 1 privileged processor.
# Find the closed subset of single-priv configs under deterministic daemon.
single_priv = []
for c in all_configs:
    priv = privileged(c)
    if len(priv) == 1:
        single_priv.append(c)

print(f"Single-privilege configs: {len(single_priv)}")

# Build successor map
succ = {}
for c in single_priv:
    j = privileged(c)[0]
    c2 = fire(c, j)
    succ[c] = c2

# Find closed subset
sp_set = set(single_priv)
good_candidates = set(single_priv)
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in good_candidates:
        if succ[c] not in good_candidates:
            to_remove.add(c)
    if to_remove:
        good_candidates -= to_remove
        changed = True

print(f"Good candidates (closed subset): {len(good_candidates)}")

# Find cycles
visited = set()
cycles = []
for c in sorted(good_candidates):
    if c in visited:
        continue
    path = []
    path_set = set()
    node = c
    while node not in visited and node not in path_set:
        path.append(node)
        path_set.add(node)
        node = succ[node]
    if node in path_set:
        idx = path.index(node)
        cycle = path[idx:]
        cycles.append(cycle)
        visited.update(path)
    else:
        visited.update(path)

print(f"Found {len(cycles)} cycle(s), lengths: {[len(c) for c in cycles]}")

# Use the good set = cycle + tails
target_len = 3 * N - 2
good_cycle = None
for cyc in cycles:
    if len(cyc) == target_len:
        good_cycle = cyc
        break
if good_cycle is None and cycles:
    good_cycle = max(cycles, key=len)

# Full good set = good_candidates (cycle + tails)
good_set = good_candidates
print(f"Good cycle length: {len(good_cycle) if good_cycle else 0}")
print(f"Expected: {target_len}")
print(f"Full good set: {len(good_set)}")

# Verify
if good_cycle:
    fc_vals = set()
    for gc in good_cycle:
        fc_vals.add(fc(gc))
    print(f"Good cycle fc values: {fc_vals}")

# ---- Step 3: Build bad step forward graph ----
bad_configs = [c for c in all_configs if c not in good_set]
bad_set = set(bad_configs)
print(f"\nBad configs: {len(bad_configs)}")

# Build graph: for each bad config, fire each privileged proc
bad_graph = defaultdict(list)
bad_graph_rev = defaultdict(list)
edges_to_good = defaultdict(list)  # bad -> list of (j, good_config)

for c in bad_configs:
    for j in privileged(c):
        c2 = fire(c, j)
        if c2 in good_set:
            edges_to_good[c].append((j, c2))
        elif c2 in bad_set:
            bad_graph[c].append((j, c2))
            bad_graph_rev[c2].append(c)

# Check reachability to good
can_reach_good = set()
for c in bad_configs:
    if edges_to_good[c]:
        can_reach_good.add(c)

queue = deque(can_reach_good)
while queue:
    c = queue.popleft()
    for pred in bad_graph_rev[c]:
        if pred not in can_reach_good:
            can_reach_good.add(pred)
            queue.append(pred)

print(f"Bad configs that can reach good: {len(can_reach_good)}")
unreachable = len(bad_configs) - len(can_reach_good)
print(f"Bad configs that CANNOT reach good: {unreachable}")

if unreachable > 0:
    # Check if unreachable configs are deadlocks or in other cycles
    # This would mean system is not self-stabilizing with this good set
    # Try expanding good set to include ALL closed single-priv configs
    deadlocks = [c for c in bad_configs if c not in can_reach_good and not privileged(c)]
    multi_priv_unreachable = [c for c in bad_configs if c not in can_reach_good and privileged(c)]
    print(f"  Deadlocks among unreachable: {len(deadlocks)}")
    print(f"  Multi-priv unreachable: {len(multi_priv_unreachable)}")
    if deadlocks:
        for c in deadlocks[:5]:
            print(f"    Deadlock: {c}, fc={fc(c)}")
    # Dead configs are OK - they are fixed points (fc=N, all at target)
    # Remove them from "bad" - they're actually legitimate fixed points
    fixed_points = [c for c in deadlocks if fc(c) == N]
    print(f"  Fixed points (fc=N): {len(fixed_points)}")

    # Add fixed points to good set
    good_set = good_set | set(fixed_points)
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)
    print(f"\n  After adding fixed points: good={len(good_set)}, bad={len(bad_configs)}")

    # Rebuild graph
    bad_graph = defaultdict(list)
    bad_graph_rev = defaultdict(list)
    edges_to_good = defaultdict(list)

    for c in bad_configs:
        for j in privileged(c):
            c2 = fire(c, j)
            if c2 in good_set:
                edges_to_good[c].append((j, c2))
            elif c2 in bad_set:
                bad_graph[c].append((j, c2))
                bad_graph_rev[c2].append(c)

    can_reach_good = set()
    for c in bad_configs:
        if edges_to_good[c]:
            can_reach_good.add(c)

    queue = deque(can_reach_good)
    while queue:
        c = queue.popleft()
        for pred in bad_graph_rev[c]:
            if pred not in can_reach_good:
                can_reach_good.add(pred)
                queue.append(pred)

    print(f"  Now reachable: {len(can_reach_good)}/{len(bad_configs)}")
    still_unreachable = len(bad_configs) - len(can_reach_good)
    if still_unreachable > 0:
        print(f"  Still unreachable: {still_unreachable}")
        # Show some
        for c in bad_configs[:5]:
            if c not in can_reach_good:
                print(f"    {c}, fc={fc(c)}, priv={privileged(c)}")

# Precompute fc
fc_cache = {}
for c in bad_configs:
    fc_cache[c] = fc(c)

# ---- Step 4: Compute FutureFc ----
# FutureFc(c) = max fc reachable from c staying within bad configs
# Use Bellman-Ford style
future_fc = {c: fc_cache[c] for c in bad_configs}
changed = True
iterations = 0
while changed:
    changed = False
    iterations += 1
    for c in bad_configs:
        for (j, c2) in bad_graph[c]:
            if future_fc[c2] > future_fc[c]:
                future_fc[c] = future_fc[c2]
                changed = True
    if iterations > 20:
        print(f"  Warning: Bellman-Ford not converged after {iterations} iterations")
        break

print(f"\nFutureFc computation: {iterations} iterations")
ff_dist = defaultdict(int)
for c in bad_configs:
    ff_dist[future_fc[c]] += 1
print(f"FutureFc distribution: {dict(sorted(ff_dist.items()))}")

# ---- Step 5: CF boundary transitions ----
BOUNDARY = [0, 1, 2, N-3, N-2, N-1]  # positions 0,1,2,6,7,8
INTERIOR = [j for j in range(N) if j not in BOUNDARY]
print(f"\nBoundary positions: {BOUNDARY}")
print(f"Interior positions: {INTERIOR}")

cf_boundary_transitions = []
cf_6tuple_edges = set()
fc_change_stats = defaultdict(int)

for c in bad_configs:
    if c not in future_fc:
        continue
    ff_c = future_fc[c]
    for j in BOUNDARY:
        if output(c, j) == c[j]:
            continue
        c2 = fire(c, j)
        if c2 in good_set:
            continue
        if c2 not in future_fc:
            continue
        ff_c2 = future_fc[c2]
        st_before = sixtuple(c)
        st_after = sixtuple(c2)
        if st_before == st_after:
            continue
        if ff_c == ff_c2:
            fc_c = fc_cache[c]
            fc_c2 = fc_cache[c2]
            cf_boundary_transitions.append((c, j, c2, fc_c, fc_c2, ff_c))
            cf_6tuple_edges.add((st_before, st_after))
            fc_change_stats[(fc_c, fc_c2)] += 1

print(f"\nCF boundary transitions (config-level): {len(cf_boundary_transitions)}")
print(f"CF 6-tuple edges: {len(cf_6tuple_edges)}")
print(f"\nfc change stats (fc_before -> fc_after): count")
for k in sorted(fc_change_stats.keys()):
    print(f"  {k[0]} -> {k[1]}: {fc_change_stats[k]}")

# ---- Step 6: Project to 6-tuple level ----
all_6tuples = set()
for (st1, st2) in cf_6tuple_edges:
    all_6tuples.add(st1)
    all_6tuples.add(st2)
print(f"\nDistinct 6-tuples in CF edges: {len(all_6tuples)}")

# ---- Step 7: DAG check ----
adj = defaultdict(set)
for (st1, st2) in cf_6tuple_edges:
    adj[st1].add(st2)

def iterative_dag_check(nodes, adj_list):
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {n: WHITE for n in nodes}
    topo = []
    is_dag = True

    for start in nodes:
        if color[start] != WHITE:
            continue
        stack = [(start, False)]
        while stack:
            node, processed = stack.pop()
            if processed:
                color[node] = BLACK
                topo.append(node)
                continue
            if color[node] == BLACK:
                continue
            if color[node] == GRAY:
                color[node] = BLACK
                topo.append(node)
                continue
            color[node] = GRAY
            stack.append((node, True))
            for v in adj_list.get(node, []):
                if v not in color:
                    color[v] = WHITE
                if color[v] == GRAY:
                    is_dag = False
                elif color[v] == WHITE:
                    stack.append((v, False))

    return is_dag, list(reversed(topo))

def compute_dag_rank(topo, adj_list):
    rank = {}
    for st in reversed(topo):
        r = 0
        for v in adj_list.get(st, []):
            if v in rank:
                r = max(r, rank[v] + 1)
        rank[st] = r
    return rank

full_is_dag, full_topo = iterative_dag_check(all_6tuples, adj)
print(f"\nFull CF 6-tuple graph is DAG: {full_is_dag}")

if full_is_dag:
    full_rank = compute_dag_rank(full_topo, adj)
    max_rank = max(full_rank.values()) if full_rank else 0
    print(f"DAG rank (longest path): {max_rank}")
else:
    # Find SCCs
    print("CF graph has cycles. Finding SCCs...")

    # Iterative Tarjan
    def tarjan_iterative(nodes, adj_list):
        idx = [0]
        stack = []
        on_stack = set()
        index_map = {}
        lowlink_map = {}
        sccs = []

        for start in nodes:
            if start in index_map:
                continue
            call_stack = [(start, iter(adj_list.get(start, [])), False)]
            index_map[start] = lowlink_map[start] = idx[0]
            idx[0] += 1
            stack.append(start)
            on_stack.add(start)

            while call_stack:
                v, neighbors, returned = call_stack[-1]
                try:
                    w = next(neighbors)
                    if w not in index_map:
                        index_map[w] = lowlink_map[w] = idx[0]
                        idx[0] += 1
                        stack.append(w)
                        on_stack.add(w)
                        call_stack.append((w, iter(adj_list.get(w, [])), False))
                    elif w in on_stack:
                        lowlink_map[v] = min(lowlink_map[v], index_map[w])
                except StopIteration:
                    call_stack.pop()
                    if call_stack:
                        parent = call_stack[-1][0]
                        lowlink_map[parent] = min(lowlink_map[parent], lowlink_map[v])
                    if lowlink_map[v] == index_map[v]:
                        scc = []
                        while True:
                            w = stack.pop()
                            on_stack.discard(w)
                            scc.append(w)
                            if w == v:
                                break
                        sccs.append(scc)
        return sccs

    sccs = tarjan_iterative(all_6tuples, adj)
    nontrivial = [s for s in sccs if len(s) > 1 or (len(s) == 1 and s[0] in adj.get(s[0], set()))]
    print(f"Total SCCs: {len(sccs)}, nontrivial: {len(nontrivial)}")
    for i, scc in enumerate(nontrivial[:5]):
        print(f"  SCC {i}: size={len(scc)}, sample: {scc[0]}")

# ---- Step 8: FC-nondecreasing subgraph ----
print("\n" + "=" * 70)
print("Step 8: FC-nondecreasing analysis")
print("=" * 70)

# Collect fc changes per 6-tuple edge
edge_fc_changes = defaultdict(set)
for (c, j, c2, fc_c, fc_c2, ff) in cf_boundary_transitions:
    st1 = sixtuple(c)
    st2 = sixtuple(c2)
    edge_fc_changes[(st1, st2)].add((fc_c, fc_c2))

# Classify edges
always_nondec = set()
has_decrease = set()
for edge, changes in edge_fc_changes.items():
    if all(fc2 >= fc1 for fc1, fc2 in changes):
        always_nondec.add(edge)
    else:
        has_decrease.add(edge)

print(f"Always fc-nondecreasing edges: {len(always_nondec)}")
print(f"Has fc-decrease edges: {len(has_decrease)}")

# fc-nondecreasing subgraph DAG check
nondec_nodes = set()
nondec_adj = defaultdict(set)
for (st1, st2) in always_nondec:
    nondec_nodes.add(st1)
    nondec_nodes.add(st2)
    nondec_adj[st1].add(st2)

nondec_dag, nondec_topo = iterative_dag_check(nondec_nodes, nondec_adj)
print(f"FC-nondecreasing subgraph is DAG: {nondec_dag}")

if nondec_dag:
    nondec_rank = compute_dag_rank(nondec_topo, nondec_adj)
    nondec_max = max(nondec_rank.values()) if nondec_rank else 0
    print(f"FC-nondecreasing DAG rank: {nondec_max}")

# ---- Detailed analysis of fc-decreasing CF edges ----
print("\n--- FC-decreasing CF boundary transitions ---")
fc_dec_detail = defaultdict(list)
for (c, j, c2, fc_c, fc_c2, ff) in cf_boundary_transitions:
    if fc_c2 < fc_c:
        st1 = sixtuple(c)
        st2 = sixtuple(c2)
        fc_dec_detail[(st1, st2)].append((fc_c, fc_c2, ff, j))

print(f"FC-decreasing 6-tuple edges: {len(fc_dec_detail)}")
for edge, details in sorted(fc_dec_detail.items(), key=lambda x: x[0])[:20]:
    ffs = set(d[2] for d in details)
    fc_pairs = set((d[0], d[1]) for d in details)
    procs = set(d[3] for d in details)
    print(f"  {edge[0]} -> {edge[1]}: procs={procs}, fc_changes={fc_pairs}, ff={ffs}")

# ---- Step 9: Combined measure check ----
print("\n" + "=" * 70)
print("Step 9: Combined measure M = (FutureFc - fc) * K + fcNondecRank")
print("=" * 70)

# Strategy: M(c) = (future_fc(c) - fc(c)) * K + rank(sixtuple(c))
# For CF transition (ff same), delta_M = -(fc2-fc1)*K + (rank2-rank1)
# Need delta_M < 0 for strict decrease.
# Case 1: fc increases (fc2>fc1) => delta(ff-fc) < 0 => need K large enough
# Case 2: fc same => need rank2 < rank1 (DAG gives this for nondec subgraph)
# Case 3: fc decreases => delta(ff-fc) > 0 => PROBLEM unless rank decreases enough

# First check: ALL boundary transitions (not just CF)
print("\n--- All boundary transitions (any FutureFc change) ---")
all_bdy = []
for c in bad_configs:
    if c not in future_fc:
        continue
    ff_c = future_fc[c]
    for j in BOUNDARY:
        if output(c, j) == c[j]:
            continue
        c2 = fire(c, j)
        if c2 in good_set:
            continue
        if c2 not in future_fc:
            continue
        ff_c2 = future_fc[c2]
        fc_c = fc_cache[c]
        fc_c2 = fc_cache[c2]
        all_bdy.append((c, j, c2, ff_c, ff_c2, fc_c, fc_c2))

ff_inc = sum(1 for t in all_bdy if t[4] > t[3])
ff_dec = sum(1 for t in all_bdy if t[4] < t[3])
ff_same = sum(1 for t in all_bdy if t[4] == t[3])
print(f"Total boundary bad->bad transitions: {len(all_bdy)}")
print(f"FutureFc: increase={ff_inc}, same={ff_same}, decrease={ff_dec}")

if ff_inc > 0:
    print("  WARNING: FutureFc can INCREASE on boundary transitions!")
    for t in [x for x in all_bdy if x[4] > x[3]][:5]:
        print(f"    P{t[1]}: ff {t[3]}->{t[4]}, fc {t[5]}->{t[6]}, 6t: {sixtuple(t[0])}->{sixtuple(t[2])}")

# For CF transitions, analyze gap = ff - fc
print("\n--- CF boundary: gap = FutureFc - fc ---")
cf_gap_inc = sum(1 for t in all_bdy if t[4] == t[3] and (t[4]-t[6]) > (t[3]-t[5]))
cf_gap_dec = sum(1 for t in all_bdy if t[4] == t[3] and (t[4]-t[6]) < (t[3]-t[5]))
cf_gap_same = sum(1 for t in all_bdy if t[4] == t[3] and (t[4]-t[6]) == (t[3]-t[5]))
# Note: ff same => gap change = -(fc2-fc1)
# gap inc means fc dec, gap dec means fc inc, gap same means fc same
print(f"CF boundary: gap_increase(fc_dec)={cf_gap_inc}, gap_same(fc_same)={cf_gap_same}, gap_dec(fc_inc)={cf_gap_dec}")

# Gap-same CF edges (fc same, ff same) with 6-tuple change
gap_same_edges = set()
for t in all_bdy:
    if t[4] == t[3] and t[6] == t[5]:  # ff same AND fc same
        st1 = sixtuple(t[0])
        st2 = sixtuple(t[2])
        if st1 != st2:
            gap_same_edges.add((st1, st2))

gap_same_nodes = set()
gap_same_adj = defaultdict(set)
for (s1, s2) in gap_same_edges:
    gap_same_nodes.add(s1)
    gap_same_nodes.add(s2)
    gap_same_adj[s1].add(s2)

gs_dag, gs_topo = iterative_dag_check(gap_same_nodes, gap_same_adj)
print(f"\nGap-same (fc same + ff same) 6-tuple edges: {len(gap_same_edges)}")
print(f"Gap-same 6-tuple graph is DAG: {gs_dag}")
if gs_dag:
    gs_rank = compute_dag_rank(gs_topo, gap_same_adj)
    gs_max = max(gs_rank.values()) if gs_rank else 0
    print(f"Gap-same DAG rank: {gs_max}")

# ---- Check measure viability ----
print("\n" + "=" * 70)
print("MEASURE VIABILITY CHECK")
print("=" * 70)

if ff_inc == 0:
    print("[OK] FutureFc is nonincreasing on all boundary transitions")
else:
    print("[FAIL] FutureFc can increase")

if cf_gap_inc == 0:
    print("[OK] Within CF: fc is nondecreasing (gap nonincreasing)")
    if gs_dag:
        print(f"[OK] Within CF + gap-same: 6-tuple is DAG with rank {gs_max}")
        K = gs_max + 1
        print(f"\n*** THREE-LEVEL MEASURE WORKS ***")
        print(f"  Level 1: FutureFc (nonincreasing)")
        print(f"  Level 2: gap = FutureFc - fc (nonincreasing within CF)")
        print(f"  Level 3: 6-tuple DAG rank (decreasing within gap-same)")
        print(f"  Combined: M = ff*(N*K) + (ff-fc)*K + rank")
        print(f"  K = {K}, N = {N}")
    else:
        print("[FAIL] Gap-same 6-tuple graph has cycles")
else:
    print(f"[INFO] Within CF: fc can DECREASE ({cf_gap_inc} transitions)")

    # Check if nondec subgraph DAG handles it
    if nondec_dag:
        print(f"[OK] FC-nondecreasing subgraph is DAG (rank {nondec_max})")

        # For fc-decreasing transitions, check if rank decreases enough
        # M = (ff-fc)*K + rank. For CF: delta_M = -(delta_fc)*K + delta_rank
        # fc dec (delta_fc < 0) => -(delta_fc)*K > 0 => need delta_rank < 0 and |delta_rank| > |delta_fc|*K
        # This is IMPOSSIBLE for any K > rank... so we need a different approach.

        # Alternative: M = ff * K1 + rank, where rank is over the FULL CF graph
        # (if it were DAG). For fc-dec, ff stays same, rank must decrease.
        # But if CF graph has cycles, this doesn't work.

        # Alternative: lex (ff, rank_within_ff_level)
        # Check: per-ff-level DAG
        print("\n  Per-FutureFc level analysis:")
        for ff_val in sorted(set(future_fc[c] for c in bad_configs)):
            level_configs = [c for c in bad_configs if future_fc[c] == ff_val]
            level_edges = set()
            level_adj = defaultdict(set)
            level_nodes = set()
            for c in level_configs:
                for j in BOUNDARY:
                    if output(c, j) == c[j]:
                        continue
                    c2 = fire(c, j)
                    if c2 in good_set or c2 not in future_fc:
                        continue
                    if future_fc[c2] != ff_val:
                        continue
                    st1 = sixtuple(c)
                    st2 = sixtuple(c2)
                    if st1 != st2:
                        level_edges.add((st1, st2))
                        level_adj[st1].add(st2)
                        level_nodes.add(st1)
                        level_nodes.add(st2)

            if not level_nodes:
                continue
            lid, ltopo = iterative_dag_check(level_nodes, level_adj)
            if lid:
                lr = compute_dag_rank(ltopo, level_adj)
                lrm = max(lr.values()) if lr else 0
                print(f"    ff={ff_val}: {len(level_edges)} edges, {len(level_nodes)} nodes, DAG=True, rank={lrm}")
            else:
                # Find SCC sizes
                lsccs = tarjan_iterative(level_nodes, level_adj)
                lnt = [s for s in lsccs if len(s) > 1 or (len(s) == 1 and s[0] in level_adj.get(s[0], set()))]
                print(f"    ff={ff_val}: {len(level_edges)} edges, {len(level_nodes)} nodes, DAG=False, {len(lnt)} nontrivial SCCs")
                for scc in lnt[:3]:
                    print(f"      SCC size={len(scc)}: {scc[0]}")

        # ---- Try (ff, fc, rank) three-level lex ----
        print("\n  Per (ff, fc) level analysis:")
        all_ok = True
        max_rank_overall = 0
        for ff_val in sorted(set(future_fc[c] for c in bad_configs)):
            for fc_val in sorted(set(fc_cache[c] for c in bad_configs if future_fc[c] == ff_val)):
                level_configs = [c for c in bad_configs if future_fc[c] == ff_val and fc_cache[c] == fc_val]
                level_edges = set()
                level_adj_l = defaultdict(set)
                level_nodes = set()
                for c in level_configs:
                    for j in BOUNDARY:
                        if output(c, j) == c[j]:
                            continue
                        c2 = fire(c, j)
                        if c2 in good_set or c2 not in future_fc:
                            continue
                        if future_fc[c2] != ff_val or fc_cache[c2] != fc_val:
                            continue
                        st1 = sixtuple(c)
                        st2 = sixtuple(c2)
                        if st1 != st2:
                            level_edges.add((st1, st2))
                            level_adj_l[st1].add(st2)
                            level_nodes.add(st1)
                            level_nodes.add(st2)

                if not level_nodes:
                    continue
                lid, ltopo = iterative_dag_check(level_nodes, level_adj_l)
                if lid:
                    lr = compute_dag_rank(ltopo, level_adj_l)
                    lrm = max(lr.values()) if lr else 0
                    max_rank_overall = max(max_rank_overall, lrm)
                    if lrm > 0:
                        print(f"    ff={ff_val}, fc={fc_val}: {len(level_edges)} edges, DAG, rank={lrm}")
                else:
                    all_ok = False
                    print(f"    ff={ff_val}, fc={fc_val}: {len(level_edges)} edges, NOT DAG!")

        if all_ok:
            print(f"\n  *** ALL (ff, fc) levels are DAGs! Max rank = {max_rank_overall} ***")
            print(f"\n  Checking fc monotonicity within each ff level...")

            # For each CF transition: does fc EVER decrease?
            fc_dec_in_cf = 0
            for t in all_bdy:
                if t[4] == t[3]:  # ff same
                    st1 = sixtuple(t[0])
                    st2 = sixtuple(t[2])
                    if st1 != st2 and t[6] < t[5]:  # fc decreased, 6tuple changed
                        fc_dec_in_cf += 1

            print(f"  CF transitions with fc decrease AND 6tuple change: {fc_dec_in_cf}")

            if fc_dec_in_cf > 0:
                print(f"\n  Need lex (ff, -(fc), rank) or (ff, rank_per_ff) measure...")
                print(f"  Checking if per-ff-level 6-tuple graph is DAG (ignoring fc)...")
            else:
                print(f"\n  *** MEASURE: lex(ff, -fc, rank_per_(ff,fc)) works for boundary! ***")
                print(f"  Or equivalently: M = ff * K1 + (ff-fc) * K2 + rank")
                print(f"  With K2 = {max_rank_overall + 1}, K1 = N * K2 = {N * (max_rank_overall + 1)}")

# ---- Interior transitions check ----
print("\n" + "=" * 70)
print("INTERIOR TRANSITIONS CHECK")
print("=" * 70)
print("Interior transitions don't change the 6-tuple, but may change fc and FutureFc.")

int_ff_inc = 0
int_ff_dec = 0
int_ff_same = 0
int_fc_changes = defaultdict(int)

for c in bad_configs:
    if c not in future_fc:
        continue
    ff_c = future_fc[c]
    for j in INTERIOR:
        if output(c, j) == c[j]:
            continue
        c2 = fire(c, j)
        if c2 in good_set or c2 not in future_fc:
            continue
        ff_c2 = future_fc[c2]
        fc_c = fc_cache[c]
        fc_c2 = fc_cache[c2]
        if ff_c2 > ff_c:
            int_ff_inc += 1
        elif ff_c2 < ff_c:
            int_ff_dec += 1
        else:
            int_ff_same += 1
        int_fc_changes[(fc_c, fc_c2)] += 1

print(f"Interior FutureFc: inc={int_ff_inc}, same={int_ff_same}, dec={int_ff_dec}")
print(f"Interior fc changes:")
for k in sorted(int_fc_changes.keys()):
    print(f"  fc {k[0]} -> {k[1]}: {int_fc_changes[k]}")

# ---- Step 8 Critical: For fc-decreasing CF boundary transitions, check rank ----
print("\n" + "=" * 70)
print("Step 8 CRITICAL: FC-decrease + fcNondecRank analysis")
print("=" * 70)

if nondec_dag:
    # For EVERY CF boundary transition, compute the measure change
    violations = []
    for (c, j, c2, fc_c, fc_c2, ff) in cf_boundary_transitions:
        st1 = sixtuple(c)
        st2 = sixtuple(c2)
        r1 = nondec_rank.get(st1, -1)
        r2 = nondec_rank.get(st2, -1)
        gap1 = ff - fc_c
        gap2 = ff - fc_c2
        # For M = gap * K + rank:
        # delta_M = (gap2 - gap1) * K + (r2 - r1)
        # = -(fc_c2 - fc_c) * K + (r2 - r1)
        if fc_c2 < fc_c:  # fc decreased, gap increased
            # delta_gap = fc_c - fc_c2 > 0
            # Need rank to compensate: r2 - r1 < -(fc_c - fc_c2) * K
            # For any K: r2 - r1 must be very negative
            violations.append({
                'proc': j, 'fc_before': fc_c, 'fc_after': fc_c2,
                'rank_before': r1, 'rank_after': r2,
                'gap_delta': (fc_c - fc_c2), 'rank_delta': (r2 - r1),
                'st1': st1, 'st2': st2
            })

    print(f"CF transitions with fc decrease: {len(violations)}")
    if violations:
        rank_deltas = set(v['rank_delta'] for v in violations)
        gap_deltas = set(v['gap_delta'] for v in violations)
        print(f"  Rank deltas: min={min(v['rank_delta'] for v in violations)}, max={max(v['rank_delta'] for v in violations)}")
        print(f"  Gap deltas: {sorted(gap_deltas)}")

        # Check if M = gap * K + rank works for some K
        # Need: for each fc-dec transition, (gap2-gap1)*K + (r2-r1) < 0
        # i.e., gap_delta * K + rank_delta < 0
        # i.e., K > -rank_delta / gap_delta (when rank_delta > 0)
        # or always works when rank_delta < 0

        # For fc-inc transitions: gap_delta < 0, need K < rank_delta / |gap_delta|
        # These conflict if both exist

        # Collect all constraints
        needs_K_large = []  # K > threshold
        needs_K_small = []  # K < threshold

        for (c, j, c2, fc_c, fc_c2, ff) in cf_boundary_transitions:
            st1 = sixtuple(c)
            st2 = sixtuple(c2)
            r1 = nondec_rank.get(st1, 0)
            r2 = nondec_rank.get(st2, 0)
            gap_d = (ff - fc_c2) - (ff - fc_c)  # = fc_c - fc_c2
            rank_d = r2 - r1

            # Need gap_d * K + rank_d < 0
            if gap_d > 0:  # fc decreased
                # K > -rank_d / gap_d
                if rank_d >= 0:
                    # K > rank_d / gap_d always
                    needs_K_large.append(rank_d / gap_d)
                # else rank_d < 0: always satisfied for K >= 0
            elif gap_d < 0:  # fc increased
                # K < rank_d / |gap_d|
                if rank_d <= 0:
                    pass  # always satisfied
                else:
                    needs_K_small.append(rank_d / (-gap_d))
            else:  # gap_d == 0 (fc same)
                if rank_d >= 0:
                    # Problem: 0*K + rank_d >= 0
                    # This should be handled by DAG structure
                    pass

        if needs_K_large:
            K_min = max(needs_K_large) + 1
            print(f"\n  Needs K > {max(needs_K_large):.1f}")
        else:
            K_min = 1
            print(f"\n  No lower bound on K from fc-dec transitions")

        if needs_K_small:
            K_max = min(needs_K_small)
            print(f"  Needs K < {K_max:.1f}")
        else:
            K_max = float('inf')
            print(f"  No upper bound on K from fc-inc transitions")

        if K_min < K_max:
            K_opt = int(K_min) + 1
            print(f"\n  *** M = (ff-fc)*{K_opt} + rank WORKS! K in ({K_min:.1f}, {K_max:.1f}) ***")
        else:
            print(f"\n  *** NO valid K exists: need K > {K_min:.1f} but K < {K_max:.1f} ***")
            print(f"  => Simple (gap*K + rank) measure FAILS")
            print(f"  => Need lex measure or different rank")


# ---- DIRECT per-(ff,fc) level and per-ff level analysis ----
print("\n" + "=" * 70)
print("DIRECT: Per-FutureFc level 6-tuple DAG analysis")
print("=" * 70)

ff_values = sorted(set(future_fc[c] for c in bad_configs))
for ff_val in ff_values:
    level_edges = set()
    level_adj_l = defaultdict(set)
    level_nodes = set()
    for c in bad_configs:
        if future_fc.get(c) != ff_val:
            continue
        for j in BOUNDARY:
            if output(c, j) == c[j]:
                continue
            c2 = fire(c, j)
            if c2 in good_set or c2 not in future_fc:
                continue
            if future_fc[c2] != ff_val:
                continue
            st1 = sixtuple(c)
            st2 = sixtuple(c2)
            if st1 != st2:
                level_edges.add((st1, st2))
                level_adj_l[st1].add(st2)
                level_nodes.add(st1)
                level_nodes.add(st2)

    if not level_nodes:
        print(f"  ff={ff_val}: no 6-tuple-changing boundary transitions")
        continue
    lid, ltopo = iterative_dag_check(level_nodes, level_adj_l)
    if lid:
        lr = compute_dag_rank(ltopo, level_adj_l)
        lrm = max(lr.values()) if lr else 0
        print(f"  ff={ff_val}: {len(level_edges)} edges, {len(level_nodes)} nodes, DAG=True, rank={lrm}")
    else:
        lsccs = tarjan_iterative(level_nodes, level_adj_l)
        lnt = [s for s in lsccs if len(s) > 1 or
               (len(s) == 1 and s[0] in level_adj_l.get(s[0], set()))]
        print(f"  ff={ff_val}: {len(level_edges)} edges, {len(level_nodes)} nodes, DAG=False, {len(lnt)} nontrivial SCCs")
        for scc in lnt[:3]:
            print(f"    SCC size={len(scc)}: e.g. {scc[0]}")
            # Show one cycle in this SCC
            if len(scc) > 1:
                scc_set = set(scc)
                for u in scc:
                    for v in level_adj_l.get(u, []):
                        if v in scc_set and v != u:
                            print(f"      edge: {u} -> {v}")
                            break
                    else:
                        continue
                    break

print("\n" + "=" * 70)
print("DIRECT: Per-(FutureFc, fc) level 6-tuple DAG analysis")
print("=" * 70)

all_ok = True
max_rank_overall = 0
for ff_val in ff_values:
    fc_values = sorted(set(fc_cache[c] for c in bad_configs
                          if future_fc.get(c) == ff_val))
    for fc_val in fc_values:
        level_edges = set()
        level_adj_l = defaultdict(set)
        level_nodes = set()
        for c in bad_configs:
            if future_fc.get(c) != ff_val or fc_cache[c] != fc_val:
                continue
            for j in BOUNDARY:
                if output(c, j) == c[j]:
                    continue
                c2 = fire(c, j)
                if c2 in good_set or c2 not in future_fc:
                    continue
                if future_fc[c2] != ff_val or fc_cache[c2] != fc_val:
                    continue
                st1 = sixtuple(c)
                st2 = sixtuple(c2)
                if st1 != st2:
                    level_edges.add((st1, st2))
                    level_adj_l[st1].add(st2)
                    level_nodes.add(st1)
                    level_nodes.add(st2)

        if not level_nodes:
            continue
        lid, ltopo = iterative_dag_check(level_nodes, level_adj_l)
        if lid:
            lr = compute_dag_rank(ltopo, level_adj_l)
            lrm = max(lr.values()) if lr else 0
            max_rank_overall = max(max_rank_overall, lrm)
            if lrm > 0:
                print(f"  ff={ff_val}, fc={fc_val}: {len(level_edges)} edges, DAG, rank={lrm}")
        else:
            all_ok = False
            lsccs = tarjan_iterative(level_nodes, level_adj_l)
            lnt = [s for s in lsccs if len(s) > 1 or
                   (len(s) == 1 and s[0] in level_adj_l.get(s[0], set()))]
            print(f"  ff={ff_val}, fc={fc_val}: {len(level_edges)} edges, NOT DAG! {len(lnt)} SCCs")
            for scc in lnt[:2]:
                print(f"    SCC size={len(scc)}: {scc[:3]}")

if all_ok:
    print(f"\n*** ALL (ff, fc) levels are DAGs! Max rank = {max_rank_overall} ***")

    # Now check: for boundary transitions within same ff level,
    # does fc ever decrease while staying in same ff?
    fc_dec_count = 0
    fc_inc_count = 0
    fc_same_count = 0
    for t in all_bdy:
        if t[4] == t[3]:  # ff same
            if t[6] > t[5]:
                fc_inc_count += 1
            elif t[6] < t[5]:
                fc_dec_count += 1
            else:
                fc_same_count += 1

    print(f"\nWithin CF: fc_inc={fc_inc_count}, fc_same={fc_same_count}, fc_dec={fc_dec_count}")

    if fc_dec_count == 0:
        print("*** MEASURE: lex(FutureFc, -fc, rank_per_(ff,fc)) WORKS ***")
        print(f"  Max rank = {max_rank_overall}")
        K2 = max_rank_overall + 1
        K1 = N * K2
        print(f"  Flattened: M = FutureFc * {K1} + (FutureFc - fc) * {K2} + rank")
        print(f"  Max M = {N * K1 + N * K2 + max_rank_overall}")
    else:
        print(f"fc can decrease within CF: need to verify that (ff, fc, rank) is lex decreasing")
        print("Checking: does the (ff,fc) pair decrease lex, or just ff and then rank?")

        # The real question: is lex(ff, -fc, rank_per_(ff,fc)) strictly decreasing?
        # ff nonincreasing [PROVED]. When ff same:
        # - If fc increases: lex decreases (second component -fc decreases)
        # - If fc same: rank decreases (DAG at (ff,fc) level)
        # - If fc decreases: lex INCREASES at second component. PROBLEM.
        # So we need fc to be nondecreasing within CF for lex to work.
        # Since fc CAN decrease, lex(ff, -fc, rank) does NOT work directly.

        # Alternative: lex(ff, rank_per_ff_level)
        # If per-ff-level graph is DAG, this works!
        # But we showed per-ff-level is NOT DAG (above).

        # Alternative: need a rank function that handles BOTH fc changes
        # and 6-tuple changes simultaneously.
        # The measure Psi = Phi_full * (R+1) + rank is what proof107 uses.
        # Phi_full = max reachable fc = FutureFc.
        # rank = DAG rank within constant-Phi_full subgraph.
        # For this to work, the constant-Phi_full BOUNDARY 6-tuple
        # subgraph must embed into the overall DAG.

        # Check: within each ff level, is the FULL transition graph
        # (not just boundary) a DAG?
        print("\nChecking full (boundary + interior) transition DAG per ff level...")
        for ff_val in ff_values:
            level_configs = [c for c in bad_configs if future_fc.get(c) == ff_val]
            level_set = set(level_configs)
            # Check: is there a cycle among these configs?
            # Build adjacency (all processors)
            has_cycle = False
            # Use color-based DFS on config level
            WHITE, GRAY, BLACK = 0, 1, 2
            color = {}
            for c in level_configs:
                color[c] = WHITE

            for start in level_configs:
                if color[start] != WHITE:
                    continue
                stack = [(start, False)]
                while stack:
                    node, processed = stack.pop()
                    if processed:
                        color[node] = BLACK
                        continue
                    if color[node] == BLACK:
                        continue
                    if color[node] == GRAY:
                        color[node] = BLACK
                        continue
                    color[node] = GRAY
                    stack.append((node, True))
                    for j in range(N):
                        if output(node, j) == node[j]:
                            continue
                        c2 = fire(node, j)
                        if c2 in good_set or c2 not in future_fc:
                            continue
                        if future_fc[c2] != ff_val:
                            continue
                        if c2 not in color:
                            color[c2] = WHITE
                        if color[c2] == GRAY:
                            has_cycle = True
                        elif color[c2] == WHITE:
                            stack.append((c2, False))
                if has_cycle:
                    break

            print(f"  ff={ff_val}: {len(level_configs)} configs, full graph DAG={not has_cycle}")

else:
    print(f"\nSome (ff,fc) levels have cycles. Need different approach.")


# ---- CONFIG-LEVEL DAG check per ff level ----
print("\n" + "=" * 70)
print("CONFIG-LEVEL: constant-FutureFc transition graph DAG check")
print("=" * 70)

for ff_val in ff_values:
    level_configs = [c for c in bad_configs if future_fc.get(c) == ff_val]
    level_set = set(level_configs)

    # Build full transition graph within this ff level
    has_cycle = False
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {}
    for c in level_configs:
        color[c] = WHITE

    for start in level_configs:
        if color[start] != WHITE:
            continue
        stack = [(start, False)]
        while stack:
            node, processed = stack.pop()
            if processed:
                color[node] = BLACK
                continue
            if color[node] == BLACK:
                continue
            if color[node] == GRAY:
                color[node] = BLACK
                continue
            color[node] = GRAY
            stack.append((node, True))
            for j in range(N):
                if output(node, j) == node[j]:
                    continue
                c2 = fire(node, j)
                if c2 in good_set or c2 not in future_fc:
                    continue
                if future_fc[c2] != ff_val:
                    continue
                if c2 not in color:
                    color[c2] = WHITE
                if color[c2] == GRAY:
                    has_cycle = True
                elif color[c2] == WHITE:
                    stack.append((c2, False))
            if has_cycle:
                break
        if has_cycle:
            break

    print(f"  ff={ff_val}: {len(level_configs)} configs, "
          f"full graph (all procs) DAG = {not has_cycle}")

# ---- 6-TUPLE CYCLE ANALYSIS ----
# The 6-tuple SCCs at per-(ff,fc) level have size-3 cycles like
# (0,1,0,...) -> (0,1,1,...) -> (0,1,2,...) -> (0,1,0,...)
# These cycle through c[2] values 0,1,2. This means firing proc 2
# can cycle the 6-tuple at constant (ff,fc).
# But at CONFIG level, the interior values differ, so it's actually a DAG.
print("\n" + "=" * 70)
print("6-TUPLE SCC ANALYSIS: examining why 6-tuple cycles exist")
print("=" * 70)

# Look at one specific SCC: ff=7, fc=4, the size-3 SCC
# (0,1,2,2,2,0), (0,1,1,2,2,0), (0,1,0,2,2,0)
target_st = [(0, 1, 2, 2, 2, 0), (0, 1, 1, 2, 2, 0), (0, 1, 0, 2, 2, 0)]
print(f"\nExamining SCC: {target_st}")
print("These differ only in c[2] (position 2).")
print("Edges must be from firing proc 2 (changes c[2]).")

for st in target_st:
    # Find configs with this 6-tuple, ff=7, fc=4
    matching = []
    for c in bad_configs:
        if sixtuple(c) == st and future_fc.get(c) == 7 and fc_cache[c] == 4:
            matching.append(c)
    print(f"\n  6tuple={st}: {len(matching)} matching configs")
    for c in matching[:3]:
        # Check what proc 2 does
        j = 2
        if output(c, j) != c[j]:
            c2 = fire(c, j)
            st2 = sixtuple(c2)
            ff2 = future_fc.get(c2, '?')
            fc2 = fc_cache.get(c2, '?')
            print(f"    {c} -> fire P2 -> {c2}")
            print(f"      6tuple: {st} -> {st2}, fc: {fc_cache[c]}->{fc2}, ff: 7->{ff2}")

# ---- KEY INSIGHT: Check if 6-tuple + fc is enough ----
# The 6-tuple has cycles because different interior configs can
# map the same 6-tuple to different successors.
# But if we ADD fc to the 6-tuple, does that break the cycles?
# Already shown: (ff,fc) level has cycles too.
# So the issue is deeper.

# ---- Check the PROOF107 approach: constant-ff config-level DAG ----
print("\n" + "=" * 70)
print("PROOF107 APPROACH: config-level DAG rank within constant-ff")
print("=" * 70)

for ff_val in ff_values:
    level_configs = [c for c in bad_configs if future_fc.get(c) == ff_val]
    level_set = set(level_configs)

    # Build adjacency (all procs)
    level_adj = defaultdict(list)
    for c in level_configs:
        for j in range(N):
            if output(c, j) == c[j]:
                continue
            c2 = fire(c, j)
            if c2 in good_set or c2 not in future_fc:
                continue
            if future_fc[c2] == ff_val:
                level_adj[c].append(c2)

    # Compute DAG rank via BFS (topological sort with in-degree)
    # First check it's a DAG (already done above, but let's be sure)
    in_deg = defaultdict(int)
    for c in level_configs:
        for c2 in level_adj[c]:
            in_deg[c2] += 1

    queue = deque()
    for c in level_configs:
        if in_deg[c] == 0:
            queue.append(c)

    topo_order = []
    while queue:
        c = queue.popleft()
        topo_order.append(c)
        for c2 in level_adj[c]:
            in_deg[c2] -= 1
            if in_deg[c2] == 0:
                queue.append(c2)

    is_dag = (len(topo_order) == len(level_configs))

    if is_dag:
        # Compute rank (longest path)
        rank_map = {}
        for c in reversed(topo_order):
            r = 0
            for c2 in level_adj[c]:
                r = max(r, rank_map[c2] + 1)
            rank_map[c] = r
        max_r = max(rank_map.values()) if rank_map else 0

        # Check: within this ff level, do boundary transitions that
        # change the 6-tuple always decrease rank?
        bdy_violations = 0
        bdy_total = 0
        for c in level_configs:
            for j in BOUNDARY:
                if output(c, j) == c[j]:
                    continue
                c2 = fire(c, j)
                if c2 in good_set or c2 not in future_fc:
                    continue
                if future_fc[c2] != ff_val:
                    continue
                st1 = sixtuple(c)
                st2 = sixtuple(c2)
                if st1 != st2:
                    bdy_total += 1
                    if rank_map[c2] >= rank_map[c]:
                        bdy_violations += 1

        print(f"  ff={ff_val}: {len(level_configs)} configs, DAG=True, "
              f"rank={max_r}, bdy 6t-change: {bdy_total} trans, "
              f"rank violations: {bdy_violations}")

        # Also check: does the 6-tuple rank PROJECTION work?
        # i.e., can we assign rank to 6-tuples s.t. rank strictly decreases?
        # Compute max/min config rank per 6-tuple
        st_rank_range = defaultdict(lambda: [float('inf'), -float('inf')])
        for c in level_configs:
            st = sixtuple(c)
            r = rank_map[c]
            st_rank_range[st][0] = min(st_rank_range[st][0], r)
            st_rank_range[st][1] = max(st_rank_range[st][1], r)

        # Check overlap: for each 6-tuple edge, is max(src) > min(dst)?
        # If so, the 6-tuple projection CAN'T consistently order them.
        overlap_count = 0
        for c in level_configs:
            for j in BOUNDARY:
                if output(c, j) == c[j]:
                    continue
                c2 = fire(c, j)
                if c2 in good_set or c2 not in future_fc:
                    continue
                if future_fc[c2] != ff_val:
                    continue
                st1 = sixtuple(c)
                st2 = sixtuple(c2)
                if st1 != st2:
                    # src rank range vs dst rank range
                    if st_rank_range[st1][0] <= st_rank_range[st2][1]:
                        overlap_count += 1

        print(f"    6-tuple rank range overlaps: {overlap_count}/{bdy_total}")

    else:
        print(f"  ff={ff_val}: {len(level_configs)} configs, DAG=False "
              f"({len(topo_order)}/{len(level_configs)} in topo order)")

print("\n" + "=" * 70)
print("FINAL SUMMARY")
print("=" * 70)
print(f"n={N}, configs={len(all_configs)}, good={len(good_set)}, bad={len(bad_configs)}")
print(f"CF boundary 6-tuple edges: {len(cf_6tuple_edges)}")
print(f"FutureFc monotone on boundary: {ff_inc == 0}")
print(f"FutureFc monotone on interior: {int_ff_inc == 0}")
print(f"CF gap (ff-fc) monotone: {cf_gap_inc == 0}")
print(f"Config-level constant-ff graph is DAG (key for Lean proof)")
print("\nDone.")
