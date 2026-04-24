#!/usr/bin/env python3
"""
Research Agent: Finding the correct inner measure for boundary-fixed CPhiSteps.
==============================================================================
Key findings from q2:
- Boundary-fixed rank = 3n-19 (confirmed n=9..12)
- ALL movers at deep interior (3..n-4)
- fc never increases
- When dfc=0: deep is ALWAYS constant
- Only 5 entries fired: (0,2,2)->0, (1,0,0)->1, (1,1,2)->2, (1,0,2)->1, (0,1,2)->0

So for dfc=0 edges, BOTH fc and deep are constant. What changes?
The DAG rank is 3n-19 ~ 3*(n-5) interior positions. Could it be that
a position-indexed counter decreases?

This script traces all dfc=0 boundary-fixed CPhiStep chains to find
the actual measure.
"""

import sys, time
from itertools import product as cartesian
from collections import defaultdict, deque, Counter

T_bot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
         (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
T_low = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
T_mid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
         (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2}
T_high = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
          (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
          (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
T_top = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}

def build_tables(n):
    tabs = []
    for i in range(n):
        if i == 0: tabs.append(T_bot)
        elif i == 1: tabs.append(T_low)
        elif i == n-1: tabs.append(T_top)
        elif i == n-2: tabs.append(T_high)
        else: tabs.append(T_mid)
    return tabs

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1) % n])

def boundary6(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def exp2_count(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] in (0, 1))
def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 1)
def exp2_weight(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] in (0, 1))
def tp_key(c, n):
    return (exp2_count(c, n), int_21(c, n), exp2_weight(c, n))

def deep_mid_hop(c, n):
    return sum(j for j in range(3, n-3) if c[j] == 2 and c[(j+1) % n] in (0, 1))


def investigate(n):
    print(f"\n{'='*70}")
    print(f"  n={n}: Analyzing dfc=0 boundary-fixed CPhiSteps")
    print(f"{'='*70}")
    t0 = time.time()

    ms = [2] + [3]*(n-2) + [2]
    tables = build_tables(n)

    all_configs = list(cartesian(*(range(m) for m in ms)))

    succ_map = {}
    for c in all_configs:
        out = []
        for i in range(n):
            L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
            o = tables[i].get((L, S, R), S)
            if o != S:
                nc = list(c); nc[i] = o; out.append((tuple(nc), i))
        succ_map[c] = out

    # Tarjan
    idx_c = [0]; stk = []; ll = {}; im = {}; ons = set(); sccs = []
    for start in all_configs:
        if start in im: continue
        cs = [(start, iter([s for s, _ in succ_map.get(start, [])]))]
        im[start] = ll[start] = idx_c[0]; idx_c[0] += 1
        stk.append(start); ons.add(start)
        while cs:
            v, ch = cs[-1]
            try:
                w = next(ch)
                if w not in im:
                    im[w] = ll[w] = idx_c[0]; idx_c[0] += 1
                    stk.append(w); ons.add(w)
                    cs.append((w, iter([s for s, _ in succ_map.get(w, [])])))
                elif w in ons:
                    ll[v] = min(ll[v], im[w])
            except StopIteration:
                cs.pop()
                if cs: ll[cs[-1][0]] = min(ll[cs[-1][0]], ll[v])
                if ll[v] == im[v]:
                    scc = []
                    while True:
                        w = stk.pop(); ons.discard(w); scc.append(w)
                        if w == v: break
                    sccs.append(scc)
    terminal = []
    for i_scc, scc in enumerate(sccs):
        ss = set(scc)
        if not any(s not in ss for v in scc for s, _ in succ_map.get(v, [])):
            terminal.append(i_scc)
    good_set = set(sccs[terminal[0]])
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)

    fc_cache = {c: fc(c, n) for c in bad_configs}
    tp_cache = {c: tp_key(c, n) for c in bad_configs}

    tp_fwd = defaultdict(list)
    tp_edges = []
    for c in bad_configs:
        for s, mover in succ_map.get(c, []):
            if s in bad_set and tp_cache.get(s) == tp_cache[c]:
                dfc = fc_cache.get(s, fc(s, n)) - fc_cache[c]
                tp_edges.append((c, s, mover, dfc))
                tp_fwd[c].append((s, dfc))

    g = {c: 0 for c in bad_configs}
    for _ in range(3 * n):
        changed = False
        for c in bad_configs:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g.get(s, 0)
                if new_g > g[c]:
                    g[c] = new_g
                    changed = True
        if not changed:
            break
    phi_full = {c: fc_cache[c] + g[c] for c in bad_configs}

    cphi_edges = [(c, s, m) for c, s, m, _ in tp_edges
                  if phi_full[c] == phi_full.get(s, 0)]

    bd_fixed = [(c, s, m) for c, s, m in cphi_edges
                if boundary6(c, n) == boundary6(s, n)]

    # Focus on dfc=0 boundary-fixed edges
    dfc0_bf = [(c, s, m) for c, s, m in bd_fixed
               if fc_cache.get(s, 0) == fc_cache[c]]

    print(f"  dfc=0 boundary-fixed CPhiSteps: {len(dfc0_bf)}")

    # For each step, record the interior state change
    print(f"\n  Interior changes (positions 3..{n-4}):")
    interior_changes = []
    for c, s, m in dfc0_bf[:20]:
        interior_c = c[3:n-3]
        interior_s = s[3:n-3]
        changes = [(j+3, c[j+3], s[j+3]) for j in range(n-6) if c[j+3] != s[j+3]]
        interior_changes.append((c, s, m, changes))
        L, S, R = c[(m-1) % n], c[m], c[(m+1) % n]
        out = tables[m].get((L, S, R), S)
        entry_name = f"({L},{S},{R})->{out}"
        print(f"    mover={m}, {entry_name}: {changes}")

    # KEY: What entries have dfc=0? These are the "hop" entries.
    # The 3 known hops: (1,0,0)->1, (0,2,2)->0, (1,1,2)->2
    # Let's verify:
    dfc0_entries = Counter()
    for c, s, m in dfc0_bf:
        L, S, R = c[(m-1) % n], c[m], c[(m+1) % n]
        out = tables[m].get((L, S, R), S)
        dfc0_entries[(L, S, R, out)] += 1
    print(f"\n  dfc=0 entries: {dict(dfc0_entries)}")

    # For the 3 hop entries, classify by direction:
    # (1,0,0)->1: left hop (copy left), value 0->1
    # (0,2,2)->0: left hop (copy left), value 2->0
    # (1,1,2)->2: right hop (copy right), value 1->2
    # These propagate a "wave" through the interior.

    # Hypothesis: the measure is the position of the "wavefront"
    # For each boundary, trace the longest chain of dfc=0 steps

    # Build the dfc=0 boundary-fixed subgraph
    dfc0_adj = defaultdict(list)
    dfc0_nodes = set()
    for c, s, m in dfc0_bf:
        dfc0_adj[c].append((s, m))
        dfc0_nodes.add(c)
        dfc0_nodes.add(s)

    # Compute rank in dfc=0 subgraph
    out_d = {c: len(dfc0_adj.get(c, [])) for c in dfc0_nodes}
    sinks = [c for c in dfc0_nodes if out_d[c] == 0]
    dfc0_rank = {c: 0 for c in sinks}
    rev = defaultdict(list)
    for c in dfc0_nodes:
        for s, _ in dfc0_adj.get(c, []):
            rev[s].append(c)
    q = deque(sinks)
    while q:
        v = q.popleft()
        for u in rev.get(v, []):
            nr = dfc0_rank[v] + 1
            if u not in dfc0_rank or nr > dfc0_rank[u]:
                dfc0_rank[u] = nr
                q.append(u)
    max_dfc0_rank = max(dfc0_rank.values()) if dfc0_rank else 0
    print(f"\n  dfc=0 subgraph DAG rank: {max_dfc0_rank}")

    # Trace the longest chain
    def trace_chain(start):
        chain = [start]
        c = start
        while dfc0_adj.get(c):
            # Pick successor with highest rank
            best_s, best_m = max(dfc0_adj[c], key=lambda x: dfc0_rank.get(x[0], 0))
            # Actually we want to go BACKWARDS - find the path with longest distance
            # Just follow any edge
            s, m = dfc0_adj[c][0]
            chain.append((s, m))
            c = s
        return chain

    # Find config with highest rank
    if dfc0_rank:
        top_config = max(dfc0_nodes, key=lambda c: dfc0_rank.get(c, 0))
        print(f"\n  Top-ranked config (rank {dfc0_rank[top_config]}):")
        print(f"    {top_config}")
        print(f"    boundary: {boundary6(top_config, n)}")
        print(f"    interior (pos 3..{n-4}): {top_config[3:n-3]}")

        # Trace chain from top
        chain = [top_config]
        c = top_config
        while dfc0_adj.get(c):
            succs = dfc0_adj[c]
            # Pick the one with highest rank (longest remaining path)
            best = max(succs, key=lambda x: dfc0_rank.get(x[0], 0))
            s, m = best
            L, S, R = c[(m-1) % n], c[m], c[(m+1) % n]
            out = tables[m].get((L, S, R), S)
            entry_type = ""
            if (L, S, R, out) == (1, 0, 0, 1): entry_type = "R-hop"
            elif (L, S, R, out) == (0, 2, 2, 0): entry_type = "R-hop"
            elif (L, S, R, out) == (1, 1, 2, 2): entry_type = "L-hop"
            print(f"    pos={m}, ({L},{S},{R})->{out} [{entry_type}], "
                  f"interior: {s[3:n-3]}, rank {dfc0_rank.get(s, 0)}")
            chain.append(s)
            c = s
            if len(chain) > max_dfc0_rank + 2:
                break

    # Now test: does mover position always strictly increase or decrease?
    print(f"\n  Mover position sequences on dfc=0 chains:")
    # For each edge, record mover relative to previous
    mover_monotone = True
    for c, s, m in dfc0_bf:
        for s2, m2 in dfc0_adj.get(s, []):
            if m2 <= m:
                pass  # Not strictly increasing
            # Check if m2 >= m always?

    # Test candidate: weighted sum of interior values
    # Position-weighted sum: sum_j j * c[j] for j in 3..n-4
    def pos_weighted_sum(c):
        return sum(j * c[j] for j in range(3, n-3))

    pws_viols = sum(1 for c, s, _ in dfc0_bf
                    if pos_weighted_sum(s) >= pos_weighted_sum(c))
    pws_viols_rev = sum(1 for c, s, _ in dfc0_bf
                        if pos_weighted_sum(s) <= pos_weighted_sum(c))
    print(f"\n  pos_weighted_sum monotone (desc): viols={pws_viols}/{len(dfc0_bf)}")
    print(f"  pos_weighted_sum monotone (asc): viols={pws_viols_rev}/{len(dfc0_bf)}")

    # Test: plain sum of interior values
    def sum_interior(c):
        return sum(c[j] for j in range(3, n-3))

    si_viols = sum(1 for c, s, _ in dfc0_bf
                   if sum_interior(s) >= sum_interior(c))
    si_viols_rev = sum(1 for c, s, _ in dfc0_bf
                       if sum_interior(s) <= sum_interior(c))
    print(f"  sum_interior monotone (desc): viols={si_viols}/{len(dfc0_bf)}")
    print(f"  sum_interior monotone (asc): viols={si_viols_rev}/{len(dfc0_bf)}")

    # Test: number of (2,x) pairs where x in {0,1} at deep interior
    def count_hoppable(c):
        return sum(1 for j in range(3, n-3) if c[j] == 2 and c[(j+1) % n] in (0, 1))

    ch_viols = sum(1 for c, s, _ in dfc0_bf
                   if count_hoppable(s) >= count_hoppable(c))
    print(f"  count_hoppable monotone (desc): viols={ch_viols}/{len(dfc0_bf)}")

    # Test: rightmost position j where c[j] != c[j+1]
    def rightmost_diff(c):
        for j in range(n-4, 2, -1):
            if c[j] != c[(j+1) % n]:
                return j
        return 0

    rd_viols = sum(1 for c, s, _ in dfc0_bf
                   if rightmost_diff(s) >= rightmost_diff(c))
    print(f"  rightmost_diff monotone (desc): viols={rd_viols}/{len(dfc0_bf)}")

    # Test: leftmost position j where c[j] != c[j-1]
    def leftmost_diff(c):
        for j in range(3, n-3):
            if c[j] != c[(j-1) % n]:
                return j
        return n

    ld_viols = sum(1 for c, s, _ in dfc0_bf
                   if leftmost_diff(s) <= leftmost_diff(c))
    ld_viols_rev = sum(1 for c, s, _ in dfc0_bf
                       if leftmost_diff(s) >= leftmost_diff(c))
    print(f"  leftmost_diff monotone (asc): viols={ld_viols}/{len(dfc0_bf)}")
    print(f"  leftmost_diff monotone (desc): viols={ld_viols_rev}/{len(dfc0_bf)}")

    # OK let me just look at how the entries transform the interior.
    # The 3 dfc=0 entries are all "hops":
    # (1,0,0)->1: c[j-1]=1, c[j]=0, c[j+1]=0 => c[j] becomes 1 (copies left)
    # (0,2,2)->0: c[j-1]=0, c[j]=2, c[j+1]=2 => c[j] becomes 0 (copies left)
    # (1,1,2)->2: c[j-1]=1, c[j]=1, c[j+1]=2 => c[j] becomes 2 (copies right)
    #
    # These all COPY a neighbor value. So:
    # After the hop, c[j] matches one neighbor that it differed from before.
    # This creates a LONGER run of equal values.
    #
    # MEASURE: count distinct runs in interior? Or sum of (n-j) * (c[j] != c[j+1])?

    # Test: number of transitions in interior (fc restricted to 3..n-4)
    def interior_fc(c):
        return sum(1 for j in range(3, n-3) if c[j] != c[(j+1) % n])

    ifc_viols = sum(1 for c, s, _ in dfc0_bf
                    if interior_fc(s) >= interior_fc(c))
    print(f"\n  interior_fc (desc): viols={ifc_viols}/{len(dfc0_bf)}")

    # Test: weighted interior transitions
    def weighted_interior_fc(c):
        return sum(j for j in range(3, n-3) if c[j] != c[(j+1) % n])

    wifc_viols = sum(1 for c, s, _ in dfc0_bf
                     if weighted_interior_fc(s) >= weighted_interior_fc(c))
    print(f"  weighted_interior_fc (desc): viols={wifc_viols}/{len(dfc0_bf)}")

    # Test: reverse-weighted interior transitions (higher j = higher weight)
    def rev_weighted_ifc(c):
        return sum((n-3-j) for j in range(3, n-3) if c[j] != c[(j+1) % n])

    rwifc_viols = sum(1 for c, s, _ in dfc0_bf
                      if rev_weighted_ifc(s) >= rev_weighted_ifc(c))
    print(f"  rev_weighted_ifc (desc): viols={rwifc_viols}/{len(dfc0_bf)}")

    # Test: count of interior positions where c[j] == 2
    def count_interior_2(c):
        return sum(1 for j in range(3, n-3) if c[j] == 2)

    ci2_viols = sum(1 for c, s, _ in dfc0_bf
                    if count_interior_2(s) >= count_interior_2(c))
    print(f"  count_interior_2 (desc): viols={ci2_viols}/{len(dfc0_bf)}")

    # Test: sum of c[j]^2 for interior j
    def sum_sq_interior(c):
        return sum(c[j]*c[j] for j in range(3, n-3))

    ssq_viols = sum(1 for c, s, _ in dfc0_bf
                    if sum_sq_interior(s) >= sum_sq_interior(c))
    ssq_viols_rev = sum(1 for c, s, _ in dfc0_bf
                        if sum_sq_interior(s) <= sum_sq_interior(c))
    print(f"  sum_sq_interior (desc): viols={ssq_viols}/{len(dfc0_bf)}")
    print(f"  sum_sq_interior (asc): viols={ssq_viols_rev}/{len(dfc0_bf)}")

    elapsed = time.time() - t0
    print(f"\n  Time: {elapsed:.1f}s")
    return max_dfc0_rank


if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    for nv in [9, 10, 11]:
        investigate(nv)
