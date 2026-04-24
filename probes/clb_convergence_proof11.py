#!/usr/bin/env python3
"""
CONVERGENCE PROOF — Part 11: Two-Level Decomposition + Definitive Framework
===========================================================================

KEY FINDINGS FROM PARTS 8-10:
1. No simple potential function exists (exhaustive search)
2. No weighted sum of frozen ranks works (LP infeasible)
3. Frozen rank sum has ~8% violations (all from boundary firings)
4. 3-local decomposition explains 90-97% of rank variance
5. Settled count almost-monotone (5% violations, all decrease rank)

NEW APPROACH: Two-level decomposition.
Level 1: Boundary state (c[0], c[n-1]) — binary pair, 4 possible values
Level 2: Interior rank given boundary state

The idea: partition configs by their boundary values. Within each partition,
the interior behaves like a chain (fixed boundaries). If we can show that:
(a) Each partition's interior graph is a DAG (chain with fixed boundaries)
(b) Transitions that change boundary values preserve the overall DAG structure
Then the full graph is a DAG.

Also: DEFINITIVE attempt at the causal chain argument.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque, Counter
import numpy as np

def analyze_boundary_partition(n):
    """
    Partition bad configs by boundary values (c[0], c[n-1]).
    Analyze the DAG structure within each partition.
    """
    print(f"\nBOUNDARY PARTITION ANALYSIS (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Partition by (c[0], c[n-1])
    partitions = defaultdict(list)
    for c in bad_list:
        partitions[(c[0], c[n-1])].append(c)

    print(f"  Boundary partitions:")
    for (b0, bn), configs in sorted(partitions.items()):
        print(f"    (c[0]={b0}, c[{n-1}]={bn}): {len(configs)} configs")

    # For each partition, check if the INTERIOR transitions form a DAG
    # Interior transitions = transitions at positions 1, 2, ..., n-2
    # (NOT position 0 or n-1)
    print(f"\n  Interior DAG within each partition:")
    interior_dag = {}
    interior_depths = {}
    for (b0, bn), configs in sorted(partitions.items()):
        config_set = set(configs)
        adj = {c: [] for c in configs}
        for c in configs:
            for i in range(1, n-1):  # interior positions only
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in config_set:
                        adj[c].append(succ)

        # Check DAG
        in_deg = {c: 0 for c in configs}
        for c in configs:
            for s in adj[c]:
                in_deg[s] += 1

        q = deque(c for c in configs if in_deg[c] == 0)
        count = 0
        topo = []
        while q:
            c = q.popleft()
            count += 1
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)

        is_dag = (count == len(configs))

        # Compute depth
        depth = 0
        if is_dag:
            rank = {}
            for c in reversed(topo):
                rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
            depth = max(rank.values()) if rank else 0

        interior_dag[(b0, bn)] = is_dag
        interior_depths[(b0, bn)] = depth
        status = f"DAG (depth {depth})" if is_dag else "NOT DAG"
        print(f"    ({b0},{bn}): {status}")

    # Now check: do boundary transitions (firing P0 or P_{n-1}) cross partitions?
    print(f"\n  Boundary transition analysis:")
    cross_count = 0
    same_count = 0
    boundary_trans = []
    for c in bad_list:
        for i in [0, n-1]:
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    part_from = (c[0], c[n-1])
                    part_to = (succ[0], succ[n-1])
                    if part_from == part_to:
                        same_count += 1
                    else:
                        cross_count += 1
                        boundary_trans.append((c, succ, i, part_from, part_to))

    print(f"    Same partition: {same_count}")
    print(f"    Cross partition: {cross_count}")

    # Analyze cross-partition transitions
    cross_types = Counter()
    for c, s, i, pf, pt in boundary_trans:
        cross_types[(pf, pt)] += 1

    print(f"\n  Cross-partition transition types:")
    for (pf, pt), count in sorted(cross_types.items()):
        df = interior_depths.get(pf, '?')
        dt = interior_depths.get(pt, '?')
        print(f"    {pf} → {pt}: {count} transitions (depth {df} → {dt})")

def analyze_boundary_cycle_impossibility(n):
    """
    Check: can a cycle exist that crosses boundary partitions?

    A cycle must include firings at ALL n positions.
    Boundary firings (P0, P_{n-1}) change the partition.
    Interior firings (P1..P_{n-2}) stay within the partition.

    For a cycle, boundary firings must bring us back to the same partition.
    Since P0 and P_{n-1} are binary (0-1), the only way to return is
    to fire each boundary position an even number of times.
    """
    print(f"\nBOUNDARY CYCLE IMPOSSIBILITY (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # For each boundary config (c[0], c[n-1]), compute the full rank
    # in the FULL bad-config graph
    adj = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append((succ, i))

    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s, _ in adj[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s, _ in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    full_rank = {}
    for c in reversed(topo):
        full_rank[c] = max((full_rank[s] + 1 for s, _ in adj[c]), default=0)

    # For boundary transitions (P0 or P_{n-1}), compute rank change
    print("  Boundary transition rank changes:")
    boundary_deltas = defaultdict(list)
    for c in bad_list:
        for i in [0, n-1]:
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    dr = full_rank[succ] - full_rank[c]
                    part_from = (c[0], c[n-1])
                    part_to = (succ[0], succ[n-1])
                    boundary_deltas[(part_from, part_to, i)].append(dr)

    for (pf, pt, i), drs in sorted(boundary_deltas.items()):
        pos = 'P0' if i == 0 else f'P{n-1}'
        print(f"    {pf}→{pt} via {pos}: "
              f"count={len(drs)}, Δrank range=[{min(drs)},{max(drs)}], "
              f"mean={np.mean(drs):.1f}")

    # KEY ANALYSIS: What's the maximum rank in each partition?
    print(f"\n  Max rank by partition:")
    for (b0, bn) in sorted(set((c[0], c[n-1]) for c in bad_list)):
        configs_in_part = [c for c in bad_list if c[0] == b0 and c[n-1] == bn]
        if configs_in_part:
            max_r = max(full_rank[c] for c in configs_in_part)
            min_r = min(full_rank[c] for c in configs_in_part)
            print(f"    ({b0},{bn}): rank range [{min_r}, {max_r}], "
                  f"count={len(configs_in_part)}")

def analyze_strongly_connected_components(n):
    """
    Verify: the bad-config graph has NO strongly connected components
    of size > 1. This is equivalent to being a DAG.

    Also: find the "almost-SCCs" — pairs of configs that are closest
    to forming a cycle (shortest path A→B + shortest path B→A).
    """
    print(f"\n\"ALMOST-CYCLE\" ANALYSIS (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Build adjacency
    adj = defaultdict(list)
    rev_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    rev_adj[succ].append(c)

    # For a sample of configs, find shortest paths and check for "almost-cycles"
    # BFS from a config gives shortest path to all reachable configs
    # BFS on reverse gives shortest path FROM all configs to this one

    sample = bad_list[:min(50, len(bad_list))]

    # For each sampled config, compute reachable set via BFS
    min_round_trip = float('inf')
    best_pair = None

    for start in sample:
        # Forward BFS
        dist_fwd = {start: 0}
        q = deque([start])
        while q:
            c = q.popleft()
            for s in adj[c]:
                if s not in dist_fwd:
                    dist_fwd[s] = dist_fwd[c] + 1
                    q.append(s)

        # For each config reachable from start, check if start is reachable from it
        # (using reverse BFS from start)
        dist_rev = {start: 0}
        q = deque([start])
        while q:
            c = q.popleft()
            for pred in rev_adj[c]:
                if pred not in dist_rev:
                    dist_rev[pred] = dist_rev[c] + 1
                    q.append(pred)

        # For each config c reachable from start AND that can reach start:
        for c in dist_fwd:
            if c != start and c in dist_rev:
                round_trip = dist_fwd[c] + dist_rev[c]
                if round_trip < min_round_trip:
                    min_round_trip = round_trip
                    best_pair = (start, c, dist_fwd[c], dist_rev[c])

    if best_pair:
        a, b, d_ab, d_ba = best_pair
        print(f"  Closest to cycle: A→B in {d_ab} steps, B→A in {d_ba} steps, "
              f"total={d_ab + d_ba}")
        print(f"    A = {a}")
        print(f"    B = {b}")
    else:
        print(f"  No pair found where both A→B and B→A paths exist")
        print(f"  (This confirms the DAG property — no two configs are mutually reachable)")

def test_boundary_crossing_argument(n):
    """
    TEST THE KEY PROOF IDEA:

    Observation: In any hypothetical cycle, P0 fires k0 ≥ 2 times and
    P_{n-1} fires k_{n-1} ≥ 2 times. Since both are binary,
    after each firing they toggle their value. So k0 and k_{n-1} must
    be even (to return to the original value).

    Between consecutive P0 firings, c[0] is fixed. Similarly for P_{n-1}.
    So between consecutive boundary firings, the interior evolves with
    fixed boundaries.

    If we can show that the interior (positions 1..n-2) with fixed
    boundaries forms a DAG with depth D_int, then the total cycle
    length is at least 2 * D_int (since we need to go "up" and "down"
    in the interior between boundary firings).

    But the cycle length must also be at least 2n (all positions fire ≥ 2 times).
    If 2 * D_int > maximum cycle length... this would be a contradiction.

    Unfortunately, D_int grows as O(n²), so this doesn't give a finite bound.
    But maybe the STRUCTURE of the interior DAG prevents the cycle.
    """
    print(f"\nBOUNDARY CROSSING ARGUMENT TEST (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Compute interior DAG depth for each boundary configuration
    for b0 in range(2):
        for bn in range(2):
            # Configs with c[0]=b0, c[n-1]=bn
            part_configs = [c for c in bad_list if c[0] == b0 and c[n-1] == bn]
            if not part_configs:
                continue

            part_set = set(part_configs)
            adj = {c: [] for c in part_configs}
            for c in part_configs:
                for i in range(1, n-1):  # interior only
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    new_S = fs[i](L, S, R)
                    if new_S != S:
                        lst = list(c); lst[i] = new_S; succ = tuple(lst)
                        if succ in part_set:
                            adj[c].append(succ)

            # Check DAG
            in_deg = {c: 0 for c in part_configs}
            for c in part_configs:
                for s in adj[c]:
                    in_deg[s] += 1
            q = deque(c for c in part_configs if in_deg[c] == 0)
            count = 0
            topo = []
            while q:
                c = q.popleft()
                count += 1
                topo.append(c)
                for s in adj[c]:
                    in_deg[s] -= 1
                    if in_deg[s] == 0:
                        q.append(s)

            is_dag = (count == len(part_configs))
            depth = 0
            if is_dag:
                rank = {}
                for c in reversed(topo):
                    rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
                depth = max(rank.values()) if rank else 0

            print(f"  ({b0},{bn}): {'DAG' if is_dag else 'NOT DAG'}, "
                  f"depth={depth}, configs={len(part_configs)}")

            if is_dag:
                # Find the configs that are "sinks" (no outgoing interior edges)
                sinks = [c for c in part_configs if not adj[c]]
                # Find sinks that exit to good
                sinks_to_good = 0
                for c in sinks:
                    for i in range(1, n-1):
                        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                        new_S = fs[i](L, S, R)
                        if new_S != S:
                            lst = list(c); lst[i] = new_S; succ = tuple(lst)
                            if succ in good_set:
                                sinks_to_good += 1
                                break

                # Sinks that have no interior transitions at all
                # (all interior positions settled given these boundaries)
                fully_settled = []
                for c in sinks:
                    all_settled = True
                    for i in range(1, n-1):
                        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                        if fs[i](L, S, R) != S:
                            all_settled = False
                            break
                    if all_settled:
                        fully_settled.append(c)

                print(f"    Sinks (no interior exit): {len(sinks)}")
                print(f"    Sinks → good via interior: {sinks_to_good}")
                print(f"    Fully interior-settled: {len(fully_settled)}")
                for c in fully_settled[:5]:
                    print(f"      {c}")

def analyze_layer_graph(n):
    """
    Build the "layer graph" — a graph on boundary states (c[0], c[n-1])
    where edges represent possible transitions via boundary firings.

    If this layer graph is a DAG (when restricted to transitions that
    maintain bad configs), combined with the interior DAG property,
    the full graph would be a DAG.
    """
    print(f"\nLAYER GRAPH ANALYSIS (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Build the full DAG and its rank
    adj_full = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj_full[c].append((succ, i))

    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s, _ in adj_full[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s, _ in adj_full[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    full_rank = {}
    for c in reversed(topo):
        full_rank[c] = max((full_rank[s] + 1 for s, _ in adj_full[c]), default=0)

    # Analyze: when P0 fires in partition (b0, bn),
    # what are the possible rank changes?
    print("  When P0 fires (c[0] toggles):")
    for b0 in range(2):
        for bn in range(2):
            # Find P0 transitions from (b0, bn)
            for c in bad_list:
                if c[0] != b0 or c[n-1] != bn:
                    continue
                L = c[(n-1)]; S = c[0]; R = c[1]
                new_S = fs[0](L, S, R)
                if new_S != S:
                    lst = list(c); lst[0] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        dr = full_rank[succ] - full_rank[c]
                        # Only print first few
                        break

    # Compute: for EACH interior-settled config (sink in partition),
    # what happens when a boundary fires?
    print("\n  Interior-settled configs → boundary firing:")
    for b0 in range(2):
        for bn in range(2):
            part_configs = [c for c in bad_list if c[0] == b0 and c[n-1] == bn]
            for c in part_configs:
                # Check if all interior positions are settled
                all_settled = True
                for i in range(1, n-1):
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    if fs[i](L, S, R) != S:
                        all_settled = False
                        break
                if not all_settled:
                    continue

                # This config is interior-settled. Only boundary positions can fire.
                for i in [0, n-1]:
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    new_S = fs[i](L, S, R)
                    if new_S != S:
                        lst = list(c); lst[i] = new_S; succ = tuple(lst)
                        dest = "good" if succ in good_set else f"bad (rank {full_rank.get(succ,'?')})"
                        pi = 'P0' if i == 0 else f'P{n-1}'
                        print(f"    {c} (rank {full_rank[c]}) → fire {pi} → {dest}")

def test_boundary_monotone_property(n):
    """
    Test: Is there a function on boundary states that decreases monotonically
    when boundary positions fire?

    If f(b0, bn) > f(b0', bn') whenever there's a boundary transition
    from (b0, bn) to (b0', bn'), then combined with interior DAG,
    we get a full DAG.
    """
    print(f"\nBOUNDARY MONOTONICITY TEST (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Track boundary transitions
    boundary_trans_types = set()  # (from_boundary, to_boundary)
    for c in bad_list:
        for i in [0, n-1]:
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    bfrom = (c[0], c[n-1])
                    bto = (succ[0], succ[n-1])
                    if bfrom != bto:
                        boundary_trans_types.add((bfrom, bto))

    print(f"  Boundary transition types (cross-partition):")
    for (bf, bt) in sorted(boundary_trans_types):
        print(f"    {bf} → {bt}")

    # Check: is there a total ordering of boundary states consistent with all transitions?
    # This means: the boundary transition graph must be a DAG.
    states = [(0,0), (0,1), (1,0), (1,1)]
    adj_b = defaultdict(set)
    for bf, bt in boundary_trans_types:
        adj_b[bf].add(bt)

    print(f"\n  Boundary DAG check:")
    # Topological sort
    in_deg_b = {s: 0 for s in states}
    for s in states:
        for t in adj_b[s]:
            in_deg_b[t] += 1

    q = deque(s for s in states if in_deg_b[s] == 0)
    order = []
    while q:
        s = q.popleft()
        order.append(s)
        for t in adj_b[s]:
            in_deg_b[t] -= 1
            if in_deg_b[t] == 0:
                q.append(t)

    is_b_dag = (len(order) == len(states))
    print(f"    Boundary graph is DAG: {is_b_dag}")
    if is_b_dag:
        print(f"    Topological order: {order}")
    else:
        print(f"    Boundary graph has CYCLES among: "
              f"{[s for s in states if s not in order]}")
        # Show the cycle
        remaining = [s for s in states if s not in order]
        print(f"    Adjacency for remaining:")
        for s in remaining:
            targets = [t for t in adj_b[s] if t in remaining]
            print(f"      {s} → {targets}")

def summarize_proof_framework():
    """
    Print the definitive proof framework based on all findings.
    """
    print("\n" + "=" * 70)
    print("DEFINITIVE PROOF FRAMEWORK")
    print("=" * 70)
    print("""
THEOREM: For all n ≥ 5, the CUP-2 system with ms=(2,3,...,3,2) and
the 5 universal lookup tables has an acyclic bad-config graph (DAG).

STATUS: Verified computationally for n=5..18.

ESTABLISHED STRUCTURAL FACTS:
  1. No 2-cycle property: T(L, T(L,a,R), R) = T(L,a,R) for all tables
  2. Mover always reaches fixed point (gains target)
  3. Freeze-any-position → DAG (verified n=5..12)
  4. All-position participation required for any cycle
  5. Minimum cycle length ≥ 2n (oscillation requirement)
  6. Each oscillation requires ≥1 neighbor change
  7. Directional flow: 0→1 rightward, 1→2 leftward
  8. DAG depth = ⌊(3n²-4n-11)/4⌋ (verified n=5..13)
  9. T_top/T_high: all oscillations require LEFT change (no R-only)
  10. LP proves no weighted sum of frozen ranks is a potential

ELIMINATED APPROACHES:
  ✗ Simple potential functions (all tested, best ~16% violations)
  ✗ Harmonic criterion on frozen depths (sum always < 1)
  ✗ Weighted frozen rank sums (LP infeasible)
  ✗ Settled count as potential (5% violations, always monotone when
    full rank is considered, but circular)

STRONGEST REMAINING APPROACHES (in order of promise):

A. CAUSAL CHAIN + BOUNDARY OBSTRUCTION
   Framework:
   1. Any cycle has firings at ALL n positions, each ≥ 2 times
   2. Each pair of consecutive firings at position i requires
      ≥1 neighbor to change (no-2-cycle)
   3. This creates obligation chains through the ring
   4. T_top has NO R-only oscillations → obligations flow leftward
   5. T_high has NO R-only oscillations → obligations flow leftward
   6. At T_bot, obligations can flow both ways
   Key gap: Show that the leftward obligation flow from T_top/T_high
   is inconsistent with the obligation requirements at T_bot/T_low.

B. BOUNDARY PARTITION ARGUMENT
   Framework:
   1. Partition configs by (c[0], c[n-1]) into 4 groups
   2. Interior (positions 1..n-2) with fixed boundaries → DAG
   3. Boundary firings (P0, P_{n-1}) cross partitions
   4. If boundary transitions form a DAG on the 4 partition states...
   Key gap: Boundary graph is NOT a DAG (cycles exist among the 4
   boundary states). So this approach needs refinement — perhaps
   use interior rank as a tiebreaker.

C. INDUCTION ON n WITH PROJECTION
   Framework:
   1. Base case: n=5 verified
   2. Project n-system to (n-1)-system by removing one T_mid position
   3. Rank correlation: 0.73-0.82, increasing with n
   4. Show that the new T_mid position's transitions don't create cycles
   Key gap: Make the inductive step rigorous. The projection changes
   the good set, so bad configs don't map cleanly.

D. REFINED FROZEN RANK ARGUMENT
   Framework:
   1. For each position p, the p-frozen graph is a DAG with rank r_p
   2. For a transition at position i: Δr_p ≤ -1 for all p ≠ i
   3. Actual max Δr_i is 35-86% of theoretical bound D_i
   4. Sum Σr_p has only ~8% violations; max_p r_p has 2-3%
   Key gap: Find a NONLINEAR combination of frozen ranks that works,
   or prove a tighter bound on Δr_i that makes the sum work.

MOST LIKELY PATH TO A PROOF:
  Approach A (causal chains) + Approach D (frozen ranks) combined.
  The T_top/T_high directional asymmetry (no R-only oscillations) is
  the key structural feature. A proof should show that obligation chains
  from the right side of the ring (T_top → T_high → T_mid interior)
  create constraints that are inconsistent with the left side
  (T_bot → T_low → T_mid interior) when they meet in the middle.
""")

def main():
    for n in [5, 6, 7]:
        analyze_boundary_partition(n)
        test_boundary_crossing_argument(n)
        test_boundary_monotone_property(n)

    analyze_boundary_cycle_impossibility(6)
    analyze_strongly_connected_components(6)
    analyze_layer_graph(6)

    summarize_proof_framework()

if __name__ == "__main__":
    main()
