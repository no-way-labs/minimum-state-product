#!/usr/bin/env python3
"""
Part 1: Interior fiber DAG check at n=9
Part 2: FutureFc check at n=10 and n=11
"""

from itertools import product as iproduct
from collections import defaultdict, deque

# === CUP-2 Tables ===
TBot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
TLow = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
THigh = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
TTop = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}


def fire(c, j, n):
    """Fire position j in config c, return new config or None if no change."""
    c = list(c)
    L = c[(j-1) % n]
    S = c[j]
    R = c[(j+1) % n]
    if j == 0:
        new_val = TBot[(L, S, R)]
    elif j == 1:
        new_val = TLow[(L, S, R)]
    elif j == n - 2:
        new_val = THigh[(L, S, R)]
    elif j == n - 1:
        new_val = TTop[(L, S, R)]
    else:
        new_val = TMid[(L, S, R)]
    if new_val == S:
        return None
    c[j] = new_val
    return tuple(c)


def compute_fc(c, n):
    """Count fixed points (positions where firing doesn't change state)."""
    count = 0
    for j in range(n):
        if fire(c, j, n) is None:
            count += 1
    return count


# ============================================================
# Part 1: Interior fiber DAG check at n=9
# ============================================================
def part1():
    print("=" * 60)
    print("PART 1: Interior fiber DAG check at n=9")
    print("=" * 60)

    n = 9
    interior_positions = [3, 4, 5]

    # Enumerate all 324 6-tuples: (c0,c1,c2,c6,c7,c8)
    # c0, c8 in {0,1}; c1,c2,c6,c7 in {0,1,2}
    six_tuples = []
    for c0 in range(2):
        for c1 in range(3):
            for c2 in range(3):
                for c6 in range(3):
                    for c7 in range(3):
                        for c8 in range(2):
                            six_tuples.append((c0, c1, c2, c6, c7, c8))

    print(f"Number of 6-tuples: {len(six_tuples)}")

    fibers_with_cycles = 0
    max_rank = -1
    max_rank_fibers = []

    for st in six_tuples:
        c0, c1, c2, c6, c7, c8 = st

        # Build all 27 configs in this fiber
        configs = []
        config_to_idx = {}
        for c3, c4, c5 in iproduct(range(3), repeat=3):
            cfg = (c0, c1, c2, c3, c4, c5, c6, c7, c8)
            idx = len(configs)
            configs.append(cfg)
            config_to_idx[cfg] = idx

        # Build adjacency list: fire at interior positions only
        adj = defaultdict(list)
        for cfg in configs:
            for j in interior_positions:
                result = fire(cfg, j, n)
                if result is not None:
                    # Check result is in the same fiber
                    if result in config_to_idx:
                        adj[config_to_idx[cfg]].append(config_to_idx[result])

        # Iterative Tarjan SCC
        num_nodes = len(configs)
        index_counter = [0]
        stack = []
        on_stack = [False] * num_nodes
        index = [-1] * num_nodes
        lowlink = [-1] * num_nodes
        sccs = []

        for start in range(num_nodes):
            if index[start] != -1:
                continue
            # Iterative DFS
            work_stack = [(start, 0)]  # (node, neighbor_index)
            while work_stack:
                v, ni = work_stack[-1]
                if index[v] == -1:
                    index[v] = lowlink[v] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(v)
                    on_stack[v] = True

                neighbors = adj.get(v, [])
                if ni < len(neighbors):
                    work_stack[-1] = (v, ni + 1)
                    w = neighbors[ni]
                    if index[w] == -1:
                        work_stack.append((w, 0))
                    elif on_stack[w]:
                        lowlink[v] = min(lowlink[v], index[w])
                else:
                    # Done with v
                    if lowlink[v] == index[v]:
                        scc = []
                        while True:
                            w = stack.pop()
                            on_stack[w] = False
                            scc.append(w)
                            if w == v:
                                break
                        sccs.append(scc)
                    work_stack.pop()
                    if work_stack:
                        parent = work_stack[-1][0]
                        lowlink[parent] = min(lowlink[parent], lowlink[v])

        has_cycle = any(len(scc) > 1 for scc in sccs)
        # Also check self-loops
        if not has_cycle:
            for v in range(num_nodes):
                if v in adj and v in adj[v]:
                    has_cycle = True
                    break

        if has_cycle:
            fibers_with_cycles += 1

        # Compute DAG rank (longest path) via topological order
        # Condense SCCs
        scc_id = [0] * num_nodes
        for i, scc in enumerate(sccs):
            for v in scc:
                scc_id[v] = i

        num_sccs = len(sccs)
        dag_adj = defaultdict(set)
        for v in range(num_nodes):
            for w in adj.get(v, []):
                if scc_id[v] != scc_id[w]:
                    dag_adj[scc_id[v]].add(scc_id[w])

        # Topological sort + longest path
        in_deg = [0] * num_sccs
        for u in range(num_sccs):
            for v in dag_adj[u]:
                in_deg[v] += 1

        queue = deque()
        dist = [0] * num_sccs
        for i in range(num_sccs):
            if in_deg[i] == 0:
                queue.append(i)

        while queue:
            u = queue.popleft()
            for v in dag_adj[u]:
                if dist[u] + 1 > dist[v]:
                    dist[v] = dist[u] + 1
                in_deg[v] -= 1
                if in_deg[v] == 0:
                    queue.append(v)

        rank = max(dist) if dist else 0

        if rank > max_rank:
            max_rank = rank
            max_rank_fibers = [st]
        elif rank == max_rank:
            max_rank_fibers.append(st)

    print(f"\nFibers with cycles: {fibers_with_cycles} / {len(six_tuples)}")
    print(f"Max DAG rank (longest path in condensed DAG): {max_rank}")
    print(f"Number of fibers achieving max rank: {len(max_rank_fibers)}")
    if len(max_rank_fibers) <= 20:
        print(f"Fibers achieving max rank (c0,c1,c2,c6,c7,c8):")
        for f in max_rank_fibers:
            print(f"  {f}")
    else:
        print(f"First 10 fibers achieving max rank:")
        for f in max_rank_fibers[:10]:
            print(f"  {f}")

    # Also compute max rank considering SCC sizes (if cycles exist)
    # Report individual node longest path for DAG fibers
    if fibers_with_cycles == 0:
        print("\nAll fibers are DAGs! Recomputing max rank as longest path in node graph...")
        global_max_rank = -1
        global_max_fibers = []

        for st in six_tuples:
            c0, c1, c2, c6, c7, c8 = st
            configs = []
            config_to_idx = {}
            for c3, c4, c5 in iproduct(range(3), repeat=3):
                cfg = (c0, c1, c2, c3, c4, c5, c6, c7, c8)
                idx = len(configs)
                configs.append(cfg)
                config_to_idx[cfg] = idx

            adj = defaultdict(list)
            for cfg in configs:
                for j in interior_positions:
                    result = fire(cfg, j, n)
                    if result is not None and result in config_to_idx:
                        adj[config_to_idx[cfg]].append(config_to_idx[result])

            # Longest path via topological sort (memoization)
            num = len(configs)
            in_deg = [0] * num
            for u in range(num):
                for v in adj.get(u, []):
                    in_deg[v] += 1

            queue = deque()
            dist = [0] * num
            for i in range(num):
                if in_deg[i] == 0:
                    queue.append(i)

            while queue:
                u = queue.popleft()
                for v in adj.get(u, []):
                    if dist[u] + 1 > dist[v]:
                        dist[v] = dist[u] + 1
                    in_deg[v] -= 1
                    if in_deg[v] == 0:
                        queue.append(v)

            rank = max(dist) if dist else 0
            if rank > global_max_rank:
                global_max_rank = rank
                global_max_fibers = [st]
            elif rank == global_max_rank:
                global_max_fibers.append(st)

        print(f"Max node-level DAG rank (longest path): {global_max_rank}")
        print(f"Number of fibers achieving max rank: {len(global_max_fibers)}")
        if len(global_max_fibers) <= 20:
            for f in global_max_fibers:
                print(f"  {f}")
        else:
            print(f"  (showing first 10)")
            for f in global_max_fibers[:10]:
                print(f"  {f}")


# ============================================================
# Part 2: FutureFc check at n=10 and n=11
# ============================================================
def part2():
    print("\n" + "=" * 60)
    print("PART 2: FutureFc check at n=10 and n=11")
    print("=" * 60)

    for n in [10, 11]:
        print(f"\n--- n = {n} ---")

        # Generate all configs: c[0],c[n-1] in {0,1}; c[1]..c[n-2] in {0,1,2}
        all_configs = []
        for c0 in range(2):
            for cn1 in range(2):
                for interior in iproduct(range(3), repeat=n-2):
                    cfg = (c0,) + interior + (cn1,)
                    all_configs.append(cfg)

        print(f"Total configs: {len(all_configs)}")

        # Compute fc for all configs
        fc_map = {}
        for cfg in all_configs:
            fc_map[cfg] = compute_fc(cfg, n)

        max_fc = max(fc_map.values())
        print(f"Max fc: {max_fc}")

        # Identify good configs (fc == n)
        good_configs = [c for c, f in fc_map.items() if f == n]
        print(f"Good configs (fc=n={n}): {len(good_configs)}")
        expected_good = (n + 2) * (n + 3) // 2 - 5
        print(f"Expected good = (n+2)(n+3)/2 - 5 = {expected_good}")

        # Trace good cycle from all-zeros
        start = tuple([0] * n)
        cycle = [start]
        visited = {start}
        current = start
        while True:
            # Find the mover: the position that fires
            moved = False
            for j in range(n):
                result = fire(current, j, n)
                if result is not None and compute_fc(result, n) == n:
                    if result not in visited or (len(cycle) > 1 and result == start):
                        current = result
                        if current == start:
                            moved = True
                            break
                        cycle.append(current)
                        visited.add(current)
                        moved = True
                        break
            if not moved or current == start:
                break

        cycle_len = len(cycle)
        expected_cycle_len = 3 * n - 2
        print(f"Good cycle length: {cycle_len} (expected 3n-2 = {expected_cycle_len})")

        good_set = set(good_configs)
        bad_configs = [c for c in all_configs if c not in good_set]
        print(f"Bad configs: {len(bad_configs)}")

        # Compute FutureFc via fixpoint iteration
        # FutureFc(c) = max fc reachable from c among bad configs,
        # or fc(c) if c is good
        # Actually: FutureFc(c) = max over all configs reachable from c of fc
        # For good configs, FutureFc = n
        # For bad configs, FutureFc(c) = max(fc(c'), over all c' reachable from c via single steps)
        # But we want the MAXIMUM fc reachable (possibly through many steps)

        # Build full successor map (all positions can fire)
        successors = defaultdict(set)
        for cfg in all_configs:
            for j in range(n):
                result = fire(cfg, j, n)
                if result is not None:
                    successors[cfg].add(result)

        # FutureFc(c) = max fc among all configs reachable from c (including c itself)
        # Initialize
        future_fc = {}
        for cfg in all_configs:
            future_fc[cfg] = fc_map[cfg]

        # Fixpoint: propagate backwards
        # If c -> c', then FutureFc(c) >= FutureFc(c')
        # Build reverse graph
        predecessors = defaultdict(set)
        for cfg in all_configs:
            for succ in successors[cfg]:
                predecessors[succ].add(cfg)

        # BFS from high-fc configs backwards
        changed = True
        iterations = 0
        while changed:
            changed = False
            iterations += 1
            for cfg in all_configs:
                for succ in successors[cfg]:
                    if future_fc[succ] > future_fc[cfg]:
                        future_fc[cfg] = future_fc[succ]
                        changed = True
            if iterations > 100:
                print(f"WARNING: fixpoint not reached after {iterations} iterations")
                break

        print(f"Fixpoint reached after {iterations} iterations")

        # Analyze FutureFc on bad configs
        bad_future_fc = [future_fc[c] for c in bad_configs]
        from collections import Counter
        fc_counts = Counter(bad_future_fc)
        print(f"FutureFc distribution on bad configs: {dict(sorted(fc_counts.items()))}")

        distinct_values = sorted(set(bad_future_fc))
        print(f"Distinct FutureFc values on bad configs: {distinct_values}")

        if len(distinct_values) == 1:
            print(f"FutureFc is CONSTANT = {distinct_values[0]} on all bad configs")
        else:
            print(f"FutureFc VARIES: {len(distinct_values)} distinct values")

        # Also check: is FutureFc always == n for all configs?
        all_future = set(future_fc[c] for c in all_configs)
        print(f"FutureFc values across ALL configs: {sorted(all_future)}")


if __name__ == "__main__":
    part1()
    part2()
