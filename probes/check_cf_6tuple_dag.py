#!/usr/bin/env python3
"""Extract the actual 6-tuple transitions occurring on CF boundary steps.
Check if they form a DAG. If yes, compute the DAG rank.
Compare across n values for n-independence."""

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def get_ms(n):
    ms = [3]*n; ms[0] = 2; ms[n-1] = 2; return ms

def get_trans(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

def frontierBitVal(a, b):
    return 0 if a == b else 1

def fc(config, n):
    return sum(frontierBitVal(config[j], config[(j+1)%n]) for j in range(n))

def fire(config, n, i):
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    new_config = list(config); new_config[i] = new_S
    return tuple(new_config)

def get_6tuple(config, n):
    return (config[0], config[1], config[2], config[n-3], config[n-2], config[n-1])

def is_boundary_pos(n, i):
    return i <= 2 or i >= n-3

def build_good_set(n):
    config = tuple([0] * n)
    good = {config}
    cur = list(config)
    for phase in range(3):
        rng = range(n) if phase % 2 == 0 else range(n-1, -1, -1)
        for i in rng:
            new = fire(tuple(cur), n, i)
            if new is not None:
                cur = list(new)
                good.add(tuple(cur))
    return good

def compute_future_fc(n, good_set):
    ms = get_ms(n)
    from itertools import product as iproduct
    all_configs = list(iproduct(*[range(m) for m in ms]))
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)
    adj = {}
    for c in bad_configs:
        adj[c] = []
        for i in range(n):
            new = fire(c, n, i)
            if new is not None and new in bad_set:
                adj[c].append(new)
    ff = {c: fc(c, n) for c in bad_configs}
    changed = True
    iters = 0
    while changed:
        changed = False
        iters += 1
        for c in bad_configs:
            for s in adj[c]:
                if ff[s] > ff[c]:
                    ff[c] = ff[s]
                    changed = True
        if iters > len(bad_configs):
            break
    return ff, bad_set

def find_sccs(adj_list, nodes):
    """Tarjan's SCC algorithm."""
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for w in adj_list.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in nodes:
        if v not in index:
            strongconnect(v)
    return sccs

def compute_dag_rank(adj_list, nodes):
    """Compute DAG rank (longest path from any source) via topological order."""
    # In-degree
    in_deg = {v: 0 for v in nodes}
    for v in nodes:
        for w in adj_list.get(v, []):
            if w in in_deg:
                in_deg[w] = in_deg.get(w, 0) + 1
    # Topo sort (Kahn's)
    from collections import deque
    queue = deque([v for v in nodes if in_deg[v] == 0])
    rank = {v: 0 for v in nodes}
    order = []
    while queue:
        v = queue.popleft()
        order.append(v)
        for w in adj_list.get(v, []):
            if w in in_deg:
                in_deg[w] -= 1
                rank[w] = max(rank[w], rank[v] + 1)
                if in_deg[w] == 0:
                    queue.append(w)
    if len(order) != len(nodes):
        return None  # Has cycle
    return rank

for n in [9, 10, 11, 12]:
    print(f"\n{'='*60}")
    print(f"n={n}")
    good_set = build_good_set(n)
    ff, bad_set = compute_future_fc(n, good_set)

    from itertools import product as iproduct

    # Extract 6-tuple transitions on CF boundary steps
    cf_6tuple_edges = set()
    all_bad_6tuple_edges = set()

    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if not is_boundary_pos(n, i):
                continue
            old_6 = get_6tuple(c, n)
            new_6 = get_6tuple(new, n)
            if old_6 == new_6:
                continue  # no 6-tuple change
            all_bad_6tuple_edges.add((old_6, new_6))
            if ff[new] == ff[c]:  # CF step
                cf_6tuple_edges.add((old_6, new_6))

    print(f"  All bad boundary 6-tuple edges: {len(all_bad_6tuple_edges)}")
    print(f"  CF boundary 6-tuple edges: {len(cf_6tuple_edges)}")

    # Check if CF edges form a DAG
    cf_nodes = set()
    cf_adj = {}
    for (a, b) in cf_6tuple_edges:
        cf_nodes.add(a)
        cf_nodes.add(b)
        cf_adj.setdefault(a, []).append(b)
    for v in cf_nodes:
        cf_adj.setdefault(v, [])

    sccs = find_sccs(cf_adj, list(cf_nodes))
    nontrivial_sccs = [s for s in sccs if len(s) > 1]
    # Also check self-loops
    self_loops = sum(1 for (a,b) in cf_6tuple_edges if a == b)

    print(f"  CF 6-tuple nodes: {len(cf_nodes)}, edges: {len(cf_6tuple_edges)}")
    print(f"  Non-trivial SCCs: {len(nontrivial_sccs)}, self-loops: {self_loops}")

    if len(nontrivial_sccs) == 0 and self_loops == 0:
        rank = compute_dag_rank(cf_adj, list(cf_nodes))
        max_rank = max(rank.values()) if rank else 0
        print(f"  CF 6-tuple graph IS a DAG! Max rank: {max_rank}")
    else:
        print(f"  CF 6-tuple graph has CYCLES!")
        for scc in nontrivial_sccs[:3]:
            print(f"    SCC of size {len(scc)}: {scc[:5]}...")

    # Also check: among CF boundary steps with 6-tuple UNCHANGED, what happens?
    cf_boundary_6tuple_same = 0
    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] != ff[c]:
                continue
            if not is_boundary_pos(n, i):
                continue
            if get_6tuple(c, n) == get_6tuple(new, n):
                cf_boundary_6tuple_same += 1
    print(f"  CF boundary steps with 6-tuple unchanged: {cf_boundary_6tuple_same}")
