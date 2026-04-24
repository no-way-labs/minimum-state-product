#!/usr/bin/env python3
"""Check: on CF boundary steps whose 6-tuple transition is in an SCC,
does Psi ALWAYS strictly decrease?
If yes: use Lex(Psi, DAG-6-tuple-rank) as the CF measure.
DAG = full CF 6-tuple graph minus SCC internal edges."""

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

def frontierTypeVal(a, b):
    if a == b: return 0
    return (b + 3 - a) % 3

def W1(n, j):
    if j + 1 == n: return 0
    if j + 2 == n: return 1
    return j + 1

def W2(n, j):
    if j + 1 == n: return 0
    if j == 0: return n - 1
    return n - 1 - j

def psiWeightVal(n, j, a, b):
    if a == b: return 0
    if frontierTypeVal(a, b) == 1: return W1(n, j)
    return W2(n, j)

def fc(config, n):
    return sum(1 for j in range(n) if config[j] != config[(j+1)%n])

def psi(config, n):
    return sum(psiWeightVal(n, j, config[j], config[(j+1)%n]) for j in range(n))

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

for n in [9, 10, 11, 12, 13]:
    print(f"\n{'='*60}")
    print(f"n={n}")
    good_set = build_good_set(n)
    ff, bad_set = compute_future_fc(n, good_set)

    # Build CF 6-tuple edge graph
    cf_6tuple_edges = set()
    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] != ff[c]:
                continue
            if not is_boundary_pos(n, i):
                continue
            old_6 = get_6tuple(c, n)
            new_6 = get_6tuple(new, n)
            if old_6 != new_6:
                cf_6tuple_edges.add((old_6, new_6))

    # Find SCCs
    cf_nodes = set()
    cf_adj = {}
    for (a, b) in cf_6tuple_edges:
        cf_nodes.add(a)
        cf_nodes.add(b)
        cf_adj.setdefault(a, []).append(b)
    for v in cf_nodes:
        cf_adj.setdefault(v, [])

    sccs = find_sccs(cf_adj, list(cf_nodes))
    nontrivial_sccs = [set(s) for s in sccs if len(s) > 1]

    # Identify SCC edges
    scc_nodes = set()
    for scc in nontrivial_sccs:
        scc_nodes |= scc
    scc_edges = set()
    for (a, b) in cf_6tuple_edges:
        if a in scc_nodes and b in scc_nodes:
            # Check if both in SAME SCC
            for scc in nontrivial_sccs:
                if a in scc and b in scc:
                    scc_edges.add((a, b))
                    break

    print(f"  CF 6-tuple edges: {len(cf_6tuple_edges)}, SCC edges: {len(scc_edges)}")
    print(f"  Non-trivial SCCs: {len(nontrivial_sccs)}")
    for scc in nontrivial_sccs:
        print(f"    SCC of size {len(scc)}: {sorted(scc)[:3]}...")

    # KEY CHECK: on CF boundary steps whose 6-tuple edge is an SCC edge,
    # does Psi ALWAYS strictly decrease?
    scc_psi_ok = 0
    scc_psi_eq = 0
    scc_psi_fail = 0
    scc_fail_examples = []

    # Also check: on CF boundary steps whose 6-tuple edge is NOT an SCC edge,
    # does the remaining DAG have a rank function?
    non_scc_edges = cf_6tuple_edges - scc_edges

    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] != ff[c]:
                continue
            if not is_boundary_pos(n, i):
                continue
            old_6 = get_6tuple(c, n)
            new_6 = get_6tuple(new, n)
            if old_6 == new_6:
                continue
            edge = (old_6, new_6)
            if edge in scc_edges:
                old_psi = psi(c, n)
                new_psi = psi(new, n)
                if new_psi < old_psi:
                    scc_psi_ok += 1
                elif new_psi == old_psi:
                    scc_psi_eq += 1
                else:
                    scc_psi_fail += 1
                    if len(scc_fail_examples) < 3:
                        scc_fail_examples.append((c, i, new, old_6, new_6, old_psi, new_psi))

    print(f"  SCC-edge CF steps: psi↓ {scc_psi_ok}, psi= {scc_psi_eq}, psi↑ {scc_psi_fail}")

    if scc_psi_fail == 0 and scc_psi_eq == 0:
        print(f"  *** Psi STRICTLY DECREASES on ALL SCC-edge CF boundary steps! ***")
    elif scc_psi_fail == 0:
        print(f"  *** Psi NON-INCREASING on SCC-edge CF boundary steps ***")

    for c, i, new, o6, n6, op, np in scc_fail_examples:
        print(f"    FAIL: pos {i}, 6t {o6}->{n6}, psi {op}->{np}, fc {fc(c,n)}->{fc(new,n)}")

    # Check if non-SCC-edge graph is a DAG and compute its rank
    non_scc_adj = {}
    non_scc_nodes = set()
    for (a, b) in non_scc_edges:
        non_scc_nodes.add(a)
        non_scc_nodes.add(b)
        non_scc_adj.setdefault(a, []).append(b)
    for v in non_scc_nodes:
        non_scc_adj.setdefault(v, [])

    non_scc_sccs = find_sccs(non_scc_adj, list(non_scc_nodes))
    non_scc_nontrivial = [s for s in non_scc_sccs if len(s) > 1]
    print(f"  Non-SCC-edge graph: {len(non_scc_edges)} edges, {len(non_scc_nontrivial)} cycles")

    if len(non_scc_nontrivial) == 0:
        # Compute DAG rank
        in_deg = {v: 0 for v in non_scc_nodes}
        for v in non_scc_nodes:
            for w in non_scc_adj.get(v, []):
                if w in in_deg:
                    in_deg[w] += 1
        from collections import deque
        queue = deque([v for v in non_scc_nodes if in_deg[v] == 0])
        rank = {v: 0 for v in non_scc_nodes}
        processed = 0
        while queue:
            v = queue.popleft()
            processed += 1
            for w in non_scc_adj.get(v, []):
                rank[w] = max(rank[w], rank[v] + 1)
                in_deg[w] -= 1
                if in_deg[w] == 0:
                    queue.append(w)
        max_rank = max(rank.values()) if rank else 0
        print(f"  Non-SCC-edge graph IS a DAG! Max rank: {max_rank}")

    # FINAL CHECK: Lex(Psi, non-SCC-DAG-rank) on ALL CF steps
    # Interior: 6-tuple unchanged → Psi must decrease
    # Boundary SCC-edge: Psi must decrease (checked above)
    # Boundary non-SCC-edge: DAG rank decreases OR 6-tuple unchanged (impossible)
    # Need to check: on boundary non-SCC-edge CF steps, does the DAG rank decrease?
    # AND on boundary steps where 6-tuple doesn't change, does Psi decrease?
    # (6-tuple unchanged on boundary fire = 0 cases from earlier check)
