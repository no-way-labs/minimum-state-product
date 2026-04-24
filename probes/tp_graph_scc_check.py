"""Check whether the TP graph in the far period-3 no-copy regime has SCCs.
For c with noDeepCopyPair and cycling site k (far: k+6 <= n):
1. Build the TP graph (configs as nodes, TP-bad steps as edges)
2. Find SCCs using Tarjan's algorithm
3. Report whether any nontrivial SCC exists
4. Check if seam steps strictly decrease |TpReachableSet| or some other measure
"""

def cup2OutVal(n, j, L, S, R):
    if j == 0: return (S + 1) % 2
    if j == 1:
        tbl = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
        return tbl.get((S, R), S)
    if j + 2 == n:
        tbl = {(0,0,0):1,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):1,
               (1,0,0):1,(1,0,1):1,(1,1,0):0,(1,1,1):2,(1,2,0):1,(1,2,1):1,
               (2,0,0):2,(2,0,1):2,(2,1,0):2,(2,1,1):0,(2,2,0):0,(2,2,1):2}
        return tbl.get((L, S, R), S)
    if j + 1 == n: return (S + 1) % 2
    TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
            (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
            (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
            (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
            (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return TMid.get((L, S, R), S)

def fb(a, b): return 1 if a != b else 0
def fc(c): return sum(fb(c[j], c[(j+1) % len(c)]) for j in range(len(c)))

def move(c, j):
    n = len(c)
    L, S, R = c[(j-1)%n], c[j], c[(j+1)%n]
    out = cup2OutVal(n, j, L, S, R)
    if out == S: return None
    return tuple(c[i] if i != j else out for i in range(n))

def tp_successors(c):
    succs = []
    for j in range(len(c)):
        d = move(c, j)
        if d is not None:
            succs.append((d, j))  # (successor, mover position)
    return succs

def tarjan_scc(nodes, adj):
    """Tarjan's SCC algorithm. adj: node -> list of successor nodes."""
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
        for w in adj.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in nodes:
        if v not in index:
            strongconnect(v)
    return sccs

# Check n=11, k=5 (far case)
for n, k in [(11, 5), (12, 5), (11, 6)]:
    if k + 6 > n: continue
    seam = {k-1, k, k+1}
    print(f"\n=== n={n}, k={k}, seam={seam} ===")

    for start in range(3):
        c = [0]*n; c[0] = 0; c[n-1] = 0
        for j in range(1, n-1): c[j] = (start + j) % 3
        c = tuple(c)
        ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
        if not ok: continue
        if c[k-1] == c[k+1]: continue

        # Build TP graph from c
        visited = {c}
        queue = [c]
        adj = {}
        seam_edges = 0
        while queue:
            cfg = queue.pop(0)
            adj[cfg] = []
            for d, j in tp_successors(cfg):
                adj[cfg].append(d)
                if j in seam:
                    seam_edges += 1
                if d not in visited:
                    visited.add(d)
                    queue.append(d)

        # Find SCCs
        sccs = tarjan_scc(visited, adj)
        nontrivial = [s for s in sccs if len(s) > 1]

        # Check: do seam steps strictly decrease |TpReachable|?
        seam_strict = True
        for cfg in visited:
            for d, j in tp_successors(cfg):
                if j not in seam: continue
                # Check |TpReachable(d)| < |TpReachable(cfg)|
                reach_cfg = set()
                q = [cfg]; reach_cfg.add(cfg)
                while q:
                    x = q.pop(0)
                    for y, _ in tp_successors(x):
                        if y not in reach_cfg:
                            reach_cfg.add(y); q.append(y)
                reach_d = set()
                q = [d]; reach_d.add(d)
                while q:
                    x = q.pop(0)
                    for y, _ in tp_successors(x):
                        if y not in reach_d:
                            reach_d.add(y); q.append(y)
                if len(reach_d) >= len(reach_cfg):
                    seam_strict = False

        # Also check: does fc strictly decrease at seam steps?
        fc_strict_seam = True
        fc_equal_seam = 0
        for cfg in visited:
            for d, j in tp_successors(cfg):
                if j not in seam: continue
                if fc(d) >= fc(cfg):
                    fc_strict_seam = False
                if fc(d) == fc(cfg):
                    fc_equal_seam += 1

        print(f"  c={c}")
        print(f"  |TP-reachable|={len(visited)}, |edges|={sum(len(v) for v in adj.values())}, seam_edges={seam_edges}")
        print(f"  SCCs: {len(sccs)} total, {len(nontrivial)} nontrivial (size>1)")
        if nontrivial:
            sizes = sorted([len(s) for s in nontrivial], reverse=True)
            print(f"  Nontrivial SCC sizes: {sizes[:5]}{'...' if len(sizes)>5 else ''}")
        print(f"  Seam steps strictly decrease |TpReachable|: {seam_strict}")
        print(f"  Seam steps strictly decrease fc: {fc_strict_seam} (fc-equal seam steps: {fc_equal_seam})")
