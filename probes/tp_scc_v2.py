"""TP graph SCC check — iterative Tarjan, skip expensive reachability check."""
import sys
sys.setrecursionlimit(100000)

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

def tp_graph(c):
    """Build TP graph by BFS from c. Returns (visited, adj)."""
    visited = {c}
    queue = [c]
    adj = {}
    while queue:
        cfg = queue.pop(0)
        succs = []
        for j in range(len(cfg)):
            d = move(cfg, j)
            if d is not None:
                succs.append((d, j))
                if d not in visited:
                    visited.add(d)
                    queue.append(d)
        adj[cfg] = succs
    return visited, adj

def kosaraju_scc(nodes, adj):
    """Kosaraju's SCC algorithm (iterative)."""
    # Step 1: compute finish order by DFS
    visited = set()
    finish = []
    for start in nodes:
        if start in visited: continue
        stack = [(start, False)]
        while stack:
            v, processed = stack.pop()
            if processed:
                finish.append(v)
                continue
            if v in visited: continue
            visited.add(v)
            stack.append((v, True))
            for d, _ in adj.get(v, []):
                if d not in visited:
                    stack.append((d, False))
    # Step 2: build reverse graph
    radj = {v: [] for v in nodes}
    for v in nodes:
        for d, _ in adj.get(v, []):
            radj[d].append(v)
    # Step 3: DFS on reverse in reverse finish order
    visited2 = set()
    sccs = []
    for v in reversed(finish):
        if v in visited2: continue
        scc = []
        stack = [v]
        while stack:
            w = stack.pop()
            if w in visited2: continue
            visited2.add(w)
            scc.append(w)
            for u in radj[w]:
                if u not in visited2:
                    stack.append(u)
        sccs.append(scc)
    return sccs

n, k = 11, 5
seam = {k-1, k, k+1}
print(f"n={n}, k={k}, seam={seam}")

for start in range(3):
    c = [0]*n; c[0] = 0; c[n-1] = 0
    for j in range(1, n-1): c[j] = (start + j) % 3
    c = tuple(c)
    ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
    if not ok: continue
    if c[k-1] == c[k+1]: continue

    visited, adj = tp_graph(c)
    sccs = kosaraju_scc(visited, adj)
    nontrivial = [s for s in sccs if len(s) > 1]

    # Check fc at seam steps
    fc_seam_stats = {"strict_drop": 0, "equal": 0, "increase": 0}
    for cfg in visited:
        for d, j in adj[cfg]:
            if j not in seam: continue
            if fc(d) < fc(cfg): fc_seam_stats["strict_drop"] += 1
            elif fc(d) == fc(cfg): fc_seam_stats["equal"] += 1
            else: fc_seam_stats["increase"] += 1

    print(f"\n  c={c}")
    print(f"  |TP-reachable|={len(visited)}")
    print(f"  SCCs: {len(sccs)} total, {len(nontrivial)} nontrivial")
    if nontrivial:
        sizes = sorted([len(s) for s in nontrivial], reverse=True)
        print(f"  Nontrivial SCC sizes: {sizes[:10]}{'...' if len(sizes)>10 else ''}")
        # Show a small SCC
        small = min(nontrivial, key=len)
        print(f"  Smallest nontrivial SCC ({len(small)} configs):")
        for cfg in small[:3]:
            print(f"    {cfg} fc={fc(cfg)}")
        # Check if SCC contains seam edges
        scc_set = set(map(tuple, small))
        seam_in_scc = 0
        for cfg in small:
            for d, j in adj[cfg]:
                if d in scc_set and j in seam:
                    seam_in_scc += 1
        print(f"    Seam edges within SCC: {seam_in_scc}")
    print(f"  Seam step fc stats: {fc_seam_stats}")
