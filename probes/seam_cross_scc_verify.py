"""Verify: ALL seam edges are cross-SCC edges (never within a TP-SCC).
This is the key fact for the seam pruning proof."""

import sys; sys.setrecursionlimit(200000)

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

def move(c, j):
    n = len(c)
    L, S, R = c[(j-1)%n], c[j], c[(j+1)%n]
    out = cup2OutVal(n, j, L, S, R)
    if out == S: return None
    return tuple(c[i] if i != j else out for i in range(n))

def kosaraju_scc(nodes, adj_list):
    visited = set(); finish = []
    for start in nodes:
        if start in visited: continue
        stack = [(start, False)]
        while stack:
            v, done = stack.pop()
            if done: finish.append(v); continue
            if v in visited: continue
            visited.add(v); stack.append((v, True))
            for d in adj_list.get(v, []):
                if d not in visited: stack.append((d, False))
    radj = {v: [] for v in nodes}
    for v in nodes:
        for d in adj_list.get(v, []):
            radj[d].append(v)
    visited2 = set(); sccs = []
    for v in reversed(finish):
        if v in visited2: continue
        scc = []
        stack = [v]
        while stack:
            w = stack.pop()
            if w in visited2: continue
            visited2.add(w); scc.append(w)
            for u in radj[w]:
                if u not in visited2: stack.append(u)
        sccs.append(scc)
    return sccs

# Check for multiple n, k values
for n, k in [(11, 5), (12, 5), (12, 6)]:
    if k + 6 > n: continue
    seam = {k-1, k, k+1}
    print(f"\nn={n}, k={k}, seam={seam}")

    for start in range(3):
        c = [0]*n; c[0] = 0; c[n-1] = 0
        for j in range(1, n-1): c[j] = (start + j) % 3
        c = tuple(c)
        ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
        if not ok: continue
        if c[k-1] == c[k+1]: continue

        # Build TP graph
        visited = {c}; queue = [c]; adj_full = {}; adj_simple = {}
        seam_info = []
        while queue:
            cfg = queue.pop(0)
            adj_full[cfg] = []; adj_simple[cfg] = []
            for j in range(n):
                d = move(cfg, j)
                if d is not None:
                    adj_full[cfg].append((d, j))
                    adj_simple[cfg].append(d)
                    if d not in visited:
                        visited.add(d); queue.append(d)

        # SCC
        sccs = kosaraju_scc(visited, adj_simple)
        scc_map = {}
        for i, scc in enumerate(sccs):
            for cfg in scc:
                scc_map[cfg] = i

        # Check seam edges: are they always cross-SCC?
        seam_within = 0
        seam_cross = 0
        for cfg in visited:
            for d, j in adj_full[cfg]:
                if j not in seam: continue
                if scc_map[cfg] == scc_map[d]:
                    seam_within += 1
                else:
                    seam_cross += 1

        nontrivial = sum(1 for s in sccs if len(s) > 1)
        print(f"  c[4:7]={c[4:7]}, |TP|={len(visited)}, SCCs={len(sccs)}, nontrivial={nontrivial}")
        print(f"  Seam edges: {seam_within} within-SCC, {seam_cross} cross-SCC")
        if seam_within > 0:
            print(f"  *** SEAM WITHIN SCC FOUND! ***")
        else:
            print(f"  ✓ All seam edges are cross-SCC")
