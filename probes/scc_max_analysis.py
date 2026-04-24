"""For each TP SCC in the far period-3 no-copy regime:
1. Does the SCC contain an SA-reachable state (from c)?
2. Is the max fc in the SCC attained at an SA-reachable state?

SA-reachable = reachable from c using only non-seam steps.
"""

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

def fb(a, b): return 1 if a != b else 0
def fc(c): return sum(fb(c[j], c[(j+1) % len(c)]) for j in range(len(c)))

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

for n, k in [(11, 5), (12, 5)]:
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

        # Build TP graph
        visited = {c}; queue = [c]; adj = {}
        while queue:
            cfg = queue.pop(0)
            adj[cfg] = []
            for j in range(n):
                d = move(cfg, j)
                if d is not None:
                    adj[cfg].append(d)
                    if d not in visited:
                        visited.add(d); queue.append(d)

        # SA-reachable from c
        sa_set = {c}; queue = [c]
        while queue:
            cfg = queue.pop(0)
            for j in range(n):
                if j in seam: continue
                d = move(cfg, j)
                if d is not None and d not in sa_set:
                    sa_set.add(d); queue.append(d)

        # SCC
        sccs = kosaraju_scc(visited, adj)
        scc_map = {}
        for i, scc in enumerate(sccs):
            for cfg in scc:
                scc_map[cfg] = i

        # For each SCC: check if it contains an SA state and if max fc is at an SA state
        scc_violations = 0
        scc_no_sa = 0
        total_nontrivial = 0
        for scc in sccs:
            if len(scc) <= 1: continue
            total_nontrivial += 1
            scc_set = set(scc)
            sa_in_scc = [cfg for cfg in scc if cfg in sa_set]
            max_fc_scc = max(fc(cfg) for cfg in scc)
            max_fc_sa_in_scc = max(fc(cfg) for cfg in sa_in_scc) if sa_in_scc else -1

            if not sa_in_scc:
                scc_no_sa += 1
                # Does this SCC have fc > max_SA(c)?
                max_sa = max(fc(cfg) for cfg in sa_set)
                if max_fc_scc > max_sa:
                    scc_violations += 1
                    print(f"  SCC VIOLATION: size={len(scc)}, max_fc={max_fc_scc}, max_sa={max_sa}")
            elif max_fc_sa_in_scc < max_fc_scc:
                # SCC has SA states but they don't achieve the max fc
                scc_violations += 1

        max_sa_global = max(fc(cfg) for cfg in sa_set)
        phi_full = max(fc(cfg) for cfg in visited)
        print(f"  c[4:7]={c[4:7]}, |TP|={len(visited)}, |SA|={len(sa_set)}")
        print(f"  PhiFull={phi_full}, max_SA={max_sa_global}")
        print(f"  Nontrivial SCCs: {total_nontrivial}")
        print(f"  SCCs with no SA state: {scc_no_sa}")
        print(f"  SCC fc violations: {scc_violations}")
        if scc_violations == 0:
            print(f"  ✓ Every SCC's max fc is attained at an SA-reachable state")
