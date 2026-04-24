#!/usr/bin/env python3
"""
Check if we can prove badStep WF via nonneg/neg decomposition with wf_of_copy_segment_wf.

The segment relation: fun y x => exists z, nonneg^*(z, x) ∧ neg(y, z)
We need some measure m with m(y) < m(x) for all (y, x) in the segment relation.

Check various candidate measures.
"""

from itertools import product as cartesian
from collections import defaultdict

# LEAN TABLES
def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
         (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
         (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
         (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def make_system(n):
    ms = [2] + [3]*(n-2) + [2]

    def get_table(i):
        if i == 0: return TBotVal
        elif i == 1: return TLowVal
        elif i + 1 == n: return TTopVal
        elif i + 2 == n: return THighVal
        else: return TMidVal

    def fc(c):
        return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

    def psi_term(c, j):
        """PsiTerm: 1 if c[j] != c[(j+1)%n] AND c[j] != c[(j-1)%n], else 0"""
        return 1 if c[j] != c[(j+1)%n] and c[j] != c[(j-1)%n] else 0

    def psi(c):
        return sum(psi_term(c, j) for j in range(n))

    def step(c, i):
        L = c[(i-1) % n]
        S = c[i]
        R = c[(i+1) % n]
        out = get_table(i)(L, S, R)
        if out != S:
            new_c = list(c)
            new_c[i] = out
            return tuple(new_c)
        return None

    all_configs = list(cartesian(*(range(m) for m in ms)))

    all_succ = defaultdict(list)
    for c in all_configs:
        for i in range(n):
            succ = step(c, i)
            if succ is not None:
                all_succ[c].append(succ)

    # Find good cycle
    def tarjan(nodes, adj):
        idx = [0]; stack = []; lowlink = {}; index_map = {}; on_stack = set(); sccs = []
        for start in nodes:
            if start in index_map: continue
            cs = [(start, iter(adj.get(start, [])))]
            index_map[start] = lowlink[start] = idx[0]; idx[0] += 1
            stack.append(start); on_stack.add(start)
            while cs:
                v, ch = cs[-1]
                try:
                    w = next(ch)
                    if w not in index_map:
                        index_map[w] = lowlink[w] = idx[0]; idx[0] += 1
                        stack.append(w); on_stack.add(w)
                        cs.append((w, iter(adj.get(w, []))))
                    elif w in on_stack:
                        lowlink[v] = min(lowlink[v], index_map[w])
                except StopIteration:
                    cs.pop()
                    if cs: lowlink[cs[-1][0]] = min(lowlink[cs[-1][0]], lowlink[v])
                    if lowlink[v] == index_map[v]:
                        scc = []
                        while True:
                            w = stack.pop(); on_stack.discard(w); scc.append(w)
                            if w == v: break
                        sccs.append(scc)
        return sccs

    sccs = tarjan(all_configs, all_succ)
    terminal = []
    for i, scc in enumerate(sccs):
        scc_set = set(scc)
        if not any(w not in scc_set for v in scc for w in all_succ.get(v, [])):
            terminal.append(i)

    good_set = set(sccs[terminal[0]])
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)

    bad_edges = []
    for c in bad_configs:
        for succ in all_succ.get(c, []):
            if succ in bad_set:
                bad_edges.append((c, succ))

    return bad_configs, bad_set, bad_edges, fc, psi, n

for test_n in [5, 6, 7, 9]:
    bad_configs, bad_set, bad_edges, fc_fn, psi_fn, n = make_system(test_n)
    print(f"\n=== n={test_n}: {len(bad_configs)} bad configs, {len(bad_edges)} bad edges ===")

    # Classify edges
    nonneg_edges = [(c,s) for c,s in bad_edges if fc_fn(s) >= fc_fn(c)]
    neg_edges = [(c,s) for c,s in bad_edges if fc_fn(s) < fc_fn(c)]
    print(f"  Nonneg edges: {len(nonneg_edges)}, Neg edges: {len(neg_edges)}")

    # Build nonneg reachability
    nonneg_adj = defaultdict(list)
    for c, s in nonneg_edges:
        nonneg_adj[c].append(s)

    # Compute nonneg_measure = (n - fc) * PSIMAX + psi
    # Actually, let's just compute nonneg reachable set for each config
    # and find all segments

    # For the segment relation: (y, x) if exists z reachable from x via nonneg, and neg(y, z)
    # Check: does fc(y) < fc(x)?

    # Compute max fc reachable via nonneg from each config
    max_fc_nonneg = {}
    for c in bad_configs:
        visited = {c}
        queue = [c]
        max_fc = fc_fn(c)
        qi = 0
        while qi < len(queue):
            v = queue[qi]; qi += 1
            for w in nonneg_adj.get(v, []):
                if w not in visited:
                    visited.add(w)
                    queue.append(w)
                    fv = fc_fn(w)
                    if fv > max_fc:
                        max_fc = fv
        max_fc_nonneg[c] = max_fc

    # Now check the segment relation:
    # For each x, find all z reachable via nonneg from x.
    # For each such z, find all y with neg(y, z).
    # Check: is fc(y) < fc(x)?

    neg_adj = defaultdict(list)
    for c, s in neg_edges:
        neg_adj[c].append(s)

    segment_violations_fc = 0
    total_segments = 0
    for x in bad_configs:
        # Find all z reachable from x via nonneg
        visited = {x}
        queue = [x]
        qi = 0
        while qi < len(queue):
            v = queue[qi]; qi += 1
            for w in nonneg_adj.get(v, []):
                if w not in visited:
                    visited.add(w)
                    queue.append(w)

        # For each z, check neg successors y
        for z in visited:
            for y in neg_adj.get(z, []):
                total_segments += 1
                if fc_fn(y) >= fc_fn(x):
                    segment_violations_fc += 1

    print(f"  Total segments: {total_segments}")
    print(f"  fc(y) >= fc(x) violations: {segment_violations_fc}")

    if segment_violations_fc == 0:
        print(f"  ** fc works as segment measure! **")
    else:
        # Check: does nonneg_measure(y) < nonneg_measure(x)?
        PSIMAX = n * n  # upper bound on psi
        def nonneg_measure(c):
            return (n - fc_fn(c)) * (PSIMAX + 1) + psi_fn(c)

        segment_violations_nm = 0
        for x in bad_configs:
            visited = {x}
            queue = [x]
            qi = 0
            while qi < len(queue):
                v = queue[qi]; qi += 1
                for w in nonneg_adj.get(v, []):
                    if w not in visited:
                        visited.add(w)
                        queue.append(w)

            for z in visited:
                for y in neg_adj.get(z, []):
                    if nonneg_measure(y) >= nonneg_measure(x):
                        segment_violations_nm += 1

        print(f"  nonneg_measure(y) >= nonneg_measure(x) violations: {segment_violations_nm}")
