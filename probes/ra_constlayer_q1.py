#!/usr/bin/env python3
"""
Research Agent: Constant Layer (CPhiStep) Investigation
========================================================
Questions:
  Q1: For boundary-fixed CPhiSteps, does Psi always decrease?
  Q2: Does CPhiStep ever change boundary?
  Q3: 6-tuple DAG condensation rank behavior
  Q4: Combined rank R(c) that decreases on ALL CPhiSteps
  Q5: wf_of_inner_segment alternative

Tests at n=9, 10, 11.
"""

import sys, time
from itertools import product as cartesian
from collections import defaultdict, deque

# ================================================================
# CUP-2 TRANSITION TABLES (n-independent, 87 entries)
# ================================================================
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

# ================================================================
# PSI WEIGHT TABLES (from SyntheticPotential.lean, all 7 pos types)
# ================================================================
wP0_table = {
    (0,0,0):5,(0,0,1):5,(0,0,2):5,(0,1,0):-5,(0,1,1):-5,(0,1,2):-1,
    (0,2,0):-5,(0,2,1):-5,(0,2,2):-5,
    (1,0,0):-5,(1,0,1):1,(1,0,2):-5,(1,1,0):1,(1,1,1):1,(1,1,2):5,
    (1,2,0):-5,(1,2,1):-5,(1,2,2):-5,
    (2,0,0):-5,(2,0,1):-5,(2,0,2):-5,(2,1,0):-5,(2,1,1):-5,(2,1,2):-5,
    (2,2,0):-5,(2,2,1):-5,(2,2,2):-5,
}
wP1_table = {
    (0,0,0):-3,(0,0,1):-5,(0,0,2):-3,(0,1,0):5,(0,1,1):5,(0,1,2):5,
    (0,2,0):-1,(0,2,1):1,(0,2,2):5,
    (1,0,0):5,(1,0,1):-1,(1,0,2):5,(1,1,0):-5,(1,1,1):-5,(1,1,2):3,
    (1,2,0):3,(1,2,1):5,(1,2,2):-3,
    (2,0,0):-5,(2,0,1):-5,(2,0,2):-5,(2,1,0):-5,(2,1,1):-5,(2,1,2):-5,
    (2,2,0):-5,(2,2,1):-5,(2,2,2):-5,
}
wP2_table = {
    (0,0,0):-5,(0,0,2):-3,(0,1,0):5,(0,1,1):5,(0,1,2):5,
    (0,2,0):5,(0,2,1):5,(0,2,2):1,
    (1,0,0):3,(1,0,1):-3,(1,0,2):5,(1,1,0):-5,(1,1,1):-5,(1,1,2):3,
    (1,2,0):5,(1,2,1):5,(1,2,2):-5,
    (2,0,0):-5,(2,0,1):5,(2,0,2):5,(2,1,0):5,(2,1,1):5,(2,1,2):5,
    (2,2,0):3,(2,2,2):-5,
}
wPn3_table = {
    (0,0,0):-5,(0,0,1):5,(0,0,2):-1,(0,1,0):5,(0,1,1):1,(0,1,2):1,
    (0,2,1):5,(0,2,2):5,
    (1,0,0):1,(1,0,1):5,(1,0,2):5,(1,1,0):-1,(1,1,1):-5,(1,1,2):-5,
    (1,2,0):5,(1,2,1):5,(1,2,2):-5,
    (2,0,0):-5,(2,0,1):-3,(2,0,2):5,(2,1,0):5,(2,1,1):1,(2,1,2):1,
    (2,2,1):5,(2,2,2):-5,
}
wPn2_table = {
    (0,0,0):-5,(0,0,1):-3,(0,0,2):-5,(0,1,0):5,(0,1,1):5,(0,1,2):-5,
    (0,2,0):3,(0,2,1):5,(0,2,2):-5,
    (1,0,0):3,(1,0,1):5,(1,0,2):-5,(1,1,0):-5,(1,1,1):-5,(1,1,2):-5,
    (1,2,0):-1,(1,2,1):-5,(1,2,2):-5,
    (2,0,0):3,(2,0,1):5,(2,0,2):-5,(2,1,0):5,(2,1,1):5,(2,1,2):-5,
    (2,2,0):-1,(2,2,1):-5,(2,2,2):-5,
}
wPn1_table = {
    (0,0,0):-5,(0,0,1):-5,(0,0,2):-5,(0,1,0):5,(0,1,1):5,(0,1,2):-5,
    (0,2,0):-5,(0,2,1):-5,(0,2,2):-5,
    (1,0,0):5,(1,0,1):5,(1,0,2):-5,(1,1,0):-3,(1,1,1):-3,(1,1,2):-5,
    (1,2,0):-5,(1,2,1):-5,(1,2,2):-5,
    (2,0,0):5,(2,0,1):5,(2,0,2):-5,(2,1,0):-5,(2,1,1):-5,(2,1,2):-5,
    (2,2,0):-5,(2,2,1):-5,(2,2,2):-5,
}
wMid_table = {
    (0,0,0):-5,(0,0,1):5,(0,0,2):3,(0,1,0):5,(0,1,1):-3,(0,1,2):-5,
    (0,2,0):-3,(0,2,1):5,
    (1,0,0):-5,(1,0,1):5,(1,0,2):1,(1,1,0):5,(1,1,1):-3,(1,1,2):-5,
    (1,2,0):-3,(1,2,1):5,
    (2,0,0):-5,(2,0,1):5,(2,0,2):5,(2,1,0):5,(2,1,1):-3,(2,1,2):-5,
    (2,2,0):-5,(2,2,1):3,(2,2,2):-2,
}

ALL_W = [wP0_table, wP1_table, wP2_table, wPn3_table,
         wPn2_table, wPn1_table, wMid_table]


def build_tables(n):
    """Return list of transition tables per position."""
    tabs = []
    for i in range(n):
        if i == 0: tabs.append(T_bot)
        elif i == 1: tabs.append(T_low)
        elif i == n - 1: tabs.append(T_top)
        elif i == n - 2: tabs.append(T_high)
        else: tabs.append(T_mid)
    return tabs


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def pos_type(n, j):
    if j == 0: return 0
    elif j == 1: return 1
    elif j == 2: return 2
    elif j == n - 3: return 3
    elif j == n - 2: return 4
    elif j == n - 1: return 5
    else: return 6


def psi(c, n):
    total = 0
    for j in range(n):
        L, S, R = c[(j-1) % n], c[j], c[(j+1) % n]
        total += ALL_W[pos_type(n, j)].get((L, S, R), 0)
    return total


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
    """deepMidHopPotential: sum of j for deep positions j in [3..n-4] where c[j]=2, c[j+1] in {0,1}."""
    total = 0
    for j in range(3, n - 3):
        if c[j] == 2 and c[(j+1) % n] in (0, 1):
            total += j
    return total


def investigate(n):
    print(f"\n{'='*70}")
    print(f"  INVESTIGATING n={n}")
    print(f"{'='*70}")
    t0 = time.time()

    ms = [2] + [3] * (n - 2) + [2]
    tables = build_tables(n)
    product = 1
    for m in ms: product *= m
    print(f"  ms = (2,3,...,3,2), product = {product}")

    all_configs = list(cartesian(*(range(m) for m in ms)))
    print(f"  Total configs: {len(all_configs)}")

    # Build transition graph with mover info
    succ_map = {}  # config -> [(succ, mover_pos)]
    for c in all_configs:
        out = []
        for i in range(n):
            L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
            o = tables[i].get((L, S, R), S)
            if o != S:
                nc = list(c); nc[i] = o; out.append((tuple(nc), i))
        succ_map[c] = out

    # Tarjan SCC to find good cycle
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
    print(f"  Good: {len(good_set)}, Bad: {len(bad_configs)}")

    # Precompute caches
    fc_cache = {}
    tp_cache = {}
    for c in bad_configs:
        fc_cache[c] = fc(c, n)
        tp_cache[c] = tp_key(c, n)

    # Build TP-preserving bad edges (bad->bad, same TP)
    tp_edges = []  # (c, s, mover, dfc)
    tp_fwd = defaultdict(list)
    for c in bad_configs:
        for s, mover in succ_map.get(c, []):
            if s in bad_set and tp_cache.get(s) == tp_cache[c]:
                dfc = fc_cache.get(s, fc(s, n)) - fc_cache[c]
                tp_edges.append((c, s, mover, dfc))
                tp_fwd[c].append((s, dfc))

    print(f"  TP-preserving bad edges: {len(tp_edges)}")

    # Compute PhiFull using fixed-point iteration (from proof107)
    # g(c) = max over TP-successors s of (dfc + g(s)), init 0
    # PhiFull(c) = fc(c) + g(c)
    g = {c: 0 for c in bad_configs}
    for iteration in range(3 * n):
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

    # Verify PhiFull non-increasing on TP edges
    phi_viols = sum(1 for c, s, _, _ in tp_edges if phi_full.get(s, 0) > phi_full.get(c, 0))
    print(f"  PhiFull non-increasing violations: {phi_viols}")
    assert phi_viols == 0, "PhiFull should be non-increasing!"

    # CPhiStep = TP-preserving bad edge with constant PhiFull
    cphi_edges = [(c, s, m) for c, s, m, _ in tp_edges
                  if phi_full[c] == phi_full.get(s, 0)]
    print(f"  CPhiStep edges: {len(cphi_edges)}")

    # Precompute Psi
    psi_cache = {}
    deep_cache = {}
    for c in bad_configs:
        psi_cache[c] = psi(c, n)
        deep_cache[c] = deep_mid_hop(c, n)

    # Classify: boundary-fixed vs boundary-changing
    bd_fixed = []
    bd_changed = []
    for c, s, m in cphi_edges:
        if boundary6(c, n) == boundary6(s, n):
            bd_fixed.append((c, s, m))
        else:
            bd_changed.append((c, s, m))

    # ================================================================
    # Q1: Psi behavior on boundary-fixed CPhiSteps
    # ================================================================
    print(f"\n  --- Q1: Psi on boundary-fixed CPhiSteps ---")
    print(f"    Boundary-fixed: {len(bd_fixed)}")
    print(f"    Boundary-changing: {len(bd_changed)}")

    if bd_fixed:
        psi_dec = sum(1 for c, s, _ in bd_fixed if psi_cache[s] < psi_cache[c])
        psi_eq = sum(1 for c, s, _ in bd_fixed if psi_cache[s] == psi_cache[c])
        psi_inc = sum(1 for c, s, _ in bd_fixed if psi_cache[s] > psi_cache[c])
        max_inc = max((psi_cache[s] - psi_cache[c] for c, s, _ in bd_fixed), default=0)
        print(f"    Psi dec/eq/inc: {psi_dec}/{psi_eq}/{psi_inc}")
        print(f"    Max Psi increase: {max_inc}")
        if psi_inc:
            for c, s, m in bd_fixed:
                dp = psi_cache[s] - psi_cache[c]
                if dp > 0:
                    print(f"      mover={m}, c={c}, Psi {psi_cache[c]}->{psi_cache[s]} (+{dp})")
                    break

    if bd_changed:
        bc_dec = sum(1 for c, s, _ in bd_changed if psi_cache[s] < psi_cache[c])
        bc_eq = sum(1 for c, s, _ in bd_changed if psi_cache[s] == psi_cache[c])
        bc_inc = sum(1 for c, s, _ in bd_changed if psi_cache[s] > psi_cache[c])
        print(f"    Boundary-changing Psi dec/eq/inc: {bc_dec}/{bc_eq}/{bc_inc}")

    # ================================================================
    # Q2: Does CPhiStep ever change boundary?
    # ================================================================
    print(f"\n  --- Q2: Boundary changes in CPhiSteps ---")
    if bd_changed:
        print(f"    YES: {len(bd_changed)} boundary-changing CPhiSteps")
        # Classify by mover position
        mover_counts = defaultdict(int)
        for _, _, m in bd_changed:
            mover_counts[m] += 1
        print(f"    By mover position: {dict(sorted(mover_counts.items()))}")
        for c, s, m in bd_changed[:3]:
            print(f"      mover={m}: {boundary6(c,n)} -> {boundary6(s,n)}, "
                  f"fc {fc_cache[c]}->{fc_cache.get(s,0)}, "
                  f"dPsi={psi_cache.get(s,0)-psi_cache[c]}")
    else:
        print(f"    NO: boundary ALWAYS fixed in CPhiSteps")

    # ================================================================
    # Q3: 6-tuple DAG analysis for CPhiStep boundary-changing edges
    # ================================================================
    print(f"\n  --- Q3: 6-tuple transition graph ---")
    six_trans = set()
    for c, s, _ in bd_changed:
        six_trans.add((boundary6(c, n), boundary6(s, n)))
    six_nodes = set()
    six_adj = defaultdict(set)
    for a, b in six_trans:
        six_adj[a].add(b)
        six_nodes.add(a); six_nodes.add(b)
    print(f"    6-tuple nodes: {len(six_nodes)}, transitions: {len(six_trans)}")

    # SCC analysis of 6-tuple graph
    if six_nodes:
        # Tarjan on 6-tuple graph
        idx2 = [0]; stk2 = []; ll2 = {}; im2 = {}; ons2 = set(); sccs2 = []
        for start in six_nodes:
            if start in im2: continue
            cs2 = [(start, iter(six_adj.get(start, set())))]
            im2[start] = ll2[start] = idx2[0]; idx2[0] += 1
            stk2.append(start); ons2.add(start)
            while cs2:
                v, ch = cs2[-1]
                try:
                    w = next(ch)
                    if w not in im2:
                        im2[w] = ll2[w] = idx2[0]; idx2[0] += 1
                        stk2.append(w); ons2.add(w)
                        cs2.append((w, iter(six_adj.get(w, set()))))
                    elif w in ons2:
                        ll2[v] = min(ll2[v], im2[w])
                except StopIteration:
                    cs2.pop()
                    if cs2: ll2[cs2[-1][0]] = min(ll2[cs2[-1][0]], ll2[v])
                    if ll2[v] == im2[v]:
                        scc = []
                        while True:
                            w = stk2.pop(); ons2.discard(w); scc.append(w)
                            if w == v: break
                        sccs2.append(scc)

        nontrivial = [scc for scc in sccs2 if len(scc) > 1]
        print(f"    SCCs: {len(sccs2)}, nontrivial: {len(nontrivial)}")
        for scc in nontrivial:
            print(f"      SCC size {len(scc)}: {scc[:5]}...")

    # ================================================================
    # Q4: Full CPhiStep DAG rank
    # ================================================================
    print(f"\n  --- Q4: Full CPhiStep DAG analysis ---")
    cphi_adj = defaultdict(list)
    cphi_nodes = set()
    for c, s, _ in cphi_edges:
        cphi_adj[c].append(s)
        cphi_nodes.add(c); cphi_nodes.add(s)

    # DAG check via color DFS
    color = {c: 0 for c in cphi_nodes}
    is_dag = True
    for start in cphi_nodes:
        if color[start] != 0: continue
        dfs = [(start, iter(cphi_adj.get(start, [])))]
        color[start] = 1
        while dfs:
            v, ch = dfs[-1]
            try:
                w = next(ch)
                if color.get(w, 0) == 1:
                    is_dag = False; break
                if color.get(w, 0) == 0:
                    color[w] = 1
                    dfs.append((w, iter(cphi_adj.get(w, []))))
            except StopIteration:
                dfs.pop(); color[v] = 2
        if not is_dag: break

    print(f"    CPhiStep DAG: {is_dag}")

    max_cphi_rank = -1
    if is_dag:
        out_d = {c: len(cphi_adj.get(c, [])) for c in cphi_nodes}
        sinks = [c for c in cphi_nodes if out_d[c] == 0]
        cphi_rank = {c: 0 for c in sinks}
        rev = defaultdict(list)
        for c in cphi_nodes:
            for s in cphi_adj.get(c, []):
                rev[s].append(c)
        q = deque(sinks)
        while q:
            v = q.popleft()
            for u in rev.get(v, []):
                nr = cphi_rank[v] + 1
                if u not in cphi_rank or nr > cphi_rank[u]:
                    cphi_rank[u] = nr
                    q.append(u)
        max_cphi_rank = max(cphi_rank.values()) if cphi_rank else 0
        print(f"    Max CPhiStep rank: {max_cphi_rank}")
        print(f"    7n-30 = {7*n - 30}")
        print(f"    Fits: {max_cphi_rank <= 7*n - 30}")

    # ================================================================
    # Q5: Inner/segment decomposition
    # ================================================================
    print(f"\n  --- Q5: Inner/segment decomposition ---")

    # Inner = boundary-fixed CPhiStep
    # Check (fc, deep) lex on inner
    inner_viols = 0
    for c, s, m in bd_fixed:
        fc_c, fc_s = fc_cache[c], fc_cache.get(s, fc(s, n))
        d_c, d_s = deep_cache[c], deep_cache.get(s, deep_mid_hop(s, n))
        if not (fc_s < fc_c or (fc_s == fc_c and d_s < d_c)):
            inner_viols += 1
    print(f"    (fc, deep) lex on bd-fixed: violations = {inner_viols}")

    # Inner DAG?
    bf_adj = defaultdict(list)
    bf_nodes = set()
    for c, s, _ in bd_fixed:
        bf_adj[c].append(s)
        bf_nodes.add(c); bf_nodes.add(s)

    if bf_nodes:
        color3 = {c: 0 for c in bf_nodes}
        bf_dag = True
        for start in bf_nodes:
            if color3[start] != 0: continue
            dfs = [(start, iter(bf_adj.get(start, [])))]
            color3[start] = 1
            while dfs:
                v, ch = dfs[-1]
                try:
                    w = next(ch)
                    if color3.get(w, 0) == 1:
                        bf_dag = False; break
                    if color3.get(w, 0) == 0:
                        color3[w] = 1
                        dfs.append((w, iter(bf_adj.get(w, []))))
                except StopIteration:
                    dfs.pop(); color3[v] = 2
            if not bf_dag: break

        print(f"    Boundary-fixed subgraph DAG: {bf_dag}")
        if bf_dag:
            out_bf = {c: len(bf_adj.get(c, [])) for c in bf_nodes}
            sinks_bf = [c for c in bf_nodes if out_bf[c] == 0]
            bf_rank = {c: 0 for c in sinks_bf}
            rev_bf = defaultdict(list)
            for c in bf_nodes:
                for s in bf_adj.get(c, []):
                    rev_bf[s].append(c)
            q = deque(sinks_bf)
            while q:
                v = q.popleft()
                for u in rev_bf.get(v, []):
                    nr = bf_rank[v] + 1
                    if u not in bf_rank or nr > bf_rank[u]:
                        bf_rank[u] = nr
                        q.append(u)
            max_bf_rank = max(bf_rank.values()) if bf_rank else 0
            print(f"    Boundary-fixed max rank: {max_bf_rank}")
    else:
        bf_dag = True
        max_bf_rank = 0
        print(f"    No boundary-fixed edges")

    # Psi behavior on boundary-changed (segment)
    if bd_changed:
        seg_always_dec = all(psi_cache.get(s, 0) < psi_cache[c] for c, s, _ in bd_changed)
        print(f"    Psi always decreases on boundary-changing: {seg_always_dec}")

    # KEY composition property:
    # If segment = "Psi decreases strictly"
    # Then inner(b,a) + segment(c,b) => Psi(a) ??? vs Psi(c)
    # We need Psi(a) < Psi(c).
    # But inner(b,a) might increase Psi! So Psi(a) could be > Psi(b).
    # segment(c,b) gives Psi(b) < Psi(c).
    # We need Psi(a) < Psi(c), which requires Psi increase from b->a < Psi(c)-Psi(b).
    # This is NOT guaranteed.
    print(f"\n    Alternative: segment = sixRank decreases")
    print(f"    Then inner(b,a) preserves boundary => preserves sixRank")
    print(f"    So segment(c,b) = sixRank(b) < sixRank(c)")
    print(f"    And sixRank(a) = sixRank(b) < sixRank(c) => segment(c,a). VALID.")
    print(f"    REQUIRES: 6-tuple graph of boundary-changing CPhiSteps is a DAG.")
    if six_nodes:
        is_six_dag = len(nontrivial) == 0
        print(f"    6-tuple DAG: {is_six_dag}")

    elapsed = time.time() - t0
    print(f"\n  Time: {elapsed:.1f}s")

    return {
        'n': n,
        'cphi': len(cphi_edges),
        'bd_fixed': len(bd_fixed),
        'bd_changed': len(bd_changed),
        'inner_viols': inner_viols,
        'is_dag': is_dag,
        'rank': max_cphi_rank,
        'bf_dag': bf_dag,
        'bf_rank': max_bf_rank if bf_dag else None,
    }


if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    results = {}
    for nv in [9, 10, 11]:
        results[nv] = investigate(nv)

    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    for nv, r in sorted(results.items()):
        print(f"  n={nv}: CPhiSteps={r['cphi']}, "
              f"bd_fixed={r['bd_fixed']}, bd_changed={r['bd_changed']}, "
              f"inner_viols={r['inner_viols']}, "
              f"DAG={r['is_dag']}, rank={r['rank']}, "
              f"bf_dag={r['bf_dag']}, bf_rank={r['bf_rank']}")
