#!/usr/bin/env python3
"""
Research Agent: Final verification and bound computation.
=========================================================
Now verified: (sixRank, fc, deepMidHopPotential) lex works on ALL CPhiSteps.

Key remaining questions:
1. The 6-tuple DAG: are the 616 transitions from CPhiSteps the SAME as the
   617 precomputed transitions in the Lean code? What about the SCC {239,245,251}?
2. Does the combined rank fit R <= 7n - 30?
3. What is the exact formula for the bound?

Also verify: boundary-changing CPhiStep ALWAYS drops Psi.
"""

import sys, time
from itertools import product as cartesian
from collections import defaultdict, deque, Counter

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
    tabs = []
    for i in range(n):
        if i == 0: tabs.append(T_bot)
        elif i == 1: tabs.append(T_low)
        elif i == n-1: tabs.append(T_top)
        elif i == n-2: tabs.append(T_high)
        else: tabs.append(T_mid)
    return tabs

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1) % n])

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

def midHopBudgetVal(L, S):
    if L == 0:
        return 1 if S == 2 else 0
    elif L == 1:
        return 2 - S
    else:
        return 0

def deepMidHopPotential(c, n):
    total = 0
    for i in range(n):
        left_i = (i - 1) % n
        total += (3 ** (n - 1 - i)) * midHopBudgetVal(c[left_i], c[i])
    return total


def investigate(n):
    print(f"\n{'='*70}")
    print(f"  n={n}")
    print(f"{'='*70}")
    t0 = time.time()

    ms = [2] + [3]*(n-2) + [2]
    tables = build_tables(n)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    succ_map = {}
    for c in all_configs:
        out = []
        for i in range(n):
            L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
            o = tables[i].get((L, S, R), S)
            if o != S:
                nc = list(c); nc[i] = o; out.append((tuple(nc), i))
        succ_map[c] = out

    # Tarjan
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

    fc_cache = {c: fc(c, n) for c in bad_configs}
    tp_cache = {c: tp_key(c, n) for c in bad_configs}

    tp_fwd = defaultdict(list)
    tp_edges = []
    for c in bad_configs:
        for s, mover in succ_map.get(c, []):
            if s in bad_set and tp_cache.get(s) == tp_cache[c]:
                dfc = fc_cache.get(s, fc(s, n)) - fc_cache[c]
                tp_edges.append((c, s, mover, dfc))
                tp_fwd[c].append((s, dfc))

    g = {c: 0 for c in bad_configs}
    for _ in range(3 * n):
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

    cphi_edges = [(c, s, m) for c, s, m, _ in tp_edges
                  if phi_full[c] == phi_full.get(s, 0)]

    bd_fixed = [(c, s, m) for c, s, m in cphi_edges
                if boundary6(c, n) == boundary6(s, n)]
    bd_changed = [(c, s, m) for c, s, m in cphi_edges
                  if boundary6(c, n) != boundary6(s, n)]

    # 6-tuple transitions from CPhiStep boundary-changing edges
    six_trans_cphi = set()
    for c, s, _ in bd_changed:
        six_trans_cphi.add((boundary6(c, n), boundary6(s, n)))

    # 6-tuple transitions from ALL constant-PhiFull TP-preserving edges (proof107 style)
    six_trans_all = set()
    six_nodes_all = set()
    for c, s, m, _ in tp_edges:
        if phi_full[c] == phi_full.get(s, 0):
            b_c = boundary6(c, n)
            b_s = boundary6(s, n)
            if b_c != b_s:
                six_trans_all.add((b_c, b_s))
                six_nodes_all.add(b_c)
                six_nodes_all.add(b_s)

    # These should be the same set
    print(f"  6-tuple transitions from CPhiStep: {len(six_trans_cphi)}")
    print(f"  6-tuple transitions from const-Phi TP: {len(six_trans_all)}")
    print(f"  Same: {six_trans_cphi == six_trans_all}")

    # Compare with the 617 from the Lean code
    # The Lean code's 617 transitions come from ALL constant-Phi_full edges at n=9
    # For n>=9 they should be identical (n-independence)
    print(f"  n-independent: should be 616 or 617 for all n >= 9")

    # 6-tuple DAG rank
    six_adj = defaultdict(set)
    six_nodes = set()
    for a, b in six_trans_cphi:
        six_adj[a].add(b)
        six_nodes.add(a); six_nodes.add(b)

    # SCC analysis
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
    print(f"  6-tuple SCCs: {len(sccs2)}, nontrivial: {len(nontrivial)}")

    # DAG rank
    out_d = {s: len(six_adj.get(s, set())) for s in six_nodes}
    sinks = [s for s in six_nodes if out_d[s] == 0]
    six_rank = {s: 0 for s in sinks}
    rev = defaultdict(list)
    for k, vs in six_adj.items():
        for v in vs:
            rev[v].append(k)
    q = deque(sinks)
    while q:
        v = q.popleft()
        for u in rev.get(v, []):
            nr = six_rank[v] + 1
            if u not in six_rank or nr > six_rank[u]:
                six_rank[u] = nr
                q.append(u)
    max_six_rank = max(six_rank.values()) if six_rank else 0
    print(f"  6-tuple DAG rank: {max_six_rank}")

    # Psi on boundary-changing CPhiSteps
    psi_cache = {c: psi(c, n) for c in bad_configs}
    bc_psi_dec = sum(1 for c, s, _ in bd_changed if psi_cache.get(s, 0) < psi_cache[c])
    bc_psi_eq = sum(1 for c, s, _ in bd_changed if psi_cache.get(s, 0) == psi_cache[c])
    bc_psi_inc = sum(1 for c, s, _ in bd_changed if psi_cache.get(s, 0) > psi_cache[c])
    print(f"\n  Psi on bd-changing CPhiSteps: dec={bc_psi_dec}, eq={bc_psi_eq}, inc={bc_psi_inc}")
    print(f"  Psi ALWAYS decreases on bd-changing: {bc_psi_inc == 0 and bc_psi_eq == 0}")

    # Full CPhiStep DAG rank
    cphi_adj = defaultdict(list)
    cphi_nodes = set()
    for c, s, _ in cphi_edges:
        cphi_adj[c].append(s)
        cphi_nodes.add(c); cphi_nodes.add(s)
    out_d2 = {c: len(cphi_adj.get(c, [])) for c in cphi_nodes}
    sinks2 = [c for c in cphi_nodes if out_d2[c] == 0]
    cphi_rank = {c: 0 for c in sinks2}
    rev2 = defaultdict(list)
    for c in cphi_nodes:
        for s in cphi_adj.get(c, []):
            rev2[s].append(c)
    q = deque(sinks2)
    while q:
        v = q.popleft()
        for u in rev2.get(v, []):
            nr = cphi_rank[v] + 1
            if u not in cphi_rank or nr > cphi_rank[u]:
                cphi_rank[u] = nr
                q.append(u)
    max_cphi_rank = max(cphi_rank.values()) if cphi_rank else 0
    print(f"\n  Full CPhiStep DAG rank: {max_cphi_rank}")
    print(f"  7n-30 = {7*n-30}")
    print(f"  Actual = 7n-30? {max_cphi_rank == 7*n-30}")
    # Check: is it closer to something else?
    # bf_rank = 3n-19 from q2
    # six_rank = 24
    # Could the total be sixRank*(something) + bf_rank?
    # 24 + (3n-19) = 3n+5. At n=9: 32. Actual: 34. Nope.
    # At n=9: rank=34, 7*9-30=33. Off by 1.
    # At n=10: rank=41, 7*10-30=40. Off by 1.
    # At n=11: rank=48, 7*11-30=47. Off by 1.
    # At n=12: rank=55, 7*12-30=54. Off by 1.
    # So actual = 7n-29!
    print(f"  7n-29 = {7*n-29}")
    print(f"  Actual = 7n-29? {max_cphi_rank == 7*n-29}")

    # Boundary-fixed DAG rank
    bf_adj = defaultdict(list)
    bf_nodes = set()
    for c, s, _ in bd_fixed:
        bf_adj[c].append(s)
        bf_nodes.add(c); bf_nodes.add(s)
    if bf_nodes:
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
    else:
        max_bf_rank = 0
    print(f"\n  Boundary-fixed DAG rank: {max_bf_rank}")
    print(f"  3n-19 = {3*n-19}")
    print(f"  Match: {max_bf_rank == 3*n-19}")

    # For wf_of_inner_segment, the overall rank is:
    # At most sixRank * (bf_rank + 1) + bf_rank = (sixRank + 1) * (bf_rank + 1) - 1
    # = (24 + 1) * (3n-18) - 1 = 25 * (3n-18) - 1 = 75n - 451
    # That's way too big. The actual rank is 7n-29.
    # So the wf_of_inner_segment gives a loose bound.
    # The tight bound comes from the product lex (sixRank, fc, deep).

    elapsed = time.time() - t0
    print(f"\n  Time: {elapsed:.1f}s")
    return max_cphi_rank, max_six_rank, max_bf_rank


if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    results = {}
    for nv in [9, 10, 11, 12, 13]:
        r = investigate(nv)
        results[nv] = r

    print(f"\n{'='*70}")
    print("FINAL SUMMARY")
    print(f"{'='*70}")
    for nv, (cr, sr, br) in sorted(results.items()):
        print(f"  n={nv}: CPhiRank={cr} (7n-29={7*nv-29}), "
              f"sixRank={sr}, bfRank={br} (3n-19={3*nv-19})")
