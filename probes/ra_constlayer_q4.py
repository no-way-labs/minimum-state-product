#!/usr/bin/env python3
"""
Research Agent: Test deepMidHopPotential as the inner measure.
=============================================================
The Lean code defines:
  midHopBudgetVal(L, S) = if L=0, S=2: 1; if L=1: 2-S; else 0
  deepMidHopPotential(c) = sum_i 3^(n-1-i) * midHopBudgetVal(c[left(i)], c[i])

This is proved in Interior.lean to decrease on every deep-interior dfc=0 step.

KEY QUESTION: Does (fc, deepMidHopPotential) lex decrease on ALL boundary-fixed CPhiSteps?
That would close the inner measure problem.
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
    """From Interior.lean."""
    if L == 0:
        return 1 if S == 2 else 0
    elif L == 1:
        return 2 - S
    else:
        return 0


def deepMidHopPotential(c, n):
    """From Interior.lean: sum_i 3^(n-1-i) * midHopBudgetVal(c[left(i)], c[i])."""
    total = 0
    for i in range(n):
        left_i = (i - 1) % n
        L = c[left_i]
        S = c[i]
        total += (3 ** (n - 1 - i)) * midHopBudgetVal(L, S)
    return total


def investigate(n):
    print(f"\n{'='*70}")
    print(f"  n={n}: Testing (fc, deepMidHopPotential) lex")
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

    print(f"  CPhiSteps: {len(cphi_edges)}")
    print(f"  Boundary-fixed: {len(bd_fixed)}")
    print(f"  Boundary-changed: {len(bd_changed)}")

    # Compute deepMidHopPotential for all bad configs
    dmhp_cache = {}
    for c in bad_configs:
        dmhp_cache[c] = deepMidHopPotential(c, n)

    # Test (fc, deepMidHopPotential) lex on boundary-fixed CPhiSteps
    # We want fc to decrease, OR fc stays same and deep decreases
    viols = 0
    viols_detail = []
    for c, s, m in bd_fixed:
        fc_c, fc_s = fc_cache[c], fc_cache.get(s, fc(s, n))
        d_c, d_s = dmhp_cache[c], dmhp_cache.get(s, deepMidHopPotential(s, n))
        if not (fc_s < fc_c or (fc_s == fc_c and d_s < d_c)):
            viols += 1
            if len(viols_detail) < 5:
                L, S, R = c[(m-1)%n], c[m], c[(m+1)%n]
                out = tables[m].get((L, S, R), S)
                viols_detail.append((c, s, m, fc_c, fc_s, d_c, d_s, L, S, R, out))

    print(f"\n  (fc, deepMidHopPotential) lex on bd-fixed:")
    print(f"    Violations: {viols}/{len(bd_fixed)}")
    for c, s, m, fc_c, fc_s, d_c, d_s, L, S, R, out in viols_detail:
        print(f"    mover={m}, ({L},{S},{R})->{out}, fc:{fc_c}->{fc_s}, deep:{d_c}->{d_s}")
        print(f"      c={c}")
        print(f"      s={s}")

    if viols == 0:
        print(f"    SUCCESS: (fc, deepMidHopPotential) lex works for inner measure!")

        # Now check: does this combine with sixRank for the full CPhiStep?
        # Full measure: (sixRank, fc, deepMidHopPotential) lex
        # Need the 6-tuple DAG rank
        six_adj = defaultdict(set)
        six_nodes = set()
        for c, s, _ in bd_changed:
            b_c = boundary6(c, n)
            b_s = boundary6(s, n)
            six_adj[b_c].add(b_s)
            six_nodes.add(b_c)
            six_nodes.add(b_s)

        # Compute 6-tuple DAG rank
        six_rank = {}
        if six_nodes:
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
            print(f"\n  6-tuple DAG rank: {max_six_rank}")

        # Full measure: (sixRank, fc, deepMidHopPotential) lex on ALL CPhiSteps
        full_viols = 0
        full_detail = []
        for c, s, m in cphi_edges:
            b_c = boundary6(c, n)
            b_s = boundary6(s, n)
            sr_c = six_rank.get(b_c, 0)
            sr_s = six_rank.get(b_s, 0)
            fc_c = fc_cache[c]
            fc_s = fc_cache.get(s, fc(s, n))
            d_c = dmhp_cache[c]
            d_s = dmhp_cache.get(s, deepMidHopPotential(s, n))
            m_c = (sr_c, fc_c, d_c)
            m_s = (sr_s, fc_s, d_s)
            # Reverse lex: we want m_s < m_c (all components decrease)
            # Actually: (sixRank DESC, fc DESC, deep DESC)
            # m_s should be strictly less in lex ordering
            # But sixRank should DECREASE (boundary-changing), or stay same (boundary-fixed)
            # fc should DECREASE or stay same
            # deep should DECREASE when fc stays same and boundary stays same
            # NOT standard lex because the "less" direction differs

            # For a proper lex: use negation.
            # Want: not (sr_s > sr_c or (sr_s == sr_c and (fc_s > fc_c or ...)))
            # Simpler: check (sr_c, fc_c, d_c) >_lex (sr_s, fc_s, d_s) in standard lex
            # where > means strictly greater = the measure decreases
            # We need: (sr_s, fc_s, d_s) < (sr_c, fc_c, d_c) in standard lex
            if not ((sr_s, fc_s, d_s) < (sr_c, fc_c, d_c)):
                full_viols += 1
                if len(full_detail) < 5:
                    full_detail.append((c, s, m, m_c, m_s))

        print(f"\n  (sixRank, fc, deepMidHopPotential) lex on ALL CPhiSteps:")
        print(f"    Violations: {full_viols}/{len(cphi_edges)}")
        for c, s, m, mc, ms_ in full_detail:
            bd_change = "BD-CHANGE" if boundary6(c, n) != boundary6(s, n) else "BD-FIXED"
            print(f"    {bd_change} mover={m}: {mc} -> {ms_}")

        if full_viols == 0:
            print(f"    SUCCESS: combined measure works for ALL CPhiSteps!")

            # Compute bound
            max_sr = max_six_rank if six_nodes else 0
            max_fc = max(fc_cache[c] for c in bad_configs)
            max_deep = max(dmhp_cache[c] for c in bad_configs)
            print(f"\n    Bounds: sixRank <= {max_sr}, fc <= {max_fc}, deep <= {max_deep}")
            print(f"    Bound for single Nat: ({max_sr}+1)*({max_fc}+1)*({max_deep}+1) = "
                  f"{(max_sr+1)*(max_fc+1)*(max_deep+1)}")
        else:
            # Analyze violations
            for c, s, m, mc, ms_ in full_detail:
                L, S, R = c[(m-1)%n], c[m], c[(m+1)%n]
                out = tables[m].get((L, S, R), S)
                print(f"      ({L},{S},{R})->{out}, c={c}")

    elapsed = time.time() - t0
    print(f"\n  Time: {elapsed:.1f}s")


if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    for nv in [9, 10, 11, 12]:
        investigate(nv)
