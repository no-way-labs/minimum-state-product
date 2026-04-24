#!/usr/bin/env python3
"""
Research Agent: Deeper investigation of boundary-fixed CPhiStep inner measure.
==============================================================================
Key finding from Q1: (fc, deep) lex FAILS on boundary-fixed CPhiSteps.
This script investigates what DOES work.

The boundary-fixed CPhiStep subgraph IS a DAG (rank 8/11/14 at n=9/10/11).
Pattern: bf_rank = 3*(n-9) + 8 = 3n - 19? Let's check.

Tests: n=9..13.
"""

import sys, time
from itertools import product as cartesian
from collections import defaultdict, deque, Counter

# CUP-2 tables (same as q1)
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
        elif i == n - 1: tabs.append(T_top)
        elif i == n - 2: tabs.append(T_high)
        else: tabs.append(T_mid)
    return tabs


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def boundary6(c, n):
    return (c[0], c[1], c[2], c[n - 3], c[n - 2], c[n - 1])


def exp2_count(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] in (0, 1))

def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 1)

def exp2_weight(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] in (0, 1))

def tp_key(c, n):
    return (exp2_count(c, n), int_21(c, n), exp2_weight(c, n))


def deep_mid_hop(c, n):
    total = 0
    for j in range(3, n - 3):
        if c[j] == 2 and c[(j + 1) % n] in (0, 1):
            total += j
    return total


def investigate_inner(n):
    print(f"\n{'='*70}")
    print(f"  n={n}: Boundary-fixed CPhiStep inner measure")
    print(f"{'='*70}")
    t0 = time.time()

    ms = [2] + [3] * (n - 2) + [2]
    tables = build_tables(n)

    all_configs = list(cartesian(*(range(m) for m in ms)))

    # Build transition graph
    succ_map = {}
    for c in all_configs:
        out = []
        for i in range(n):
            L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
            o = tables[i].get((L, S, R), S)
            if o != S:
                nc = list(c); nc[i] = o; out.append((tuple(nc), i))
        succ_map[c] = out

    # Tarjan SCC
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

    # TP-preserving bad edges
    tp_fwd = defaultdict(list)
    tp_edges = []
    for c in bad_configs:
        for s, mover in succ_map.get(c, []):
            if s in bad_set and tp_cache.get(s) == tp_cache[c]:
                dfc = fc_cache.get(s, fc(s, n)) - fc_cache[c]
                tp_edges.append((c, s, mover, dfc))
                tp_fwd[c].append((s, dfc))

    # PhiFull via fixed-point
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

    # CPhiStep = TP edge with constant PhiFull
    cphi_edges = [(c, s, m) for c, s, m, _ in tp_edges
                  if phi_full[c] == phi_full.get(s, 0)]

    # Boundary-fixed CPhiSteps only
    bd_fixed = [(c, s, m) for c, s, m in cphi_edges
                if boundary6(c, n) == boundary6(s, n)]

    print(f"  CPhiSteps: {len(cphi_edges)}, boundary-fixed: {len(bd_fixed)}")

    if not bd_fixed:
        print(f"  No boundary-fixed CPhiSteps!")
        return

    # Classify movers for boundary-fixed CPhiSteps
    mover_counts = Counter(m for _, _, m in bd_fixed)
    print(f"  Mover positions: {dict(sorted(mover_counts.items()))}")

    # For each boundary-fixed CPhiStep, what entry is fired?
    # Entry = (L, S, R) -> out at position mover
    entry_info = []
    for c, s, m in bd_fixed:
        L, S, R = c[(m-1) % n], c[m], c[(m+1) % n]
        out = tables[m].get((L, S, R), S)
        dfc = fc_cache.get(s, fc(s, n)) - fc_cache[c]
        entry_info.append((c, s, m, L, S, R, out, dfc))

    # What entries appear?
    entry_counts = Counter((L, S, R, out) for _, _, m, L, S, R, out, _ in entry_info)
    print(f"\n  Entries fired (L,S,R)->out:")
    for (L, S, R, out), cnt in sorted(entry_counts.items(), key=lambda x: -x[1]):
        # Classify: is this a copy-left (out==L) or copy-right (out==R)?
        cl = "copy-L" if out == L else ("copy-R" if out == R else "other")
        print(f"    ({L},{S},{R})->{out} [{cl}]: {cnt}")

    # Check dfc distribution
    dfc_counts = Counter(dfc for _, _, _, _, _, _, _, dfc in entry_info)
    print(f"\n  dfc distribution: {dict(sorted(dfc_counts.items()))}")

    # For dfc=0 entries: what's the deep behavior?
    deep_cache = {c: deep_mid_hop(c, n) for c in bad_configs}
    dfc0_entries = [(c, s, m, L, S, R, out) for c, s, m, L, S, R, out, dfc in entry_info if dfc == 0]
    if dfc0_entries:
        deep_inc = sum(1 for c, s, _, _, _, _, _ in dfc0_entries
                       if deep_cache.get(s, deep_mid_hop(s, n)) > deep_cache[c])
        deep_dec = sum(1 for c, s, _, _, _, _, _ in dfc0_entries
                       if deep_cache.get(s, deep_mid_hop(s, n)) < deep_cache[c])
        deep_eq = len(dfc0_entries) - deep_inc - deep_dec
        print(f"\n  dfc=0 steps: {len(dfc0_entries)}")
        print(f"    deep dec/eq/inc: {deep_dec}/{deep_eq}/{deep_inc}")

        # For deep_inc cases: what's happening?
        for c, s, m, L, S, R, out in dfc0_entries:
            d_c = deep_cache[c]
            d_s = deep_cache.get(s, deep_mid_hop(s, n))
            if d_s > d_c:
                print(f"    DEEP INCREASE: mover={m}, ({L},{S},{R})->{out}, "
                      f"deep {d_c}->{d_s}, c={c}")
                break

    # Now investigate: what DOES decrease on ALL boundary-fixed CPhiSteps?
    # The boundary-fixed subgraph is a DAG. Let's compute its rank.
    bf_adj = defaultdict(list)
    bf_nodes = set()
    for c, s, _ in bd_fixed:
        bf_adj[c].append(s)
        bf_nodes.add(c); bf_nodes.add(s)

    # DAG rank
    out_d = {c: len(bf_adj.get(c, [])) for c in bf_nodes}
    sinks = [c for c in bf_nodes if out_d[c] == 0]
    bf_rank = {c: 0 for c in sinks}
    rev = defaultdict(list)
    for c in bf_nodes:
        for s in bf_adj.get(c, []):
            rev[s].append(c)
    q = deque(sinks)
    while q:
        v = q.popleft()
        for u in rev.get(v, []):
            nr = bf_rank[v] + 1
            if u not in bf_rank or nr > bf_rank[u]:
                bf_rank[u] = nr
                q.append(u)
    max_bf_rank = max(bf_rank.values()) if bf_rank else 0
    print(f"\n  Boundary-fixed DAG rank: {max_bf_rank}")

    # Test candidate measures on bd-fixed CPhiSteps
    # All should strictly decrease on every edge

    # Candidate 1: fc (does it decrease on bd-fixed?)
    fc_viols_bf = sum(1 for c, s, _ in bd_fixed if fc_cache.get(s, 0) >= fc_cache[c])
    fc_dec_bf = sum(1 for c, s, _ in bd_fixed if fc_cache.get(s, 0) < fc_cache[c])
    print(f"\n  fc monotone on bd-fixed: dec={fc_dec_bf}, non-dec={fc_viols_bf}")

    # For fc-increasing steps: what entry?
    fc_inc_bf = [(c, s, m) for c, s, m in bd_fixed
                 if fc_cache.get(s, fc(s, n)) > fc_cache[c]]
    if fc_inc_bf:
        print(f"  fc INCREASES: {len(fc_inc_bf)}")
        for c, s, m in fc_inc_bf[:3]:
            L, S, R = c[(m-1) % n], c[m], c[(m+1) % n]
            out = tables[m].get((L, S, R), S)
            print(f"    mover={m}, ({L},{S},{R})->{out}, fc {fc_cache[c]}->{fc_cache.get(s,0)}")

    # Candidate 2: number of interior 2-values
    def count_2s(c):
        return sum(1 for j in range(3, n-3) if c[j] == 2)

    c2_viols = sum(1 for c, s, _ in bd_fixed
                   if count_2s(s) >= count_2s(c))
    print(f"  count_2s monotone on bd-fixed: viols={c2_viols}/{len(bd_fixed)}")

    # Candidate 3: number of interior "hop sources" (c[j]=2, c[j+1] in {0,1})
    def hop_sources(c):
        return sum(1 for j in range(3, n-3) if c[j] == 2 and c[(j+1) % n] in (0, 1))

    hs_viols = sum(1 for c, s, _ in bd_fixed
                   if hop_sources(s) >= hop_sources(c))
    print(f"  hop_sources monotone on bd-fixed: viols={hs_viols}/{len(bd_fixed)}")

    # The proof107 approach: interior has no cycle with boundary fixed.
    # But there ARE boundary-fixed CPhiSteps with fc increasing!
    # These are boundary-adjacent moves (positions 3..n-4 but close to boundary).

    # Let me check: is the mover always at position 3..n-4 for boundary-fixed?
    deep_movers = sum(1 for _, _, m in bd_fixed if 3 <= m <= n - 4)
    boundary_adj_movers = sum(1 for _, _, m in bd_fixed if m < 3 or m > n - 4)
    print(f"\n  Mover depth: deep(3..{n-4})={deep_movers}, boundary-adj={boundary_adj_movers}")

    # Wait: positions 0,1,2 and n-3,n-2,n-1 change the boundary!
    # So boundary-fixed means mover is at 3..n-4.
    # But proof107 says these are copy-neighbor moves with fc non-increasing...
    # Unless mover is not a "deep interior" position.

    # Let's check which positions actually appear
    print(f"\n  DETAILED mover analysis for boundary-fixed CPhiSteps:")
    for pos in sorted(set(m for _, _, m in bd_fixed)):
        edges_at = [(c, s) for c, s, m in bd_fixed if m == pos]
        fc_inc = sum(1 for c, s in edges_at if fc_cache.get(s, 0) > fc_cache[c])
        fc_dec = sum(1 for c, s in edges_at if fc_cache.get(s, 0) < fc_cache[c])
        fc_eq = len(edges_at) - fc_inc - fc_dec
        print(f"    pos={pos}: {len(edges_at)} edges, fc dec/eq/inc: {fc_dec}/{fc_eq}/{fc_inc}")

    # Also check the (fc, deepAll) lex where deepAll counts ALL positions 2..n-3
    def deep_all(c, n):
        return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j+1) % n] in (0, 1))

    deep_all_cache = {c: deep_all(c, n) for c in bad_configs}
    da_viols = sum(1 for c, s, _ in bd_fixed
                   if not (fc_cache.get(s, 0) < fc_cache[c] or
                           (fc_cache.get(s, 0) == fc_cache[c] and
                            deep_all_cache.get(s, 0) < deep_all_cache[c])))
    print(f"\n  (fc, deepAll) lex on bd-fixed: viols={da_viols}/{len(bd_fixed)}")

    # Check (n-fc, Psi) lex (the nonneg_measure) on bd-fixed only
    from ra_constlayer_q1 import psi as psi_fn
    psi_cache = {c: psi_fn(c, n) for c in bad_configs}

    nonneg_viols = 0
    for c, s, _ in bd_fixed:
        m_c = (n - fc_cache[c], psi_cache[c])
        m_s = (n - fc_cache.get(s, 0), psi_cache.get(s, 0))
        if not (m_s < m_c):
            nonneg_viols += 1
    print(f"  (n-fc, Psi) lex on bd-fixed: viols={nonneg_viols}/{len(bd_fixed)}")

    elapsed = time.time() - t0
    print(f"\n  Time: {elapsed:.1f}s")
    return max_bf_rank


if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    ranks = {}
    for nv in [9, 10, 11, 12]:
        r = investigate_inner(nv)
        if r is not None:
            ranks[nv] = r

    print(f"\n{'='*70}")
    print("BOUNDARY-FIXED DAG RANK PATTERN")
    print(f"{'='*70}")
    for nv, r in sorted(ranks.items()):
        print(f"  n={nv}: bf_rank={r}, 3(n-9)+8={3*(nv-9)+8}, 3n-19={3*nv-19}")
