#!/usr/bin/env python3
"""
CONVERGENCE PROOF 22: Excursion Graph Deep Structure
=====================================================

The excursion graph is cycle-free for n=5..12. WHY?

This script:
1. Compute excursion graph depth (longest path) for each n
2. Characterize anomalous sources that are "terminal" (dead-end in exc graph)
3. Look for what value DOES decrease: boundary pattern? config hash?
4. Check if a MODIFIED (fc, Ψ) with position-dependent adjustment works
5. KEY: Check if Ψ_adj = Ψ - α·Q (for suitable α) works as replacement for Ψ
   in a (fc, Ψ_adj) lex potential for ALL transitions
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict, Counter


def frontier_type(a, b):
    if a == b:
        return 0
    return (b - a) % 3


def w1(j, n):
    if j == n - 1:
        return 0
    if j == n - 2:
        return 1
    return j + 1


def w2(j, n):
    if j == n - 1:
        return 0
    if 1 <= j <= n - 2:
        return n - 1 - j
    return n - 1


def psi(c, n):
    total = 0
    for j in range(n):
        ft = frontier_type(c[j], c[(j + 1) % n])
        if ft == 1:
            total += w1(j, n)
        elif ft == 2:
            total += w2(j, n)
    return total


def fc_val(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def Q_val(c, n):
    return sum(1 for j in range(n) if c[j] == c[(j + 1) % n] and c[j] in (0, 1))


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def classify_entry(L, S, R, out):
    if out == S:
        return "stay"
    if out == L:
        return "copy_L"
    if out == R:
        return "copy_R"
    return "anomalous"


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad configs")
    print(f"{'=' * 70}")

    # Build transitions
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    all_trans = []

    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    cls = classify_entry(L, S, R, out)
                    all_trans.append((c, succ, i, dfc, cls))
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if cls == "anomalous":
                        anom_edges.append((c, succ, i, dfc))

    n_anom = len(anom_edges)
    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_targets = set(succ for _, succ, _, _ in anom_edges)

    # Build excursion graph
    target_to_sources = defaultdict(list)
    for b in anom_targets:
        visited = set()
        queue = deque([b])
        visited.add(b)
        while queue:
            node = queue.popleft()
            if node in anom_sources and node != b:
                target_to_sources[b].append(node)
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        if b in anom_sources:
            target_to_sources[b].append(b)

    exc_graph = defaultdict(set)
    for c, succ, i, dfc in anom_edges:
        for src in target_to_sources.get(succ, []):
            exc_graph[c].add(src)

    # ═══════════════════════════════════════════════════════════
    # 1. Excursion graph depth
    # ═══════════════════════════════════════════════════════════
    # Topological sort of excursion graph
    all_exc_nodes = set(exc_graph.keys())
    for src_set in exc_graph.values():
        all_exc_nodes |= src_set

    in_deg = {v: 0 for v in all_exc_nodes}
    for a in exc_graph:
        for b in exc_graph[a]:
            in_deg[b] = in_deg.get(b, 0) + 1

    q = deque(v for v in all_exc_nodes if in_deg[v] == 0)
    topo = []
    while q:
        v = q.popleft()
        topo.append(v)
        for w in exc_graph.get(v, set()):
            in_deg[w] -= 1
            if in_deg[w] == 0:
                q.append(w)

    if len(topo) != len(all_exc_nodes):
        print(f"  EXCURSION GRAPH HAS CYCLE!")
        return None

    exc_rank = {}
    for v in reversed(topo):
        exc_rank[v] = max((exc_rank[w] + 1 for w in exc_graph.get(v, set())),
                          default=0)

    exc_depth = max(exc_rank.values()) if exc_rank else 0
    print(f"  Excursion graph: {len(all_exc_nodes)} nodes, depth={exc_depth}")

    # ═══════════════════════════════════════════════════════════
    # 2. Characterize nodes at each depth
    # ═══════════════════════════════════════════════════════════
    depth_dist = Counter(exc_rank.values())
    print(f"  Depth distribution: {dict(sorted(depth_dist.items()))}")

    # Terminal nodes (depth 0)
    terminals = [v for v in all_exc_nodes if exc_rank[v] == 0]
    # Non-terminal with max depth
    max_depth_nodes = [v for v in all_exc_nodes if exc_rank[v] == exc_depth]

    print(f"\n  Terminal nodes ({len(terminals)}):")
    term_fc = Counter(fc_val(v, n) for v in terminals)
    term_q = Counter(Q_val(v, n) for v in terminals)
    print(f"    fc distribution: {dict(sorted(term_fc.items()))}")
    print(f"    Q distribution: {dict(sorted(term_q.items()))}")

    # Which anomalous entries fire at terminal nodes?
    term_entries = Counter()
    for c, succ, i, dfc in anom_edges:
        if c in terminals:
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = succ[i]
            tname = {0: 'T_bot', 1: 'T_low', n-2: 'T_high',
                     n-1: 'T_top'}.get(i, 'T_mid')
            term_entries[(tname, L, S, R, out)] += 1
    print(f"    Entry types: {dict(sorted(term_entries.items()))}")

    if max_depth_nodes and exc_depth > 0:
        print(f"\n  Max-depth nodes ({len(max_depth_nodes)}, depth={exc_depth}):")
        for v in max_depth_nodes[:5]:
            print(f"    {v}: fc={fc_val(v,n)}, Q={Q_val(v,n)}, "
                  f"Ψ={psi(v,n)}, exc_rank={exc_rank[v]}")

    # ═══════════════════════════════════════════════════════════
    # 3. Try Ψ_adj = Ψ - α·Q as potential for ALL transitions
    # For Δfc=0: need ΔΨ_adj < 0 → ΔΨ - α·ΔQ < 0
    #   Since ΔΨ < 0 on Δfc=0, and ΔQ can be positive:
    #   Need α·ΔQ < ΔΨ, i.e., α < ΔΨ/ΔQ when ΔQ > 0
    #   Or α > ΔΨ/ΔQ when ΔQ < 0
    # For anomalous: need Δfc > 0 to dominate, or ΔΨ_adj < 0
    #   ΔΨ_adj = ΔΨ - α·ΔQ. With ΔQ ≤ -1: -α·ΔQ ≥ α.
    #   So ΔΨ_adj = ΔΨ + α (at least).
    #   For anomalous with ΔΨ ≥ 0: ΔΨ_adj ≥ α > 0. INCREASES!
    # So (fc, Ψ_adj) lex has anomalous violations when Δfc>0.
    # Unless α is negative (but then Δfc=0 might fail).
    # ═══════════════════════════════════════════════════════════

    # Let's try: (fc, Ψ - α·Q) lex for negative α (so -α·Q adds to Ψ)
    # For Δfc=0: ΔΨ - α·ΔQ. α<0 means -α>0.
    #   ΔΨ < 0. If ΔQ > 0: -α·ΔQ > 0 (adds positive). Bad if too large.
    #   Need: |ΔΨ| > |α|·ΔQ.
    # For anomalous: ΔΨ ≥ 0, ΔQ ≤ -1.
    #   ΔΨ - α·ΔQ = ΔΨ + |α|. Since ΔΨ ≥ 0: always ≥ |α| > 0. Still increases!

    # So (fc, Ψ±Q) can't handle anomalous edges at all.
    # Anomalous edges ALWAYS increase any function that's monotone in both Ψ and Q.

    # ═══════════════════════════════════════════════════════════
    # 4. EXCURSION GRAPH POTENTIAL: try (fc, Ψ) restricted to exc nodes
    # Also try Q, and various config properties
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Excursion graph potential search:")

    def test_exc_potential(name, phi_func):
        violations = 0
        total = 0
        for a in exc_graph:
            for ap in exc_graph[a]:
                total += 1
                if phi_func(ap) >= phi_func(a):
                    violations += 1
        print(f"    {name}: {violations}/{total} violations")
        return violations

    test_exc_potential("fc", lambda c: fc_val(c, n))
    test_exc_potential("Ψ", lambda c: psi(c, n))
    test_exc_potential("Q", lambda c: Q_val(c, n))
    test_exc_potential("(fc,Ψ) lex", lambda c: (fc_val(c, n), psi(c, n)))
    test_exc_potential("-Q", lambda c: -Q_val(c, n))
    test_exc_potential("(-Q, fc, Ψ)", lambda c: (-Q_val(c, n), fc_val(c, n), psi(c, n)))
    test_exc_potential("fc - Q", lambda c: fc_val(c, n) - Q_val(c, n))
    test_exc_potential("Ψ - Q", lambda c: psi(c, n) - Q_val(c, n))
    test_exc_potential("(fc-Q, Ψ)", lambda c: (fc_val(c,n) - Q_val(c,n), psi(c,n)))
    test_exc_potential("(-Q, Ψ)", lambda c: (-Q_val(c, n), psi(c, n)))

    # Value-based features
    test_exc_potential("n_zeros", lambda c: sum(1 for v in c if v == 0))
    test_exc_potential("-n_zeros", lambda c: -sum(1 for v in c if v == 0))
    test_exc_potential("n_twos", lambda c: sum(1 for v in c if v == 2))
    test_exc_potential("value_sum", lambda c: sum(c))
    test_exc_potential("-value_sum", lambda c: -sum(c))
    test_exc_potential("(n_twos, fc, Ψ)",
                       lambda c: (sum(1 for v in c if v == 2), fc_val(c,n), psi(c,n)))
    test_exc_potential("(-n_twos, fc, Ψ)",
                       lambda c: (-sum(1 for v in c if v == 2), fc_val(c,n), psi(c,n)))

    # Boundary values
    test_exc_potential("c[0]", lambda c: c[0])
    test_exc_potential("c[n-1]", lambda c: c[n-1])
    test_exc_potential("(c[0],c[n-1])", lambda c: (c[0], c[n-1]))
    test_exc_potential("c[0]+c[n-1]", lambda c: c[0] + c[n-1])

    # ═══════════════════════════════════════════════════════════
    # 5. FULL REGRESSION on excursion rank
    # ═══════════════════════════════════════════════════════════
    if len(all_exc_nodes) > 10:
        import numpy as np
        nodes = list(all_exc_nodes)
        y = np.array([exc_rank[v] for v in nodes], dtype=float)

        # Feature matrix
        features = {}
        features['fc'] = [fc_val(v, n) for v in nodes]
        features['psi'] = [psi(v, n) for v in nodes]
        features['Q'] = [Q_val(v, n) for v in nodes]
        features['n0'] = [sum(1 for x in v if x == 0) for v in nodes]
        features['n1'] = [sum(1 for x in v if x == 1) for v in nodes]
        features['n2'] = [sum(1 for x in v if x == 2) for v in nodes]
        features['sum'] = [sum(v) for v in nodes]
        features['c0'] = [v[0] for v in nodes]
        features['cn'] = [v[n-1] for v in nodes]

        # Position-specific values
        for j in range(min(n, 6)):
            features[f'c[{j}]'] = [v[j] for v in nodes]

        feat_names = list(features.keys())
        X = np.column_stack([features[f] for f in feat_names])
        X_bias = np.column_stack([X, np.ones(len(X))])

        try:
            w, _, _, _ = np.linalg.lstsq(X_bias, y, rcond=None)
            y_pred = X_bias @ w
            ss_res = np.sum((y - y_pred) ** 2)
            ss_tot = np.sum((y - np.mean(y)) ** 2)
            r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
            max_err = np.max(np.abs(y - y_pred))

            print(f"\n  Linear regression on exc_rank:")
            print(f"    R² = {r2:.4f}, max error = {max_err:.2f}")
            for i, fname in enumerate(feat_names):
                if abs(w[i]) > 0.01:
                    print(f"      {fname}: {w[i]:.4f}")
            print(f"      bias: {w[-1]:.4f}")
        except Exception as e:
            print(f"    Regression failed: {e}")

    # ═══════════════════════════════════════════════════════════
    # 6. CRITICAL TEST: Does the excursion graph decompose by
    #    anomalous entry type?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Excursion edges by entry type pair:")
    # For each excursion edge a → a': what anomalous entry fires at a,
    # and what entry fires at a'?
    src_entry = {}
    for c, succ, i, dfc in anom_edges:
        tname = {0: 'T_bot', 1: 'T_low', n-2: 'T_high',
                 n-1: 'T_top'}.get(i, 'T_mid')
        L = c[(i - 1) % n]
        S = c[i]
        R = c[(i + 1) % n]
        out = succ[i]
        key = (tname, L, S, R, out)
        if c not in src_entry:
            src_entry[c] = []
        src_entry[c].append(key)

    edge_type_pairs = Counter()
    for a in exc_graph:
        if a not in src_entry:
            continue
        for ap in exc_graph[a]:
            if ap not in src_entry:
                continue
            for entry_a in src_entry[a]:
                for entry_ap in src_entry[ap]:
                    edge_type_pairs[(entry_a[0], entry_ap[0])] += 1

    print(f"    Entry type transitions:")
    for (ta, tap), cnt in sorted(edge_type_pairs.items(),
                                  key=lambda x: -x[1]):
        print(f"      {ta} → {tap}: {cnt}")

    # ═══════════════════════════════════════════════════════════
    # 7. KEY STRUCTURAL: What is c[0], c[n-1] at anomalous sources?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Boundary values at anomalous sources:")
    boundary_dist = Counter()
    for a in anom_sources:
        boundary_dist[(a[0], a[n-1])] += 1
    print(f"    (c[0], c[n-1]) distribution: {dict(sorted(boundary_dist.items()))}")

    # After anomalous firing and Δfc≤0 path: boundary values at reachable sources?
    print(f"\n  Boundary values: source → reachable source transitions")
    boundary_transitions = Counter()
    for a in exc_graph:
        for ap in exc_graph[a]:
            boundary_transitions[((a[0], a[n-1]), (ap[0], ap[n-1]))] += 1
    for (ba, bap), cnt in sorted(boundary_transitions.items(),
                                  key=lambda x: -x[1])[:15]:
        print(f"    {ba} → {bap}: {cnt}")

    return exc_depth


if __name__ == '__main__':
    all_results = {}
    for nv in range(5, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        d = analyze(nv)
        all_results[nv] = d

    print(f"\n{'=' * 70}")
    print(f"SUMMARY: Excursion graph depths")
    print(f"{'=' * 70}")
    for nv, d in sorted(all_results.items()):
        print(f"  n={nv}: excursion depth = {d}")
