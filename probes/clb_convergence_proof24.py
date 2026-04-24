#!/usr/bin/env python3
"""
CONVERGENCE PROOF 24: Reverse-Anomalous Analysis & Q as Excursion Potential
==========================================================================

KEY INSIGHT from analytical work:
- P₂ = #(adjacent (2,2) pairs) is INVARIANT under all anomalous edges
  (none of the 5 anomalous entries create/destroy (2,2) pairs)
- Q = #(0,0)+#(1,1) always decreases on anomalous edges
- fc + Q + P₂ = n (partition of adjacent pairs)

CRITICAL TEST: Does Q strictly decrease on the EXCURSION GRAPH?
If so, Q is a potential for the excursion graph, proving it's a DAG,
which (combined with CUP's (fc,Ψ) for Δfc≤0) proves full convergence.

This script:
1. Verifies P₂ invariance on anomalous edges analytically
2. Tests Q as an excursion potential (the key test)
3. Analyzes reverse-anomalous table entries
4. If Q works: characterize the proof structure
5. If Q fails: analyze the failing excursion steps
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict


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
    """Q = #(adjacent same-value pairs where value ∈ {0,1})."""
    count = 0
    for j in range(n):
        a, b = c[j], c[(j + 1) % n]
        if a == b and a in (0, 1):
            count += 1
    return count


def P2_val(c, n):
    """P₂ = #(adjacent (2,2) pairs)."""
    count = 0
    for j in range(n):
        if c[j] == 2 and c[(j + 1) % n] == 2:
            count += 1
    return count


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

    # Classify all transitions
    anom_edges = []
    dfc_le0_adj = defaultdict(list)

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
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if cls == "anomalous":
                        anom_edges.append((c, succ, i, dfc))

    print(f"  Anomalous transitions (bad→bad): {len(anom_edges)}")

    # ═══════════════════════════════════════════════════════════
    # TEST 1: P₂ invariance on anomalous edges
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 1: P₂ invariance on anomalous edges")
    p2_violations = 0
    for c, succ, i, dfc in anom_edges:
        p2_c = P2_val(c, n)
        p2_s = P2_val(succ, n)
        if p2_c != p2_s:
            p2_violations += 1
            print(f"    VIOLATION: P₂ changed {p2_c}→{p2_s} at {c}→{succ}")
    print(f"    P₂ invariant: {p2_violations == 0} ({p2_violations} violations)")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Q always decreases on anomalous edges
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 2: Q decreases on anomalous edges")
    q_violations = 0
    q_deltas = defaultdict(int)
    for c, succ, i, dfc in anom_edges:
        qc = Q_val(c, n)
        qs = Q_val(succ, n)
        dq = qs - qc
        q_deltas[dq] += 1
        if dq >= 0:
            q_violations += 1
    print(f"    Q always decreases: {q_violations == 0} ({q_violations} violations)")
    print(f"    ΔQ distribution: {dict(sorted(q_deltas.items()))}")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Reverse-anomalous entry analysis
    # For each anomalous entry, check if the "reverse" is possible
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 3: Reverse-anomalous entry analysis")
    anom_entries = [
        ("T_bot", T_bot, 0, 0, 0, 1, 2, 3),  # (name, table, L, S, R, out, m_S, m_R)
        ("T_bot", T_bot, 1, 1, 2, 0, 2, 3),
        ("T_mid", T_mid, 2, 1, 1, 0, 3, 3),
        ("T_high", T_high, 1, 1, 1, 2, 3, 2),
        ("T_top", T_top, 2, 0, 0, 1, 2, 2),
    ]

    for tname, table, aL, aS, aR, aout, m_S, m_R in anom_entries:
        # The anomalous entry: (aL, aS, aR) → aout
        # For a 2-edge cycle: need a transition at same position that sends aout → aS
        # This requires table(L', aout, R') = aS for some L', R'
        # where L' and R' are the neighbor values AFTER the anomalous edge
        # (which are the same since only pos i changed)
        print(f"    {tname}({aL},{aS},{aR})→{aout}: reverse {aout}→{aS}?")
        reverse_found = False
        for L in range(3):  # max domain
            for R in range(max(m_S, m_R)):
                key = (L, aout, R)
                if key in table:
                    rev_out = table[key]
                    if rev_out == aS:
                        # Check if this is with the SAME neighbors
                        same_nbrs = (L == aL and R == aR)
                        print(f"      YES: {tname}({L},{aout},{R})→{aS}"
                              f" {'(same neighbors!)' if same_nbrs else ''}")
                        reverse_found = True
        if not reverse_found:
            print(f"      NO reverse entry found: {aout}→{aS} never happens")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Build excursion graph and test Q as potential
    # THIS IS THE KEY TEST
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 4: Q as excursion graph potential")

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_targets = set(succ for _, succ, _, _ in anom_edges)

    # For each anomalous target, BFS in Δfc≤0 subgraph to find reachable sources
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

    # Build excursion graph edges: source c → reachable source c' via anomalous + Δfc≤0
    exc_graph = defaultdict(set)
    exc_edges_detail = []  # (source, anom_target, reachable_source, anom_pos)
    for c, succ, i, dfc in anom_edges:
        for src in target_to_sources.get(succ, []):
            exc_graph[c].add(src)
            exc_edges_detail.append((c, succ, src, i))

    # Test Q as excursion potential
    q_exc_violations = 0
    q_exc_total = 0
    q_exc_violation_details = []
    for a in exc_graph:
        for ap in exc_graph[a]:
            q_exc_total += 1
            qa = Q_val(a, n)
            qap = Q_val(ap, n)
            if qap >= qa:
                q_exc_violations += 1
                q_exc_violation_details.append((a, ap, qa, qap))

    print(f"    Excursion edges: {q_exc_total}")
    print(f"    Q violations: {q_exc_violations}/{q_exc_total}")
    if q_exc_violations == 0:
        print(f"    *** Q IS A VALID EXCURSION POTENTIAL! ***")
    else:
        print(f"    Q fails as excursion potential")
        for a, ap, qa, qap in q_exc_violation_details[:5]:
            print(f"      {a} (Q={qa}) → {ap} (Q={qap})")

    # ═══════════════════════════════════════════════════════════
    # TEST 5: (Q, fc, Ψ) lexicographic as excursion potential
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 5: (Q, fc, Ψ) lex as excursion potential")
    qfp_violations = 0
    for a in exc_graph:
        for ap in exc_graph[a]:
            val_a = (Q_val(a, n), fc_val(a, n), psi(a, n))
            val_ap = (Q_val(ap, n), fc_val(ap, n), psi(ap, n))
            if val_ap >= val_a:
                qfp_violations += 1
    print(f"    (Q, fc, Ψ) violations: {qfp_violations}/{q_exc_total}")

    # ═══════════════════════════════════════════════════════════
    # TEST 6: (Q, Ψ) as excursion potential
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 6: Other Q-based excursion potentials")

    def test_exc(name, phi):
        viol = 0
        for a in exc_graph:
            for ap in exc_graph[a]:
                if phi(ap) >= phi(a):
                    viol += 1
        print(f"    {name}: {viol}/{q_exc_total}")
        return viol

    test_exc("Q alone", lambda c: Q_val(c, n))
    test_exc("(Q, Ψ)", lambda c: (Q_val(c, n), psi(c, n)))
    test_exc("(Q, P₂, fc, Ψ)", lambda c: (Q_val(c, n), P2_val(c, n),
                                             fc_val(c, n), psi(c, n)))
    test_exc("(Q, -P₂, fc, Ψ)", lambda c: (Q_val(c, n), -P2_val(c, n),
                                              fc_val(c, n), psi(c, n)))
    test_exc("(Q, fc+Q, Ψ)", lambda c: (Q_val(c, n), fc_val(c, n) + Q_val(c, n),
                                          psi(c, n)))

    # Count of 2s
    def n2(c):
        return sum(1 for v in c if v == 2)

    test_exc("(Q, n₂, fc, Ψ)", lambda c: (Q_val(c, n), n2(c), fc_val(c, n), psi(c, n)))
    test_exc("(Q, -n₂, fc, Ψ)", lambda c: (Q_val(c, n), -n2(c), fc_val(c, n), psi(c, n)))

    # Interior sum
    def isum(c):
        return sum(c[j] for j in range(2, n - 2))

    test_exc("(Q, isum, fc, Ψ)", lambda c: (Q_val(c, n), isum(c),
                                              fc_val(c, n), psi(c, n)))

    # 2·Q + fc (since Δ(2Q+fc) = 2ΔQ + Δfc; on anomalous: 2(-1)+1 = -1 or 2(-2)+2 = -2)
    test_exc("2Q+fc", lambda c: 2 * Q_val(c, n) + fc_val(c, n))
    test_exc("(2Q+fc, Ψ)", lambda c: (2 * Q_val(c, n) + fc_val(c, n), psi(c, n)))
    test_exc("(2Q+fc, fc, Ψ)", lambda c: (2 * Q_val(c, n) + fc_val(c, n),
                                            fc_val(c, n), psi(c, n)))

    # ═══════════════════════════════════════════════════════════
    # TEST 7: Net ΔQ on each excursion step
    # For each edge a→a' in excursion graph via anomalous target b:
    # decompose: ΔQ(a→b) + ΔQ(b→...→a')
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 7: ΔQ decomposition on excursion steps")
    dq_anom_hist = defaultdict(int)
    dq_path_hist = defaultdict(int)
    dq_total_hist = defaultdict(int)

    for c, succ, src, i in exc_edges_detail:
        qa = Q_val(c, n)
        qb = Q_val(succ, n)
        qap = Q_val(src, n)
        dq_anom = qb - qa
        dq_path = qap - qb
        dq_total = qap - qa
        dq_anom_hist[dq_anom] += 1
        dq_path_hist[dq_path] += 1
        dq_total_hist[dq_total] += 1

    print(f"    ΔQ(anomalous edge): {dict(sorted(dq_anom_hist.items()))}")
    print(f"    ΔQ(Δfc≤0 path):    {dict(sorted(dq_path_hist.items()))}")
    print(f"    ΔQ(total excursion): {dict(sorted(dq_total_hist.items()))}")

    # If total is always < 0, Q is an excursion potential
    max_total = max(dq_total_hist.keys()) if dq_total_hist else -999
    print(f"    Max ΔQ(total): {max_total}")
    if max_total < 0:
        print(f"    *** Q STRICTLY DECREASES ON EVERY EXCURSION STEP ***")

    # ═══════════════════════════════════════════════════════════
    # TEST 8: For violations, trace the path to understand WHY Q increases
    # ═══════════════════════════════════════════════════════════
    if q_exc_violations > 0:
        print(f"\n  TEST 8: Analyzing Q-violation excursion steps")
        for a, ap, qa, qap in q_exc_violation_details[:3]:
            print(f"    Source {a} (Q={qa}) → Target {ap} (Q={qap})")
            # Find which anomalous edge connects them
            for c, succ, src, i in exc_edges_detail:
                if c == a and src == ap:
                    qb = Q_val(succ, n)
                    L = a[(i - 1) % n]
                    S = a[i]
                    R = a[(i + 1) % n]
                    out = succ[i]
                    tname = {0: 'T_bot', 1: 'T_low', n-2: 'T_high',
                             n-1: 'T_top'}.get(i, f'T_mid[{i}]')
                    print(f"      Anomalous: {tname}({L},{S},{R})→{out}, "
                          f"ΔQ_anom={qb-qa}")
                    print(f"      Target config: {succ} (Q={qb})")
                    print(f"      Path endpoint: {ap} (Q={qap})")
                    print(f"      ΔQ_path = {qap-qb}")

                    # BFS to find shortest Δfc≤0 path from succ to ap
                    pred = {succ: None}
                    queue = deque([succ])
                    found = False
                    while queue and not found:
                        node = queue.popleft()
                        for nxt in dfc_le0_adj.get(node, []):
                            if nxt not in pred:
                                pred[nxt] = node
                                if nxt == ap:
                                    found = True
                                    break
                                queue.append(nxt)

                    if found:
                        path = []
                        cur = ap
                        while cur is not None:
                            path.append(cur)
                            cur = pred[cur]
                        path.reverse()
                        print(f"      Δfc≤0 path length: {len(path)-1}")
                        for pi, pc in enumerate(path[:8]):
                            print(f"        [{pi}] {pc} Q={Q_val(pc,n)} "
                                  f"fc={fc_val(pc,n)} Ψ={psi(pc,n)}")
                        if len(path) > 8:
                            print(f"        ... ({len(path)-8} more)")
                    break

    # ═══════════════════════════════════════════════════════════
    # TEST 9: Systematic potential search on excursion graph
    # Try all functions of form (f₁, f₂, fc, Ψ) where f₁, f₂ are
    # simple counting functions
    # ═══════════════════════════════════════════════════════════
    if q_exc_violations > 0:
        print(f"\n  TEST 9: Systematic excursion potential search")

        # Building blocks
        def make_counter(val, positions):
            """Count occurrences of val at given positions."""
            def f(c):
                return sum(1 for j in positions if c[j] == val)
            return f

        # Position sets
        all_pos = list(range(n))
        interior = list(range(2, n - 2))
        boundary = [0, 1, n - 2, n - 1]
        left_half = list(range(n // 2))
        right_half = list(range(n // 2, n))

        building_blocks = {}
        for val in [0, 1, 2]:
            building_blocks[f"#({val})_all"] = make_counter(val, all_pos)
            building_blocks[f"#({val})_int"] = make_counter(val, interior)
            building_blocks[f"#({val})_bnd"] = make_counter(val, boundary)
        building_blocks["Q"] = lambda c: Q_val(c, n)
        building_blocks["P₂"] = lambda c: P2_val(c, n)
        building_blocks["fc"] = lambda c: fc_val(c, n)
        building_blocks["Ψ"] = lambda c: psi(c, n)
        building_blocks["fc+Q"] = lambda c: fc_val(c, n) + Q_val(c, n)
        building_blocks["2Q+fc"] = lambda c: 2 * Q_val(c, n) + fc_val(c, n)

        best_name = None
        best_violations = q_exc_total + 1

        for name1, f1 in building_blocks.items():
            # Single potential
            viol = sum(1 for a in exc_graph for ap in exc_graph[a]
                       if f1(ap) >= f1(a))
            if viol < best_violations:
                best_violations = viol
                best_name = name1
            if viol == 0:
                print(f"    FOUND ZERO-VIOLATION: {name1}")

            # With (fc, Ψ) tiebreaker
            viol2 = sum(1 for a in exc_graph for ap in exc_graph[a]
                        if (f1(ap), fc_val(ap, n), psi(ap, n)) >=
                           (f1(a), fc_val(a, n), psi(a, n)))
            if viol2 == 0:
                print(f"    FOUND ZERO-VIOLATION: ({name1}, fc, Ψ)")

            # Two-level lex: (f1, f2, fc, Ψ)
            for name2, f2 in building_blocks.items():
                if name2 == name1:
                    continue
                viol3 = sum(1 for a in exc_graph for ap in exc_graph[a]
                            if (f1(ap), f2(ap), fc_val(ap, n), psi(ap, n)) >=
                               (f1(a), f2(a), fc_val(a, n), psi(a, n)))
                if viol3 == 0:
                    print(f"    FOUND ZERO-VIOLATION: ({name1}, {name2}, fc, Ψ)")

        print(f"    Best single potential: {best_name} ({best_violations} violations)")

    return q_exc_violations


if __name__ == '__main__':
    all_results = {}
    for nv in range(5, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        v = analyze(nv)
        all_results[nv] = v

    print(f"\n{'=' * 70}")
    print(f"SUMMARY: Q as excursion potential")
    print(f"{'=' * 70}")
    for nv, v in sorted(all_results.items()):
        status = "✓ ZERO VIOLATIONS" if v == 0 else f"✗ {v} violations"
        print(f"  n={nv}: {status}")
