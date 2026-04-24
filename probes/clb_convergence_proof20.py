#!/usr/bin/env python3
"""
CONVERGENCE PROOF 20: Excursion Potential Discovery
====================================================

PROVEN SO FAR:
- (fc, Ψ) lex is a valid potential for the Δfc≤0 subgraph (all n)
- Excursion graph (anomalous source → Δfc≤0 path → anomalous source)
  has NO cycles for n=5..9

THIS SCRIPT: Find the potential function on the excursion graph.

Key hypothesis: Ψ (or some modified quantity) strictly decreases along
excursion chains: if source a takes anomalous edge to b, and b reaches
source a' via Δfc≤0 paths, then Ψ(a') < Ψ(a).

If true, this gives a proof:
1. Between anomalous firings, (fc, Ψ) lex decreases (proved by CUP)
2. At anomalous firing boundaries, the excursion potential decreases
3. Since the excursion potential is bounded below, no infinite path = DAG
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict, Counter


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


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


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

    # ═══════════════════════════════════════════════════════════
    # Build excursion graph with full metadata
    # ═══════════════════════════════════════════════════════════
    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_targets = set(succ for _, succ, _, _ in anom_edges)

    # For each anomalous target, BFS to find reachable anomalous sources
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

    # Build excursion graph: source → reachable sources (via anomalous + Δfc≤0)
    exc_graph = defaultdict(set)
    for c, succ, i, dfc in anom_edges:
        for src in target_to_sources.get(succ, []):
            exc_graph[c].add(src)

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Does Ψ decrease along excursion chains?
    # For each edge a → a' in excursion graph: is Ψ(a') < Ψ(a)?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 1: Ψ monotonicity on excursion graph")
    psi_violations = 0
    psi_strict = 0
    psi_equal = 0
    psi_decrease = 0
    psi_viol_examples = []
    for a in exc_graph:
        pa = psi(a, n)
        for ap in exc_graph[a]:
            pap = psi(ap, n)
            if pap < pa:
                psi_decrease += 1
            elif pap == pa:
                psi_equal += 1
            elif pap > pa:
                psi_violations += 1
                if len(psi_viol_examples) < 5:
                    psi_viol_examples.append((a, ap, pa, pap))
    total_exc = psi_decrease + psi_equal + psi_violations
    print(f"    Ψ decreases: {psi_decrease}/{total_exc}")
    print(f"    Ψ equal: {psi_equal}/{total_exc}")
    print(f"    Ψ increases (violations): {psi_violations}/{total_exc}")
    for a, ap, pa, pap in psi_viol_examples:
        print(f"      {a} (Ψ={pa}) → {ap} (Ψ={pap})")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Does fc decrease along excursion chains?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 2: fc monotonicity on excursion graph")
    fc_violations = 0
    fc_equal = 0
    fc_decrease = 0
    for a in exc_graph:
        fa = fc(a, n)
        for ap in exc_graph[a]:
            fap = fc(ap, n)
            if fap < fa:
                fc_decrease += 1
            elif fap == fa:
                fc_equal += 1
            else:
                fc_violations += 1
    total_exc = fc_decrease + fc_equal + fc_violations
    print(f"    fc decreases: {fc_decrease}/{total_exc}")
    print(f"    fc equal: {fc_equal}/{total_exc}")
    print(f"    fc increases (violations): {fc_violations}/{total_exc}")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Does (fc, Ψ) lex decrease on excursion graph?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 3: (fc, Ψ) lex monotonicity on excursion graph")
    lex_violations = 0
    lex_equal = 0
    lex_decrease = 0
    lex_viol_examples = []
    for a in exc_graph:
        fa = fc(a, n)
        pa = psi(a, n)
        for ap in exc_graph[a]:
            fap = fc(ap, n)
            pap = psi(ap, n)
            pair_a = (fa, pa)
            pair_ap = (fap, pap)
            if pair_ap < pair_a:
                lex_decrease += 1
            elif pair_ap == pair_a:
                lex_equal += 1
            else:
                lex_violations += 1
                if len(lex_viol_examples) < 5:
                    lex_viol_examples.append((a, ap, pair_a, pair_ap))
    total_exc = lex_decrease + lex_equal + lex_violations
    print(f"    (fc,Ψ) lex decreases: {lex_decrease}/{total_exc}")
    print(f"    (fc,Ψ) lex equal: {lex_equal}/{total_exc}")
    print(f"    (fc,Ψ) lex increases (violations): {lex_violations}/{total_exc}")
    for a, ap, pa, pap in lex_viol_examples:
        print(f"      {a} ({pa}) → {ap} ({pap})")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Characterize anomalous source structure
    # What do anomalous sources look like? fc values, positions
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 4: Anomalous source characterization")
    src_fc_dist = Counter(fc(a, n) for a in anom_sources)
    print(f"    fc distribution of anom sources: {dict(sorted(src_fc_dist.items()))}")

    # For each anomalous source, which anomalous entry fires?
    src_entry_dist = Counter()
    for c, succ, i, dfc in anom_edges:
        L = c[(i - 1) % n]
        S = c[i]
        R = c[(i + 1) % n]
        out = succ[i]
        tname = {0: 'T_bot', 1: 'T_low', n-2: 'T_high', n-1: 'T_top'}.get(i, 'T_mid')
        src_entry_dist[(tname, i, L, S, R, out)] += 1
    print(f"    Anomalous entries firing:")
    for (tn, pos, L, S, R, out), cnt in sorted(src_entry_dist.items()):
        print(f"      {tn}(P{pos}): ({L},{S},{R})→{out}, {cnt}x")

    # ═══════════════════════════════════════════════════════════
    # TEST 5: Per-anomalous-entry excursion analysis
    # For each entry type, what's the (fc,Ψ) dynamics?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 5: Per-entry excursion dynamics")

    # Group anom edges by entry type
    entry_groups = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        L = c[(i - 1) % n]
        S = c[i]
        R = c[(i + 1) % n]
        out = succ[i]
        tname = {0: 'T_bot', 1: 'T_low', n-2: 'T_high', n-1: 'T_top'}.get(i, 'T_mid')
        entry_groups[(tname, i, L, S, R, out)].append((c, succ, i, dfc))

    for (tn, pos, L, S, R, out), edges in sorted(entry_groups.items()):
        # For these edges: what (fc,Ψ) do sources have, and targets?
        src_fc_psi = [(fc(c, n), psi(c, n)) for c, _, _, _ in edges]
        tgt_fc_psi = [(fc(s, n), psi(s, n)) for _, s, _, _ in edges]

        src_fc_vals = sorted(set(f for f, p in src_fc_psi))
        tgt_fc_vals = sorted(set(f for f, p in tgt_fc_psi))
        src_psi_range = (min(p for _, p in src_fc_psi), max(p for _, p in src_fc_psi))
        tgt_psi_range = (min(p for _, p in tgt_fc_psi), max(p for _, p in tgt_fc_psi))

        # Check excursion: what (fc,Ψ) do reachable sources have?
        reachable_fc_psi = []
        for c, succ, _, _ in edges:
            for src in target_to_sources.get(succ, []):
                reachable_fc_psi.append((fc(src, n), psi(src, n)))

        print(f"\n    {tn}(P{pos}): ({L},{S},{R})→{out}, Δfc=+{delta_fc(L,S,R,out)}")
        print(f"      Source fc: {src_fc_vals}, Ψ range: {src_psi_range}")
        print(f"      Target fc: {tgt_fc_vals}, Ψ range: {tgt_psi_range}")
        if reachable_fc_psi:
            reach_fc_vals = sorted(set(f for f, p in reachable_fc_psi))
            reach_psi_range = (min(p for _, p in reachable_fc_psi),
                               max(p for _, p in reachable_fc_psi))
            print(f"      Reachable source fc: {reach_fc_vals}, Ψ range: {reach_psi_range}")
        else:
            print(f"      No reachable anomalous sources (dead end)")

    # ═══════════════════════════════════════════════════════════
    # TEST 6: STRONGEST TEST - excursion-level (fc,Ψ) gap
    # For each anom edge a→b, and each reachable source a' from b:
    # Compare (fc(a), Ψ(a)) with (fc(a'), Ψ(a'))
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 6: Excursion gap analysis (per-edge)")
    n_edges_checked = 0
    n_fc_gap = 0  # fc(a') < fc(a)
    n_fc_equal = 0  # fc(a') = fc(a)
    n_fc_above = 0  # fc(a') > fc(a)
    n_psi_gap_when_fc_eq = 0
    n_psi_equal_when_fc_eq = 0
    n_psi_above_when_fc_eq = 0
    worst_examples = []

    for c, succ, i, dfc in anom_edges:
        fc_src = fc(c, n)
        psi_src = psi(c, n)
        for ap in target_to_sources.get(succ, []):
            fc_ap = fc(ap, n)
            psi_ap = psi(ap, n)
            n_edges_checked += 1
            if fc_ap < fc_src:
                n_fc_gap += 1
            elif fc_ap == fc_src:
                n_fc_equal += 1
                if psi_ap < psi_src:
                    n_psi_gap_when_fc_eq += 1
                elif psi_ap == psi_src:
                    n_psi_equal_when_fc_eq += 1
                    worst_examples.append((c, succ, ap, fc_src, psi_src, fc_ap, psi_ap))
                else:
                    n_psi_above_when_fc_eq += 1
                    worst_examples.append((c, succ, ap, fc_src, psi_src, fc_ap, psi_ap))
            else:
                n_fc_above += 1
                worst_examples.append((c, succ, ap, fc_src, psi_src, fc_ap, psi_ap))

    print(f"    Total excursion edges checked: {n_edges_checked}")
    print(f"    fc(a') < fc(a): {n_fc_gap}")
    print(f"    fc(a') = fc(a): {n_fc_equal}")
    print(f"      of which Ψ(a') < Ψ(a): {n_psi_gap_when_fc_eq}")
    print(f"      of which Ψ(a') = Ψ(a): {n_psi_equal_when_fc_eq}")
    print(f"      of which Ψ(a') > Ψ(a): {n_psi_above_when_fc_eq}")
    print(f"    fc(a') > fc(a): {n_fc_above}")

    if n_fc_above + n_psi_above_when_fc_eq + n_psi_equal_when_fc_eq == 0:
        print(f"    *** (fc,Ψ) LEX STRICTLY DECREASES ON EXCURSION GRAPH ***")
    elif n_fc_above + n_psi_above_when_fc_eq == 0:
        if n_psi_equal_when_fc_eq > 0:
            print(f"    (fc,Ψ) lex NON-INCREASING (but {n_psi_equal_when_fc_eq} equalities)")
    else:
        print(f"    (fc,Ψ) violations: {n_fc_above + n_psi_above_when_fc_eq}")

    if worst_examples:
        print(f"    Worst examples:")
        for c, succ, ap, fc_s, ps, fap, pap in worst_examples[:10]:
            print(f"      src {c} (fc={fc_s},Ψ={ps}) →[anom]→ {succ} →[Δfc≤0]→ "
                  f"{ap} (fc={fap},Ψ={pap})")

    # ═══════════════════════════════════════════════════════════
    # TEST 7: Try modified Ψ with different weights
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 7: Modified potential search")

    # Try: Φ = a*fc + b*Ψ for various (a,b)
    # This is a linear combination. For Δfc≤0 subgraph: need aΔfc + bΔΨ < 0.
    # CUP proved: lex (fc, Ψ) works, meaning:
    #   if Δfc < 0: done (any Ψ)
    #   if Δfc = 0: ΔΨ < 0
    # Linear combo afc + bΨ works if: a*Δfc + b*ΔΨ < 0 for all transitions
    # For Δfc=0: need b*ΔΨ < 0 → b > 0 (since ΔΨ < 0)
    # For Δfc<0: need a*Δfc + b*ΔΨ < 0 → a > b*max(ΔΨ)/(-min(Δfc))

    # Compute max ΔΨ on Δfc<0 edges and min Δfc
    max_psi_up_on_fc_down = 0  # max ΔΨ when Δfc < 0
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
                    dfc_val = delta_fc(L, S, R, out)
                    dpsi = psi(succ, n) - psi(c, n)
                    if dfc_val < 0 and dpsi > max_psi_up_on_fc_down:
                        max_psi_up_on_fc_down = dpsi

    print(f"    Max ΔΨ when Δfc<0: {max_psi_up_on_fc_down}")

    # For Φ = a*fc + Ψ: need a > max_psi_up_on_fc_down
    # Try Φ = K*fc + Ψ for various K
    for K in [max_psi_up_on_fc_down + 1, 2*n, 3*n, n*n]:
        n_violations = 0
        for c in bad_list:
            for i in range(n):
                L_v = c[(i - 1) % n]
                S_v = c[i]
                R_v = c[(i + 1) % n]
                out_v = fs[i](L_v, S_v, R_v)
                if out_v != S_v:
                    lst = list(c)
                    lst[i] = out_v
                    succ = tuple(lst)
                    if succ in bad_set:
                        phi_c = K * fc(c, n) + psi(c, n)
                        phi_s = K * fc(succ, n) + psi(succ, n)
                        if phi_s >= phi_c:
                            n_violations += 1
        total_trans = sum(1 for c in bad_list for i in range(n)
                         if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i]
                         and tuple(list(c)[:i] + [fs[i](c[(i-1)%n], c[i], c[(i+1)%n])] + list(c)[i+1:]) in bad_set)
        print(f"    Φ = {K}*fc + Ψ: {n_violations}/{total_trans} violations")

    # ═══════════════════════════════════════════════════════════
    # TEST 8: n²*fc + Ψ — is this the universal potential?
    # ═══════════════════════════════════════════════════════════
    K = n * n
    print(f"\n  TEST 8: Φ = n²·fc + Ψ = {K}·fc + Ψ")
    # Check ALL transitions
    violations = []
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
                    phi_c = K * fc(c, n) + psi(c, n)
                    phi_s = K * fc(succ, n) + psi(succ, n)
                    if phi_s >= phi_c:
                        dfc = delta_fc(L, S, R, out)
                        cls = classify_entry(L, S, R, out)
                        violations.append((c, succ, i, phi_c, phi_s, dfc, cls))

    if not violations:
        print(f"    *** ZERO VIOLATIONS! Φ = {K}·fc + Ψ IS A VALID POTENTIAL! ***")
    else:
        print(f"    {len(violations)} violations")
        for c, succ, i, pc, ps, dfc, cls in violations[:10]:
            print(f"      {c}→{succ}: Φ={pc}→{ps}, Δfc={dfc:+d}, type={cls}")

    return len(violations) if violations else 0


if __name__ == '__main__':
    all_results = {}
    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        v = analyze(nv)
        all_results[nv] = v

    print(f"\n{'=' * 70}")
    print(f"SUMMARY")
    print(f"{'=' * 70}")
    for nv, v in sorted(all_results.items()):
        status = "POTENTIAL FOUND" if v == 0 else f"{v} violations"
        print(f"  n={nv}: {status}")
