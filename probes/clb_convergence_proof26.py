#!/usr/bin/env python3
"""
CONVERGENCE PROOF 26: Full DAG Rank Analysis
=============================================

Compute the FULL DAG rank for every bad config and correlate with
config features to find a closed-form formula.

Key insight from proof24: Q=0 ⟹ no anomalous edge enabled.
So configs with Q=0 are "absorbed" into the Δfc≤0 DAG.

This script:
1. Compute full DAG rank for each bad config
2. Stratify by (fc, Q) and look for rank formulas
3. Test if rank = f(interior) + g(boundary) is separable
4. Check if rank correlates with (Q, fc, Ψ) or (Q, Ψ)
5. Find the EXACT potential by testing all simple formulas
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict, Counter


def fc_val(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


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


def Q_val(c, n):
    return sum(1 for j in range(n) if c[j] == c[(j + 1) % n] and c[j] in (0, 1))


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

    # Build adjacency
    adj = defaultdict(list)
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
                    adj[c].append(succ)

    # Compute DAG rank via reverse topological order
    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s in adj[c]:
            in_deg[s] += 1

    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    assert len(topo) == len(bad_list), "NOT A DAG!"

    rank = {}
    for c in reversed(topo):
        rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)

    max_rank = max(rank.values())
    print(f"  Max DAG depth: {max_rank}")

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Rank distribution by (fc, Q)
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 1: Rank stats by (fc, Q)")
    fq_stats = defaultdict(list)
    for c in bad_list:
        fq_stats[(fc_val(c, n), Q_val(c, n))].append(rank[c])

    print(f"    {'(fc,Q)':>8} {'count':>6} {'min_r':>6} {'max_r':>6} {'avg_r':>8}")
    for key in sorted(fq_stats.keys()):
        ranks = fq_stats[key]
        print(f"    {str(key):>8} {len(ranks):>6} {min(ranks):>6} "
              f"{max(ranks):>6} {sum(ranks)/len(ranks):>8.1f}")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Does rank = α·Ψ_max·fc + β·Ψ + γ·Q + ... ?
    # Linear regression of rank on (fc, Ψ, Q)
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 2: Linear regression rank ~ fc + Ψ + Q")
    N = len(bad_list)
    features = []
    targets = []
    for c in bad_list:
        f = fc_val(c, n)
        p = psi(c, n)
        qq = Q_val(c, n)
        features.append((1, f, p, qq, f * p, f * qq, p * qq))
        targets.append(rank[c])

    # Simple least squares (manual, no numpy)
    # Just compute correlations
    mean_r = sum(targets) / N
    var_r = sum((t - mean_r) ** 2 for t in targets) / N

    for idx, fname in enumerate(["const", "fc", "Ψ", "Q", "fc·Ψ", "fc·Q", "Ψ·Q"]):
        vals = [f[idx] for f in features]
        mean_v = sum(vals) / N
        cov = sum((vals[i] - mean_v) * (targets[i] - mean_r) for i in range(N)) / N
        var_v = sum((v - mean_v) ** 2 for v in vals) / N
        if var_v > 0 and var_r > 0:
            corr = cov / (var_v ** 0.5 * var_r ** 0.5)
        else:
            corr = 0
        print(f"    corr(rank, {fname:>5}) = {corr:+.4f}")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Test candidate potentials on FULL graph
    # A valid potential must STRICTLY DECREASE on every edge
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 3: Full-graph potential search")
    total_edges = sum(len(adj[c]) for c in bad_list)

    def test_pot(name, phi):
        viol = 0
        for c in bad_list:
            for s in adj[c]:
                if phi(s) >= phi(c):
                    viol += 1
        pct = 100 * viol / total_edges if total_edges > 0 else 0
        print(f"    {name:>35}: {viol:>7}/{total_edges} ({pct:.1f}%)")
        return viol

    # Known potentials
    test_pot("(fc, Ψ) lex",
             lambda c: (fc_val(c, n), psi(c, n)))
    test_pot("(Q, fc, Ψ) lex",
             lambda c: (Q_val(c, n), fc_val(c, n), psi(c, n)))
    test_pot("(-Q, fc, Ψ) lex",
             lambda c: (-Q_val(c, n), fc_val(c, n), psi(c, n)))

    # Key new idea: (fc+Q, Ψ) — since fc+Q = n - P₂
    test_pot("(fc+Q, Ψ) lex",
             lambda c: (fc_val(c, n) + Q_val(c, n), psi(c, n)))

    # Linearized: Ψ_max * fc + Ψ
    psi_max = max(psi(c, n) for c in bad_list) + 1
    test_pot(f"Ψ_max·fc + Ψ (Ψ_max={psi_max})",
             lambda c: psi_max * fc_val(c, n) + psi(c, n))

    # The linearized version should work for Δfc≤0 edges
    # Count violations split by anomalous vs non-anomalous
    anom_viol = 0
    nonanom_viol = 0
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
                    phi_c = psi_max * fc_val(c, n) + psi(c, n)
                    phi_s = psi_max * fc_val(succ, n) + psi(succ, n)
                    if phi_s >= phi_c:
                        if out != L and out != R:
                            anom_viol += 1
                        else:
                            nonanom_viol += 1
    print(f"    Ψ_max·fc+Ψ violations: {anom_viol} anomalous, "
          f"{nonanom_viol} non-anomalous")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: The CORRECT potential must satisfy:
    #   Φ(c) > Φ(c') for ALL edges c→c'
    # Since the DAG rank IS such a function, correlate rank
    # with candidate formulas
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 4: Rank correlation with candidate formulas")

    def corr_with_rank(phi):
        vals = [phi(c) for c in bad_list]
        mean_v = sum(vals) / N
        cov = sum((vals[i] - mean_v) * (targets[i] - mean_r) for i in range(N)) / N
        var_v = sum((v - mean_v) ** 2 for v in vals) / N
        if var_v > 0 and var_r > 0:
            return cov / (var_v ** 0.5 * var_r ** 0.5)
        return 0

    candidates = {
        "Ψ_max·fc + Ψ": lambda c: psi_max * fc_val(c, n) + psi(c, n),
        "fc": lambda c: fc_val(c, n),
        "Ψ": lambda c: psi(c, n),
        "Q": lambda c: Q_val(c, n),
        "fc + Q": lambda c: fc_val(c, n) + Q_val(c, n),
        "fc · Q": lambda c: fc_val(c, n) * Q_val(c, n),
        "Ψ + Q": lambda c: psi(c, n) + Q_val(c, n),
        "Ψ · Q": lambda c: psi(c, n) * Q_val(c, n),
        "Ψ_max·fc + Ψ + Q": lambda c: psi_max * fc_val(c, n) + psi(c, n) + Q_val(c, n),
        "2Ψ_max·Q + Ψ_max·fc + Ψ": lambda c: 2 * psi_max * Q_val(c, n) + psi_max * fc_val(c, n) + psi(c, n),
        "int_sum": lambda c: sum(c[j] for j in range(2, n - 2)),
        "c[2]": lambda c: c[2],
        "sum(c)": lambda c: sum(c),
    }

    for name, phi in sorted(candidates.items(), key=lambda x: -abs(corr_with_rank(x[1]))):
        r = corr_with_rank(phi)
        print(f"    corr(rank, {name:>30}) = {r:+.4f}")

    # ═══════════════════════════════════════════════════════════
    # TEST 5: Exact match search
    # For each candidate Φ, check if rank(c) is a monotone
    # function of Φ(c) — i.e., Φ(c) > Φ(c') ⟹ rank(c) > rank(c')
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 5: Monotonicity check (is rank monotone in Φ?)")

    for name, phi in candidates.items():
        # Group by phi value, check if rank ranges don't overlap
        phi_groups = defaultdict(list)
        for c in bad_list:
            phi_groups[phi(c)].append(rank[c])
        sorted_phi = sorted(phi_groups.keys())
        monotone = True
        for i in range(len(sorted_phi) - 1):
            max_lower = max(phi_groups[sorted_phi[i]])
            min_upper = min(phi_groups[sorted_phi[i + 1]])
            if max_lower >= min_upper:
                monotone = False
                break
        print(f"    {name:>35}: {'MONOTONE ✓' if monotone else 'NOT monotone'}")

    # ═══════════════════════════════════════════════════════════
    # TEST 6: Analyze configs at same rank — what varies?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 6: Config feature variance within rank levels")
    rank_groups = defaultdict(list)
    for c in bad_list:
        rank_groups[rank[c]].append(c)

    # For top 5 rank levels, show fc, Ψ, Q ranges
    for r_val in sorted(rank_groups.keys(), reverse=True)[:8]:
        configs = rank_groups[r_val]
        fcs = [fc_val(c, n) for c in configs]
        psis = [psi(c, n) for c in configs]
        qs = [Q_val(c, n) for c in configs]
        ints = [sum(c[j] for j in range(2, n - 2)) for c in configs]
        print(f"    rank={r_val:>3}: {len(configs):>4} configs, "
              f"fc=[{min(fcs)},{max(fcs)}], "
              f"Ψ=[{min(psis)},{max(psis)}], "
              f"Q=[{min(qs)},{max(qs)}], "
              f"int_sum=[{min(ints)},{max(ints)}]")

    return max_rank


if __name__ == '__main__':
    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        analyze(nv)
