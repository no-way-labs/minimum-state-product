#!/usr/bin/env python3
"""
CONVERGENCE PROOF — Part 10: Frozen-Rank Interaction Analysis
=============================================================

KEY INSIGHT from Part 9: The rank function is almost additive in local
3-windows (R²=0.97 for n=5). The residuals are small.

NEW APPROACH: Use the n frozen-rank functions r_0, r_1, ..., r_{n-1} together.

For a transition at position i:
  r_p STRICTLY DECREASES for all p ≠ i (since the transition is in the p-frozen DAG)
  r_i may INCREASE (since the transition is NOT in the i-frozen DAG)

Questions:
1. What is the ACTUAL maximum increase in r_i when position i fires?
2. Is the actual increase always < (n-1), which would make Σ r_p a potential?
3. Is there a WEIGHTED sum Σ w_p * r_p that always decreases?
4. What is the actual distribution of (Δr_i, Σ_{p≠i} Δr_p)?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque, Counter
import numpy as np

def compute_frozen_ranks(n):
    """Compute ALL frozen-position rank functions for given n."""
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # For each position p, compute the p-frozen rank
    frozen_ranks = {}  # p -> {config: rank}

    for freeze in range(n):
        # Build frozen graph
        adj = {c: [] for c in bad_list}
        for c in bad_list:
            for i in range(n):
                if i == freeze:
                    continue
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        # Topological sort
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

        assert len(topo) == len(bad_list), f"Position {freeze}: NOT A DAG!"

        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
        frozen_ranks[freeze] = rank

    return frozen_ranks, bad_list, bad_set, ms, fs, good_set

def analyze_frozen_rank_changes(n):
    """
    For each transition, compute the change in ALL frozen ranks.
    """
    print(f"\nFROZEN RANK CHANGE ANALYSIS (n={n})")
    print("=" * 70)

    frozen_ranks, bad_list, bad_set, ms, fs, good_set = compute_frozen_ranks(n)

    # Compute the full DAG rank too
    adj_full = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj_full[c].append((succ, i))

    # For each transition, compute Δr_p for all p
    print(f"\n  For each transition at position i:")
    print(f"  Δr_i = change in i-frozen rank (can increase)")
    print(f"  Σ Δr_{'{p≠i}'} = sum of changes in other frozen ranks (all ≤ -1)")

    # Collect statistics
    delta_i_max = {}  # position -> max Δr_i
    delta_i_stats = defaultdict(list)
    delta_others_stats = defaultdict(list)

    for c in bad_list:
        for succ, i in adj_full[c]:
            # Compute Δr_i
            dr_i = frozen_ranks[i].get(succ, 0) - frozen_ranks[i].get(c, 0)
            # Compute Σ Δr_p for p ≠ i
            dr_others = sum(frozen_ranks[p].get(succ, 0) - frozen_ranks[p].get(c, 0)
                           for p in range(n) if p != i)

            delta_i_stats[i].append(dr_i)
            delta_others_stats[i].append(dr_others)

    print(f"\n  {'Pos':>4s} {'Type':>5s} {'Max Δr_i':>10s} {'Min Δr_i':>10s} "
          f"{'Mean Δr_i':>10s} {'Max Σoth':>10s} {'Min Σoth':>10s}")
    print("  " + "-" * 65)

    for i in range(n):
        if i == 0: tt = 'bot'
        elif i == 1: tt = 'low'
        elif i == n-2: tt = 'high'
        elif i == n-1: tt = 'top'
        else: tt = 'mid'

        dri = delta_i_stats[i]
        dro = delta_others_stats[i]
        max_ri = max(dri) if dri else 0
        min_ri = min(dri) if dri else 0
        mean_ri = np.mean(dri) if dri else 0
        max_ro = max(dro) if dro else 0
        min_ro = min(dro) if dro else 0

        print(f"  {i:>4d} {tt:>5s} {max_ri:>+10d} {min_ri:>+10d} "
              f"{mean_ri:>+10.2f} {max_ro:>+10d} {min_ro:>+10d}")

    # KEY QUESTION: Is max(Δr_i) < |min(Σ Δr_others)|?
    # If so, Σ r_p is a potential function.
    print(f"\n  POTENTIAL FUNCTION TEST: Σ r_p")

    violations = 0
    total = 0
    max_net_increase = float('-inf')
    worst_transition = None

    for c in bad_list:
        sum_c = sum(frozen_ranks[p][c] for p in range(n))
        for succ, i in adj_full[c]:
            sum_s = sum(frozen_ranks[p][succ] for p in range(n))
            delta = sum_s - sum_c
            total += 1
            if delta >= 0:
                violations += 1
            if delta > max_net_increase:
                max_net_increase = delta
                worst_transition = (c, succ, i)

    print(f"  Violations: {violations}/{total} ({100*violations/total:.1f}%)")
    print(f"  Max net increase in Σr_p: {max_net_increase}")
    if worst_transition:
        c, s, i = worst_transition
        print(f"  Worst: {c} → fire P{i} → {s}")
        for p in range(n):
            dr = frozen_ranks[p][s] - frozen_ranks[p][c]
            print(f"    r_{p}: {frozen_ranks[p][c]} → {frozen_ranks[p][s]} (Δ={dr:+d})")

def analyze_weighted_sum(n):
    """
    Find optimal weights for Σ w_p * r_p to minimize violations.
    """
    print(f"\nOPTIMAL WEIGHTED FROZEN RANK SUM (n={n})")
    print("=" * 70)

    frozen_ranks, bad_list, bad_set, ms, fs, good_set = compute_frozen_ranks(n)

    # Build transition list
    transitions = []
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    transitions.append((c, succ, i))

    # For each transition, compute the vector of Δr_p
    T = len(transitions)
    delta_matrix = np.zeros((T, n))
    for idx, (c, succ, i) in enumerate(transitions):
        for p in range(n):
            delta_matrix[idx, p] = frozen_ranks[p][succ] - frozen_ranks[p][c]

    # We want: for all transitions, Σ w_p * Δr_p < 0
    # i.e., delta_matrix @ w < 0 (component-wise)
    # This is a linear feasibility problem.

    # Check if the uniform weight works
    uniform = delta_matrix @ np.ones(n)
    n_viol_uniform = np.sum(uniform >= 0)
    print(f"  Uniform weights (all 1): {n_viol_uniform}/{T} violations")

    # Try to find weights via linear programming
    # Minimize slack s such that delta_matrix @ w <= -s with s > 0
    # Or equivalently: maximize s such that delta_matrix @ w <= -s, w >= 0, ||w||=1

    # Simple approach: grid search over weight ratios for small n
    if n <= 6:
        best_violations = T
        best_weights = None
        # Try various weight vectors
        grid = np.arange(0.1, 3.1, 0.1)
        for w0 in grid:
            for w1 in grid:
                for wm in grid:
                    # All mid positions get weight wm
                    w = np.array([w0, w1] + [wm]*(n-4) + [w1, w0])
                    vals = delta_matrix @ w
                    v = np.sum(vals >= 0)
                    if v < best_violations:
                        best_violations = v
                        best_weights = w.copy()

        print(f"  Best symmetric weights: {best_violations}/{T} violations")
        if best_weights is not None:
            print(f"    Weights: {best_weights}")

    # Also try: optimize using scipy if available
    try:
        from scipy.optimize import linprog

        # We want: delta_matrix @ w < 0 for all rows
        # With normalization Σ w_p = 1 and w_p > 0
        # This is: delta_matrix @ w <= -ε for some ε > 0

        # LP: maximize ε subject to delta_matrix @ w <= -ε, Σ w_p = 1, w_p ≥ 0
        # Rewrite: delta_matrix @ w + ε ≤ 0
        # Variables: [w_0, ..., w_{n-1}, ε]

        c_obj = np.zeros(n + 1)
        c_obj[-1] = -1  # maximize ε = minimize -ε

        A_ub = np.hstack([delta_matrix, np.ones((T, 1))])  # delta @ w + ε <= 0
        b_ub = np.zeros(T)

        A_eq = np.zeros((1, n + 1))
        A_eq[0, :n] = 1  # Σ w_p = 1
        b_eq = np.array([1.0])

        bounds = [(0.001, None)] * n + [(None, None)]  # w_p > 0, ε unrestricted

        result = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                        bounds=bounds, method='highs')

        if result.success and result.x[-1] > 0:
            w_opt = result.x[:n]
            eps = result.x[-1]
            print(f"\n  LP solution: FEASIBLE with ε = {eps:.4f}")
            print(f"  Optimal weights: {w_opt}")
            # Verify
            vals = delta_matrix @ w_opt
            actual_min = np.min(vals)
            print(f"  Min weighted delta: {actual_min:.4f}")
        else:
            print(f"\n  LP solution: INFEASIBLE (no weighted sum works)")
            if result.success:
                print(f"  ε = {result.x[-1]:.4f} (≤ 0 means no solution)")
    except ImportError:
        print("  (scipy not available for LP)")

def analyze_delta_ri_bound(n):
    """
    For each position i and each transition at i,
    compute Δr_i and compare to the theoretical bound D_i.

    The key question: is the ACTUAL max Δr_i much less than D_i?
    """
    print(f"\nACTUAL vs THEORETICAL Δr_i BOUNDS (n={n})")
    print("=" * 70)

    frozen_ranks, bad_list, bad_set, ms, fs, good_set = compute_frozen_ranks(n)

    for i in range(n):
        D_i = max(frozen_ranks[i].values())  # theoretical max depth

        actual_max_increase = 0
        for c in bad_list:
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    dr = frozen_ranks[i][succ] - frozen_ranks[i][c]
                    if dr > actual_max_increase:
                        actual_max_increase = dr

        ratio = actual_max_increase / D_i if D_i > 0 else 0
        if i == 0: tt = 'bot'
        elif i == 1: tt = 'low'
        elif i == n-2: tt = 'high'
        elif i == n-1: tt = 'top'
        else: tt = 'mid'

        print(f"  P{i} ({tt:>4s}): D_i={D_i:>3d}, actual max Δr_i={actual_max_increase:>+3d}, "
              f"ratio={ratio:.3f}")

def test_frozen_rank_sum_potential(n):
    """
    Test the sum Σ_p r_p as a potential function.
    Also test whether the sum decreases on EVERY transition
    (not just most transitions).
    """
    print(f"\nFROZEN RANK SUM AS POTENTIAL (n={n})")
    print("=" * 70)

    frozen_ranks, bad_list, bad_set, ms, fs, good_set = compute_frozen_ranks(n)

    # Compute sum for each config
    rank_sum = {c: sum(frozen_ranks[p][c] for p in range(n)) for c in bad_list}

    # Check every transition
    violations = []
    total = 0
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    total += 1
                    delta = rank_sum[succ] - rank_sum[c]
                    if delta >= 0:
                        violations.append((c, succ, i, delta))

    print(f"  Transitions: {total}")
    print(f"  Violations (Σr increases or stays): {len(violations)}/{total}")
    if violations:
        print(f"  Violation details:")
        for c, s, i, d in violations[:20]:
            drs = [frozen_ranks[p][s] - frozen_ranks[p][c] for p in range(n)]
            dr_str = ", ".join(f"{dr:+d}" for dr in drs)
            print(f"    {c} → fire P{i} → Δ={d:+d} [{dr_str}]")

def test_max_frozen_rank_potential(n):
    """
    Test max_p r_p as a potential function.
    """
    print(f"\nMAX FROZEN RANK AS POTENTIAL (n={n})")
    print("=" * 70)

    frozen_ranks, bad_list, bad_set, ms, fs, good_set = compute_frozen_ranks(n)

    rank_max = {c: max(frozen_ranks[p][c] for p in range(n)) for c in bad_list}

    violations = 0
    total = 0
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    total += 1
                    if rank_max[succ] >= rank_max[c]:
                        violations += 1

    print(f"  Violations: {violations}/{total} ({100*violations/total:.1f}%)")

def test_composition_potential(n):
    """
    Test the potential: (settled_count, -Σr_p)
    Lexicographic: first compare by settled_count (should increase),
    then by -Σr_p (should decrease, i.e., Σr_p should increase).

    Wait, we need BOTH directions to work:
    - settled_count should increase (good direction)
    - When settled_count is tied, need a tiebreaker

    Actually: define φ(c) = (n - settled(c), Σr_p(c))
    Transitions should decrease φ lexicographically.
    - n-settled usually decreases (good) → φ[0] decreases
    - When tied, need Σr_p to decrease → need sum of frozen ranks to decrease
    """
    print(f"\nCOMPOSITION POTENTIAL TEST (n={n})")
    print("=" * 70)

    frozen_ranks, bad_list, bad_set, ms, fs, good_set = compute_frozen_ranks(n)
    rank_sum = {c: sum(frozen_ranks[p][c] for p in range(n)) for c in bad_list}

    def settled(c):
        count = 0
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) == S:
                count += 1
        return count

    # Test (n-settled, rank_sum) as lexicographic potential
    violations_lex = 0
    total = 0
    delta_settled_dist = Counter()

    for c in bad_list:
        sc = settled(c)
        rs = rank_sum[c]
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    total += 1
                    sc2 = settled(succ)
                    rs2 = rank_sum[succ]
                    delta_s = sc2 - sc

                    # Lexicographic: (n-sc, rs) should decrease
                    # i.e., (n-sc2, rs2) < (n-sc, rs)
                    # i.e., sc2 > sc, or (sc2 == sc and rs2 < rs)
                    if sc2 < sc:
                        violations_lex += 1  # unsettled count increased
                    elif sc2 == sc and rs2 >= rs:
                        violations_lex += 1  # tied and sum didn't decrease

    print(f"  LEX(-unsettled, -Σr_p): {violations_lex}/{total} violations "
          f"({100*violations_lex/total:.1f}%)")

    # What about (-unsettled, rank_sum) where rank_sum must INCREASE (since individual
    # transitions decrease rank)?
    # No, this doesn't make sense.

    # Let's try: (-unsettled, full_rank) where full_rank is the actual DAG rank
    # Full DAG rank
    adj_full = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj_full[c].append(succ)

    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s in adj_full[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj_full[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    full_rank = {}
    for c in reversed(topo):
        full_rank[c] = max((full_rank[s] + 1 for s in adj_full[c]), default=0)

    # Test settled count as first lex component
    settled_always_inc = True
    settled_inc_or_tied = True
    rank_dec_when_settled_tied = True

    viol_settled_dec = 0
    viol_tied_rank = 0

    for c in bad_list:
        sc = settled(c)
        for s in adj_full[c]:
            sc2 = settled(s)
            if sc2 < sc:
                settled_always_inc = False
                viol_settled_dec += 1
            elif sc2 == sc:
                if full_rank[s] >= full_rank[c]:
                    rank_dec_when_settled_tied = False
                    viol_tied_rank += 1

    total_trans = sum(len(adj_full[c]) for c in bad_list)
    print(f"\n  Settled analysis:")
    print(f"    settled DECREASES: {viol_settled_dec}/{total_trans} "
          f"({100*viol_settled_dec/total_trans:.1f}%)")
    print(f"    settled TIED + rank NOT decreasing: {viol_tied_rank}/{total_trans} "
          f"({100*viol_tied_rank/total_trans:.1f}%)")

    # When settled decreases, how much does rank decrease?
    if viol_settled_dec > 0:
        print(f"\n  When settled DECREASES:")
        for c in bad_list:
            sc = settled(c)
            for s in adj_full[c]:
                if settled(s) < sc:
                    dr = full_rank[s] - full_rank[c]
                    print(f"    {c} → {s}: Δsettle={settled(s)-sc}, Δrank={dr}")

def main():
    for n in [5, 6, 7]:
        print("\n" + "=" * 70)
        print(f"FROZEN RANK ANALYSIS FOR n={n}")
        print("=" * 70)

        analyze_frozen_rank_changes(n)
        analyze_delta_ri_bound(n)
        test_frozen_rank_sum_potential(n)
        test_max_frozen_rank_potential(n)

        if n <= 6:
            analyze_weighted_sum(n)
            test_composition_potential(n)

if __name__ == "__main__":
    main()
