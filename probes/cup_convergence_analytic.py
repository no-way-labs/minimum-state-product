#!/usr/bin/env python3
"""CUP: Attempt analytic convergence proof via frontier potential functions.

Key observations:
- d_i = (c_{i+1} - c_i) % 3 for linear differences (0..n-2), d_{n-1} = (c_0 - c_{n-1}) % 3
- Type-1 frontier at position i: d_i = 1 (value increases by 1 going right)
- Type-2 frontier at position i: d_i = 2 (value increases by 2 going right)
- Constraint: sum(d_i) ≡ 0 (mod 3)

Middle move dynamics:
- Copy-R at P_i (d_i=1): d_i→0, d_{i-1} changes by +1 mod 3
  - If d_{i-1}=0: shift type-1 from i to i-1 (leftward). Δfrontiers=0.
  - If d_{i-1}=1: type change 1→2 at i-1, destroy at i. Δfrontiers=0.
  - If d_{i-1}=2: annihilation! Destroy both. Δfrontiers=-2.

- Copy-L at P_i (d_{i-1}=2): d_{i-1}→0, d_i changes by +2 mod 3
  - If d_i=0: shift type-2 from i-1 to i (rightward). Δfrontiers=0.
  - If d_i=1: annihilation! Destroy both. Δfrontiers=-2.
  - If d_i=2: type change 2→1 at i, destroy at i-1. Δfrontiers=0.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict


def sol3_v1_rules(ms, n):
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f
    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f
    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f
    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def get_privileged(c, fs, n):
    priv = []
    for i in range(n):
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(c, i, fs, n):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    lst = list(c); lst[i] = fs[i](L, S, R); return tuple(lst)


def get_frontiers(c, n):
    """Return dict: position -> type (1 or 2) for each frontier."""
    frontiers = {}
    for i in range(n):
        d = (c[(i+1) % n] - c[i]) % 3
        if d != 0:
            frontiers[i] = d
    return frontiers


def frontier_count(c, n):
    return sum(1 for i in range(n) if (c[(i+1) % n] - c[i]) % 3 != 0)


# ========= POTENTIAL FUNCTION CANDIDATES =========

def phi_weighted_distance(c, n):
    """Type-1 frontiers weighted by distance to bottom (position i → weight i).
    Type-2 frontiers weighted by distance to top (position i → weight n-2-i).
    For positions 0..n-2 (linear), and n-1 (wrap).
    """
    total = 0
    for i in range(n):
        d = (c[(i+1) % n] - c[i]) % 3
        if d == 1:
            # Type-1 propagates left (toward bottom). Weight = distance to bottom.
            # Position i frontier → weight i (for interior i=0..n-2)
            total += i + 1  # +1 to avoid weight 0
        elif d == 2:
            # Type-2 propagates right (toward top). Weight = distance to top.
            total += (n - 1 - i) + 1  # +1 to avoid weight 0
    return total


def phi_distance_product(c, n):
    """Sum of (position + 1) for each frontier, regardless of type."""
    total = 0
    for i in range(n):
        d = (c[(i+1) % n] - c[i]) % 3
        if d != 0:
            total += i + 1
    return total


def phi_frontier_count(c, n):
    return frontier_count(c, n)


def phi_max_distance(c, n):
    """Lexicographic: (frontier_count, sum of weighted distances)."""
    fc = frontier_count(c, n)
    wd = phi_weighted_distance(c, n)
    return (fc, wd)


def phi_frontier_type_sum(c, n):
    """Sum of (n * frontier_count + position_weighted_type).
    Idea: frontiers count most, then positions break ties."""
    fc = frontier_count(c, n)
    wd = phi_weighted_distance(c, n)
    return fc * n * n + wd


def phi_pair_potential(c, n):
    """For each pair of frontiers of opposite type, sum their distance.
    Captures the idea that annihilation happens when they meet."""
    frontiers = get_frontiers(c, n)
    type1 = sorted([pos for pos, t in frontiers.items() if t == 1])
    type2 = sorted([pos for pos, t in frontiers.items() if t == 2])

    # Also count total frontiers
    fc = len(type1) + len(type2)

    # For pair potential: match type-1 and type-2 greedily
    # (they annihilate when adjacent)
    pair_dist = 0
    for p1 in type1:
        for p2 in type2:
            # Linear distance between positions
            d = abs(p1 - p2)
            pair_dist += d

    return (fc, pair_dist)


def phi_entropy(c, n):
    """Number of distinct values that appear more than once, negated.
    Idea: convergence increases homogeneity."""
    from collections import Counter
    cnt = Counter(c)
    return len(cnt)


# ========= TESTING FRAMEWORK =========

def test_potential(phi_name, phi_fn, n, verbose=False):
    """Test if phi is strictly decreasing on every bad→bad move.
    Also test if phi is non-increasing on every bad→good move."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    violations = 0
    total_moves = 0
    worst_increase = None

    for c in bad_set:
        priv = get_privileged(c, fs, n)
        phi_c = phi_fn(c, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            total_moves += 1
            if succ in bad_set:
                phi_s = phi_fn(succ, n)
                if phi_s >= phi_c:
                    violations += 1
                    if verbose and violations <= 5:
                        fc = get_frontiers(c, n)
                        fs_f = get_frontiers(succ, n)
                        print(f"  VIOLATION: {c} (Φ={phi_c}, F={fc}) "
                              f"--P{p}--> {succ} (Φ={phi_s}, F={fs_f})")
                    if worst_increase is None or phi_s - phi_c > worst_increase[0]:
                        worst_increase = (phi_s - phi_c, c, p, succ)

    bad_good = 0
    bad_good_total = 0
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        phi_c = phi_fn(c, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in good_set:
                bad_good_total += 1
                phi_s = phi_fn(succ, n)
                if phi_s > phi_c:
                    bad_good += 1

    print(f"  {phi_name} n={n}: {violations}/{total_moves} bad→bad violations"
          f" ({bad_good}/{bad_good_total} bad→good increases)")
    if worst_increase:
        delta, c, p, s = worst_increase
        print(f"    Worst: Δ={delta}, {c} --P{p}--> {s}")
    return violations


def analyze_frontier_changes(n):
    """For each bad config move, categorize the frontier change."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    categories = defaultdict(int)

    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            fc_before = frontier_count(c, n)
            fc_after = frontier_count(succ, n)
            delta = fc_after - fc_before

            if p == 0:
                mtype = "BOTTOM"
            elif p == n - 1:
                mtype = "TOP"
            else:
                mtype = "MIDDLE"

            categories[(mtype, delta)] += 1

    print(f"\nn={n}: Frontier count changes by move type:")
    for (mtype, delta), count in sorted(categories.items()):
        print(f"  {mtype} Δ={delta:+d}: {count} moves")


def search_refined_potential(n):
    """Try position-dependent coefficients for frontier weighting.

    Φ(c) = Σ_i a[i] * [d_i == 1] + b[i] * [d_i == 2]

    We need: for every bad→bad move P_j:
      Φ(succ) < Φ(c)

    This is a system of linear inequalities in a[i], b[i].
    """
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Collect all bad→bad transitions
    transitions = []
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                # Compute frontier vectors
                before_1 = [0] * n  # d_i == 1 indicators
                before_2 = [0] * n  # d_i == 2 indicators
                after_1 = [0] * n
                after_2 = [0] * n
                for i in range(n):
                    d = (c[(i+1)%n] - c[i]) % 3
                    if d == 1: before_1[i] = 1
                    elif d == 2: before_2[i] = 1
                    d = (succ[(i+1)%n] - succ[i]) % 3
                    if d == 1: after_1[i] = 1
                    elif d == 2: after_2[i] = 1

                # We need: Σ a[i]*(after_1[i]-before_1[i]) + b[i]*(after_2[i]-before_2[i]) < 0
                # i.e., Σ a[i]*delta_1[i] + b[i]*delta_2[i] < 0
                delta_1 = [after_1[i] - before_1[i] for i in range(n)]
                delta_2 = [after_2[i] - before_2[i] for i in range(n)]
                transitions.append((c, p, succ, delta_1, delta_2))

    print(f"\nn={n}: {len(transitions)} bad→bad transitions")

    # Try to solve with LP: find a[0..n-1], b[0..n-1] >= 1 such that
    # for all transitions: Σ a[i]*delta_1[i] + b[i]*delta_2[i] <= -1
    try:
        from scipy.optimize import linprog

        # Variables: a[0]..a[n-1], b[0]..b[n-1] (total 2n)
        # Constraints: for each transition t:
        #   Σ_i a[i]*delta_1[i] + b[i]*delta_2[i] <= -1
        #   a[i] >= 1, b[i] >= 1

        num_vars = 2 * n
        A_ub = []
        b_ub = []

        for _, _, _, d1, d2 in transitions:
            row = d1 + d2  # [delta_1[0],...,delta_1[n-1], delta_2[0],...,delta_2[n-1]]
            A_ub.append(row)
            b_ub.append(-1)

        # Lower bounds: all >= 1
        bounds = [(1, None)] * num_vars

        # Objective: minimize sum of coefficients (find simplest weights)
        c_obj = [1] * num_vars

        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

        if res.success:
            a = res.x[:n]
            b = res.x[n:]
            print(f"  LP FEASIBLE! Found weights:")
            print(f"    a (type-1): {[round(x, 2) for x in a]}")
            print(f"    b (type-2): {[round(x, 2) for x in b]}")

            # Verify
            def phi_lp(c, n):
                total = 0
                for i in range(n):
                    d = (c[(i+1)%n] - c[i]) % 3
                    if d == 1: total += a[i]
                    elif d == 2: total += b[i]
                return total

            violations = 0
            for cc, p, succ, _, _ in transitions:
                if phi_lp(succ, n) >= phi_lp(cc, n):
                    violations += 1
            print(f"  Verification: {violations} violations")
            return a, b
        else:
            print(f"  LP INFEASIBLE — no position-dependent linear potential exists")
            return None
    except ImportError:
        print("  scipy not available, skipping LP")
        return None


def search_quadratic_potential(n):
    """Try Φ(c) = Σ_i Σ_j w[i,j] * f_i * f_j + Σ_i a[i]*f_i
    where f_i = d_i indicator (0 or 1).

    This captures pairwise frontier interactions.
    """
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # For each bad→bad transition, compute frontier indicators before/after
    transitions = []
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                f_before = [1 if (c[(i+1)%n]-c[i])%3 != 0 else 0 for i in range(n)]
                f_after = [1 if (succ[(i+1)%n]-succ[i])%3 != 0 else 0 for i in range(n)]
                transitions.append((f_before, f_after))

    print(f"\nn={n}: {len(transitions)} bad→bad transitions for quadratic LP")

    try:
        from scipy.optimize import linprog

        # Variables: linear terms a[0..n-1] + quadratic terms w[i,j] for i<=j
        # Total: n + n*(n+1)/2 variables
        num_linear = n
        num_quad = n * (n + 1) // 2
        num_vars = num_linear + num_quad

        def quad_index(i, j):
            if i > j: i, j = j, i
            return num_linear + i * (2 * n - i - 1) // 2 + (j - i)

        A_ub = []
        b_ub = []

        for f_b, f_a in transitions:
            row = [0.0] * num_vars
            # Linear: Σ a[i] * (f_after[i] - f_before[i])
            for i in range(n):
                row[i] = f_a[i] - f_b[i]
            # Quadratic: Σ w[i,j] * (f_after[i]*f_after[j] - f_before[i]*f_before[j])
            for i in range(n):
                for j in range(i, n):
                    idx = quad_index(i, j)
                    mult = 1 if i == j else 2
                    row[idx] = mult * (f_a[i] * f_a[j] - f_b[i] * f_b[j])
            A_ub.append(row)
            b_ub.append(-1)

        bounds = [(0.01, 100)] * num_vars
        c_obj = [1] * num_vars

        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

        if res.success:
            print(f"  Quadratic LP FEASIBLE!")
            a = res.x[:num_linear]
            print(f"    Linear: {[round(x, 2) for x in a]}")
            return True
        else:
            print(f"  Quadratic LP INFEASIBLE")
            return False
    except ImportError:
        print("  scipy not available")
        return False


def check_bottom_top_frontier_creation(n):
    """For each bottom/top move from a bad config, analyze frontier creation.
    Key question: does the bottom/top ALWAYS have some compensating decrease elsewhere?"""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    print(f"\nn={n}: Bottom/top frontier creation analysis")

    for mover_type, mover_idx in [("BOTTOM", 0), ("TOP", n-1)]:
        increases = []
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            if mover_idx not in priv:
                continue
            succ = apply_move(c, mover_idx, fs, n)
            fc_b = get_frontiers(c, n)
            fc_a = get_frontiers(succ, n)
            fc_before = len(fc_b)
            fc_after = len(fc_a)
            if fc_after > fc_before:
                increases.append((c, succ, fc_b, fc_a))

        print(f"\n  {mover_type}: {len(increases)} frontier-increasing moves")
        if increases and n <= 6:
            for c, s, fb, fa in increases[:10]:
                print(f"    {c} (F={fb}) → {s} (F={fa})")
                # Check: is the successor still bad?
                if s in bad_set:
                    # Check: what's the privilege set of successor?
                    priv_s = get_privileged(s, fs, n)
                    print(f"      Successor priv: {priv_s} ({'BAD' if len(priv_s) >= 2 else 'GOOD'})")
                else:
                    print(f"      Successor is GOOD")


def trace_worst_daemon(n, max_steps=200):
    """For each bad config, trace the WORST daemon path.
    At each step, choose the move that maximizes frontier count.
    If tied, choose the move that leads to maximum subsequent frontier count."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Find config with most frontiers
    max_fc = 0
    worst_start = None
    for c in bad_set:
        fc = frontier_count(c, n)
        if fc > max_fc:
            max_fc = fc
            worst_start = c

    # Trace from worst_start with frontier-maximizing daemon
    c = worst_start
    print(f"\nn={n}: Tracing frontier-max daemon from {c} (frontiers={max_fc})")

    visited = set()
    for step in range(max_steps):
        if c in good_set:
            print(f"  Step {step}: Reached good config {c}")
            break
        if c in visited:
            print(f"  Step {step}: CYCLE DETECTED at {c}!")
            break
        visited.add(c)

        priv = get_privileged(c, fs, n)
        fc_c = frontier_count(c, n)

        # Choose move that maximizes frontier count of successor
        best_p = None
        best_fc = -1
        for p in priv:
            succ = apply_move(c, p, fs, n)
            fc_s = frontier_count(succ, n)
            if fc_s > best_fc:
                best_fc = fc_s
                best_p = p

        succ = apply_move(c, best_p, fs, n)
        if n <= 6 and step < 30:
            fronts = get_frontiers(c, n)
            print(f"  Step {step}: {c} F={fronts} --P{best_p}--> frontier_count={best_fc}")

        c = succ


if __name__ == "__main__":
    print("=" * 70)
    print("FRONTIER CHANGE ANALYSIS")
    print("=" * 70)
    for n_val in [3, 4, 5, 6]:
        analyze_frontier_changes(n_val)

    print("\n" + "=" * 70)
    print("BOTTOM/TOP FRONTIER CREATION")
    print("=" * 70)
    for n_val in [4, 5, 6]:
        check_bottom_top_frontier_creation(n_val)

    print("\n" + "=" * 70)
    print("POTENTIAL FUNCTION SEARCH")
    print("=" * 70)
    for n_val in [4, 5, 6]:
        print(f"\n--- n={n_val} ---")
        test_potential("weighted_dist", phi_weighted_distance, n_val)
        test_potential("frontier_count", phi_frontier_count, n_val)
        test_potential("type_sum", phi_frontier_type_sum, n_val, verbose=True)

    print("\n" + "=" * 70)
    print("LINEAR POTENTIAL SEARCH (LP)")
    print("=" * 70)
    for n_val in [4, 5, 6]:
        search_refined_potential(n_val)

    print("\n" + "=" * 70)
    print("WORST DAEMON TRACES")
    print("=" * 70)
    for n_val in [4, 5, 6]:
        trace_worst_daemon(n_val)
