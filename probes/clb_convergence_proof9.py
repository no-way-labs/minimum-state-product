#!/usr/bin/env python3
"""
CONVERGENCE PROOF — Part 9: Rank Function Decomposition
========================================================

Strategy: Compute the EXACT rank function (longest path to a good config)
for small n, then decompose it to find a provable structure.

Key question: Can rank(c) be expressed as a function of LOCAL patterns
in the configuration c? Specifically:

  rank(c) = Σ_{i} w(c[i-1], c[i], c[i+1], position_type(i))

where w is a weight function depending on the local 3-window and
the table type at position i?

If this works, the DAG property reduces to showing that EVERY transition
strictly increases the sum — a provable local property.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque, Counter
import numpy as np

def compute_rank(n):
    """Compute exact rank for all bad configs: rank = longest path to any good config."""
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Build adjacency: c -> list of successors in bad
    adj = {c: [] for c in bad_list}
    # Also track transitions to good (these give rank 0 paths)
    exits_to_good = {c: False for c in bad_list}

    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                else:
                    exits_to_good[c] = True

    # Compute rank via topological sort (reverse)
    # rank[c] = max over successors s: rank[s] + 1 if s in bad, else 0
    # For configs that exit to good: rank contribution = 0 for that edge

    # First: topological sort via Kahn's algorithm
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

    assert len(topo) == len(bad_list), "Not a DAG!"

    # Compute rank in reverse topological order
    rank = {}
    for c in reversed(topo):
        if not adj[c] and exits_to_good[c]:
            rank[c] = 0
        elif not adj[c]:
            rank[c] = 0  # dead end in bad (shouldn't happen with liveness)
        else:
            rank[c] = max(rank[s] + 1 for s in adj[c])

    return rank, bad_list, adj, ms, fs, good_set

def test_local_decomposition(n=5):
    """
    Test if rank can be expressed as a sum of local terms.

    For each config c, define features based on local 3-windows:
      x_{i,L,S,R} = 1 if (c[i-1], c[i], c[i+1]) = (L, S, R)

    Then rank(c) ≈ Σ_i w_{type(i), L, S, R} * x_{i,L,S,R}

    Fit the weights w to minimize ||Ax - b||^2 where b = rank vector.
    """
    print(f"LOCAL DECOMPOSITION TEST (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)
    max_rank = max(rank.values())
    print(f"  Bad configs: {len(bad_list)}, max rank: {max_rank}")

    # Build feature matrix
    # Features: for each position i and each local pattern (L,S,R),
    # one binary indicator
    position_types = {}
    for i in range(n):
        if i == 0:
            position_types[i] = 'bot'
        elif i == 1:
            position_types[i] = 'low'
        elif i == n-2:
            position_types[i] = 'high'
        elif i == n-1:
            position_types[i] = 'top'
        else:
            position_types[i] = 'mid'

    # Enumerate all possible local patterns per position type
    type_patterns = {}
    for i in range(n):
        mL = ms[(i-1)%n]; mS = ms[i]; mR = ms[(i+1)%n]
        t = position_types[i]
        if t not in type_patterns:
            type_patterns[t] = []
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        type_patterns[t].append((L,S,R))

    # Build feature index
    feature_names = []
    feature_idx = {}
    for t in ['bot', 'low', 'mid', 'high', 'top']:
        if t in type_patterns:
            for pat in type_patterns[t]:
                name = f"{t}_{pat}"
                feature_idx[name] = len(feature_names)
                feature_names.append(name)

    n_features = len(feature_names)
    print(f"  Features: {n_features} (local 3-window indicators)")

    # Build matrix A and vector b
    N = len(bad_list)
    A = np.zeros((N, n_features))
    b = np.array([rank[c] for c in bad_list], dtype=float)

    for idx, c in enumerate(bad_list):
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            t = position_types[i]
            name = f"{t}_{(L,S,R)}"
            A[idx, feature_idx[name]] += 1  # could be >1 if multiple mid positions

    # Least squares fit
    w, residuals, matrix_rank, sv = np.linalg.lstsq(A, b, rcond=None)

    # Predict
    pred = A @ w
    errors = b - pred
    rmse = np.sqrt(np.mean(errors**2))
    max_err = np.max(np.abs(errors))
    r2 = 1 - np.sum(errors**2) / np.sum((b - np.mean(b))**2)

    print(f"  Fit quality: RMSE={rmse:.3f}, max_err={max_err:.3f}, R²={r2:.4f}")
    print(f"  (Max rank = {max_rank}, mean rank = {np.mean(b):.1f})")

    # Print weights
    print(f"\n  Weights (sorted by magnitude):")
    sorted_idx = np.argsort(-np.abs(w))
    for j in sorted_idx[:20]:
        print(f"    {feature_names[j]:>20s}: {w[j]:+.3f}")

    # Check: for EVERY transition c -> c', does the weighted sum DECREASE?
    # (rank increases = weighted sum should decrease if sum ≈ -rank)
    violations = 0
    total_trans = 0
    for c in bad_list:
        pred_c = pred[bad_list.index(c)]
        for s in adj[c]:
            pred_s = pred[bad_list.index(s)]
            total_trans += 1
            if pred_s <= pred_c:  # should increase (since rank increases)
                violations += 1

    print(f"\n  Transition monotonicity: {violations}/{total_trans} violations "
          f"({100*violations/total_trans:.1f}%)")

    return w, feature_names, feature_idx, rank, bad_list

def test_rank_difference_patterns(n=5):
    """
    For each transition c -> c' (firing position p, changing S -> S'),
    compute rank(c') - rank(c) and categorize by transition type.

    This reveals which transitions advance rank the most/least.
    """
    print(f"\nRANK DIFFERENCE BY TRANSITION TYPE (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)

    # Build detailed transitions
    transitions = []
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in set(bad_list):
                    dr = rank[succ] - rank[c]
                    transitions.append({
                        'pos': i,
                        'old': S, 'new': new_S,
                        'L': L, 'R': R,
                        'dr': dr,
                        'c': c, 'succ': succ,
                    })

    # Group by (position_type, old, new)
    pos_type = {}
    for i in range(n):
        if i == 0: pos_type[i] = 'bot'
        elif i == 1: pos_type[i] = 'low'
        elif i == n-2: pos_type[i] = 'high'
        elif i == n-1: pos_type[i] = 'top'
        else: pos_type[i] = 'mid'

    by_type = defaultdict(list)
    for t in transitions:
        key = (pos_type[t['pos']], t['old'], t['new'])
        by_type[key].append(t['dr'])

    print(f"\n  {'Type':>15s} {'Old→New':>8s} {'Count':>6s} {'Mean Δr':>8s} "
          f"{'Min':>5s} {'Max':>5s} {'Always+':>8s}")
    print("  " + "-" * 65)

    for key in sorted(by_type.keys()):
        typ, old, new = key
        drs = by_type[key]
        mean_dr = np.mean(drs)
        min_dr = min(drs)
        max_dr = max(drs)
        always_pos = all(d > 0 for d in drs)
        print(f"  {typ:>15s} {old}→{new:>5d} {len(drs):>6d} {mean_dr:>+8.2f} "
              f"{min_dr:>+5d} {max_dr:>+5d} {'YES' if always_pos else 'no':>8s}")

    # Group by (position_type, old, new, L, R) for more detail
    print(f"\n  Detailed by (type, old→new, L, R):")
    by_detail = defaultdict(list)
    for t in transitions:
        key = (pos_type[t['pos']], t['old'], t['new'], t['L'], t['R'])
        by_detail[key].append(t['dr'])

    for key in sorted(by_detail.keys()):
        typ, old, new, L, R = key
        drs = by_detail[key]
        mean_dr = np.mean(drs)
        always_pos = all(d > 0 for d in drs)
        sign = "✓" if always_pos else "✗"
        print(f"    {typ:>5s} {old}→{new} (L={L},R={R}): "
              f"n={len(drs):>3d}, mean={mean_dr:>+6.2f}, "
              f"range=[{min(drs):+d},{max(drs):+d}] {sign}")

def test_pairwise_window(n=5):
    """
    Test if rank can be decomposed using PAIRWISE windows:
    rank(c) ≈ Σ_i w(c[i], c[i+1], type(i,i+1))

    This is a 2-local decomposition. Might work better because the
    interaction between consecutive positions is the key structure.
    """
    print(f"\nPAIRWISE WINDOW DECOMPOSITION (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)

    # Build pairwise features
    feature_names = []
    feature_idx = {}

    for i in range(n):
        j = (i+1) % n
        mS = ms[i]; mR = ms[j]
        for s in range(mS):
            for r in range(mR):
                name = f"pair_{i}_{j}_{s}_{r}"
                feature_idx[name] = len(feature_names)
                feature_names.append(name)

    n_features = len(feature_names)
    N = len(bad_list)
    A = np.zeros((N, n_features))
    b = np.array([rank[c] for c in bad_list], dtype=float)

    for idx, c in enumerate(bad_list):
        for i in range(n):
            j = (i+1) % n
            name = f"pair_{i}_{j}_{c[i]}_{c[j]}"
            A[idx, feature_idx[name]] = 1

    w, residuals, matrix_rank, sv = np.linalg.lstsq(A, b, rcond=None)
    pred = A @ w
    errors = b - pred
    rmse = np.sqrt(np.mean(errors**2))
    max_err = np.max(np.abs(errors))
    r2 = 1 - np.sum(errors**2) / np.sum((b - np.mean(b))**2)

    print(f"  Features: {n_features}")
    print(f"  Fit: RMSE={rmse:.3f}, max_err={max_err:.3f}, R²={r2:.4f}")

    # Check monotonicity
    violations = 0
    total = 0
    for c in bad_list:
        c_idx = bad_list.index(c)
        for s in adj[c]:
            s_idx = bad_list.index(s)
            total += 1
            if pred[s_idx] <= pred[c_idx]:
                violations += 1

    print(f"  Monotonicity violations: {violations}/{total} ({100*violations/total:.1f}%)")

def test_quadratic_local(n=5):
    """
    Test rank ≈ Σ_i a_i * c[i] + Σ_i b_i * c[i]² + Σ_i d_i * c[i]*c[i+1] + const

    Quadratic in the state values with local interactions.
    """
    print(f"\nQUADRATIC LOCAL DECOMPOSITION (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)

    N = len(bad_list)
    features = []
    names = []

    # Constant
    features.append(np.ones(N))
    names.append('const')

    for i in range(n):
        # Linear
        f = np.array([c[i] for c in bad_list], dtype=float)
        features.append(f)
        names.append(f'c[{i}]')

        # Quadratic (self)
        features.append(f**2)
        names.append(f'c[{i}]²')

        # Cross with next
        j = (i+1) % n
        g = np.array([c[j] for c in bad_list], dtype=float)
        features.append(f * g)
        names.append(f'c[{i}]*c[{j}]')

    A = np.column_stack(features)
    b = np.array([rank[c] for c in bad_list], dtype=float)

    w, residuals, matrix_rank, sv = np.linalg.lstsq(A, b, rcond=None)
    pred = A @ w
    errors = b - pred
    rmse = np.sqrt(np.mean(errors**2))
    r2 = 1 - np.sum(errors**2) / np.sum((b - np.mean(b))**2)

    print(f"  Features: {A.shape[1]}, R²={r2:.4f}, RMSE={rmse:.3f}")

    for i, name in enumerate(names):
        if abs(w[i]) > 0.01:
            print(f"    {name:>15s}: {w[i]:+.4f}")

    # Monotonicity
    violations = 0
    total = 0
    bad_idx = {c: i for i, c in enumerate(bad_list)}
    for c in bad_list:
        for s in adj[c]:
            total += 1
            if pred[bad_idx[s]] <= pred[bad_idx[c]]:
                violations += 1
    print(f"  Monotonicity violations: {violations}/{total} ({100*violations/total:.1f}%)")

def test_integer_rank_structure(n=5):
    """
    Analyze the exact integer rank function structure.

    Key questions:
    - What is the distribution of rank values?
    - What is the minimum rank increment per transition?
    - Are there "rank plateaus"?
    - Does rank have a specific structure relative to good-cycle distance?
    """
    print(f"\nEXACT RANK STRUCTURE (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)
    max_rank = max(rank.values())

    # Distribution
    rank_counts = Counter(rank.values())
    print(f"  Rank distribution:")
    for r in range(max_rank + 1):
        count = rank_counts.get(r, 0)
        bar = '#' * min(count, 50)
        if count > 0:
            print(f"    {r:>3d}: {count:>4d} {bar}")

    # Rank increments
    increments = []
    for c in bad_list:
        for s in adj[c]:
            dr = rank[s] - rank[c]
            increments.append(dr)

    inc_counts = Counter(increments)
    print(f"\n  Rank increment distribution (Δrank = rank(succ) - rank(c)):")
    for dr in sorted(inc_counts.keys()):
        print(f"    Δ={dr:+3d}: {inc_counts[dr]:>5d}")

    # Configs at rank 0 (immediate predecessors of good configs)
    rank0 = [c for c in bad_list if rank[c] == 0]
    print(f"\n  Rank-0 configs (exit to good in 1 step): {len(rank0)}")
    for c in rank0[:10]:
        # Find which move leads to good
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in good_set:
                    print(f"    {c} → fire P{i} ({S}→{new_S}) → {succ} (good)")
                    break

    # Highest-rank configs
    top_rank = max_rank
    top_configs = [c for c in bad_list if rank[c] == top_rank]
    print(f"\n  Highest-rank configs (rank={top_rank}): {len(top_configs)}")
    for c in top_configs:
        priv = []
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        print(f"    {c}  privileged: {priv}")

def analyze_rank_vs_features(n=5):
    """
    For each feature, compute its EXACT correlation with rank.
    Also check whether any feature is a monotone function of rank.
    """
    print(f"\nRANK vs FEATURES ANALYSIS (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)

    # Feature functions
    def count_val(c, v):
        return sum(1 for x in c if x == v)

    def n_priv(c):
        n = len(c)
        count = 0
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) != S:
                count += 1
        return count

    def at_target(c):
        """Count positions at their fixed point."""
        n = len(c)
        count = 0
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) == S:
                count += 1
        return count

    def sum_vals(c):
        return sum(c)

    def leftward_agreement(c):
        """Count positions where c[i] = c[i-1] (leftward agreement)."""
        n = len(c)
        return sum(1 for i in range(n) if c[i] == c[(i-1)%n])

    def rightward_agreement(c):
        n = len(c)
        return sum(1 for i in range(n) if c[i] == c[(i+1)%n])

    def position_weighted_sum(c):
        return sum(i * c[i] for i in range(len(c)))

    features = {
        'sum': sum_vals,
        'n_priv': n_priv,
        'at_target': at_target,
        'count_0': lambda c: count_val(c, 0),
        'count_1': lambda c: count_val(c, 1),
        'count_2': lambda c: count_val(c, 2),
        'left_agree': leftward_agreement,
        'right_agree': rightward_agreement,
        'pos_weighted': position_weighted_sum,
    }

    ranks = np.array([rank[c] for c in bad_list])

    print(f"  {'Feature':>15s} {'Corr':>8s} {'Mono↑':>8s} {'Mono↓':>8s}")
    print("  " + "-" * 45)

    for fname, ffunc in features.items():
        vals = np.array([ffunc(c) for c in bad_list])
        corr = np.corrcoef(ranks, vals)[0,1]

        # Check monotonicity: is higher feature value always higher rank?
        violations_up = 0
        violations_down = 0
        total = 0
        for c in bad_list:
            c_f = ffunc(c)
            c_r = rank[c]
            for s in adj[c]:
                s_f = ffunc(s)
                s_r = rank[s]
                total += 1
                if s_f > c_f and s_r < c_r:
                    violations_up += 1
                if s_f < c_f and s_r > c_r:
                    violations_down += 1

        pct_up = 100 * violations_up / total if total > 0 else 0
        pct_down = 100 * violations_down / total if total > 0 else 0
        print(f"  {fname:>15s} {corr:>+8.3f} {pct_up:>7.1f}% {pct_down:>7.1f}%")

def analyze_transition_rank_guarantee(n=5):
    """
    THE KEY QUESTION: Is there a transition type that ALWAYS increases rank?

    If some transition types always increase rank, and others sometimes decrease,
    this could lead to a proof by showing the decreasing ones are bounded.
    """
    print(f"\nTRANSITION RANK GUARANTEE ANALYSIS (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)
    bad_set = set(bad_list)

    # Categorize each transition
    type_stats = defaultdict(lambda: {'total': 0, 'always_inc': True,
                                        'min_dr': float('inf'), 'max_dr': float('-inf'),
                                        'drs': []})

    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    dr = rank[succ] - rank[c]
                    # Key: local type is (table_type, L, old_S, R, new_S)
                    if i == 0: tt = 'bot'
                    elif i == 1: tt = 'low'
                    elif i == n-2: tt = 'high'
                    elif i == n-1: tt = 'top'
                    else: tt = 'mid'

                    key = (tt, L, S, R, new_S)
                    stats = type_stats[key]
                    stats['total'] += 1
                    stats['drs'].append(dr)
                    stats['min_dr'] = min(stats['min_dr'], dr)
                    stats['max_dr'] = max(stats['max_dr'], dr)
                    if dr <= 0:
                        stats['always_inc'] = False

    print(f"\n  {'Transition':>30s} {'Count':>6s} {'Min':>5s} {'Max':>5s} {'Mean':>7s} {'Always+':>8s}")
    print("  " + "-" * 70)

    always_inc_types = []
    sometimes_dec_types = []

    for key in sorted(type_stats.keys()):
        tt, L, S, R, new_S = key
        stats = type_stats[key]
        mean_dr = np.mean(stats['drs'])
        label = f"{tt}({L},{S},{R})→{new_S}"
        status = "✓" if stats['always_inc'] else "✗"
        print(f"  {label:>30s} {stats['total']:>6d} {stats['min_dr']:>+5d} "
              f"{stats['max_dr']:>+5d} {mean_dr:>+7.2f} {status:>8s}")

        if stats['always_inc']:
            always_inc_types.append(key)
        else:
            sometimes_dec_types.append(key)

    print(f"\n  Always rank-increasing: {len(always_inc_types)}/{len(type_stats)} types")
    print(f"  Sometimes rank-decreasing: {len(sometimes_dec_types)}/{len(type_stats)} types")

    if sometimes_dec_types:
        print(f"\n  Types that can DECREASE rank:")
        for key in sometimes_dec_types:
            tt, L, S, R, new_S = key
            stats = type_stats[key]
            n_dec = sum(1 for d in stats['drs'] if d <= 0)
            print(f"    {tt}({L},{S},{R})→{new_S}: {n_dec}/{stats['total']} "
                  f"decrease (min={stats['min_dr']:+d})")

def check_settling_rank(n=5):
    """
    Test a specific hypothesis: "settled count" (number of positions at their
    fixed point) as a first-level lexicographic component.

    Does settled count ALWAYS increase? If not, what's the distribution?
    """
    print(f"\nSETTLED COUNT ANALYSIS (n={n})")
    print("=" * 60)

    rank, bad_list, adj, ms, fs, good_set = compute_rank(n)
    bad_set = set(bad_list)

    def settled_count(c):
        count = 0
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) == S:
                count += 1
        return count

    # For each transition, check if settled count changes
    changes = Counter()
    for c in bad_list:
        sc = settled_count(c)
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    sc2 = settled_count(succ)
                    delta = sc2 - sc
                    changes[delta] += 1

    print("  Settled count change per transition:")
    for d in sorted(changes.keys()):
        print(f"    Δ={d:+d}: {changes[d]:>5d}")

    # The mover ALWAYS becomes settled (verified earlier).
    # But its neighbors might become unsettled.
    # Net change: +1 (mover settles) + possible -k (neighbors unsettle)

    # Count specifically: how many neighbors become unsettled?
    unsettling = Counter()
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    # Check each neighbor
                    n_unsettle = 0
                    for j in [(i-1)%n, (i+1)%n]:
                        # Was j settled before?
                        L_j = c[(j-1)%n]; S_j = c[j]; R_j = c[(j+1)%n]
                        was_settled = (fs[j](L_j, S_j, R_j) == S_j)
                        # Is j settled after?
                        L_j2 = succ[(j-1)%n]; S_j2 = succ[j]; R_j2 = succ[(j+1)%n]
                        is_settled = (fs[j](L_j2, S_j2, R_j2) == S_j2)
                        if was_settled and not is_settled:
                            n_unsettle += 1
                    unsettling[n_unsettle] += 1

    print("\n  Neighbors unsettled per transition:")
    for k in sorted(unsettling.keys()):
        print(f"    {k} neighbors unsettled: {unsettling[k]:>5d}")

def main():
    for n in [5, 6]:
        print("\n" + "=" * 70)
        print(f"ANALYSIS FOR n={n}")
        print("=" * 70)

        # Test local decomposition
        test_local_decomposition(n)

        # Test rank differences
        test_rank_difference_patterns(n)

        # Test pairwise decomposition
        test_pairwise_window(n)

        # Quadratic
        test_quadratic_local(n)

        # Integer rank structure
        test_integer_rank_structure(n)

        # Feature analysis
        analyze_rank_vs_features(n)

        # Transition guarantee
        analyze_transition_rank_guarantee(n)

        # Settling
        check_settling_rank(n)

if __name__ == "__main__":
    main()
