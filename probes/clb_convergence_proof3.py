#!/usr/bin/env python3
"""Convergence proof investigation — Part 3.

Strategy: reverse-engineer the DAG rank function.
1. Compute all features for each bad config
2. Correlate with actual DAG rank
3. Try to fit rank = f(features)
4. Test cycle impossibility via propagation chain analysis
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque, defaultdict, Counter
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
import math


def get_bad_graph(n):
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)
    adj = {c: [] for c in bad_set}
    for c in bad_set:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append((succ, i))
    return ms, fs, good_set, bad_set, adj


def compute_ranks(bad_set, adj):
    in_deg = {c: 0 for c in bad_set}
    adj_simple = {c: [] for c in bad_set}
    for c in bad_set:
        for succ, mover in adj[c]:
            adj_simple[c].append(succ)
            in_deg[succ] += 1
    q = deque(c for c in bad_set if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj_simple[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    rank = {}
    for c in reversed(topo):
        succs = adj_simple[c]
        rank[c] = max((rank[s] + 1 for s in succs), default=0)
    return rank


def compute_features(c, n, ms, fs):
    """Compute a rich feature vector for config c."""
    features = {}

    # Basic
    features['sum'] = sum(c)
    features['frontier'] = sum(1 for i in range(n) if c[i] != c[(i+1) % n])
    features['count_2'] = sum(1 for i in range(1, n-1) if c[i] == 2)
    features['count_0'] = sum(1 for i in range(n) if c[i] == 0)
    features['count_1'] = sum(1 for i in range(n) if c[i] == 1)

    # Privilege structure
    priv_positions = []
    for i in range(n):
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv_positions.append(i)
    features['n_priv'] = len(priv_positions)
    features['priv_spread'] = (max(priv_positions) - min(priv_positions)) if priv_positions else 0
    features['leftmost_priv'] = priv_positions[0] if priv_positions else n
    features['rightmost_priv'] = priv_positions[-1] if priv_positions else 0

    # Position-weighted sums
    features['left_weighted_sum'] = sum(i * c[i] for i in range(n))
    features['right_weighted_sum'] = sum((n-1-i) * c[i] for i in range(n))

    # Consecutive pairs
    features['n_01_pairs'] = sum(1 for i in range(n) if c[i] == 0 and c[(i+1)%n] == 1)
    features['n_10_pairs'] = sum(1 for i in range(n) if c[i] == 1 and c[(i+1)%n] == 0)
    features['n_12_pairs'] = sum(1 for i in range(n) if c[i] == 1 and c[(i+1)%n] == 2)
    features['n_21_pairs'] = sum(1 for i in range(n) if c[i] == 2 and c[(i+1)%n] == 1)
    features['n_02_pairs'] = sum(1 for i in range(n) if c[i] == 0 and c[(i+1)%n] == 2)
    features['n_20_pairs'] = sum(1 for i in range(n) if c[i] == 2 and c[(i+1)%n] == 0)

    # Run structure
    max_run = 1
    for v in range(3):
        run = 0
        for i in range(n):
            if c[i] == v:
                run += 1
                max_run = max(max_run, run)
            else:
                run = 0
    features['max_run'] = max_run

    # "Disorder" - number of consecutive same-value pairs
    features['n_same_pairs'] = sum(1 for i in range(n) if c[i] == c[(i+1)%n])

    # Left-right agreement with target
    left_agree = 0
    for i in range(n):
        L = c[(i-1)%n]; R = c[(i+1)%n]; S = c[i]
        if fs[i](L, S, R) == S:
            left_agree += 1
    features['n_at_target'] = left_agree

    # Boundary-interior decomposition
    features['boundary_sum'] = c[0] + c[n-1]
    features['interior_sum'] = sum(c[1:n-1])

    return features


def spearman_corr(x, y):
    """Compute Spearman rank correlation."""
    n = len(x)
    if n < 3:
        return 0

    # Rank the values
    def rank_values(v):
        indexed = sorted(range(n), key=lambda i: v[i])
        ranks = [0] * n
        i = 0
        while i < n:
            j = i
            while j < n and v[indexed[j]] == v[indexed[i]]:
                j += 1
            avg_rank = (i + j - 1) / 2.0
            for k in range(i, j):
                ranks[indexed[k]] = avg_rank
            i = j
        return ranks

    rx = rank_values(x)
    ry = rank_values(y)

    mean_rx = sum(rx) / n
    mean_ry = sum(ry) / n

    num = sum((rx[i] - mean_rx) * (ry[i] - mean_ry) for i in range(n))
    den_x = sum((rx[i] - mean_rx) ** 2 for i in range(n))
    den_y = sum((ry[i] - mean_ry) ** 2 for i in range(n))

    if den_x == 0 or den_y == 0:
        return 0
    return num / (den_x * den_y) ** 0.5


def main():
    # ================================================================
    # PART 1: FEATURE CORRELATION WITH DAG RANK
    # ================================================================
    print("=" * 90)
    print("PART 1: FEATURE CORRELATION WITH DAG RANK")
    print("=" * 90)

    for nv in [6, 7, 8]:
        ms, fs, good_set, bad_set, adj = get_bad_graph(nv)
        rank = compute_ranks(bad_set, adj)

        configs = list(bad_set)
        ranks = [rank[c] for c in configs]

        feature_names = None
        feature_vecs = {}

        for c in configs:
            f = compute_features(c, nv, ms, fs)
            if feature_names is None:
                feature_names = sorted(f.keys())
            for name in feature_names:
                if name not in feature_vecs:
                    feature_vecs[name] = []
                feature_vecs[name].append(f[name])

        print(f"\nn={nv}: {len(configs)} bad configs, max_rank={max(ranks)}")
        print(f"{'Feature':>25s}  {'Spearman':>8s}")
        print("-" * 40)

        correlations = []
        for name in feature_names:
            corr = spearman_corr(feature_vecs[name], ranks)
            correlations.append((abs(corr), corr, name))

        correlations.sort(reverse=True)
        for ac, corr, name in correlations:
            print(f"  {name:>25s}  {corr:>+8.4f}")

    # ================================================================
    # PART 2: MULTI-FEATURE REGRESSION
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 2: BEST LINEAR COMBINATION (2-feature)")
    print("=" * 90)

    for nv in [6, 7]:
        ms, fs, good_set, bad_set, adj = get_bad_graph(nv)
        rank = compute_ranks(bad_set, adj)
        configs = list(bad_set)
        ranks = [rank[c] for c in configs]

        # Compute features
        all_features = {}
        feature_names = None
        for c in configs:
            f = compute_features(c, nv, ms, fs)
            if feature_names is None:
                feature_names = sorted(f.keys())
            all_features[c] = f

        transitions = []
        for c in bad_set:
            for succ, mover in adj[c]:
                transitions.append((c, succ, mover))

        # Try all pairs of features as potential: a*f1 + b*f2 strictly decreasing
        print(f"\nn={nv}: testing 2-feature combinations as strictly decreasing potential")
        best_combo = None
        best_viol = len(transitions)

        top_features = ['n_priv', 'frontier', 'n_at_target', 'count_2',
                        'sum', 'left_weighted_sum', 'count_0',
                        'interior_sum', 'n_same_pairs', 'priv_spread',
                        'leftmost_priv', 'rightmost_priv']

        for f1 in top_features:
            for f2 in top_features:
                if f1 >= f2:
                    continue
                # Try coefficients: a*f1 + b*f2 should decrease
                for a in range(-3, 4):
                    for b in range(-3, 4):
                        if a == 0 and b == 0:
                            continue
                        viol = 0
                        for c, cp, mv in transitions:
                            sc = a * all_features[c][f1] + b * all_features[c][f2]
                            scp = a * all_features[cp][f1] + b * all_features[cp][f2]
                            if sc <= scp:
                                viol += 1
                        if viol < best_viol:
                            best_viol = viol
                            best_combo = (a, f1, b, f2)

        pct = 100 * best_viol / len(transitions)
        a, f1, b, f2 = best_combo
        print(f"  Best: {a}*{f1} + {b}*{f2}: {best_viol} violations ({pct:.1f}%)")

        # Also try all 2-feature LEX combinations
        print(f"\n  Testing lexicographic 2-feature:")
        best_lex = None
        best_lex_viol = len(transitions)
        for f1 in top_features:
            for f2 in top_features:
                if f1 == f2:
                    continue
                for s1 in [1, -1]:
                    for s2 in [1, -1]:
                        viol = 0
                        for c, cp, mv in transitions:
                            v1c = s1 * all_features[c][f1]
                            v1cp = s1 * all_features[cp][f1]
                            v2c = s2 * all_features[c][f2]
                            v2cp = s2 * all_features[cp][f2]
                            if (v1c, v2c) <= (v1cp, v2cp):
                                viol += 1
                        if viol < best_lex_viol:
                            best_lex_viol = viol
                            best_lex = (s1, f1, s2, f2)

        pct = 100 * best_lex_viol / len(transitions)
        s1, f1, s2, f2 = best_lex
        d1 = "↑" if s1 > 0 else "↓"
        d2 = "↑" if s2 > 0 else "↓"
        print(f"  Best lex: ({f1}{d1}, {f2}{d2}): {best_lex_viol} violations ({pct:.1f}%)")

    # ================================================================
    # PART 3: PROPAGATION CHAIN ANALYSIS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 3: PROPAGATION CHAIN — CYCLE IMPOSSIBILITY")
    print("=" * 90)

    # In a hypothetical cycle of length L:
    # 1. Each position that changes fires ≥2 times
    # 2. Between firings of same position, a neighbor must fire
    # 3. Define "support set" S = positions that fire
    # 4. S must be connected (adjacent positions)
    # 5. Each position in S fires ≥2 times

    # Key constraint: for position i to fire twice with S going a→b→a,
    # the neighbors must change between the two firings.
    # The no-2-cycle property ensures b→a requires different (L,R) than a→b.

    # Q: What is the minimum |S| for a cycle to exist?
    # Each position in S fires ≥2 times, and S is connected.
    # The "boundary" of S (positions adjacent to non-S positions) have
    # one neighbor that doesn't change, constraining their possible oscillations.

    print("\nAnalyzing T_mid oscillation requirements:")
    print("For position i using T_mid, what oscillation paths exist?")
    print("And what neighbor changes are required?")

    # For each possible oscillation a→b→a at a T_mid position:
    osc_requirements = []
    for a in range(3):
        for b in range(3):
            if a == b:
                continue
            # First: a→b requires some (L1, R1)
            # Then: b→a requires some (L2, R2) with (L2,R2) ≠ (L1,R1)
            # (because of no-2-cycle: T_mid(L1,b,R1) = b, so (L2,R2) ≠ (L1,R1))
            first_options = [(L, R) for L in range(3) for R in range(3)
                             if T_mid[(L, a, R)] == b]
            for L1, R1 in first_options:
                # After first firing, S=b. Need T_mid(L2, b, R2) = a
                second_options = [(L2, R2) for L2 in range(3) for R2 in range(3)
                                  if T_mid[(L2, b, R2)] == a]
                for L2, R2 in second_options:
                    L_change = (L1 != L2)
                    R_change = (R1 != R2)
                    osc_requirements.append({
                        'val': a, 'via': b,
                        'L1': L1, 'R1': R1, 'L2': L2, 'R2': R2,
                        'L_change': L_change, 'R_change': R_change
                    })

    # Count how many require L change, R change, both
    both = sum(1 for r in osc_requirements if r['L_change'] and r['R_change'])
    l_only = sum(1 for r in osc_requirements if r['L_change'] and not r['R_change'])
    r_only = sum(1 for r in osc_requirements if not r['L_change'] and r['R_change'])
    neither = sum(1 for r in osc_requirements if not r['L_change'] and not r['R_change'])
    total = len(osc_requirements)
    print(f"\n  Total oscillation paths: {total}")
    print(f"  Require L change only: {l_only}")
    print(f"  Require R change only: {r_only}")
    print(f"  Require both L and R: {both}")
    print(f"  Require neither (IMPOSSIBLE BY NO-2-CYCLE): {neither}")

    if neither > 0:
        print("  WARNING: found oscillations with same (L,R)!")
        for r in osc_requirements:
            if not r['L_change'] and not r['R_change']:
                print(f"    {r['val']}→{r['via']}→{r['val']} with L={r['L1']},R={r['R1']}")

    # For each oscillation that requires BOTH neighbors to change,
    # the left AND right neighbors must each fire ≥1 time between the two firings.
    print(f"\n  Oscillations requiring ONLY left change: {l_only}")
    for r in osc_requirements:
        if r['L_change'] and not r['R_change']:
            print(f"    {r['val']}→{r['via']}→{r['val']}: "
                  f"L: {r['L1']}→{r['L2']}, R: {r['R1']}→{r['R2']}")

    print(f"\n  Oscillations requiring ONLY right change: {r_only}")
    for r in osc_requirements:
        if not r['L_change'] and r['R_change']:
            print(f"    {r['val']}→{r['via']}→{r['val']}: "
                  f"L: {r['L1']}→{r['L2']}, R: {r['R1']}→{r['R2']}")

    # ================================================================
    # PART 4: CHAIN DIRECTIONALITY
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 4: CHAIN DIRECTIONALITY — DO OBLIGATIONS PROPAGATE?")
    print("=" * 90)

    # For a left-only oscillation at position i:
    # - L changes from L1 to L2, meaning position i-1 fires
    # - Position i-1's value changes from L1 to L2
    # - For i-1 to return to L1 (cycle requirement), i-1 must oscillate too
    # - i-1's oscillation requires ITS neighbors to change
    # This creates a LEFTWARD chain of obligations!
    #
    # For a right-only oscillation:
    # Creates a RIGHTWARD chain.
    #
    # For a both-change oscillation:
    # Creates chains in BOTH directions.
    #
    # KEY QUESTION: can these chains form a closed loop?

    # Let's build the "obligation graph": for each (position, oscillation type),
    # what obligations does it create at neighbors?

    print("\nT_mid obligation chains:")
    print("For each oscillation, what value change is required at each neighbor?")

    for r in osc_requirements:
        if r['L_change'] and not r['R_change']:
            print(f"\n  [{r['val']}→{r['via']}→{r['val']}] at pos i, R={r['R1']} fixed:")
            print(f"    LEFT neighbor (pos i-1) must change: {r['L1']}→{r['L2']}")
            # What oscillation does i-1 need? It changes from L1 to L2.
            # This is a single change, not a full oscillation. For a cycle,
            # i-1 must also return to L1, so it needs L1→L2→...→L1.
            # The simplest return is via L2→L1.
            # What are the requirements for L1→L2 at position i-1 (using T_mid)?
            l1, l2 = r['L1'], r['L2']
            needed = [(LL, RR) for LL in range(3) for RR in range(3)
                      if T_mid[(LL, l1, RR)] == l2]
            # But R at position i-1 is c[i] = r['val'] (before i fires)
            # Actually, the timing matters. When i-1 fires, what is c[i]?
            # It could be r['val'] or r['via'] depending on when i-1 fires.
            print(f"    For i-1's value {l1}→{l2}: needs (LL,RR) ∈ {needed}")
            if r['val'] in [rr for _, rr in needed]:
                print(f"      ✓ Compatible with R=c[i]={r['val']} (before i fires)")
            if r['via'] in [rr for _, rr in needed]:
                print(f"      ✓ Compatible with R=c[i]={r['via']} (after i fires)")

    # ================================================================
    # PART 5: FIXED-POINT CONVERGENCE ZONES
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 5: FIXED-POINT CONVERGENCE ZONES")
    print("=" * 90)

    # For T_mid, define the "agreement zone": positions i where
    # T_mid(c[i-1], c[i], c[i+1]) = c[i] (position is at fixed point).
    # Q: Can the agreement zone only grow (never shrink)?
    # We know it can shrink (that's why n_settled has violations).
    # But WHICH positions can leave the agreement zone?

    nv = 6
    ms, fs, good_set, bad_set, adj = get_bad_graph(nv)
    rank = compute_ranks(bad_set, adj)

    transitions = []
    for c in bad_set:
        for succ, mover in adj[c]:
            transitions.append((c, succ, mover))

    # For each transition, which positions enter/leave agreement zone?
    enter_counts = Counter()  # (mover_pos, affected_pos, relative_pos) → count
    leave_counts = Counter()

    for c, cp, mv in transitions:
        for i in range(nv):
            L_old = c[(i-1) % nv]; S_old = c[i]; R_old = c[(i+1) % nv]
            L_new = cp[(i-1) % nv]; S_new = cp[i]; R_new = cp[(i+1) % nv]
            was_settled = (fs[i](L_old, S_old, R_old) == S_old)
            now_settled = (fs[i](L_new, S_new, R_new) == S_new)
            rel = i - mv
            if was_settled and not now_settled:
                leave_counts[(mv, i, rel)] += 1
            elif not was_settled and now_settled:
                enter_counts[(mv, i, rel)] += 1

    print(f"\nn={nv}: Positions that LEAVE agreement zone when mover fires:")
    for key in sorted(leave_counts.keys()):
        mv, pos, rel = key
        print(f"  Mover P{mv}, affected P{pos} (rel={rel:+d}): {leave_counts[key]} times")

    # Aggregate by relative position
    print(f"\n  Aggregated by relative position:")
    rel_leave = Counter()
    rel_enter = Counter()
    for (mv, pos, rel), cnt in leave_counts.items():
        rel_leave[rel] += cnt
    for (mv, pos, rel), cnt in enter_counts.items():
        rel_enter[rel] += cnt

    for rel in sorted(set(list(rel_leave.keys()) + list(rel_enter.keys()))):
        print(f"    rel={rel:+d}: enter={rel_enter.get(rel,0)}, leave={rel_leave.get(rel,0)}")

    # ================================================================
    # PART 6: THE "INVERSION COUNT" POTENTIAL
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 6: INVERSION-BASED POTENTIALS")
    print("=" * 90)

    # In the good cycle, values follow a specific order pattern.
    # Phase 1: (0,0,...) → (1,1,...) — values increase L→R
    # Phase 2: (1,1,...) → values become 2 R→L
    # Phase 3: (2,2,...) → reset to 0 L→R
    #
    # An "inversion" is a position where the natural order is violated.
    # E.g., c[i] > c[i+1] when we expect increasing, or c[i] < c[i+1] when decreasing.

    for nv in [5, 6, 7, 8]:
        ms, fs, good_set, bad_set, adj = get_bad_graph(nv)
        transitions = []
        for c in bad_set:
            for succ, mover in adj[c]:
                transitions.append((c, succ, mover))

        # Inversion count: pair (i,j) with i<j where c[i] > c[j]
        def inversions(c):
            count = 0
            for i in range(nv):
                for j in range(i+1, nv):
                    if c[i] > c[j]:
                        count += 1
            return count

        # Descent count: positions where c[i] > c[i+1]
        def descents(c):
            return sum(1 for i in range(nv-1) if c[i] > c[i+1])

        # "Disorder" = inversions + 2-count (combining two measures)
        viol_inv = 0
        viol_desc = 0
        for c, cp, mv in transitions:
            if inversions(cp) >= inversions(c):
                viol_inv += 1
            if descents(cp) >= descents(c):
                viol_desc += 1
        print(f"  n={nv}: inversions decrease: {viol_inv}/{len(transitions)} "
              f"({100*viol_inv/len(transitions):.1f}%)")
        print(f"  n={nv}: descents decrease: {viol_desc}/{len(transitions)} "
              f"({100*viol_desc/len(transitions):.1f}%)")

    # ================================================================
    # PART 7: TRY THE "SUM OF SQUARES" AND "ENTROPY" POTENTIALS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 7: SUM-OF-SQUARES AND ENTROPY POTENTIALS")
    print("=" * 90)

    for nv in [5, 6, 7, 8]:
        ms, fs, good_set, bad_set, adj = get_bad_graph(nv)
        transitions = []
        for c in bad_set:
            for succ, mover in adj[c]:
                transitions.append((c, succ, mover))

        def sum_sq(c):
            return sum(v * v for v in c)

        def value_entropy(c):
            """Count-based entropy of value distribution."""
            counts = Counter(c)
            total = len(c)
            ent = 0
            for cnt in counts.values():
                p = cnt / total
                if p > 0:
                    ent -= p * math.log2(p)
            return ent

        def max_val(c):
            return max(c)

        # Sum of absolute differences from mean
        def sum_abs_dev(c):
            mean = sum(c) / len(c)
            return sum(abs(v - mean) for v in c)

        for name, func, direction in [
            ('sum_sq ↓', sum_sq, -1),
            ('sum_sq ↑', sum_sq, 1),
            ('entropy ↓', value_entropy, -1),
            ('entropy ↑', value_entropy, 1),
            ('sum_abs_dev ↓', sum_abs_dev, -1),
            ('sum_abs_dev ↑', sum_abs_dev, 1),
        ]:
            viol = 0
            for c, cp, mv in transitions:
                sc = direction * func(c)
                scp = direction * func(cp)
                if sc <= scp:
                    viol += 1
            pct = 100 * viol / len(transitions)
            if pct < 40:
                print(f"  n={nv}: {name}: {viol}/{len(transitions)} ({pct:.1f}%)")

    # ================================================================
    # PART 8: THE "PRIVILEGE POSITION VECTOR" POTENTIAL
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 8: PRIVILEGE POSITION VECTOR")
    print("=" * 90)

    # Idea: the POSITIONS of privileges matter, not just the count.
    # Define the privilege vector as the sorted list of privileged positions.
    # Use lexicographic comparison on this vector.

    for nv in [5, 6, 7]:
        ms, fs, good_set, bad_set, adj = get_bad_graph(nv)
        transitions = []
        for c in bad_set:
            for succ, mover in adj[c]:
                transitions.append((c, succ, mover))

        def priv_vector(c):
            pv = []
            for i in range(nv):
                L = c[(i-1)%nv]; S = c[i]; R = c[(i+1)%nv]
                if fs[i](L, S, R) != S:
                    pv.append(i)
            return tuple(pv)

        # Lex comparison: should the privilege vector decrease?
        # The mover is removed from the PV, and neighbors might be added/removed.
        viol = 0
        for c, cp, mv in transitions:
            pvc = priv_vector(c)
            pvcp = priv_vector(cp)
            if pvc <= pvcp:  # should decrease lexicographically
                viol += 1
        print(f"  n={nv}: priv_vector lex↓: {viol}/{len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

        # Reverse lex?
        viol = 0
        for c, cp, mv in transitions:
            pvc = priv_vector(c)[::-1]
            pvcp = priv_vector(cp)[::-1]
            if pvc <= pvcp:
                viol += 1
        print(f"  n={nv}: priv_vector rev_lex↓: {viol}/{len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

        # Max privilege position decreasing?
        viol = 0
        for c, cp, mv in transitions:
            pvc = priv_vector(c)
            pvcp = priv_vector(cp)
            mc = max(pvc) if pvc else -1
            mcp = max(pvcp) if pvcp else -1
            if mc <= mcp:
                viol += 1
        print(f"  n={nv}: max_priv_pos ↓: {viol}/{len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

    # ================================================================
    # PART 9: DIRECT RANK ANALYSIS — WHAT FUNCTION FITS?
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 9: RANK DISTRIBUTION ANALYSIS")
    print("=" * 90)

    nv = 6
    ms, fs, good_set, bad_set, adj = get_bad_graph(nv)
    rank = compute_ranks(bad_set, adj)

    # For each rank value, what's the average of each feature?
    max_rank = max(rank.values())
    print(f"\nn={nv}: rank vs feature averages")
    print(f"{'rank':>4} {'cnt':>4} {'sum':>5} {'front':>5} {'2s':>4} {'priv':>4} "
          f"{'target':>6} {'inv':>5}")

    for r in range(max_rank + 1):
        configs_at_rank = [c for c in bad_set if rank[c] == r]
        if not configs_at_rank:
            continue
        n_cfg = len(configs_at_rank)
        avg = lambda f: sum(f(c) for c in configs_at_rank) / n_cfg

        avg_sum = avg(lambda c: sum(c))
        avg_front = avg(lambda c: sum(1 for i in range(nv) if c[i] != c[(i+1)%nv]))
        avg_2s = avg(lambda c: sum(1 for i in range(1,nv-1) if c[i] == 2))
        avg_priv = avg(lambda c: sum(1 for i in range(nv)
                                     if fs[i](c[(i-1)%nv], c[i], c[(i+1)%nv]) != c[i]))
        avg_target = avg(lambda c: sum(1 for i in range(nv)
                                       if fs[i](c[(i-1)%nv], c[i], c[(i+1)%nv]) == c[i]))
        avg_inv = avg(lambda c: sum(1 for i in range(nv) for j in range(i+1,nv)
                                    if c[i] > c[j]))

        print(f"{r:>4} {n_cfg:>4} {avg_sum:>5.2f} {avg_front:>5.2f} {avg_2s:>4.2f} "
              f"{avg_priv:>4.2f} {avg_target:>6.2f} {avg_inv:>5.2f}")


if __name__ == "__main__":
    main()
