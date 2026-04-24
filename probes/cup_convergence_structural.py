#!/usr/bin/env python3
"""CUP: Key structural lemmas for convergence proof.

Key discoveries to verify:
1. Every bad config has >= 1 privileged MIDDLE proc.
2. After bottom move, bottom is NOT privileged.
3. After top move, top is NOT privileged.
4. For every bad config, at least one move reduces frontier count.
5. Token (privilege) count analysis.
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


def frontier_count(c, n):
    return sum(1 for i in range(n) if (c[(i+1) % n] - c[i]) % 3 != 0)


def get_d_vector(c, n):
    return tuple((c[(i+1)%n] - c[i]) % 3 for i in range(n))


# ========= LEMMA VERIFICATION =========

def verify_lemma_middle_privilege(max_n=10):
    """Verify: every bad config has >= 1 privileged MIDDLE proc."""
    print("=" * 60)
    print("LEMMA: Every bad config has >= 1 middle privilege")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        violations = 0
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            middle_priv = [p for p in priv if 1 <= p <= n - 2]
            if not middle_priv:
                violations += 1
                if violations <= 3:
                    print(f"  VIOLATION n={n}: {c} priv={priv}")

        ok = "✓" if violations == 0 else f"✗ ({violations} violations)"
        print(f"  n={n}: {ok} ({len(bad_set)} bad configs)")


def verify_lemma_boundary_cooldown(max_n=10):
    """Verify: after bottom/top move, that proc is NOT privileged."""
    print("\n" + "=" * 60)
    print("LEMMA: Boundary cooldown (self-disabling)")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        configs = list(cartesian(*(range(m) for m in ms)))

        bot_violations = 0
        top_violations = 0
        total_bot = 0
        total_top = 0

        for c in configs:
            priv = get_privileged(c, fs, n)
            # Bottom
            if 0 in priv:
                total_bot += 1
                succ = apply_move(c, 0, fs, n)
                succ_priv = get_privileged(succ, fs, n)
                if 0 in succ_priv:
                    bot_violations += 1
            # Top
            if n - 1 in priv:
                total_top += 1
                succ = apply_move(c, n - 1, fs, n)
                succ_priv = get_privileged(succ, fs, n)
                if n - 1 in succ_priv:
                    top_violations += 1

        bot_ok = "✓" if bot_violations == 0 else f"✗ ({bot_violations})"
        top_ok = "✓" if top_violations == 0 else f"✗ ({top_violations})"
        print(f"  n={n}: bottom {bot_ok} (of {total_bot}), top {top_ok} (of {total_top})")


def verify_lemma_helpful_move(max_n=10):
    """Verify: for every bad config, at least one move REDUCES frontier count."""
    print("\n" + "=" * 60)
    print("LEMMA: Helpful move exists (some move reduces frontiers)")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        violations = 0
        violation_list = []
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            fc = frontier_count(c, n)
            has_reduction = False
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    has_reduction = True
                    break
                fc_s = frontier_count(succ, n)
                if fc_s < fc:
                    has_reduction = True
                    break
            if not has_reduction:
                violations += 1
                violation_list.append(c)

        ok = "✓" if violations == 0 else f"✗ ({violations} violations)"
        print(f"  n={n}: {ok}")
        if violations > 0 and n <= 6:
            for c in violation_list[:5]:
                priv = get_privileged(c, fs, n)
                fc = frontier_count(c, n)
                moves = []
                for p in priv:
                    s = apply_move(c, p, fs, n)
                    fc_s = frontier_count(s, n)
                    in_good = s in good_set
                    moves.append(f"P{p}→fc={fc_s}{'G' if in_good else ''}")
                print(f"    {c} fc={fc} d={get_d_vector(c,n)} priv={priv} → {', '.join(moves)}")


def verify_lemma_helpful_move_extended(max_n=10):
    """Even if frontier count doesn't decrease, does some move lead to
    a config with a HELPFUL move (frontier-reducing)?
    I.e., 2-step helpful: for every bad config, there's a 2-step path
    that reduces frontiers."""
    print("\n" + "=" * 60)
    print("LEMMA: 2-step helpful (frontier reduction within 2 moves)")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        violations = 0
        for c in bad_set:
            fc = frontier_count(c, n)
            priv = get_privileged(c, fs, n)
            # Check 1-step
            found = False
            for p in priv:
                s1 = apply_move(c, p, fs, n)
                if s1 in good_set or frontier_count(s1, n) < fc:
                    found = True
                    break
                # Check 2-step
                priv2 = get_privileged(s1, fs, n)
                for p2 in priv2:
                    s2 = apply_move(s1, p2, fs, n)
                    if s2 in good_set or frontier_count(s2, n) < fc:
                        found = True
                        break
                if found:
                    break
            if not found:
                violations += 1

        ok = "✓" if violations == 0 else f"✗ ({violations})"
        print(f"  n={n}: {ok}")


def analyze_privilege_count(max_n=9):
    """For each bad config, count the number of privileged processors.
    Track how privilege count changes under each move."""
    print("\n" + "=" * 60)
    print("PRIVILEGE COUNT ANALYSIS")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        priv_dist = defaultdict(int)
        delta_priv = defaultdict(int)

        for c in bad_set:
            priv = get_privileged(c, fs, n)
            pc = len(priv)
            priv_dist[pc] += 1

            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    delta_priv[('to_good', pc)] += 1
                else:
                    priv_s = get_privileged(succ, fs, n)
                    delta = len(priv_s) - pc
                    delta_priv[(delta, pc)] += 1

        print(f"\n  n={n}:")
        print(f"    Privilege count distribution: ", dict(sorted(priv_dist.items())))
        # Show privilege count change stats
        for key in sorted(delta_priv.keys()):
            if key[0] == 'to_good':
                print(f"    priv={key[1]} → good: {delta_priv[key]}")
            else:
                delta, pc = key
                print(f"    priv={pc} Δpriv={delta:+d}: {delta_priv[key]}")


def check_X_invariant(max_n=7):
    """Check X = Σc_i changes for each move type.
    Verify: middle moves give ΔX ∈ {+1, -2}, bottom ∈ {+1, -1}, top varies."""
    print("\n" + "=" * 60)
    print("X = Σc_i CHANGE ANALYSIS")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        configs = list(cartesian(*(range(m) for m in ms)))

        changes = defaultdict(lambda: defaultdict(int))
        for c in configs:
            X = sum(c)
            priv = get_privileged(c, fs, n)
            for p in priv:
                succ = apply_move(c, p, fs, n)
                X_s = sum(succ)
                delta = X_s - X
                if p == 0:
                    mt = "BOTTOM"
                elif p == n - 1:
                    mt = "TOP"
                else:
                    mt = "MIDDLE"
                changes[mt][delta] += 1

        print(f"\n  n={n}:")
        for mt in ["BOTTOM", "MIDDLE", "TOP"]:
            if mt in changes:
                delta_counts = dict(sorted(changes[mt].items()))
                print(f"    {mt}: ΔX = {delta_counts}")


def check_combo_potential(max_n=9):
    """Try Φ = (frontier_count, -X mod 3) lexicographic.
    Or Φ = 3*frontier_count + (X mod 3).
    Or other simple combos."""
    print("\n" + "=" * 60)
    print("COMBINED POTENTIAL SEARCH")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # Try: Φ = n² * F + c_0 * n + X mod 3
        # Try: Φ = F * big + position-of-nearest-annihilation-pair
        # Try: Φ = c_0 (just tracking bottom state)

        # Simple: does c_0 help break ties when frontier count is tied?
        def phi_fc_c0(c):
            return (frontier_count(c, n), c[0])

        def phi_fc_X(c):
            return (frontier_count(c, n), sum(c) % 3)

        def phi_fc_negX(c):
            return (frontier_count(c, n), -(sum(c) % 3))

        def phi_fc_X_full(c):
            return (frontier_count(c, n), sum(c))

        # Test
        for name, phi in [("fc_c0", phi_fc_c0), ("fc_X3", phi_fc_X),
                          ("fc_negX3", phi_fc_negX), ("fc_Xfull", phi_fc_X_full)]:
            violations = 0
            for c in bad_set:
                priv = get_privileged(c, fs, n)
                phi_c = phi(c)
                for p in priv:
                    succ = apply_move(c, p, fs, n)
                    if succ in bad_set:
                        phi_s = phi(succ)
                        if phi_s >= phi_c:
                            violations += 1
            if violations == 0:
                print(f"  n={n} {name}: ✓ VALID POTENTIAL!")
            else:
                if n <= 6:
                    print(f"  n={n} {name}: ✗ {violations} violations")


def check_DAG_depth_structure(max_n=9):
    """Compute the DAG rank of each bad config (longest path to good).
    Analyze: what's the maximum rank, and does it follow a pattern?"""
    print("\n" + "=" * 60)
    print("DAG DEPTH ANALYSIS")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # Compute worst-case rank
        rank = {}
        changed = True
        while changed:
            changed = False
            for c in bad_set:
                if c in rank:
                    continue
                priv = get_privileged(c, fs, n)
                worst = 0
                all_resolved = True
                for p in priv:
                    succ = apply_move(c, p, fs, n)
                    if succ in good_set:
                        steps = 1
                    elif succ in rank:
                        steps = 1 + rank[succ]
                    else:
                        all_resolved = False
                        break
                    worst = max(worst, steps)
                if all_resolved:
                    rank[c] = worst
                    changed = True

        max_rank = max(rank.values()) if rank else 0
        # Distribution of ranks
        rank_dist = defaultdict(int)
        for r in rank.values():
            rank_dist[r] += 1

        # Frontier count of max-rank configs
        max_configs = [c for c, r in rank.items() if r == max_rank]
        fcs = [frontier_count(c, n) for c in max_configs]

        print(f"  n={n}: max_rank={max_rank}, "
              f"max_rank_configs={len(max_configs)}, "
              f"their fc={sorted(set(fcs))}")

        # Check: is max_rank_config's fc always small?
        # Check correlation between rank and fc
        fc_maxrank = defaultdict(int)
        fc_maxval = defaultdict(int)
        for c, r in rank.items():
            fc = frontier_count(c, n)
            fc_maxrank[fc] = max(fc_maxrank[fc], r)
            fc_maxval[fc] += 1

        print(f"    Max rank by fc: {dict(sorted(fc_maxrank.items()))}")


if __name__ == "__main__":
    verify_lemma_middle_privilege(10)
    verify_lemma_boundary_cooldown(10)
    verify_lemma_helpful_move(9)
    verify_lemma_helpful_move_extended(9)
    check_X_invariant(7)
    check_combo_potential(7)
    check_DAG_depth_structure(9)
