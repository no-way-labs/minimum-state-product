#!/usr/bin/env python3
"""CUP: Analyze the rank function to find a closed-form expression.

The rank R(c) = worst-case steps to reach good set.
This is the UNIQUE valid decreasing potential. Find its structure.
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


def compute_ranks(n):
    """Compute worst-case rank for every bad config."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

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

    return rank, fs, good_set, bad_set


def analyze_rank_by_features(n):
    """Analyze rank as a function of various features."""
    rank, fs, good_set, bad_set = compute_ranks(n)
    if not rank:
        return

    print(f"\n{'='*60}")
    print(f"n={n}: RANK ANALYSIS")
    print(f"{'='*60}")

    # Features for each config
    data = []
    for c in sorted(bad_set):
        if c not in rank:
            continue
        d = get_d_vector(c, n)
        fc = frontier_count(c, n)
        c0 = c[0]
        cn = c[n-1]

        # Type counts
        n1 = sum(1 for x in d if x == 1)  # type-1 count
        n2 = sum(1 for x in d if x == 2)  # type-2 count

        # Position sums
        pos1 = sum(i for i, x in enumerate(d) if x == 1)
        pos2 = sum(n-1-i for i, x in enumerate(d) if x == 2)

        # Propagation potential
        psi = pos1 + pos2

        # "Interior" frontiers (excluding boundary positions)
        int_fc = sum(1 for i in range(1, n-1) if d[i] != 0)

        # d at boundaries
        d0 = d[0]
        dn2 = d[n-2]
        dn1 = d[n-1]

        r = rank[c]
        data.append({
            'c': c, 'd': d, 'rank': r, 'fc': fc, 'c0': c0, 'cn': cn,
            'n1': n1, 'n2': n2, 'psi': psi, 'int_fc': int_fc,
            'd0': d0, 'dn2': dn2, 'dn1': dn1, 'pos1': pos1, 'pos2': pos2
        })

    # Group by fc and find rank range
    by_fc = defaultdict(list)
    for d in data:
        by_fc[d['fc']].append(d)

    print(f"\n  Rank range by fc:")
    for fc in sorted(by_fc.keys()):
        ranks = [d['rank'] for d in by_fc[fc]]
        print(f"    fc={fc}: rank {min(ranks)}-{max(ranks)}, count={len(ranks)}")

    # For the max fc configs, what determines rank?
    max_fc = max(by_fc.keys())
    print(f"\n  All configs with fc={max_fc}:")
    for d in sorted(by_fc[max_fc], key=lambda x: -x['rank']):
        print(f"    {d['c']} d={d['d']} rank={d['rank']} c0={d['c0']} "
              f"cn={d['cn']} psi={d['psi']}")

    # Check: does rank correlate with psi within each fc level?
    print(f"\n  Rank vs psi correlation by fc:")
    for fc in sorted(by_fc.keys()):
        items = by_fc[fc]
        if len(items) < 2:
            continue
        # Check if rank = a*psi + b*c0 + c*cn + d
        # Simple: check max rank for each psi value
        by_psi = defaultdict(list)
        for d in items:
            by_psi[(d['psi'], d['c0'], d['cn'])].append(d['rank'])
        pairs = []
        for (psi, c0, cn), ranks in sorted(by_psi.items()):
            pairs.append((psi, c0, cn, min(ranks), max(ranks)))
        if len(pairs) <= 12:
            print(f"    fc={fc}:")
            for psi, c0, cn, rmin, rmax in pairs:
                print(f"      psi={psi} c0={c0} cn={cn}: rank={rmin}-{rmax}")


def check_potential_candidates(n):
    """Try various potential functions and check if they strictly decrease
    on ALL bad→bad transitions."""
    rank, fs, good_set, bad_set = compute_ranks(n)

    print(f"\n{'='*60}")
    print(f"n={n}: POTENTIAL FUNCTION SEARCH")
    print(f"{'='*60}")

    def get_features(c):
        d = get_d_vector(c, n)
        fc = frontier_count(c, n)
        pos1 = sum(i for i, x in enumerate(d) if x == 1)
        pos2 = sum(n-1-i for i, x in enumerate(d) if x == 2)
        psi = pos1 + pos2
        n1 = sum(1 for x in d if x == 1)
        n2 = sum(1 for x in d if x == 2)
        c0 = c[0]
        cn = c[n-1]
        return fc, psi, n1, n2, c0, cn, d

    # Candidate potentials
    def phi_lex_fc_psi(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return (fc, psi)

    def phi_lex_fc_psi_c0(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return (fc, psi, c0)

    def phi_weighted(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return n * n * fc + psi

    def phi_lex_fc_psi_cn(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return (fc, psi, cn)

    def phi_lex_fc_n1_psi(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return (fc, n1, psi)

    def phi_lex_fc_c0_psi(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return (fc, c0, psi)

    # New: try frontier types near boundaries
    def phi_boundary_aware(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        # Count "resolved" boundaries (d_i = 0 at boundary positions)
        resolved = sum(1 for i in [0, n-2, n-1] if d[i] == 0)
        return (fc, -resolved, psi)

    # Track total weighted position
    def phi_total_weighted(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        # Ψ_total = pos1 + (n-1-pos2_actual) where pos2_actual = Σi for d_i=2
        pos2_actual = sum(i for i, x in enumerate(d) if x == 2)
        return (fc, pos1 + pos2_actual)

    def phi_lex_fc_d_tuple(c):
        """Lexicographic on (fc, d-vector in some canonical order)."""
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return (fc,) + d

    def phi_lex_fc_d_reversed(c):
        fc, psi, n1, n2, c0, cn, d = get_features(c)
        return (fc,) + d[::-1]

    candidates = [
        ("fc_psi", phi_lex_fc_psi),
        ("fc_psi_c0", phi_lex_fc_psi_c0),
        ("n²fc+psi", phi_weighted),
        ("fc_psi_cn", phi_lex_fc_psi_cn),
        ("fc_n1_psi", phi_lex_fc_n1_psi),
        ("fc_c0_psi", phi_lex_fc_c0_psi),
        ("fc_boundary_psi", phi_boundary_aware),
        ("fc_pos1+pos2actual", phi_total_weighted),
        ("fc_d_lex", phi_lex_fc_d_tuple),
        ("fc_d_revlex", phi_lex_fc_d_reversed),
    ]

    for name, phi in candidates:
        violations = 0
        violation_examples = []
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            phi_c = phi(c)
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in bad_set:
                    phi_s = phi(succ)
                    if phi_s >= phi_c:
                        violations += 1
                        if len(violation_examples) < 2:
                            violation_examples.append((c, p, succ, phi_c, phi_s))
        if violations == 0:
            print(f"  {name}: ✓ VALID POTENTIAL!")
        else:
            print(f"  {name}: ✗ {violations} violations")
            for c, p, s, pc, ps in violation_examples:
                mt = "BOT" if p==0 else ("TOP" if p==n-1 else f"M{p}")
                print(f"    {c} {mt}→ {s}  Φ: {pc} → {ps}")


def study_moves_that_increase_psi(n):
    """For (fc,psi) violations: what move types cause them?"""
    rank, fs, good_set, bad_set = compute_ranks(n)

    print(f"\n{'='*60}")
    print(f"n={n}: MOVES THAT INCREASE (fc,psi)")
    print(f"{'='*60}")

    violations_by_type = defaultdict(list)
    for c in bad_set:
        d = get_d_vector(c, n)
        fc = frontier_count(c, n)
        pos1 = sum(i for i, x in enumerate(d) if x == 1)
        pos2 = sum(n-1-i for i, x in enumerate(d) if x == 2)
        psi = pos1 + pos2
        phi_c = (fc, psi)

        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            ds = get_d_vector(succ, n)
            fcs = frontier_count(succ, n)
            pos1s = sum(i for i, x in enumerate(ds) if x == 1)
            pos2s = sum(n-1-i for i, x in enumerate(ds) if x == 2)
            psis = pos1s + pos2s
            phi_s = (fcs, psis)

            if phi_s >= phi_c:
                mt = "BOT" if p == 0 else ("TOP" if p == n-1 else "MID")
                delta_fc = fcs - fc
                delta_psi = psis - psi
                violations_by_type[(mt, delta_fc, delta_psi)].append(
                    (c, p, succ, d, ds))

    for key in sorted(violations_by_type.keys()):
        mt, dfc, dpsi = key
        items = violations_by_type[key]
        print(f"  {mt} Δfc={dfc:+d} Δψ={dpsi:+d}: {len(items)} cases")
        for c, p, s, d, ds in items[:2]:
            print(f"    {d} P{p}→ {ds}")


def find_minimal_counterexample(n):
    """For each potential candidate that fails, find the SIMPLEST
    counterexample (lowest fc, smallest d-vector)."""
    rank, fs, good_set, bad_set = compute_ranks(n)

    print(f"\n{'='*60}")
    print(f"n={n}: TOP MOVE psi ANALYSIS")
    print(f"{'='*60}")

    # Focus on top moves: when top fires, how much does psi change?
    for c in sorted(bad_set):
        d = get_d_vector(c, n)
        priv = get_privileged(c, fs, n)
        if n-1 not in priv:
            continue
        fc = frontier_count(c, n)
        pos1 = sum(i for i, x in enumerate(d) if x == 1)
        pos2 = sum(n-1-i for i, x in enumerate(d) if x == 2)
        psi = pos1 + pos2

        succ = apply_move(c, n-1, fs, n)
        ds = get_d_vector(succ, n)
        fcs = frontier_count(succ, n)
        pos1s = sum(i for i, x in enumerate(ds) if x == 1)
        pos2s = sum(n-1-i for i, x in enumerate(ds) if x == 2)
        psis = pos1s + pos2s

        delta_psi = psis - psi
        delta_fc = fcs - fc

        if succ in bad_set:
            print(f"  {d} TOP→ {ds}  Δfc={delta_fc:+d} Δψ={delta_psi:+d}  "
                  f"rank: {rank[c]}→{rank.get(succ, 'G')}")


def check_augmented_psi(n):
    """Try Φ = n²·fc + ψ + correction_for_boundary.
    The correction must handle top's ψ increase (+n-2) and bottom's ψ increase.

    Idea: After top fires, ψ increases by n-2 and fc increases by 2.
    But n²·2 >> n-2, so fc decrease dominates IF fc always decreases before top fires again.
    The issue is top can fire when fc DOESN'T decrease first (fc=0 before top).
    """
    rank, fs, good_set, bad_set = compute_ranks(n)

    print(f"\n{'='*60}")
    print(f"n={n}: AUGMENTED POTENTIAL SEARCH")
    print(f"{'='*60}")

    # Try: Φ = A·fc + B·ψ where we search for A, B > 0
    # Need: A·Δfc + B·Δψ < 0 for ALL bad→bad transitions.
    # Middle shift: Δfc=0, Δψ=-1. Need -B < 0. ✓
    # Middle type change: Δfc=-1, Δψ=varies. Need -A + B·Δψ < 0, i.e., B·Δψ < A.
    # Middle annihilation: Δfc=-2, Δψ<0. Need -2A + B·Δψ < 0. Always true.
    # Top: Δfc=+2, Δψ varies. Need 2A + B·Δψ < 0, i.e., B·Δψ < -2A.
    # Bottom: varies.

    # Find min Δψ for top moves
    top_dpsi = []
    bot_dpsi = []
    mid_tc_dpsi = []  # Middle type change
    mid_shift_dpsi = []

    for c in bad_set:
        d = get_d_vector(c, n)
        fc = frontier_count(c, n)
        pos1 = sum(i for i, x in enumerate(d) if x == 1)
        pos2 = sum(n-1-i for i, x in enumerate(d) if x == 2)
        psi = pos1 + pos2

        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            ds = get_d_vector(succ, n)
            fcs = frontier_count(succ, n)
            pos1s = sum(i for i, x in enumerate(ds) if x == 1)
            pos2s = sum(n-1-i for i, x in enumerate(ds) if x == 2)
            psis = pos1s + pos2s

            delta_fc = fcs - fc
            delta_psi = psis - psi

            if p == 0:
                bot_dpsi.append((delta_fc, delta_psi, d, ds))
            elif p == n-1:
                top_dpsi.append((delta_fc, delta_psi, d, ds))
            else:
                if delta_fc == 0:
                    mid_shift_dpsi.append((delta_psi, d, ds))
                else:
                    mid_tc_dpsi.append((delta_fc, delta_psi, d, ds))

    print(f"  Middle shifts: Δψ ∈ {{{min(x[0] for x in mid_shift_dpsi) if mid_shift_dpsi else '?'}..{max(x[0] for x in mid_shift_dpsi) if mid_shift_dpsi else '?'}}}")
    print(f"  Middle type change/annihilation:")
    tc_by_dfc = defaultdict(list)
    for dfc, dpsi, d, ds in mid_tc_dpsi:
        tc_by_dfc[dfc].append(dpsi)
    for dfc in sorted(tc_by_dfc):
        vals = tc_by_dfc[dfc]
        print(f"    Δfc={dfc}: Δψ ∈ [{min(vals)}, {max(vals)}]")

    print(f"  Top moves:")
    top_by_dfc = defaultdict(list)
    for dfc, dpsi, d, ds in top_dpsi:
        top_by_dfc[dfc].append(dpsi)
    for dfc in sorted(top_by_dfc):
        vals = top_by_dfc[dfc]
        print(f"    Δfc={dfc}: Δψ ∈ [{min(vals)}, {max(vals)}]")

    print(f"  Bottom moves:")
    bot_by_dfc = defaultdict(list)
    for dfc, dpsi, d, ds in bot_dpsi:
        bot_by_dfc[dfc].append(dpsi)
    for dfc in sorted(bot_by_dfc):
        vals = bot_by_dfc[dfc]
        print(f"    Δfc={dfc}: Δψ ∈ [{min(vals)}, {max(vals)}]")

    # For A·fc + B·ψ to work: need 2A + B·max(top Δψ | Δfc=+2) < 0
    # i.e., B·max_top_dpsi < -2A, so max_top_dpsi < -2A/B.
    # For this to hold, need max_top_dpsi < 0 (top must decrease ψ).
    all_top_dpsi_at_dfc2 = top_by_dfc.get(2, [])
    if all_top_dpsi_at_dfc2:
        max_top_dpsi = max(all_top_dpsi_at_dfc2)
        print(f"\n  For A·fc + B·ψ: max top Δψ (when Δfc=+2) = {max_top_dpsi}")
        if max_top_dpsi >= 0:
            print(f"  → A·fc + B·ψ CANNOT work (top increases both fc and ψ)")


if __name__ == "__main__":
    for nv in [4, 5, 6]:
        check_potential_candidates(nv)

    for nv in [4, 5, 6]:
        study_moves_that_increase_psi(nv)

    for nv in [4, 5, 6]:
        check_augmented_psi(nv)

    for nv in [5]:
        analyze_rank_by_features(nv)
