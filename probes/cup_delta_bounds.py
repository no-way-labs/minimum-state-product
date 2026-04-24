#!/usr/bin/env python3
"""CUP: Compute tight bounds on Δ(Ψ+f) for each Δfc level.

Key insight: if max Δ(Ψ+f) for Δfc=-1 transitions is < n-½,
then Φ = A·fc + Ψ + f works for some A in (max_Δ(Ψ+f), n-½).
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


def psi(c, n):
    d = get_d_vector(c, n)
    total = 0
    for i in range(n):
        if d[i] == 1:
            total += i
        elif d[i] == 2:
            total += (n - 1 - i)
    return total


def f_boundary(c_0, d_n1, n):
    table = {
        (0, 0): 0,
        (0, 1): -(3*n - 2),
        (0, 2): -(3*n - 3),
        (1, 0): 2*(n - 1),
        (1, 1): -n,
        (1, 2): -(n - 1),
    }
    return table[(c_0, d_n1)]


def psi_plus_f(c, n):
    d = get_d_vector(c, n)
    return psi(c, n) + f_boundary(c[0], d[n-1], n)


def compute_delta_bounds(n):
    """Compute max Δ(Ψ+f) for each Δfc level, over all bad→bad transitions."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Track max Δ(Ψ+f) by Δfc level and mover type
    by_dfc = defaultdict(lambda: {'max_dpsi': float('-inf'), 'min_dpsi': float('inf'),
                                   'count': 0, 'worst': None})
    by_dfc_type = defaultdict(lambda: {'max_dpsi': float('-inf'), 'count': 0, 'worst': None})

    for c in bad_set:
        pf_c = psi_plus_f(c, n)
        fc_c = frontier_count(c, n)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            pf_s = psi_plus_f(succ, n)
            fc_s = frontier_count(succ, n)
            dfc = fc_s - fc_c
            dpsi = pf_s - pf_c
            mt = "BOT" if p == 0 else ("TOP" if p == n-1 else "MID")

            rec = by_dfc[dfc]
            rec['count'] += 1
            if dpsi > rec['max_dpsi']:
                rec['max_dpsi'] = dpsi
                rec['worst'] = (c, succ, p, mt)
            if dpsi < rec['min_dpsi']:
                rec['min_dpsi'] = dpsi

            rec2 = by_dfc_type[(dfc, mt)]
            rec2['count'] += 1
            if dpsi > rec2['max_dpsi']:
                rec2['max_dpsi'] = dpsi
                rec2['worst'] = (c, succ, p)

    return by_dfc, by_dfc_type


def analytic_top_dfc2(n):
    """Analytically compute Δ(Ψ+f) for top Δfc=+2 transition."""
    # Top fires: (d_{n-2}, d_{n-1}) = (0,0) → (1,2)
    # ΔΨ = (n-2) - 0 + 0 - 0 = n-2  [d_{n-2}: 0→1 contributes +(n-2); d_{n-1}: 0→2 contributes +0]
    # Δf: d_{n-1} changes 0→2
    #   c_0=0: f(0,0)-f(0,2) wait, Δf = f(c_0,2) - f(c_0,0)
    #   c_0=0: -(3n-3) - 0 = -(3n-3)
    #   c_0=1: -(n-1) - 2(n-1) = -3(n-1)
    for c0 in [0, 1]:
        dpsi = (n - 2)  # ΔΨ
        df = f_boundary(c0, 2, n) - f_boundary(c0, 0, n)
        print(f"  Top Δfc=+2, c_0={c0}: ΔΨ={dpsi}, Δf={df}, Δ(Ψ+f)={dpsi+df}")


def analytic_bot_dfc1(n):
    """Analytically compute Δ(Ψ+f) for bottom Δfc=+1 transition."""
    # Bottom Δfc=+1: c_0=1, d_0=1, d_{n-1}=0
    # After: c_0'=0, d_0'=(d_0+1)%3=2, d_{n-1}'=(d_{n-1}-1)%3=2
    # ΔΨ at position 0: d_0: 1→2. Was: 0 (d=1 at i=0 contributes i=0). Now: n-1 (d=2 at i=0 contributes n-1-0).
    # ΔΨ at position n-1: d_{n-1}: 0→2. Was: 0. Now: n-1-(n-1)=0. ΔΨ_{n-1}=0.
    dpsi = (n - 1)  # net ΔΨ
    df = f_boundary(0, 2, n) - f_boundary(1, 0, n)  # c_0: 1→0, d_{n-1}: 0→2
    print(f"  Bot Δfc=+1: ΔΨ={dpsi}, Δf={df}, Δ(Ψ+f)={dpsi+df}")


if __name__ == "__main__":
    print("=" * 70)
    print("ANALYTIC Δ(Ψ+f) FOR Δfc>0 TRANSITIONS")
    print("=" * 70)
    for nv in [4, 5, 6, 7, 8]:
        print(f"\nn={nv}:")
        analytic_top_dfc2(nv)
        analytic_bot_dfc1(nv)

    print("\n" + "=" * 70)
    print("COMPUTATIONAL: max Δ(Ψ+f) BY Δfc LEVEL (bad→bad only)")
    print("=" * 70)
    for nv in range(3, 11):
        by_dfc, by_dfc_type = compute_delta_bounds(nv)
        print(f"\nn={nv}: (threshold for A: need A < {nv} - 0.5 = {nv - 0.5})")
        for dfc in sorted(by_dfc.keys()):
            rec = by_dfc[dfc]
            print(f"  Δfc={dfc:+d}: {rec['count']:5d} transitions, "
                  f"Δ(Ψ+f) ∈ [{rec['min_dpsi']:+d}, {rec['max_dpsi']:+d}]"
                  f"  ({rec['worst'][3]})")
        # Check feasibility
        max_neg_dfc_dpsi = max(
            (rec['max_dpsi'] for dfc, rec in by_dfc.items() if dfc < 0),
            default=float('-inf'))
        threshold = nv - 0.5
        if max_neg_dfc_dpsi < threshold:
            print(f"  → FEASIBLE: max Δ(Ψ+f) for Δfc<0 = {max_neg_dfc_dpsi} < {threshold}")
            # Find optimal A
            A_lo = max_neg_dfc_dpsi
            A_hi = threshold
            print(f"  → A ∈ ({A_lo}, {A_hi}), e.g. A = {(A_lo + A_hi) / 2:.1f}")
        else:
            print(f"  → INFEASIBLE: max Δ(Ψ+f) for Δfc<0 = {max_neg_dfc_dpsi} ≥ {threshold}")

    print("\n" + "=" * 70)
    print("DETAILED: max Δ(Ψ+f) BY (Δfc, mover type)")
    print("=" * 70)
    for nv in [4, 5, 6, 7]:
        by_dfc, by_dfc_type = compute_delta_bounds(nv)
        print(f"\nn={nv}:")
        for (dfc, mt) in sorted(by_dfc_type.keys()):
            rec = by_dfc_type[(dfc, mt)]
            print(f"  {mt:3s} Δfc={dfc:+d}: {rec['count']:4d} trans, "
                  f"max Δ(Ψ+f) = {rec['max_dpsi']:+d}")
