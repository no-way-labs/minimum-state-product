#!/usr/bin/env python3
"""CUP: LP search for potential Φ = A·fc + Ψ + f(c_0, c_{n-1}, d_0, d_{n-1}).

With 54 parameters for f plus weight A, solve the LP to check feasibility.
If feasible, we have an analytic convergence proof.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict
import subprocess


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


def get_boundary_state(c, n):
    """Return (c_0, c_{n-1}, d_0, d_{n-1})."""
    d = get_d_vector(c, n)
    return (c[0], c[n-1], d[0], d[n-1])


def enumerate_transitions(n):
    """Get all bad→bad transitions with their Δfc, ΔΨ, and boundary state changes."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    transitions = []
    for c in bad_set:
        psi_c = psi(c, n)
        fc_c = frontier_count(c, n)
        bs_c = get_boundary_state(c, n)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            psi_s = psi(succ, n)
            fc_s = frontier_count(succ, n)
            bs_s = get_boundary_state(succ, n)
            transitions.append({
                'c': c, 'succ': succ, 'proc': p,
                'dfc': fc_s - fc_c,
                'dpsi': psi_s - psi_c,
                'bs_before': bs_c,
                'bs_after': bs_s,
            })
    return transitions


def solve_lp_scipy(n):
    """Use scipy linprog to check if the LP is feasible."""
    try:
        from scipy.optimize import linprog
        import numpy as np
    except ImportError:
        print("scipy not available, skipping LP")
        return None

    transitions = enumerate_transitions(n)
    print(f"n={n}: {len(transitions)} bad→bad transitions")

    # Variables: A (weight), f(c0, cn1, d0, dn1) for each boundary state.
    # Boundary states: c0 ∈ {0,1}, cn1 ∈ {0,1,2}, d0 ∈ {0,1,2}, dn1 ∈ {0,1,2}
    # Total f variables: 2*3*3*3 = 54
    # Variable ordering: x[0] = A, x[1..54] = f values

    bs_list = []
    bs_index = {}
    for c0 in range(2):
        for cn1 in range(3):
            for d0 in range(3):
                for dn1 in range(3):
                    bs = (c0, cn1, d0, dn1)
                    bs_index[bs] = len(bs_list) + 1  # +1 because x[0] = A
                    bs_list.append(bs)

    num_vars = 1 + len(bs_list)  # A + 54 f values

    # Constraints: A*dfc + dpsi + f(bs_after) - f(bs_before) <= -1
    # I.e., A*dfc + dpsi + f_after - f_before + 1 <= 0
    A_ub = []
    b_ub = []

    for t in transitions:
        row = [0.0] * num_vars
        row[0] = t['dfc']  # coefficient of A
        bs_b = t['bs_before']
        bs_a = t['bs_after']
        if bs_b in bs_index:
            row[bs_index[bs_b]] = -1.0  # -f_before
        if bs_a in bs_index:
            row[bs_index[bs_a]] = 1.0   # +f_after
        A_ub.append(row)
        b_ub.append(-1.0 - t['dpsi'])  # dpsi + ... <= -1 → ... <= -1 - dpsi

    # Also: A >= 0
    row = [0.0] * num_vars
    row[0] = -1.0
    A_ub.append(row)
    b_ub.append(0.0)

    # Objective: minimize 0 (feasibility check)
    c_obj = [0.0] * num_vars

    # Bounds: A >= 0, f values unbounded
    bounds = [(0, None)] + [(None, None)] * len(bs_list)

    result = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

    if result.success:
        A_val = result.x[0]
        print(f"  FEASIBLE! A = {A_val:.4f}")
        # Print f values
        for bs in bs_list:
            idx = bs_index[bs]
            val = result.x[idx]
            if abs(val) > 0.01:
                print(f"    f{bs} = {val:.4f}")
        return result.x
    else:
        print(f"  INFEASIBLE: {result.message}")
        return None


def solve_lp_with_extra_state(n):
    """Try LP with f depending on even more state.

    f(c_0, c_1, c_{n-2}, c_{n-1}).
    c_0 ∈ {0,1}, c_1 ∈ {0,1,2}, c_{n-2} ∈ {0,1,2}, c_{n-1} ∈ {0,1,2}
    Total: 2*3*3*3 = 54 parameters (same count, different state)
    """
    try:
        from scipy.optimize import linprog
    except ImportError:
        print("scipy not available")
        return None

    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    def get_extra_state(c, n):
        return (c[0], c[1], c[n-2], c[n-1])

    es_list = []
    es_index = {}
    for c0 in range(2):
        for c1 in range(3):
            for cn2 in range(3):
                for cn1 in range(3):
                    es = (c0, c1, cn2, cn1)
                    es_index[es] = len(es_list) + 1
                    es_list.append(es)

    num_vars = 1 + len(es_list)

    A_ub_rows = []
    b_ub_vals = []

    for c in bad_set:
        psi_c = psi(c, n)
        fc_c = frontier_count(c, n)
        es_c = get_extra_state(c, n)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            psi_s = psi(succ, n)
            fc_s = frontier_count(succ, n)
            es_s = get_extra_state(succ, n)

            row = [0.0] * num_vars
            row[0] = fc_s - fc_c
            if es_c in es_index:
                row[es_index[es_c]] = -1.0
            if es_s in es_index:
                row[es_index[es_s]] = 1.0
            A_ub_rows.append(row)
            b_ub_vals.append(-1.0 - (psi_s - psi_c))

    # A >= 0
    row = [0.0] * num_vars
    row[0] = -1.0
    A_ub_rows.append(row)
    b_ub_vals.append(0.0)

    c_obj = [0.0] * num_vars
    bounds = [(0, None)] + [(None, None)] * len(es_list)

    res = linprog(c_obj, A_ub=A_ub_rows, b_ub=b_ub_vals, bounds=bounds, method='highs')

    if res.success:
        print(f"  Extra-state LP FEASIBLE! A = {res.x[0]:.4f}")
        return res.x
    else:
        print(f"  Extra-state LP INFEASIBLE: {res.message}")
        return None


def solve_lp_full_boundary(n):
    """Try LP with f depending on (c_0, c_{n-1}, d_0, d_1, d_{n-2}, d_{n-1}).

    More boundary state. 2*3*3*3*3*3 = 486 parameters.
    """
    try:
        from scipy.optimize import linprog
    except ImportError:
        print("scipy not available")
        return None

    ms = [2] + [3] * (n - 1)
    fs_rules = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs_rules)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    def get_fb_state(c, n):
        d = get_d_vector(c, n)
        return (c[0], c[n-1], d[0], d[1], d[n-2], d[n-1])

    fb_list = []
    fb_index = {}
    for c0 in range(2):
        for cn1 in range(3):
            for d0 in range(3):
                for d1 in range(3):
                    for dn2 in range(3):
                        for dn1 in range(3):
                            fb = (c0, cn1, d0, d1, dn2, dn1)
                            fb_index[fb] = len(fb_list) + 1
                            fb_list.append(fb)

    num_vars = 1 + len(fb_list)
    print(f"  Full boundary LP: {num_vars} variables, ", end='')

    A_ub_rows = []
    b_ub_vals = []

    for c in bad_set:
        psi_c = psi(c, n)
        fc_c = frontier_count(c, n)
        fb_c = get_fb_state(c, n)
        priv = get_privileged(c, fs_rules, n)
        for p in priv:
            succ = apply_move(c, p, fs_rules, n)
            if succ not in bad_set:
                continue
            psi_s = psi(succ, n)
            fc_s = frontier_count(succ, n)
            fb_s = get_fb_state(succ, n)

            row = [0.0] * num_vars
            row[0] = fc_s - fc_c
            if fb_c in fb_index:
                row[fb_index[fb_c]] = -1.0
            if fb_s in fb_index:
                row[fb_index[fb_s]] = 1.0
            A_ub_rows.append(row)
            b_ub_vals.append(-1.0 - (psi_s - psi_c))

    print(f"{len(A_ub_rows)} constraints")

    row = [0.0] * num_vars
    row[0] = -1.0
    A_ub_rows.append(row)
    b_ub_vals.append(0.0)

    c_obj = [0.0] * num_vars
    bounds = [(0, None)] + [(None, None)] * len(fb_list)

    res = linprog(c_obj, A_ub=A_ub_rows, b_ub=b_ub_vals, bounds=bounds, method='highs')

    if res.success:
        A_val = res.x[0]
        print(f"  FEASIBLE! A = {A_val:.4f}")
        # Print nonzero f values (top 20 by magnitude)
        f_vals = [(fb_list[i], res.x[i+1]) for i in range(len(fb_list))
                  if abs(res.x[i+1]) > 0.01]
        f_vals.sort(key=lambda x: -abs(x[1]))
        for fb, val in f_vals[:20]:
            print(f"    f{fb} = {val:.4f}")
        return res.x
    else:
        print(f"  INFEASIBLE: {res.message}")
        return None


if __name__ == "__main__":
    print("=" * 70)
    print("LP SEARCH: Φ = A·fc + Ψ + f(c_0, c_{n-1}, d_0, d_{n-1})")
    print("=" * 70)
    for nv in range(3, 8):
        print(f"\nn={nv}:")
        solve_lp_scipy(nv)

    print("\n" + "=" * 70)
    print("LP SEARCH: Φ = A·fc + Ψ + f(c_0, c_1, c_{n-2}, c_{n-1})")
    print("=" * 70)
    for nv in range(3, 8):
        print(f"\nn={nv}:")
        solve_lp_with_extra_state(nv)

    print("\n" + "=" * 70)
    print("LP SEARCH: Φ = A·fc + Ψ + f(c_0, c_{n-1}, d_0, d_1, d_{n-2}, d_{n-1})")
    print("=" * 70)
    for nv in range(3, 8):
        print(f"\nn={nv}:")
        solve_lp_full_boundary(nv)
