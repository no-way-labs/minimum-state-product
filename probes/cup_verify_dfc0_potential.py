#!/usr/bin/env python3
"""Verify that Ψ + f(c_0, d_{n-1}) strictly decreases on ALL Δfc=0 bad→bad transitions."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system


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


def phi(c, n):
    d = get_d_vector(c, n)
    return psi(c, n) + f_boundary(c[0], d[n-1], n)


def verify_dfc0_potential(n):
    """Check ΔΦ < 0 for all Δfc=0 bad→bad transitions."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    violations = 0
    total_dfc0 = 0
    max_dphi = float('-inf')

    for c in bad_set:
        fc_c = frontier_count(c, n)
        phi_c = phi(c, n)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            fc_s = frontier_count(succ, n)
            if fc_s != fc_c:
                continue  # only Δfc=0
            total_dfc0 += 1
            phi_s = phi(succ, n)
            dphi = phi_s - phi_c
            if dphi > max_dphi:
                max_dphi = dphi
            if dphi >= 0:
                violations += 1
                d = get_d_vector(c, n)
                ds = get_d_vector(succ, n)
                mt = "BOT" if p == 0 else ("TOP" if p == n-1 else f"M{p}")
                print(f"  VIOLATION: {mt} c={c} d={d} → d'={ds} ΔΦ={dphi}")

    return violations, total_dfc0, max_dphi


if __name__ == "__main__":
    print("Verifying Ψ + f(c_0, d_{n-1}) on Δfc=0 bad→bad transitions")
    print("=" * 60)
    for nv in range(3, 15):
        total = 2 * 3**(nv-1)
        if total > 500000:
            print(f"n={nv}: SKIPPED (product={total})")
            continue
        v, t, mx = verify_dfc0_potential(nv)
        status = "✓" if v == 0 else f"✗ ({v} violations)"
        print(f"n={nv}: {t} Δfc=0 transitions, max ΔΦ={mx}, {status}")
