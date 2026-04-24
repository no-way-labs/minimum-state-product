#!/usr/bin/env python3
"""CUP: Verify the potential function Φ = W·fc + Ψ + f(c_0, d_{n-1}).

Key discovery: Ψ + f(c_0, d_{n-1}) strictly decreases on ALL Δfc=0 transitions.
Now verify that Φ = (n-1)·fc + Ψ + f(c_0, d_{n-1}) works for the FULL graph,
or identify the remaining edge cases.

f(c_0, d_{n-1}):
  (0,0): 0
  (0,1): -(3n-2)
  (0,2): -(3n-3)
  (1,0): 2(n-1)
  (1,1): -n
  (1,2): -(n-1)
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
    """Propagation potential: Σ_{d_i=1} i + Σ_{d_i=2} (n-1-i)."""
    d = get_d_vector(c, n)
    total = 0
    for i in range(n):
        if d[i] == 1:
            total += i
        elif d[i] == 2:
            total += (n - 1 - i)
    return total


def f_boundary(c_0, d_n1, n):
    """Boundary correction f(c_0, d_{n-1})."""
    table = {
        (0, 0): 0,
        (0, 1): -(3*n - 2),
        (0, 2): -(3*n - 3),
        (1, 0): 2*(n - 1),
        (1, 1): -n,
        (1, 2): -(n - 1),
    }
    return table[(c_0, d_n1)]


def phi_full(c, n, W):
    """Full potential: W·fc + Ψ + f(c_0, d_{n-1})."""
    d = get_d_vector(c, n)
    return W * frontier_count(c, n) + psi(c, n) + f_boundary(c[0], d[n-1], n)


def verify_potential(n, W=None):
    """Verify that Φ = W·fc + Ψ + f strictly decreases on ALL bad→bad transitions."""
    if W is None:
        W = n - 1
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    violations = []
    for c in bad_set:
        phi_c = phi_full(c, n, W)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            phi_s = phi_full(succ, n, W)
            delta = phi_s - phi_c
            if delta >= 0:
                d = get_d_vector(c, n)
                ds = get_d_vector(succ, n)
                dfc = frontier_count(succ, n) - frontier_count(c, n)
                mt = "BOT" if p == 0 else ("TOP" if p == n-1 else "MID")
                violations.append((c, succ, p, delta, dfc, d, ds, mt))

    if violations:
        print(f"  n={n}, W={W}: {len(violations)} violations")
        for c, s, p, delta, dfc, d, ds, mt in violations[:5]:
            print(f"    {mt} Δfc={dfc:+d} ΔΦ={delta:+d}: "
                  f"d={d} c0={c[0]} → d={ds} c0={s[0]}")
    else:
        print(f"  n={n}, W={W}: ✓ VALID POTENTIAL!")
    return len(violations)


def search_optimal_W(n):
    """Find the W value that minimizes violations."""
    best_W = None
    best_v = float('inf')
    for W in range(1, 5*n):
        v = verify_potential(n, W)
        if v < best_v:
            best_v = v
            best_W = W
        if v == 0:
            break
    if best_v > 0:
        print(f"  n={n}: best W={best_W} with {best_v} violations")
    return best_W


def analyze_violations_detailed(n, W=None):
    """For the violations, check if they involve specific bottom cases."""
    if W is None:
        W = n - 1
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    by_case = defaultdict(list)
    for c in bad_set:
        phi_c = phi_full(c, n, W)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ not in bad_set:
                continue
            phi_s = phi_full(succ, n, W)
            delta = phi_s - phi_c
            if delta >= 0:
                d = get_d_vector(c, n)
                dfc = frontier_count(succ, n) - frontier_count(c, n)
                mt = "BOT" if p == 0 else ("TOP" if p == n-1 else "MID")
                by_case[(mt, dfc, c[0], d[0], d[n-1])].append(
                    (c, succ, delta))

    print(f"\n  n={n}, W={W}: Violation cases:")
    for key in sorted(by_case.keys()):
        mt, dfc, c0, d0, dn1 = key
        items = by_case[key]
        print(f"    {mt} Δfc={dfc:+d} c0={c0} d0={d0} dn1={dn1}: "
              f"{len(items)} violations (ΔΦ={items[0][2]:+d})")


def try_adjusted_f(n):
    """Try adjusting f values to handle all transitions.

    The issue: bottom Δfc=-1 with c_0=0, d_{n-1}=1 gives ΔΦ=+1 with W=n-1.

    Key question: does this case EVER produce a bad→bad transition?
    """
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Check: bottom fires with c_0=0, d_0=1, d_{n-1}=1 (Δfc=-1).
    # Is the successor ALWAYS good?
    bad_to_bad_cases = []
    for c in bad_set:
        d = get_d_vector(c, n)
        if c[0] != 0 or d[0] != 1 or d[n-1] != 1:
            continue
        priv = get_privileged(c, fs, n)
        if 0 not in priv:
            continue
        succ = apply_move(c, 0, fs, n)
        dfc = frontier_count(succ, n) - frontier_count(c, n)
        if dfc != -1:
            continue
        if succ in bad_set:
            bad_to_bad_cases.append((c, succ, d, get_d_vector(succ, n)))

    print(f"\n  n={n}: BOT with c0=0,d0=1,dn1=1 (Δfc=-1) → bad: "
          f"{len(bad_to_bad_cases)} cases")
    for c, s, d, ds in bad_to_bad_cases[:5]:
        print(f"    {c} d={d} → {s} d={ds}")

    # Also check: bottom c_0=1, d_0=2, d_{n-1}=2 (Δfc=-1)
    bad_to_bad_2 = []
    for c in bad_set:
        d = get_d_vector(c, n)
        if c[0] != 1 or d[0] != 2 or d[n-1] != 2:
            continue
        priv = get_privileged(c, fs, n)
        if 0 not in priv:
            continue
        succ = apply_move(c, 0, fs, n)
        dfc = frontier_count(succ, n) - frontier_count(c, n)
        if succ in bad_set:
            bad_to_bad_2.append((c, succ, d, get_d_vector(succ, n), dfc))

    print(f"  n={n}: BOT with c0=1,d0=2,dn1=2 (Δfc=-1) → bad: "
          f"{len(bad_to_bad_2)} cases")
    for c, s, d, ds, dfc in bad_to_bad_2[:5]:
        print(f"    {c} d={d} → {s} d={ds} Δfc={dfc}")

    # Check ALL bottom bad→bad cases with Δfc=-1
    all_bot_m1 = []
    for c in bad_set:
        d = get_d_vector(c, n)
        priv = get_privileged(c, fs, n)
        if 0 not in priv:
            continue
        succ = apply_move(c, 0, fs, n)
        dfc = frontier_count(succ, n) - frontier_count(c, n)
        if dfc == -1 and succ in bad_set:
            all_bot_m1.append((c, succ, c[0], d[0], d[n-1]))

    print(f"  n={n}: ALL bottom bad→bad Δfc=-1: {len(all_bot_m1)} cases")
    by_type = defaultdict(int)
    for c, s, c0, d0, dn1 in all_bot_m1:
        by_type[(c0, d0, dn1)] += 1
    for key in sorted(by_type.keys()):
        print(f"    c0={key[0]} d0={key[1]} dn1={key[2]}: {by_type[key]}")


if __name__ == "__main__":
    print("=" * 60)
    print("VERIFY Φ = (n-1)·fc + Ψ + f(c_0, d_{n-1})")
    print("=" * 60)
    for nv in range(3, 10):
        verify_potential(nv, nv - 1)

    print("\n" + "=" * 60)
    print("DETAILED VIOLATION ANALYSIS")
    print("=" * 60)
    for nv in [4, 5, 6]:
        analyze_violations_detailed(nv, nv - 1)

    print("\n" + "=" * 60)
    print("EDGE CASE: Bottom Δfc=-1 bad→bad transitions")
    print("=" * 60)
    for nv in range(3, 10):
        try_adjusted_f(nv)

    print("\n" + "=" * 60)
    print("SEARCH FOR OPTIMAL W")
    print("=" * 60)
    for nv in [4, 5, 6, 7]:
        search_optimal_W(nv)
