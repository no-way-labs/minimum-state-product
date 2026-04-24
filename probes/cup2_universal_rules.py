#!/usr/bin/env python3
"""Define universal (n-independent) rules for ms=(2,3,...,3,2).

The transition rules are 5 fixed lookup tables that do NOT depend on n:
  T_bot:  P0 (binary, m_L=2, m_S=2, m_R=3) — 12 entries
  T_low:  P1 (ternary, m_L=2, m_S=3, m_R=3) — 18 entries
  T_mid:  P_i for 2 ≤ i ≤ n-3 (ternary, 3×3×3) — 27 entries
  T_high: P_{n-2} (ternary, m_L=3, m_S=3, m_R=2) — 18 entries
  T_top:  P_{n-1} (binary, m_L=3, m_S=2, m_R=2) — 12 entries

These are extracted from the greedy construction at n=8 (large enough for all types).
Valid for n ≥ 6 (n=5 has a 1-entry difference in T_mid; n=4 has no T_mid procs).
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque
from verifier import verify_system
import time

# Import the greedy builder to extract tables
from cup2_clb_general import build_system_general


def extract_universal_tables():
    """Extract the 5 universal lookup tables from the n=8 construction."""
    ms, fs, comp, cycle, movers = build_system_general(8)
    n = 8

    T_bot = {}   # P0: (L∈{0,1}, S∈{0,1}, R∈{0,1,2}) → output
    T_low = {}   # P1: (L∈{0,1}, S∈{0,1,2}, R∈{0,1,2}) → output
    T_mid = {}   # P_i interior: (L∈{0,1,2}, S∈{0,1,2}, R∈{0,1,2}) → output
    T_high = {}  # P_{n-2}: (L∈{0,1,2}, S∈{0,1,2}, R∈{0,1}) → output
    T_top = {}   # P_{n-1}: (L∈{0,1,2}, S∈{0,1}, R∈{0,1}) → output

    for L in range(2):
        for S in range(2):
            for R in range(3):
                T_bot[(L, S, R)] = fs[0](L, S, R)

    for L in range(2):
        for S in range(3):
            for R in range(3):
                T_low[(L, S, R)] = fs[1](L, S, R)

    p_mid = 4  # truly interior at n=8
    for L in range(3):
        for S in range(3):
            for R in range(3):
                T_mid[(L, S, R)] = fs[p_mid](L, S, R)

    for L in range(3):
        for S in range(3):
            for R in range(2):
                T_high[(L, S, R)] = fs[n - 2](L, S, R)

    for L in range(3):
        for S in range(2):
            for R in range(2):
                T_top[(L, S, R)] = fs[n - 1](L, S, R)

    return T_bot, T_low, T_mid, T_high, T_top


def build_universal_system(n, T_bot, T_low, T_mid, T_high, T_top):
    """Build transition functions from universal tables."""
    ms = [2] + [3] * (n - 2) + [2]

    def make_f(table):
        def f(L, S, R):
            return table[(L, S, R)]
        return f

    fs = [make_f(T_bot)]  # P0
    fs.append(make_f(T_low))  # P1
    for i in range(2, n - 2):
        fs.append(make_f(T_mid))  # interior
    fs.append(make_f(T_high))  # P_{n-2}
    fs.append(make_f(T_top))  # P_{n-1}

    return ms, fs


def liveness_fix(ms, fs, n):
    """Apply liveness fix: for dead configs, activate cheapest free entry."""
    all_configs = list(cartesian(*(range(m) for m in ms)))

    # Find dead configs
    dead = []
    for c in all_configs:
        has_priv = False
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            if fs[i](L, S, R) != S:
                has_priv = True
                break
        if not has_priv:
            dead.append(c)

    if not dead:
        return fs, 0

    # For each dead config, we need to modify one entry
    # Build mutable lookup tables
    tables = []
    for i in range(n):
        if i == 0:
            tables.append(dict(T_bot))
        elif i == 1:
            tables.append(dict(T_low))
        elif i < n - 2:
            tables.append(dict(T_mid))
        elif i == n - 2:
            tables.append(dict(T_high))
        else:
            tables.append(dict(T_top))

    good_set = set()  # We don't have the good cycle here; just fix liveness
    non_good_set = set(all_configs)  # approximate

    for c in dead:
        best_p = None
        best_cost = float('inf')
        best_out = None
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            for out in range(ms[p]):
                if out != S:
                    # Cost: number of configs sharing this (p,L,S,R) pattern that
                    # would gain a bad→bad edge
                    cost = sum(
                        1 for c2 in all_configs
                        if c2[(p - 1) % n] == L and c2[p] == S and c2[(p + 1) % n] == R
                        and c2 != c
                        and tuple(c2[j] if j != p else out for j in range(n)) not in good_set
                    )
                    if cost < best_cost:
                        best_cost = cost
                        best_p = p
                        best_out = out

        if best_p is not None:
            L = c[(best_p - 1) % n]
            S = c[best_p]
            R = c[(best_p + 1) % n]
            tables[best_p][(L, S, R)] = best_out

    # Rebuild fs from tables
    new_fs = []
    for i in range(n):
        tbl = tables[i]
        def make_f(t):
            def f(L, S, R):
                return t[(L, S, R)]
            return f
        new_fs.append(make_f(tbl))

    return new_fs, len(dead)


# Extract universal tables
T_bot, T_low, T_mid, T_high, T_top = extract_universal_tables()


def print_table(name, table, m_L, m_S, m_R):
    print(f"\n{name} ({m_L}×{m_S}×{m_R} = {m_L*m_S*m_R} entries):")
    priv = sum(1 for k, v in table.items() if v != k[1])
    print(f"  {priv} privileged entries")
    for L in range(m_L):
        for S in range(m_S):
            entries = []
            for R in range(m_R):
                out = table[(L, S, R)]
                mark = "*" if out != S else " "
                entries.append(f"f({L},{S},{R})={out}{mark}")
            print(f"  {' '.join(entries)}")


def main():
    print("UNIVERSAL TRANSITION RULES FOR ms=(2,3,...,3,2)")
    print("=" * 70)

    print_table("T_bot (P0, bottom binary)", T_bot, 2, 2, 3)
    print_table("T_low (P1, lower boundary ternary)", T_low, 2, 3, 3)
    print_table("T_mid (interior ternary)", T_mid, 3, 3, 3)
    print_table("T_high (P_{n-2}, upper boundary ternary)", T_high, 3, 3, 2)
    print_table("T_top (P_{n-1}, top binary)", T_top, 3, 2, 2)

    # Verify universal rules (without liveness fix) + greedy construction
    print("\n\nVERIFICATION WITH UNIVERSAL RULES")
    print("=" * 70)
    print(f"{'n':>3} {'dead':>5} {'valid_raw':>10} {'valid_fix':>10} {'good':>5} {'cyc':>4} {'t':>5}")
    print("-" * 70)

    for nv in range(6, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            print(f"{nv:>3} SKIP")
            continue

        t0 = time.time()
        ms, fs = build_universal_system(nv, T_bot, T_low, T_mid, T_high, T_top)

        # Count dead configs
        all_configs = list(cartesian(*(range(m) for m in ms)))
        dead_count = sum(1 for c in all_configs if not any(
            fs[i](c[(i-1)%nv], c[i], c[(i+1)%nv]) != c[i] for i in range(nv)))

        # Try raw verification
        result_raw = verify_system(ms, fs)
        raw_valid = result_raw['valid']

        # Now apply liveness fix using the greedy construction
        ms2, fs2, comp2, cycle2, movers2 = build_system_general(nv)
        result_fix = verify_system(ms2, fs2)
        fix_valid = result_fix['valid']
        n_good = len(result_fix.get('good_configs', set())) if fix_valid else '?'
        cyc_len = result_fix.get('cycle_length', '?') if fix_valid else '?'

        elapsed = time.time() - t0
        print(f"{nv:>3} {dead_count:>5} {'Y' if raw_valid else 'N':>10} "
              f"{'Y' if fix_valid else 'N':>10} {n_good:>5} {cyc_len:>4} {elapsed:>5.1f}")

    # Check: are universal rules identical to greedy for the non-dead-fix entries?
    print("\n\nCOMPARING UNIVERSAL vs GREEDY (non-liveness-fix entries)")
    print("-" * 60)
    for nv in [7, 8, 9, 10]:
        ms_u, fs_u = build_universal_system(nv, T_bot, T_low, T_mid, T_high, T_top)
        ms_g, fs_g, comp_g, _, _ = build_system_general(nv)
        n = nv
        diffs = 0
        for p in range(n):
            m_L = ms_g[(p - 1) % n]
            m_S = ms_g[p]
            m_R = ms_g[(p + 1) % n]
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        u = fs_u[p](L, S, R)
                        g = fs_g[p](L, S, R)
                        if u != g:
                            diffs += 1
        print(f"  n={nv}: {diffs} differences between universal and greedy")


if __name__ == "__main__":
    main()
