#!/usr/bin/env python3
"""sol3_z3_search.py — Z3 search for self-stabilizing systems at product 8748.

Direct Sol 3 adaptation fails at 8748 = {2,2,3^7}. Use Z3 to search for
valid systems with constrained structure:

Approach: Each processor's rule f_i(L,S,R) is a Z3 integer variable.
Constraints encode all 5 Dijkstra properties.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

import z3
from itertools import product as cartesian
from verifier import verify_system
import time


def build_z3_system(ms, n, timeout_ms=60000):
    """Build and solve Z3 model for a self-stabilizing system.

    Variables: f[i][L][S][R] = new state for processor i given (L,S,R)
    Constraints:
    1. Range: 0 <= f[i][L][S][R] < m_i
    2. Find good configs forming a cycle with 1 privilege each
    3. No cycles among bad configs
    """
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    # Create rule variables
    f = {}
    for i in range(n):
        m_L = ms[(i-1) % n]
        m_S = ms[i]
        m_R = ms[(i+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    var = z3.Int(f'f_{i}_{L}_{S}_{R}')
                    f[(i, L, S, R)] = var
                    # Range constraint
                    solver.add(var >= 0, var < m_S)

    # This full encoding is too expensive for n=9 (8748 configs).
    # Instead, use a STRUCTURED approach:
    # Constrain the rule to follow Sol 3 pattern with parameters.
    return None  # Placeholder — use structured approach instead


def structured_z3_search(ms, n, timeout_ms=120000):
    """Structured Z3 search: each processor type uses a parameterized rule.

    For ternary procs (m_i=3), use Sol 3 rules with parameters:
      - bottom: f(L,S,R) = a if condition_b else S
      - middle: f(L,S,R) = ... with parameters for which comparisons
      - top: f(L,S,R) = ...

    For binary procs (m_i=2), parametrize as:
      f(L,S,R) = table[L][R] xor S  or similar small table

    Actually, for binary procs with L,R each up to 3 states:
      f_i has at most 3*2*3 = 18 entries (if both neighbors are ternary)
      or 2*2*3 = 12 entries (if one neighbor is binary)
    That's small enough to enumerate or Z3-parametrize.

    For ternary procs: 3*3*3 = 27 entries each. 7 ternary procs = 189 entries.
    Plus 2 binary procs with ~18 entries each = 36 entries.
    Total ~225 entries — each is a Z3 variable.

    But the convergence constraint (no cycles among 8730 bad configs) is the hard part.
    We can't enumerate all possible paths.

    Alternative: encode convergence as a ranking function.
    For each non-good config c, define rank(c) ∈ {1,...,N}.
    Constraint: for every non-good config c, every successor c' of c satisfies:
    - if c' is good: OK
    - if c' is non-good: rank(c') < rank(c)

    This ensures no cycles (a finite strictly decreasing sequence can't cycle).
    """
    t0 = time.time()

    solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    total_product = 1
    for m in ms:
        total_product *= m

    # Create rule variables
    f = {}
    for i in range(n):
        m_L = ms[(i-1) % n]
        m_S = ms[i]
        m_R = ms[(i+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    var = z3.Int(f'f_{i}_{L}_{S}_{R}')
                    f[(i, L, S, R)] = var
                    solver.add(var >= 0, var < m_S)

    all_configs = list(cartesian(*(range(m) for m in ms)))
    config_idx = {c: idx for idx, c in enumerate(all_configs)}

    # Privilege: f_i(L,S,R) != S means P_i is privileged
    def is_priv(c, i):
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        return f[(i, L, S, R)] != S

    def successor(c, i):
        """Return symbolic successor when P_i moves at config c."""
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        new_S = f[(i, L, S, R)]
        return new_S  # Only the state of proc i changes

    # Good/bad indicators
    is_good = {}
    for c in all_configs:
        is_good[c] = z3.Bool(f'good_{config_idx[c]}')

    # Constraint: good configs have exactly 1 privilege
    for c in all_configs:
        priv_count = z3.Sum([z3.If(is_priv(c, i), 1, 0) for i in range(n)])
        solver.add(z3.Implies(is_good[c], priv_count == 1))

    # Constraint: non-good configs have at least 1 privilege (liveness)
    for c in all_configs:
        priv_count = z3.Sum([z3.If(is_priv(c, i), 1, 0) for i in range(n)])
        solver.add(priv_count >= 1)

    # Constraint: good configs are closed under the transition
    # When the unique privileged proc moves, the result is also good
    for c in all_configs:
        for i in range(n):
            # If c is good and P_i is privileged (the unique one):
            is_c_good_i_priv = z3.And(is_good[c], f[(i, c[(i-1)%n], c[i], c[(i+1)%n])] != c[i])

            # Compute successor
            new_c = list(c)
            # new_c[i] = f[(i, ...)] — but this is symbolic!
            # We need to enumerate possible values
            for v in range(ms[i]):
                new_c_v = list(c)
                new_c_v[i] = v
                new_c_v = tuple(new_c_v)
                # If f = v and c is good and i is privileged:
                cond = z3.And(is_c_good_i_priv,
                             f[(i, c[(i-1)%n], c[i], c[(i+1)%n])] == v)
                solver.add(z3.Implies(cond, is_good[new_c_v]))

    # Constraint: at least one good config exists
    solver.add(z3.Or([is_good[c] for c in all_configs]))

    # Constraint: convergence — ranking function
    # For each config c, rank(c) is an integer
    rank = {}
    for c in all_configs:
        rank[c] = z3.Int(f'rank_{config_idx[c]}')
        solver.add(rank[c] >= 0)
        solver.add(rank[c] < total_product)
        # Good configs have rank 0
        solver.add(z3.Implies(is_good[c], rank[c] == 0))

    # For non-good configs: every possible move must decrease rank or reach good
    for c in all_configs:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            for v in range(ms[i]):
                new_c = list(c)
                new_c[i] = v
                new_c = tuple(new_c)
                # If c is non-good, and P_i is privileged (f != S), and f == v:
                cond = z3.And(
                    z3.Not(is_good[c]),
                    f[(i, L, S, R)] == v,
                    v != S  # P_i is privileged
                )
                # Then successor has lower rank (or is good)
                solver.add(z3.Implies(cond,
                    z3.Or(is_good[new_c], rank[new_c] < rank[c])))

    # Fairness: the good cycle visits all n processors
    # This is hard to encode directly. Skip for now — check post-hoc.

    print(f"  Z3 model built in {time.time()-t0:.1f}s")
    print(f"  Variables: {len(f)} rule + {len(is_good)} good + {len(rank)} rank")
    print(f"  Solving...")

    result = solver.check()
    elapsed = time.time() - t0
    print(f"  Result: {result} ({elapsed:.1f}s)")

    if result == z3.sat:
        model = solver.model()
        # Extract rule table
        rules = {}
        for key, var in f.items():
            rules[key] = model[var].as_long()

        # Extract good set
        good_set = set()
        for c, var in is_good.items():
            if z3.is_true(model[var]):
                good_set.add(c)

        print(f"  Good configs: {len(good_set)}")

        # Build rule functions and verify
        def make_fn(proc_i):
            def fn(L, S, R):
                return rules[(proc_i, L, S, R)]
            return fn

        fs = [make_fn(i) for i in range(n)]
        verification = verify_system(ms, fs)
        print(f"  Verification: {verification.get('valid', False)}")
        if verification.get('valid'):
            props = verification.get('properties', {})
            for k, v in props.items():
                print(f"    {k}: {v}")

        return rules, good_set, verification

    return None, None, None


def main():
    n = 9
    print("=" * 70)
    print("Z3 SEARCH FOR SELF-STABILIZING SYSTEM AT PRODUCT 8748")
    print("=" * 70)

    # The full Z3 encoding with 8748 configs is very expensive.
    # Let's first try smaller instances to validate the approach.

    # Test on n=5 first (known: M_5 = 96)
    print("\n--- Validation: n=5, ms=(2,2,2,3,4), product=96 ---")
    n_test = 5
    ms_test = [2, 2, 2, 3, 4]
    total = 1
    for m in ms_test:
        total *= m
    print(f"  Total configs: {total}")

    rules, good, ver = structured_z3_search(ms_test, n_test, timeout_ms=30000)

    if rules is None:
        print("  Z3 failed on n=5 validation — trying smaller timeout-friendly formulation")

    # Try n=5 with Sol 3 adaptation to validate
    print("\n--- Validation: Sol 3 at n=5, ms=(3,3,3,3,3) ---")
    ms_5 = [3, 3, 3, 3, 3]
    from sol3_adapt import sol3_original
    fs_5 = sol3_original(5, K=3)
    ver_5 = verify_system(ms_5, fs_5)
    print(f"  Valid: {ver_5.get('valid')}")

    # Now try the real target
    print("\n--- Target: n=9, ms=(2,2,3,3,3,3,3,3,3), product=8748 ---")
    ms_target = [2, 2, 3, 3, 3, 3, 3, 3, 3]
    total_target = 1
    for m in ms_target:
        total_target *= m
    print(f"  Total configs: {total_target}")
    print(f"  This will be very expensive. Trying with 120s timeout...")

    rules, good, ver = structured_z3_search(ms_target, 9, timeout_ms=120000)


if __name__ == "__main__":
    main()
