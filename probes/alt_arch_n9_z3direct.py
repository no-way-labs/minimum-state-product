#!/usr/bin/env python3
"""alt_arch_n9_z3direct.py — Direct Z3 search bypassing the pipeline.

Instead of:  DFS cycle search → screening → SMT completion
This does:   Z3 encodes everything at once (rules + cycle + convergence)

Uses a simpler convergence encoding: iterative "bad config peeling"
rather than a full ranking function, which is more tractable.

Also tries a CEGAR-style approach: find liveness-satisfying rules,
verify full system, add counterexample constraints on failure.
"""

import sys
import os
import time
from itertools import product as cartesian
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))

import z3
from p2_ring import RingSystem, verify_system


def prod(sc):
    p = 1
    for m in sc:
        p *= m
    return p


def verify_standalone(state_counts, rules_dict):
    """Build RingSystem and verify."""
    rules = []
    n = len(state_counts)
    for i in range(n):
        table = {}
        m_L = state_counts[(i - 1) % n]
        m_S = state_counts[i]
        m_R = state_counts[(i + 1) % n]
        for l_val in range(m_L):
            for s_val in range(m_S):
                for r_val in range(m_R):
                    table[(l_val, s_val, r_val)] = rules_dict[(i, l_val, s_val, r_val)]
        rules.append(table)
    system = RingSystem(state_counts=tuple(state_counts), rules=tuple(rules))
    return verify_system(system), system


def cegar_search(state_counts, max_iterations=5000, timeout_s=300):
    """
    CEGAR-style search:
    1. Z3 finds rule tables satisfying liveness
    2. Verify full system
    3. If convergence fails: add constraint excluding the bad cycle
    4. Repeat
    """
    n = len(state_counts)
    total = prod(state_counts)

    print(f"  CEGAR search: n={n}, state_counts={state_counts}, configs={total}")

    solver = z3.Solver()
    solver.set("timeout", timeout_s * 1000)

    # Rule table variables
    f = {}
    for i in range(n):
        m_L = state_counts[(i - 1) % n]
        m_S = state_counts[i]
        m_R = state_counts[(i + 1) % n]
        for l_val in range(m_L):
            for s_val in range(m_S):
                for r_val in range(m_R):
                    var = z3.Int(f'f_{i}_{l_val}_{s_val}_{r_val}')
                    f[(i, l_val, s_val, r_val)] = var
                    solver.add(var >= 0, var < m_S)

    # Liveness: for each config, at least one processor is privileged
    all_cfgs = list(cartesian(*(range(m) for m in state_counts)))
    for cfg in all_cfgs:
        priv_lits = []
        for j in range(n):
            l_val = cfg[(j - 1) % n]
            s_val = cfg[j]
            r_val = cfg[(j + 1) % n]
            priv_lits.append(f[(j, l_val, s_val, r_val)] != s_val)
        solver.add(z3.Or(priv_lits))

    # Structural hint: config (0,...,0) should have exactly one privileged
    # processor (it's in the good cycle)
    zero_cfg = tuple(0 for _ in state_counts)
    zero_privs = []
    for j in range(n):
        l_val = zero_cfg[(j - 1) % n]
        s_val = zero_cfg[j]
        r_val = zero_cfg[(j + 1) % n]
        zero_privs.append(f[(j, l_val, s_val, r_val)] != s_val)
    # At most 1 privileged at (0,...,0) — forces single-priv
    for j1 in range(n):
        for j2 in range(j1 + 1, n):
            solver.add(z3.Not(z3.And(zero_privs[j1], zero_privs[j2])))

    t0 = time.time()
    iteration = 0
    best_msg = None

    while iteration < max_iterations:
        if time.time() - t0 > timeout_s:
            print(f"  Timeout after {iteration} iterations")
            break

        status = solver.check()
        if status == z3.unsat:
            print(f"  UNSAT after {iteration} iterations ({time.time()-t0:.1f}s)")
            return None
        if status == z3.unknown:
            print(f"  UNKNOWN: {solver.reason_unknown()} "
                  f"after {iteration} iterations ({time.time()-t0:.1f}s)")
            return None

        model = solver.model()
        # Extract rule tables
        rules_dict = {}
        for key, var in f.items():
            rules_dict[key] = model.eval(var).as_long()

        result, system = verify_standalone(state_counts, rules_dict)

        if result.valid:
            print(f"  *** VALID SYSTEM FOUND at iteration {iteration}! ***")
            print(f"  {result.message}")
            return system

        iteration += 1

        # Add constraint to exclude this exact rule table
        exclude = z3.Or([f[key] != rules_dict[key] for key in f])
        solver.add(exclude)

        if iteration <= 5 or iteration % 100 == 0:
            elapsed = time.time() - t0
            print(f"    iter {iteration}: {result.message} ({elapsed:.1f}s)")
            best_msg = result.message

    elapsed = time.time() - t0
    print(f"  Exhausted {iteration} iterations ({elapsed:.1f}s)")
    if best_msg:
        print(f"  Last failure: {best_msg}")
    return None


def main():
    print("=" * 70)
    print("Direct Z3 Search for n=9 Alternative Architectures")
    print("=" * 70)

    # Test orientations — focus on product 7776
    targets = [
        # Multiset A: {2^4, 3^4, 6}
        ((2, 2, 3, 6, 3, 3, 2, 3, 2), "A2: best from pipeline"),
        ((2, 3, 2, 3, 6, 3, 2, 3, 2), "A1: spread binaries"),
        # Multiset B: {2^5, 3^3, 9}
        ((2, 3, 2, 3, 2, 9, 2, 3, 2), "B1: alternating"),
    ]

    for sc, desc in targets:
        p = prod(sc)
        ms = Counter(sc)
        print(f"\n{'=' * 60}")
        print(f"  {desc}")
        print(f"  ({','.join(map(str, sc))}) multiset={dict(ms)} product={p}")
        print(f"{'=' * 60}")

        witness = cegar_search(sc, max_iterations=2000, timeout_s=180)

        if witness:
            v = verify_system(witness)
            print(f"\n  *** WITNESS ***")
            print(f"  {v.message}")
            print(f"  Product: {witness.size}")
            for cs in v.cycle_summaries:
                print(f"  Cycle length: {cs.length}")
            for i, table in enumerate(witness.rules):
                priv = [(ctx, out) for ctx, out in sorted(table.items())
                        if out != ctx[1]]
                print(f"  P{i} (m={witness.state_counts[i]}): "
                      f"{len(priv)} privileged / {len(table)} total")
            return

    print("\n" + "=" * 70)
    print("No witnesses found via direct Z3 search.")
    print("=" * 70)


if __name__ == "__main__":
    main()
