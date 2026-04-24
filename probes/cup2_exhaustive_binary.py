#!/usr/bin/env python3
"""Exhaustive search over P0 and P_{n-1} binary transition functions.

Fix Sol 3 middle rules for ternary processors P1..P_{n-2}.
Enumerate ALL binary transition functions for P0 and P_{n-1} that are
compatible with the bounce cycle's determined entries.
Test each combination for validity.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system


def make_middle(m_i):
    def f(L, S, R):
        if (S + 1) % m_i == L % m_i:
            return L % m_i
        if (S + 1) % m_i == R % m_i:
            return R % m_i
        return S
    return f


def build_bounce_cycle(ms, n):
    """Build bounce cycle: movers [0,1,...,n-1,n-2,...,1] repeating."""
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (3 * n)
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step + 1]
        if nc in visited:
            raise RuntimeError(f"Revisited {nc} at step {step}")
        visited.add(nc)
        cycle.append(nc)
    raise RuntimeError("Cycle didn't close")


def get_determined_entries(cycle, movers, ms, n):
    """Extract determined transition entries from the cycle."""
    det = {}  # (proc, L, S, R) -> output
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S  # non-mover stays
    return det


def enumerate_binary_fns(m_L, m_S, m_R, determined):
    """Enumerate all binary (m_S=2) functions compatible with determined entries.

    determined: dict of (L,S,R) -> output for this specific processor.
    Returns list of lookup tables (dict: (L,S,R) -> output).
    """
    # All input triples
    inputs = [(L, S, R) for L in range(m_L) for S in range(m_S) for R in range(m_R)]

    # Split into determined and free
    free_inputs = [t for t in inputs if t not in determined]

    # Each free input can take value 0 or 1 (binary)
    results = []
    for bits in cartesian(range(m_S), repeat=len(free_inputs)):
        table = dict(determined)
        for i, t in enumerate(free_inputs):
            table[t] = bits[i]
        results.append(table)

    return results


def table_to_fn(table):
    """Convert lookup table to function."""
    def f(L, S, R):
        return table[(L, S, R)]
    return f


def main():
    for nv in [5]:
        ms = [2] + [3] * (nv - 2) + [2]
        n = nv
        print(f"n={n}, ms={tuple(ms)}, product={4 * 3**(n-2)}")

        cycle, movers = build_bounce_cycle(ms, n)
        print(f"Bounce cycle length: {len(cycle)}")

        det = get_determined_entries(cycle, movers, ms, n)

        # Determined entries for P0
        det_p0 = {(L, S, R): v for (p, L, S, R), v in det.items() if p == 0}
        m_L0 = ms[n - 1]  # P0's left = P_{n-1} (binary)
        m_S0 = ms[0]       # P0 = binary
        m_R0 = ms[1]       # P0's right = P1 (ternary)
        total_p0 = m_L0 * m_S0 * m_R0
        free_p0 = total_p0 - len(det_p0)

        # Determined entries for P_{n-1}
        det_ptop = {(L, S, R): v for (p, L, S, R), v in det.items() if p == n - 1}
        m_Ltop = ms[n - 2]  # P_{n-1}'s left = P_{n-2} (ternary)
        m_Stop = ms[n - 1]  # P_{n-1} = binary
        m_Rtop = ms[0]      # P_{n-1}'s right = P0 (binary)
        total_ptop = m_Ltop * m_Stop * m_Rtop
        free_ptop = total_ptop - len(det_ptop)

        print(f"P0: {len(det_p0)}/{total_p0} determined, {free_p0} free → {2**free_p0} candidates")
        print(f"P{n-1}: {len(det_ptop)}/{total_ptop} determined, {free_ptop} free → {2**free_ptop} candidates")
        print(f"Total combinations: {2**free_p0 * 2**free_ptop}")

        # Print determined entries
        print(f"\nP0 determined: {det_p0}")
        print(f"P{n-1} determined: {det_ptop}")

        # Enumerate compatible functions
        p0_candidates = enumerate_binary_fns(m_L0, m_S0, m_R0, det_p0)
        ptop_candidates = enumerate_binary_fns(m_Ltop, m_Stop, m_Rtop, det_ptop)

        print(f"\nSearching {len(p0_candidates)} × {len(ptop_candidates)} = "
              f"{len(p0_candidates) * len(ptop_candidates)} combinations...")

        valid_count = 0
        tested = 0
        for p0_table in p0_candidates:
            for ptop_table in ptop_candidates:
                tested += 1
                if tested % 10000 == 0:
                    print(f"  tested {tested}...")

                # Build function list
                fs = [table_to_fn(p0_table)]
                for i in range(1, n - 1):
                    fs.append(make_middle(ms[i]))
                fs.append(table_to_fn(ptop_table))

                # Quick liveness check first
                configs = list(cartesian(*(range(m) for m in ms)))
                dead = False
                for c in configs:
                    has_priv = False
                    for i in range(n):
                        L = c[(i - 1) % n]
                        S = c[i]
                        R = c[(i + 1) % n]
                        if fs[i](L, S, R) != S:
                            has_priv = True
                            break
                    if not has_priv:
                        dead = True
                        break

                if dead:
                    continue

                # Full verification
                result = verify_system(ms, fs)
                if result['valid']:
                    valid_count += 1
                    gcnt = len(result.get('good_configs', set()))
                    clen = result.get('cycle_length', '?')
                    print(f"\n  VALID #{valid_count}: good={gcnt}, cycle_len={clen}")

                    # Print the binary rules
                    print(f"  P0 table:")
                    for L in range(m_L0):
                        for S in range(m_S0):
                            for R in range(m_R0):
                                out = p0_table[(L, S, R)]
                                priv = "←" if out != S else " "
                                det_mark = "D" if (L, S, R) in det_p0 else "F"
                                print(f"    f({L},{S},{R})={out} {priv} {det_mark}")

                    print(f"  P{n-1} table:")
                    for L in range(m_Ltop):
                        for S in range(m_Stop):
                            for R in range(m_Rtop):
                                out = ptop_table[(L, S, R)]
                                priv = "←" if out != S else " "
                                det_mark = "D" if (L, S, R) in det_ptop else "F"
                                print(f"    f({L},{S},{R})={out} {priv} {det_mark}")

                    if valid_count >= 20:
                        print("  (stopping after 20 valid)")
                        break
            if valid_count >= 20:
                break

        print(f"\nTotal: {valid_count} valid out of {tested} tested")


if __name__ == "__main__":
    main()
