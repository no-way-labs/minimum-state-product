#!/usr/bin/env python3
"""Generalize CLB's construction to arbitrary n for ms=(2,3,...,3,2).

Build the bounce-cycle witness for each n, then examine the transition
tables looking for closed-form patterns.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system


def build_system_general(n):
    """CLB construction for arbitrary n with ms=(2,3,...,3,2)."""
    ms = tuple([2] + [3] * (n - 2) + [2])

    # Build bounce cycle
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (3 * n)
    movers = None
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            raise RuntimeError("Cycle didn't close")
        visited.add(nc)
        cycle.append(nc)

    if movers is None:
        raise RuntimeError("Cycle didn't close")

    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Extract determined entries
    det = {}
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
                det[key] = S

    # Find free entries
    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = float('inf')
        for out in range(ms[p]):
            ng = 0
            good_count = 0
            if out != S:
                for c in non_good:
                    if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                        new_c = tuple(c[j] if j != p else out for j in range(n))
                        if new_c in good_set:
                            good_count += 1
                        elif new_c in non_good_set:
                            ng += 1
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    # Liveness fix
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n)
        )
        if not has_priv:
            # Find cheapest entry to activate
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = sum(
                                1 for c2 in non_good
                                if c2[(p - 1) % n] == L2 and c2[p] == S2 and c2[(p + 1) % n] == R2
                                and tuple(c2[j] if j != p else out for j in range(n)) in non_good_set
                            )
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    # Build transition functions
    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    return ms, fs, comp, cycle, movers


def main():
    print("CLB construction for ms=(2,3,...,3,2)")
    print("=" * 80)

    for nv in range(4, 11):
        ms_tuple = tuple([2] + [3] * (nv - 2) + [2])
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            print(f"\nn={nv}: SKIP (prod={prod})")
            continue

        print(f"\nn={nv}, ms={ms_tuple}, prod={prod}")
        try:
            ms, fs, comp, cycle, movers = build_system_general(nv)
        except RuntimeError as e:
            print(f"  Error: {e}")
            continue

        result = verify_system(ms, fs)
        status = "VALID" if result['valid'] else "INVALID"
        if result['valid']:
            gcnt = len(result.get('good_configs', set()))
            clen = result.get('cycle_length', '?')
            print(f"  {status}: good={gcnt}, cycle_len={clen}")
        else:
            props = result.get('properties', {})
            failures = {k: v[1] for k, v in props.items() if not v[0]}
            print(f"  {status}: {failures}")

        # Print privileged entries for boundary procs
        n = nv
        print(f"  P0 (bottom binary) privileged entries:")
        m_L0 = ms[n - 1]
        m_S0 = ms[0]
        m_R0 = ms[1]
        for L in range(m_L0):
            for S in range(m_S0):
                for R in range(m_R0):
                    out = fs[0](L, S, R)
                    if out != S:
                        print(f"    f({L},{S},{R})={out}")

        print(f"  P{n-1} (top binary) privileged entries:")
        m_Ltop = ms[n - 2]
        m_Stop = ms[n - 1]
        m_Rtop = ms[0]
        for L in range(m_Ltop):
            for S in range(m_Stop):
                for R in range(m_Rtop):
                    out = fs[n - 1](L, S, R)
                    if out != S:
                        print(f"    f({L},{S},{R})={out}")

        # For P1 and P_{n-2} (ternary adjacent to binary), compare with Sol3
        for p_idx in [1, n - 2]:
            m_L = ms[(p_idx - 1) % n]
            m_S = ms[p_idx]
            m_R = ms[(p_idx + 1) % n]
            sol3_mismatches = 0
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        actual = fs[p_idx](L, S, R)
                        # Sol 3 middle
                        sol3 = S
                        if (S + 1) % 3 == L % 3:
                            sol3 = L % 3
                        elif (S + 1) % 3 == R % 3:
                            sol3 = R % 3
                        if actual != sol3:
                            sol3_mismatches += 1
            print(f"  P{p_idx} vs Sol3 middle: {sol3_mismatches} mismatches")

        # For interior middles, compare with Sol3
        if n > 4:
            p_idx = n // 2
            m_L = ms[(p_idx - 1) % n]
            m_S = ms[p_idx]
            m_R = ms[(p_idx + 1) % n]
            sol3_mismatches = 0
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        actual = fs[p_idx](L, S, R)
                        sol3 = S
                        if (S + 1) % 3 == L % 3:
                            sol3 = L % 3
                        elif (S + 1) % 3 == R % 3:
                            sol3 = R % 3
                        if actual != sol3:
                            sol3_mismatches += 1
            print(f"  P{p_idx} (interior middle) vs Sol3: {sol3_mismatches} mismatches")


if __name__ == "__main__":
    main()
