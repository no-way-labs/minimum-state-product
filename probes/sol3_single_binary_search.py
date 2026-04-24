#!/usr/bin/env python3
"""sol3_single_binary_search.py — Search over one binary proc's rules at 8748.

Fix all ternary rules as Sol 3, fix one binary as Sol 3 v1 bottom,
exhaustively search the other binary proc's 12-18 entries.
Try all 9 rotations to vary binary proc separation.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

import time
from itertools import product as cartesian
from verifier import verify_system


def sol3_middle(L, S, R):
    if (S + 1) % 3 == L:
        return L
    if (S + 1) % 3 == R:
        return R
    return S


def sol3_top(L, S, R):
    if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
        return (L % 3 + 1) % 3
    return S


def sol3_bottom_m(m0):
    """Sol 3 v1 bottom for m-state proc."""
    def f(L, S, R):
        if (S + 1) % m0 == R % m0:
            return (S - 1) % m0
        return S
    return f


def sol3_middle_m(m_i):
    """Sol 3 v1 middle for m-state proc."""
    def f(L, S, R):
        if (S + 1) % m_i == L % m_i:
            return L % m_i
        if (S + 1) % m_i == R % m_i:
            return R % m_i
        return S
    return f


def sol3_top_m(m_top):
    """Sol 3 v1 top for m-state proc."""
    def f(L, S, R):
        if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
            return (L % m_top + 1) % m_top
        return S
    return f


def main():
    n = 9
    print("=" * 70)
    print("SINGLE BINARY PROC EXHAUSTIVE SEARCH AT PRODUCT 8748")
    print("=" * 70)

    ms_base = (2, 2, 3, 3, 3, 3, 3, 3, 3)

    # Try all rotations
    tested_rots = set()
    for rot in range(n):
        ms = tuple(ms_base[(i + rot) % n] for i in range(n))
        if ms in tested_rots:
            continue
        tested_rots.add(ms)

        bin_pos = [i for i in range(n) if ms[i] == 2]
        sep = min((bin_pos[1] - bin_pos[0]) % n, (bin_pos[0] - bin_pos[1]) % n)

        print(f"\n{'=' * 60}")
        print(f"ms={ms}, binary at {bin_pos}, sep={sep}")
        print(f"{'=' * 60}")

        ms_list = list(ms)

        # Build Sol 3 rules for all processors
        # P_0 is always "bottom", P_{n-1} is always "top"
        base_fs = []
        for i in range(n):
            if i == 0:
                base_fs.append(sol3_bottom_m(ms_list[i]))
            elif i == n - 1:
                base_fs.append(sol3_top_m(ms_list[i]))
            else:
                base_fs.append(sol3_middle_m(ms_list[i]))

        # For each binary processor position, try exhaustive search
        for bp in bin_pos:
            m_bp = ms_list[bp]
            assert m_bp == 2
            m_L = ms_list[(bp - 1) % n]
            m_R = ms_list[(bp + 1) % n]
            n_entries = m_L * m_bp * m_R

            entries = [(L, S, R) for L in range(m_L) for S in range(m_bp) for R in range(m_R)]
            entry_idx = {k: i for i, k in enumerate(entries)}

            role = "bottom" if bp == 0 else ("top" if bp == n-1 else "middle")
            print(f"\n  Searching P{bp} ({role}, m=2, {n_entries} entries)...")

            n_tested = 0
            n_valid = 0
            t0 = time.time()

            for mask in range(1 << n_entries):
                n_tested += 1

                # Build rule for this binary proc
                def make_fn(m, eidx, msk):
                    def fn(L, S, R):
                        idx = eidx[(L, S, R)]
                        if msk & (1 << idx):
                            return 1 - S  # privileged: toggle
                        return S  # not privileged
                    return fn

                # Replace the base rule for this proc
                fs = list(base_fs)
                fs[bp] = make_fn(m_bp, entry_idx, mask)

                result = verify_system(ms_list, fs)
                if result.get('valid', False):
                    n_valid += 1
                    elapsed = time.time() - t0
                    print(f"\n    *** VALID SYSTEM FOUND! (mask={bin(mask)}) ***")
                    print(f"    Tested {n_tested}/{1 << n_entries} in {elapsed:.1f}s")
                    props = result.get('properties', {})
                    for k, v in props.items():
                        print(f"      {k}: {v}")

                    # Show the rule
                    print(f"    Rule table for P{bp}:")
                    for L, S, R in entries:
                        val = fs[bp](L, S, R)
                        if val != S:
                            print(f"      f({L},{S},{R}) = {val} [PRIV]")

                    # Don't break — find all valid rules
                    if n_valid >= 3:
                        break

                if n_tested % 1000 == 0:
                    elapsed = time.time() - t0
                    print(f"    Tested {n_tested}/{1 << n_entries} ({elapsed:.1f}s)")

            elapsed = time.time() - t0
            print(f"    Done: {n_tested} tested, {n_valid} valid ({elapsed:.1f}s)")


if __name__ == "__main__":
    main()
