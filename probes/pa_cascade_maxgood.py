#!/usr/bin/env python3
"""Compute max good cycle length and check interior coupling."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from verifier import all_configs, privileged_set, verify_system
from cycle_first_search import witness_n7


def make_fs(tables):
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R): return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


def main():
    # Check n=7 valid system structure more carefully
    ms7, tables7 = witness_n7()
    n = len(ms7)
    fs = make_fs(tables7)
    result = verify_system(list(ms7), fs, verbose=False)
    good_set = result.get('good_configs', set())

    binary_procs = [p for p in range(n) if ms7[p] == 2]

    print(f"n=7 valid system: ms={ms7}")
    print(f"Binary: {binary_procs}")
    border = [(binary_procs[0] - 1) % n, (binary_procs[-1] + 1) % n]
    interior = [p for p in range(n) if p not in binary_procs and p not in border]
    print(f"Border: {border}")
    print(f"Interior: {interior}")
    print(f"Good cycle length: {len(good_set)}")

    # Count fires per proc in good cycle
    good_list = sorted(good_set)
    # Need to reconstruct the cycle order
    # Each good config has exactly one mover
    mover_map = {}
    for c in good_set:
        priv = privileged_set(c, fs, ms7)
        if len(priv) == 1:
            mover_map[c] = priv[0]

    fire_count = {}
    for c, p in mover_map.items():
        fire_count[p] = fire_count.get(p, 0) + 1

    print(f"\nFires per proc in good cycle:")
    for p in range(n):
        ctx_size = ms7[(p-1) % n] * ms7[p] * ms7[(p+1) % n]
        print(f"  P{p} (m={ms7[p]}): fires {fire_count.get(p,0)} times, "
              f"context size={ctx_size}")

    # Interior fires breakdown
    for p in interior:
        print(f"\n  Interior P{p} detailed:")
        for c in sorted(good_set):
            if mover_map.get(c) == p:
                L = c[(p-1)%n]
                S = c[p]
                R = c[(p+1)%n]
                bt = tuple(c[i] for i in binary_procs)
                print(f"    binary={bt}, ctx=({L},{S},{R})")

    # How many interior fires happen at binary=(1,1,1)?
    for bt_target in [(0,0,0), (1,1,1)]:
        count = 0
        for c in good_set:
            bt = tuple(c[i] for i in binary_procs)
            if bt == bt_target and mover_map.get(c) in interior:
                count += 1
        print(f"\n  Interior fires at binary={bt_target}: {count}")

    # Now compute max good cycle length at n=8
    ms8 = (2,2,2,3,3,3,3,4)
    n8 = 8
    print(f"\nn=8: ms={ms8}")
    print(f"Context sizes per proc:")
    for p in range(n8):
        ctx = ms8[(p-1)%n8] * ms8[p] * ms8[(p+1)%n8]
        print(f"  P{p}: {ctx}")

    # P1 fires exactly 2 (anti-diagonal)
    max_total = sum(ms8[(p-1)%n8] * ms8[p] * ms8[(p+1)%n8] for p in range(n8))
    print(f"Sum of context sizes: {max_total}")
    print(f"With P1 capped at 2: {max_total - 8 + 2}")

    # At binary=(1,1,1):
    # P3: ctx = (1, c3, c4): 3*3 = 9
    # P4: ctx = (c3, c4, c5): 3*3*3 = 27
    # P5: ctx = (c4, c5, c6): 3*3*3 = 27
    # P6: ctx = (c5, c6, c7): 3*3*4 = 36
    # P7: ctx = (c6, c7, 1): 3*4 = 12
    # Total non-binary contexts at (1,1,1): 9+27+27+36+12 = 111
    print(f"\nNon-binary contexts at (1,1,1): {9+27+27+36+12}")
    print(f"Non-binary configs at (1,1,1): 324")
    print(f"Ratio: {111/324:.1%}")


if __name__ == '__main__':
    main()
