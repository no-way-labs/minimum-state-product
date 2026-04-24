#!/usr/bin/env python3
"""Analyze the structure of the good config set.

Questions:
1. What do good configs look like? Is there a pattern?
2. How are bad configs distributed relative to good configs?
3. What's the "distance" from bad to good, and how does it decrease?
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import Counter, defaultdict
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def main():
    print("GOOD CONFIG STRUCTURE ANALYSIS")
    print("=" * 80)

    for nv in [5, 6, 7]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        cycle = result.get('cycle', [])

        print(f"\nn={nv}: {len(good_set)} good configs")

        # Print all good configs with their properties
        if nv <= 6:
            print("  Good configs:")
            for c in sorted(good_set):
                # Count frontiers
                front = sum(1 for i in range(n) if c[i] != c[(i + 1) % n])
                priv = []
                for i in range(n):
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    if fs[i](L, S, R) != S:
                        priv.append(i)
                print(f"    {c}  front={front} priv={priv}")

        # What values appear at each position?
        print(f"\n  Value distribution at each position:")
        for p in range(n):
            vals = Counter(c[p] for c in good_set)
            print(f"    P{p}: {dict(sorted(vals.items()))}")

        # Adjacent pairs in good configs
        print(f"\n  Adjacent pair distribution (P_i, P_{'{i+1}'}'):")
        for p in range(n):
            pairs = Counter((c[p], c[(p+1)%n]) for c in good_set)
            print(f"    P{p}-P{(p+1)%n}: {dict(sorted(pairs.items()))}")

    # Check: is the good set characterized by some local property?
    print("\n\nLOCAL CHARACTERIZATION OF GOOD SET")
    print("-" * 70)
    for nv in [5, 6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))

        # Check: how many configs have exactly 1 privilege?
        single_priv = set()
        for c in all_configs:
            privs = []
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                if fs[i](L, S, R) != S:
                    privs.append(i)
            if len(privs) == 1:
                single_priv.add(c)

        # Is good_set ⊂ single_priv?
        good_single = good_set & single_priv
        single_not_good = single_priv - good_set
        print(f"  n={nv}: good={len(good_set)}, single_priv={len(single_priv)}, "
              f"good∩single={len(good_single)}, single-good={len(single_not_good)}")

        # What are the single-priv configs NOT in good set?
        if nv <= 6 and single_not_good:
            print(f"    Single-priv but not good:")
            for c in sorted(single_not_good):
                privs = []
                for i in range(n):
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    if fs[i](L, S, R) != S:
                        privs.append(i)
                # What's the successor?
                p = privs[0]
                lst = list(c)
                lst[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                succ = tuple(lst)
                in_good = succ in good_set
                print(f"      {c} P{p} → {succ} {'(GOOD)' if in_good else '(BAD)'}")

    # The good set = cycle ∪ tails. Let's understand the tail structure.
    print("\n\nTAIL STRUCTURE")
    print("-" * 70)
    for nv in [5, 6, 7]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        cycle_configs = set()

        # Build successor map for good configs
        succ_map = {}
        for c in good_set:
            privs = []
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                if fs[i](L, S, R) != S:
                    privs.append(i)
            if len(privs) == 1:
                p = privs[0]
                lst = list(c)
                lst[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                succ_map[c] = tuple(lst)

        # Find the cycle by following successors
        start = tuple([0] * n)
        current = start
        cycle_list = []
        while True:
            cycle_list.append(current)
            cycle_configs.add(current)
            current = succ_map[current]
            if current == start:
                break

        tail_configs = good_set - cycle_configs
        print(f"\n  n={nv}: cycle={len(cycle_configs)}, tails={len(tail_configs)}")

        # For each tail config, trace to cycle
        if nv <= 6:
            tail_lengths = []
            for c in sorted(tail_configs):
                path = [c]
                cur = c
                while cur not in cycle_configs:
                    cur = succ_map[cur]
                    path.append(cur)
                tail_lengths.append(len(path) - 1)
                entry_point = cur
                entry_idx = cycle_list.index(entry_point)
                print(f"    {c} →{'→'.join(str(x) for x in path[1:])} "
                      f"(len={len(path)-1}, enters cycle at idx {entry_idx})")

            if tail_lengths:
                print(f"    Tail length distribution: {Counter(tail_lengths)}")


if __name__ == "__main__":
    main()
