#!/usr/bin/env python3
"""Attempt analytical convergence proof for CUP-2 universal rules.

Strategy: look for a layered convergence argument.
Layer 1: Value-2 count decreases (or stays same but something else decreases)
Layer 2: Once no 2's remain, the {0,1}-valued system converges quickly
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import Counter, defaultdict
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def count_2s(c, n):
    """Number of ternary processors with value 2."""
    return sum(1 for i in range(1, n - 1) if c[i] == 2)


def count_nonzero(c, n):
    return sum(1 for x in c if x > 0)


def main():
    print("CONVERGENCE ANALYSIS: VALUE-2 DRAINAGE")
    print("=" * 80)

    for nv in [5, 6, 7, 8, 9]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        if not result['valid']:
            continue
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Collect bad→bad transitions
        transitions = []
        for c in bad_set:
            for i in range(n):
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        transitions.append((c, succ, i))

        print(f"\nn={nv}: {len(bad_set)} bad, {len(transitions)} bad→bad transitions")

        # Test: does count_2s always decrease or stay same?
        two_increases = 0
        two_stays = 0
        two_decreases = 0
        for c, cp, mv in transitions:
            d = count_2s(cp, n) - count_2s(c, n)
            if d > 0:
                two_increases += 1
            elif d < 0:
                two_decreases += 1
            else:
                two_stays += 1

        print(f"  count_2s: increases={two_increases}, stays={two_stays}, decreases={two_decreases}")

        if two_increases > 0:
            # Show the increasing transitions
            print(f"  Transitions that INCREASE count_2s:")
            shown = 0
            for c, cp, mv in transitions:
                d = count_2s(cp, n) - count_2s(c, n)
                if d > 0 and shown < 5:
                    print(f"    {c} →[P{mv}]→ {cp}: 2s: {count_2s(c,n)}→{count_2s(cp,n)}")
                    shown += 1

        # For transitions with same count_2s, check total_sum
        same_2s_trans = [(c, cp, mv) for c, cp, mv in transitions
                         if count_2s(cp, n) == count_2s(c, n)]
        if same_2s_trans:
            sum_inc = sum(1 for c, cp, mv in same_2s_trans if sum(cp) > sum(c))
            sum_dec = sum(1 for c, cp, mv in same_2s_trans if sum(cp) < sum(c))
            sum_same = sum(1 for c, cp, mv in same_2s_trans if sum(cp) == sum(c))
            print(f"  Same-2s transitions ({len(same_2s_trans)}): "
                  f"sum↑={sum_inc}, sum=={sum_same}, sum↓={sum_dec}")

        # What about total_sum as primary, count_2s as secondary?
        print(f"\n  Testing (total_sum, count_2s) lex:")
        viol = 0
        for c, cp, mv in transitions:
            sc, scp = sum(c), sum(cp)
            tc, tcp = count_2s(c, n), count_2s(cp, n)
            if (sc, tc) <= (scp, tcp):
                viol += 1
        print(f"    violations: {viol} / {len(transitions)}")

        # What about treating the transitions by which TABLE is used?
        print(f"\n  By-table analysis of count_2s changes:")
        for tbl_name in ['bot', 'low', 'mid', 'high', 'top']:
            tbl_trans = []
            for c, cp, mv in transitions:
                if mv == 0 and tbl_name == 'bot':
                    tbl_trans.append((c, cp, mv))
                elif mv == 1 and tbl_name == 'low':
                    tbl_trans.append((c, cp, mv))
                elif 2 <= mv <= n - 3 and tbl_name == 'mid':
                    tbl_trans.append((c, cp, mv))
                elif mv == n - 2 and tbl_name == 'high':
                    tbl_trans.append((c, cp, mv))
                elif mv == n - 1 and tbl_name == 'top':
                    tbl_trans.append((c, cp, mv))

            if not tbl_trans:
                continue
            inc = sum(1 for c, cp, mv in tbl_trans if count_2s(cp, n) > count_2s(c, n))
            dec = sum(1 for c, cp, mv in tbl_trans if count_2s(cp, n) < count_2s(c, n))
            same = len(tbl_trans) - inc - dec
            print(f"    {tbl_name:>5}: total={len(tbl_trans)}, 2s↑={inc}, 2s=={same}, 2s↓={dec}")

    # Deeper: for T_mid, which entries create/destroy 2s?
    print("\n\nT_MID: 2-VALUE CREATION/DESTRUCTION")
    print("-" * 60)
    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = T_mid[(L, S, R)]
                if out != S:
                    old2 = (1 if S == 2 else 0)
                    new2 = (1 if out == 2 else 0)
                    change = new2 - old2
                    if change != 0:
                        print(f"  T_mid({L},{S},{R})={out}: 2-count change = {change:+d}")

    print("\nT_LOW: 2-VALUE CREATION/DESTRUCTION")
    for L in range(2):
        for S in range(3):
            for R in range(3):
                out = T_low[(L, S, R)]
                if out != S:
                    old2 = (1 if S == 2 else 0)
                    new2 = (1 if out == 2 else 0)
                    change = new2 - old2
                    if change != 0:
                        print(f"  T_low({L},{S},{R})={out}: 2-count change = {change:+d}")

    print("\nT_HIGH: 2-VALUE CREATION/DESTRUCTION")
    for L in range(3):
        for S in range(3):
            for R in range(2):
                out = T_high[(L, S, R)]
                if out != S:
                    old2 = (1 if S == 2 else 0)
                    new2 = (1 if out == 2 else 0)
                    change = new2 - old2
                    if change != 0:
                        print(f"  T_high({L},{S},{R})={out}: 2-count change = {change:+d}")

    # Test: binary-only subspace. What if all ternary procs are in {0,1}?
    print("\n\nBINARY-ONLY SUBSPACE ANALYSIS")
    print("-" * 60)
    for nv in [5, 6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']

        # Configs where all ternary procs ∈ {0,1}
        binary_configs = []
        for c in cartesian(*(range(m) for m in ms)):
            if all(c[i] <= 1 for i in range(1, n - 1)):
                binary_configs.append(c)

        binary_bad = [c for c in binary_configs if c not in good_set]
        binary_good = [c for c in binary_configs if c in good_set]

        # Check: do transitions from binary-bad stay in binary?
        escapes = 0  # transitions from binary to non-binary
        for c in binary_bad:
            for i in range(n):
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S and new_S == 2:
                    escapes += 1

        print(f"  n={nv}: binary_configs={len(binary_configs)}, "
              f"binary_bad={len(binary_bad)}, binary_good={len(binary_good)}, "
              f"escape_to_2={escapes}")

    # What entries in T_mid can produce value 2 from {0,1} inputs?
    print("\n  T_mid entries that produce 2 from {0,1} inputs:")
    for L in range(2):
        for S in range(2):
            for R in range(2):
                out = T_mid[(L, S, R)]
                if out == 2:
                    print(f"    T_mid({L},{S},{R}) = 2")

    print("\n  T_low entries that produce 2 from inputs with S∈{0,1}, L∈{0,1}, R∈{0,1}:")
    for L in range(2):
        for S in range(2):
            for R in range(2):
                out = T_low[(L, S, R)]
                if out == 2:
                    print(f"    T_low({L},{S},{R}) = 2")

    print("\n  T_high entries that produce 2 from inputs with S∈{0,1}, L∈{0,1}, R∈{0,1}:")
    for L in range(2):
        for S in range(2):
            for R in range(2):
                out = T_high[(L, S, R)]
                if out == 2:
                    print(f"    T_high({L},{S},{R}) = 2")


if __name__ == "__main__":
    main()
