#!/usr/bin/env python3
"""clb_convergence_proof.py — Find the convergence proof structure.

Key insight: for each table T and each (L,R), the function
  a -> T(L,a,R)
has NO 2-cycles. It converges to a fixed point in at most 2 iterations.

This means: if neighbors are fixed, each processor converges in ≤2 steps.
The question is whether this LOCAL contraction implies GLOBAL convergence.

Strategy:
1. Verify the "no 2-cycle" property for all tables
2. Compute the "target" for each (L,R) at each table
3. Define Φ(c) = number of positions at their local target
4. Test whether Φ is non-decreasing on bad→bad transitions
5. If not, find the right decomposition
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, Counter
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def get_table(p, n):
    if p == 0:
        return T_bot
    elif p == 1:
        return T_low
    elif p <= n - 3:
        return T_mid
    elif p == n - 2:
        return T_high
    else:
        return T_top


def fixed_point(table, L, R, m_S):
    """Find the fixed point(s) of a -> table(L,a,R)."""
    fps = []
    for a in range(m_S):
        if table[(L, a, R)] == a:
            fps.append(a)
    return fps


def target_value(table, L, S, R, m_S):
    """Find what value S converges to under repeated application of table with fixed L,R."""
    a = S
    for _ in range(3):
        a = table[(L, a, R)]
    return a


def main():
    # ================================================================
    # Part 1: Verify "no 2-cycle" property
    # ================================================================
    print("=" * 80)
    print("PART 1: FIXED-POINT CONTRACTION PROPERTY")
    print("=" * 80)

    tables = [
        ("T_bot", T_bot, 2, 2, 3),
        ("T_low", T_low, 2, 3, 3),
        ("T_mid", T_mid, 3, 3, 3),
        ("T_high", T_high, 3, 3, 2),
        ("T_top", T_top, 3, 2, 2),
    ]

    for name, table, m_L, m_S, m_R in tables:
        print(f"\n{name} (m_L={m_L}, m_S={m_S}, m_R={m_R}):")
        has_2cycle = False
        for L in range(m_L):
            for R in range(m_R):
                # Check if f_{L,R} has a 2-cycle
                for a in range(m_S):
                    b = table[(L, a, R)]
                    if b != a:
                        c = table[(L, b, R)]
                        if c == a:
                            print(f"  2-CYCLE at ({L},*,{R}): {a} -> {b} -> {a}")
                            has_2cycle = True

                # Show convergence behavior
                fps = fixed_point(table, L, R, m_S)
                orbits = []
                for a in range(m_S):
                    orbit = [a]
                    for _ in range(3):
                        orbit.append(table[(L, orbit[-1], R)])
                    orbits.append(orbit)

                # Determine convergence speed
                all_conv_1 = all(orbit[1] == orbit[2] for orbit in orbits)
                is_identity = all(orbit[0] == orbit[1] for orbit in orbits)

                if not is_identity:
                    conv = "1-step" if all_conv_1 else "2-step"
                    print(f"  ({L},*,{R}): fps={fps}, {conv}: "
                          + ", ".join(f"{o[0]}→{o[1]}→{o[2]}" for o in orbits if o[0] != o[1]))

        if not has_2cycle:
            print(f"  NO 2-CYCLES ✓")

    # ================================================================
    # Part 2: Target map analysis
    # ================================================================
    print(f"\n{'=' * 80}")
    print("PART 2: TARGET MAP — what does each position 'want' to be?")
    print("=" * 80)

    print("\nT_mid target values (most important — applies to n-4 positions):")
    print("  (L,R) → target(S=0), target(S=1), target(S=2)")
    for L in range(3):
        for R in range(3):
            targets = [target_value(T_mid, L, S, R, 3) for S in range(3)]
            if len(set(targets)) == 1:
                print(f"  ({L},{R}) → all→{targets[0]}  (constant)")
            else:
                changed = any(T_mid[(L, S, R)] != S for S in range(3))
                mark = " (has privilege)" if changed else " (identity)"
                print(f"  ({L},{R}) → {targets}{mark}")

    # ================================================================
    # Part 3: Test convergence measures
    # ================================================================
    print(f"\n{'=' * 80}")
    print("PART 3: CONVERGENCE MEASURE SEARCH")
    print("=" * 80)

    for nv in [5, 6, 7, 8]:
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

        print(f"\nn={nv}: {len(bad_set)} bad, {len(transitions)} bad→bad")

        # Measure 1: "at_target" — number of positions at their local target
        def at_target(c):
            count = 0
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                table = get_table(p, n)
                t = target_value(table, L, S, R, ms[p])
                if S == t:
                    count += 1
            return count

        # Measure 2: "sum_deviation" — sum of |S - target|
        def sum_deviation(c):
            dev = 0
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                table = get_table(p, n)
                t = target_value(table, L, S, R, ms[p])
                dev += abs(S - t)
            return dev

        # Measure 3: "privilege_count" — number of privileged processors
        def priv_count(c):
            cnt = 0
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                if fs[p](L, S, R) != S:
                    cnt += 1
            return cnt

        # Measure 4: "on_target_excl_mover" — at_target but excluding the mover's neighbors
        # When we fire position i, positions i-1 and i+1 might change targets
        # This counts how many non-affected positions are at target

        # Measure 5: combined (priv_count, -at_target)
        # If priv_count decreases, good. If same, at_target should increase.

        # Test all measures
        measures = [
            ("at_target ↑", at_target, False),  # should increase
            ("-sum_dev ↑", lambda c: -sum_deviation(c), False),
            ("priv_count ↓", priv_count, True),   # should decrease
        ]

        for mname, mfn, want_decrease in measures:
            viol = 0
            for c, cp, mv in transitions:
                mc, mcp = mfn(c), mfn(cp)
                if want_decrease:
                    if mcp >= mc:
                        viol += 1
                else:
                    if mcp <= mc:
                        viol += 1
            pct = 100 * viol / len(transitions) if transitions else 0
            status = "PERFECT" if viol == 0 else f"{viol} ({pct:.1f}%)"
            print(f"  {mname:>20}: violations = {status}")

        # Test lexicographic: (priv_count ↓, at_target ↑)
        viol = 0
        for c, cp, mv in transitions:
            pc, pcp = priv_count(c), priv_count(cp)
            ac, acp = at_target(c), at_target(cp)
            if (pc, -ac) <= (pcp, -acp):  # want (pc, -ac) to strictly decrease
                viol += 1
        pct = 100 * viol / len(transitions) if transitions else 0
        print(f"  {'lex(priv↓, target↑)':>20}: violations = "
              f"{'PERFECT' if viol == 0 else f'{viol} ({pct:.1f}%)'}")

        # Test: (at_target ↑, -priv_count ↑)
        viol = 0
        for c, cp, mv in transitions:
            ac, acp = at_target(c), at_target(cp)
            pc, pcp = priv_count(c), priv_count(cp)
            if (-ac, pc) >= (-acp, pcp):
                viol += 1
        pct = 100 * viol / len(transitions) if transitions else 0
        print(f"  {'lex(target↑, priv↓)':>20}: violations = "
              f"{'PERFECT' if viol == 0 else f'{viol} ({pct:.1f}%)'}")

    # ================================================================
    # Part 4: Analyze what happens at transitions in detail
    # ================================================================
    print(f"\n{'=' * 80}")
    print("PART 4: TRANSITION DETAIL ANALYSIS (n=6)")
    print("=" * 80)

    nv = 6
    ms, fs = build_system(nv)
    n = nv
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

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

    # For each transition, compute: which positions changed target? which moved on/off target?
    target_gained = Counter()  # (table, position_relative) → count of positions that gained target
    target_lost = Counter()

    for c, cp, mv in transitions:
        for p in range(n):
            L_old = c[(p - 1) % n]
            S_old = c[p]
            R_old = c[(p + 1) % n]
            table = get_table(p, n)
            t_old = target_value(table, L_old, S_old, R_old, ms[p])
            was_on = (S_old == t_old)

            L_new = cp[(p - 1) % n]
            S_new = cp[p]
            R_new = cp[(p + 1) % n]
            t_new = target_value(table, L_new, S_new, R_new, ms[p])
            now_on = (S_new == t_new)

            rel = "mover" if p == mv else "left" if p == (mv + 1) % n else "right" if p == (mv - 1) % n else "far"

            if not was_on and now_on:
                target_gained[rel] += 1
            elif was_on and not now_on:
                target_lost[rel] += 1

    print(f"\nTarget gain/loss by position relative to mover:")
    for rel in ['mover', 'left', 'right', 'far']:
        g = target_gained.get(rel, 0)
        l = target_lost.get(rel, 0)
        print(f"  {rel:>6}: gained={g}, lost={l}, net={g-l}")

    # ================================================================
    # Part 5: Cycle impossibility argument
    # ================================================================
    print(f"\n{'=' * 80}")
    print("PART 5: CYCLE STRUCTURE CONSTRAINTS")
    print("=" * 80)

    # For each table entry that fires in a bad→bad transition,
    # what VALUE CHANGE does it make? And what NEIGHBOR CONDITIONS does it require?
    print("\nValue changes in bad→bad transitions:")
    change_counts = Counter()
    change_neighbor_conditions = defaultdict(list)

    for c, cp, mv in transitions:
        old_S = c[mv]
        new_S = cp[mv]
        L = c[(mv - 1) % n]
        R = c[(mv + 1) % n]

        tbl = "bot" if mv == 0 else "low" if mv == 1 else \
              "mid" if mv < n - 2 else "high" if mv == n - 2 else "top"

        change = (tbl, old_S, new_S)
        change_counts[change] += 1
        change_neighbor_conditions[change].append((L, R))

    for key in sorted(change_counts.keys()):
        tbl, old_S, new_S = key
        conds = change_neighbor_conditions[key]
        lr_dist = Counter(conds)
        top_conds = lr_dist.most_common(3)
        cond_str = ", ".join(f"(L={l},R={r})x{cnt}" for (l, r), cnt in top_conds)
        print(f"  {tbl:>4} {old_S}→{new_S}: {change_counts[key]:>5}x  conditions: {cond_str}")

    # Key analysis: for T_mid transitions, can we have a cyclic chain?
    # A -> B -> C -> A where A,B,C are value changes at a single position
    print("\nT_mid value transitions (which transitions are possible?):")
    mid_transitions = set()
    for (L, S, R), out in T_mid.items():
        if out != S:
            mid_transitions.add((S, out))
    print(f"  Possible changes: {sorted(mid_transitions)}")

    # Check: for each (old→new) change, what must L be?
    print("\nT_mid: required L for each value change:")
    for old_S in range(3):
        for new_S in range(3):
            if old_S == new_S:
                continue
            L_values = set()
            for L in range(3):
                for R in range(3):
                    if T_mid[(L, old_S, R)] == new_S:
                        L_values.add(L)
            if L_values:
                R_values = set()
                for L in L_values:
                    for R in range(3):
                        if T_mid[(L, old_S, R)] == new_S:
                            R_values.add(R)
                print(f"  {old_S}→{new_S}: requires L∈{sorted(L_values)}, R∈{sorted(R_values)}")

    # ================================================================
    # Part 6: The "directional flow" analysis
    # ================================================================
    print(f"\n{'=' * 80}")
    print("PART 6: DIRECTIONAL FLOW ANALYSIS")
    print("=" * 80)

    # For T_mid, the target depends on (L,R). Let's see which direction
    # information flows: does the target depend more on L or R?
    print("\nT_mid target dependency:")
    print("  Which values of (L,R) have target = L?")
    for L in range(3):
        for R in range(3):
            targets = set(target_value(T_mid, L, S, R, 3) for S in range(3))
            if len(targets) == 1:
                t = targets.pop()
                dep = ""
                if t == L:
                    dep = "= L"
                elif t == R:
                    dep = "= R"
                print(f"    ({L},{R}): target={t} {dep}")
            else:
                # Multiple targets depending on S
                ts = [target_value(T_mid, L, S, R, 3) for S in range(3)]
                print(f"    ({L},{R}): target depends on S: {ts}")

    # ================================================================
    # Part 7: Attempt a decomposition argument
    # ================================================================
    print(f"\n{'=' * 80}")
    print("PART 7: DECOMPOSITION ATTEMPT — 'fc-like' measure")
    print("=" * 80)

    # Define: for a config c, the "left agreement" = longest prefix from P0
    # where c[p] matches the "target cascade" starting from P0.
    #
    # The idea: P0's value determines P1's target, which determines P2's target, etc.
    # If the config agrees with this cascade from the left, it's "well-formed."

    for nv in [5, 6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        if not result['valid']:
            continue
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

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

        # Define left_agreement(c): longest prefix where c[p] = target(c[p-1], c[p+1])
        def left_agreement(c):
            # Count how many positions from left are "at target" given their left neighbor
            count = 0
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                table = get_table(p, n)
                t = target_value(table, L, S, R, ms[p])
                if S == t:
                    count += 1
                else:
                    break
            return count

        # Define cascade_agreement: compute target starting from P0's actual value
        def cascade_target(c):
            """Compute the target cascade: what would positions want to be,
            given the actual values of their neighbors?"""
            targets = list(c)  # start with actual
            for p in range(n):
                L = targets[(p - 1) % n]
                R = c[(p + 1) % n]  # use ACTUAL right neighbor
                table = get_table(p, n)
                targets[p] = target_value(table, L, c[p], R, ms[p])
            return tuple(targets)

        def cascade_match(c):
            """How many positions match their cascade target?"""
            ct = cascade_target(c)
            return sum(1 for p in range(n) if c[p] == ct[p])

        # Test measures
        for mname, mfn in [
            ("left_agreement", left_agreement),
            ("cascade_match", cascade_match),
        ]:
            viol_dec = 0  # violations where measure decreases
            viol_same = 0  # where measure stays same
            for c, cp, mv in transitions:
                mc, mcp = mfn(c), mfn(cp)
                if mcp < mc:
                    viol_dec += 1
                elif mcp == mc:
                    viol_same += 1
            total = len(transitions)
            inc = total - viol_dec - viol_same
            print(f"  n={nv} {mname}: ↑={inc} ={viol_same} ↓={viol_dec} "
                  f"(↓ violations = {100*viol_dec/total:.1f}%)")

    # ================================================================
    # Part 8: The key observation — what makes cycles impossible?
    # ================================================================
    print(f"\n{'=' * 80}")
    print("PART 8: DIRECT CYCLE IMPOSSIBILITY ANALYSIS")
    print("=" * 80)

    # For a hypothetical cycle, every position must return to its value.
    # For ternary: need net change ≡ 0 mod 3, so ≥3 changes (or 0).
    # For binary: need net change ≡ 0 mod 2, so ≥2 changes (or 0).
    #
    # Key: for T_mid, 0→1 requires L=1.
    # So if mid-proc p goes 0→1, its left neighbor must be 1.
    # This creates a CHAIN: to have L=1 at time of the transition,
    # the left neighbor must have been SET to 1 earlier.

    # Let's verify: in bad→bad transitions at T_mid,
    # the change 0→1 ALWAYS requires L=1 (not just sometimes)
    print("\nT_mid change 0→1 — required neighbor values:")
    for L in range(3):
        for R in range(3):
            if T_mid[(L, 0, R)] == 1:
                print(f"  T_mid({L},0,{R})=1")

    print("\nT_mid change 1→2 — required neighbor values:")
    for L in range(3):
        for R in range(3):
            if T_mid[(L, 1, R)] == 2:
                print(f"  T_mid({L},1,{R})=2")

    print("\nT_mid change 2→0 — required neighbor values:")
    for L in range(3):
        for R in range(3):
            if T_mid[(L, 2, R)] == 0:
                print(f"  T_mid({L},2,{R})=0")

    print("\nT_mid change 1→0 — required neighbor values:")
    for L in range(3):
        for R in range(3):
            if T_mid[(L, 1, R)] == 0:
                print(f"  T_mid({L},1,{R})=0")

    print("\nT_mid change 0→2 — required neighbor values:")
    for L in range(3):
        for R in range(3):
            if T_mid[(L, 0, R)] == 2:
                print(f"  T_mid({L},0,{R})=2")

    print("\nT_mid change 2→1 — required neighbor values:")
    for L in range(3):
        for R in range(3):
            if T_mid[(L, 2, R)] == 1:
                print(f"  T_mid({L},2,{R})=1")


if __name__ == "__main__":
    main()
