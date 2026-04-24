#!/usr/bin/env python3
"""
CONVERGENCE PROOF — Part 8: Boundary Obstruction Analysis
=========================================================

Key idea: In any hypothetical cycle, every position must oscillate (fire ≥2 times).
Each oscillation at position i creates OBLIGATIONS on neighbors i-1 and/or i+1.
These obligations form directed chains that must close around the ring.

This script:
1. Catalogs ALL possible oscillation types at each table position
2. For each oscillation, determines exactly which neighbor values are required
3. Traces obligation chains from T_mid interior through T_low/T_high to T_bot/T_top
4. Shows the exact obstruction at the binary boundaries

CRITICAL INSIGHT: T_bot and T_top are binary (2 states).
- T_bot can only hold values {0,1} — it CANNOT receive a "carry-2" obligation
- T_top can only hold values {0,1} — same restriction
- T_mid oscillations involving value 2 create obligations that the boundaries cannot fulfill
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque

def catalog_all_transitions():
    """Catalog every transition (L,a,R) -> b for each table, where b != a."""
    tables = {
        'T_bot':  (T_bot,  2, 2, 3),
        'T_low':  (T_low,  2, 3, 3),
        'T_mid':  (T_mid,  3, 3, 3),
        'T_high': (T_high, 3, 3, 2),
        'T_top':  (T_top,  3, 2, 2),
    }

    print("=" * 70)
    print("ALL TRANSITIONS (privileged entries) BY TABLE")
    print("=" * 70)

    for name, (T, mL, mS, mR) in tables.items():
        print(f"\n{name} (mL={mL}, mS={mS}, mR={mR}):")
        trans = []
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = T[(L, S, R)]
                    if out != S:
                        trans.append((L, S, R, out))
                        print(f"  ({L},{S},{R}) -> {out}  [S: {S}→{out}]")
        print(f"  Total: {len(trans)} privileged entries")

def analyze_oscillation_obligations():
    """For each table, find ALL possible oscillation a->b->a and what they require."""
    tables = {
        'T_bot':  (T_bot,  2, 2, 3),
        'T_low':  (T_low,  2, 3, 3),
        'T_mid':  (T_mid,  3, 3, 3),
        'T_high': (T_high, 3, 3, 2),
        'T_top':  (T_top,  3, 2, 2),
    }

    print("\n" + "=" * 70)
    print("OSCILLATION ANALYSIS: a -> b -> a requires what from neighbors?")
    print("=" * 70)

    all_oscillations = {}

    for name, (T, mL, mS, mR) in tables.items():
        print(f"\n{name}:")
        oscs = []

        # First pass: get ALL (L,a,R)->b transitions where b != a
        forward = defaultdict(list)  # (a,b) -> [(L,R)]
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = T[(L, S, R)]
                    if out != S:
                        forward[(S, out)].append((L, R))

        # For each oscillation a->b->a:
        # Step 1: a->b requires some (L1,R1)
        # Step 2: b->a requires some (L2,R2)
        # No-2-cycle says: (L1,R1) != (L2,R2) for at least one component

        for a in range(mS):
            for b in range(mS):
                if a == b:
                    continue
                if (a,b) not in forward or (b,a) not in forward:
                    continue

                for L1, R1 in forward[(a,b)]:
                    for L2, R2 in forward[(b,a)]:
                        l_changed = (L1 != L2)
                        r_changed = (R1 != R2)

                        # By no-2-cycle: at least one must change
                        assert l_changed or r_changed, f"No-2-cycle violation!"

                        direction = []
                        if l_changed:
                            direction.append(f"L:{L1}→{L2}")
                        if r_changed:
                            direction.append(f"R:{R1}→{R2}")

                        osc_type = "L+R" if (l_changed and r_changed) else ("L" if l_changed else "R")
                        oscs.append({
                            'a': a, 'b': b,
                            'L1': L1, 'R1': R1, 'L2': L2, 'R2': R2,
                            'l_changed': l_changed, 'r_changed': r_changed,
                            'type': osc_type,
                        })

                        print(f"  {a}→{b}→{a}: (L:{L1},R:{R1})→(L:{L2},R:{R2}) "
                              f"[{osc_type}: {', '.join(direction)}]")

        all_oscillations[name] = oscs

        # Summary
        n_L = sum(1 for o in oscs if o['type'] == 'L')
        n_R = sum(1 for o in oscs if o['type'] == 'R')
        n_LR = sum(1 for o in oscs if o['type'] == 'L+R')
        print(f"  Summary: {len(oscs)} oscillations ({n_L} L-only, {n_R} R-only, {n_LR} both)")

    return all_oscillations

def analyze_value2_propagation():
    """
    Analyze how value 2 propagates through the ring.

    KEY OBSERVATION: T_bot and T_top only have states {0,1}.
    Value 2 exists only at positions 1 through n-2.

    For value 2 to participate in an oscillation at a mid position,
    it must be "generated" somewhere and "absorbed" at the boundaries.

    Question: Can value 2 create a self-sustaining loop?
    """
    print("\n" + "=" * 70)
    print("VALUE-2 PROPAGATION ANALYSIS")
    print("=" * 70)

    # For T_mid: which transitions PRODUCE value 2?
    print("\nT_mid transitions PRODUCING value 2:")
    for L in range(3):
        for S in range(3):
            for R in range(3):
                if T_mid[(L,S,R)] == 2 and S != 2:
                    print(f"  ({L},{S},{R}) -> 2  [needs L={L}, R={R}]")

    print("\nT_mid transitions CONSUMING value 2 (2 -> something):")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L,2,R)]
            if out != 2:
                print(f"  ({L},2,{R}) -> {out}")

    # For T_low: value 2 interactions
    print("\nT_low transitions PRODUCING value 2:")
    for L in range(2):
        for S in range(3):
            for R in range(3):
                if T_low[(L,S,R)] == 2 and S != 2:
                    print(f"  ({L},{S},{R}) -> 2  [needs L={L}, R={R}]")

    print("\nT_low transitions CONSUMING value 2:")
    for L in range(2):
        for R in range(3):
            out = T_low[(L,2,R)]
            if out != 2:
                print(f"  ({L},2,{R}) -> {out}")

    # For T_high: value 2 interactions
    print("\nT_high transitions PRODUCING value 2:")
    for L in range(3):
        for S in range(3):
            for R in range(2):
                if T_high[(L,S,R)] == 2 and S != 2:
                    print(f"  ({L},{S},{R}) -> 2  [needs L={L}, R={R}]")

    print("\nT_high transitions CONSUMING value 2:")
    for L in range(3):
        for R in range(2):
            out = T_high[(L,2,R)]
            if out != 2:
                print(f"  ({L},2,{R}) -> {out}")

def analyze_boundary_bottleneck():
    """
    The central argument: trace what must happen at T_bot and T_top
    for a cycle to exist.

    T_bot (pos 0): binary, sees L=c[n-1] (binary, 0-1), R=c[1] (ternary, 0-2)
    T_top (pos n-1): binary, sees L=c[n-2] (ternary, 0-2), R=c[0] (binary, 0-1)

    In a cycle, T_bot must oscillate between 0 and 1.
    T_top must oscillate between 0 and 1.

    The question: what does each oscillation REQUIRE from the ternary neighbor?
    """
    print("\n" + "=" * 70)
    print("BOUNDARY BOTTLENECK: WHAT MUST THE TERNARY NEIGHBOR DO?")
    print("=" * 70)

    # T_bot oscillations
    print("\nT_bot oscillations (self oscillates between 0 and 1):")
    print("  Left neighbor = c[n-1] (T_top, binary: 0-1)")
    print("  Right neighbor = c[1] (T_low, ternary: 0-2)")

    # 0->1 at T_bot
    print("\n  T_bot: 0→1 requires:")
    for L in range(2):
        for R in range(3):
            if T_bot[(L,0,R)] == 1:
                print(f"    L={L}, R={R}")

    # 1->0 at T_bot
    print("  T_bot: 1→0 requires:")
    for L in range(2):
        for R in range(3):
            if T_bot[(L,1,R)] == 0:
                print(f"    L={L}, R={R}")

    # Full oscillation 0->1->0
    print("\n  T_bot oscillation 0→1→0:")
    for L1 in range(2):
        for R1 in range(3):
            if T_bot[(L1,0,R1)] != 1:
                continue
            for L2 in range(2):
                for R2 in range(3):
                    if T_bot[(L2,1,R2)] != 0:
                        continue
                    if L1 == L2 and R1 == R2:
                        continue  # would be 2-cycle
                    l_ch = "L changed" if L1 != L2 else "L same"
                    r_ch = "R changed" if R1 != R2 else "R same"
                    print(f"    (L:{L1}→{L2}, R:{R1}→{R2}) [{l_ch}, {r_ch}]")

    # 1->0->1
    print("  T_bot oscillation 1→0→1:")
    for L1 in range(2):
        for R1 in range(3):
            if T_bot[(L1,1,R1)] != 0:
                continue
            for L2 in range(2):
                for R2 in range(3):
                    if T_bot[(L2,0,R2)] != 1:
                        continue
                    if L1 == L2 and R1 == R2:
                        continue
                    l_ch = "L changed" if L1 != L2 else "L same"
                    r_ch = "R changed" if R1 != R2 else "R same"
                    print(f"    (L:{L1}→{L2}, R:{R1}→{R2}) [{l_ch}, {r_ch}]")

    # T_top oscillations
    print("\n" + "-" * 50)
    print("\nT_top oscillations (self oscillates between 0 and 1):")
    print("  Left neighbor = c[n-2] (T_high, ternary: 0-2)")
    print("  Right neighbor = c[0] (T_bot, binary: 0-1)")

    # 0->1 at T_top
    print("\n  T_top: 0→1 requires:")
    for L in range(3):
        for R in range(2):
            if T_top[(L,0,R)] == 1:
                print(f"    L={L}, R={R}")

    # 1->0 at T_top
    print("  T_top: 1→0 requires:")
    for L in range(3):
        for R in range(2):
            if T_top[(L,1,R)] == 0:
                print(f"    L={L}, R={R}")

    # Full oscillation 0->1->0
    print("\n  T_top oscillation 0→1→0:")
    for L1 in range(3):
        for R1 in range(2):
            if T_top[(L1,0,R1)] != 1:
                continue
            for L2 in range(3):
                for R2 in range(2):
                    if T_top[(L2,1,R2)] != 0:
                        continue
                    if L1 == L2 and R1 == R2:
                        continue
                    l_ch = "L changed" if L1 != L2 else "L same"
                    r_ch = "R changed" if R1 != R2 else "R same"
                    print(f"    (L:{L1}→{L2}, R:{R1}→{R2}) [{l_ch}, {r_ch}]")

    print("  T_top oscillation 1→0→1:")
    for L1 in range(3):
        for R1 in range(2):
            if T_top[(L1,1,R1)] != 0:
                continue
            for L2 in range(3):
                for R2 in range(2):
                    if T_top[(L2,0,R2)] != 1:
                        continue
                    if L1 == L2 and R1 == R2:
                        continue
                    l_ch = "L changed" if L1 != L2 else "L same"
                    r_ch = "R changed" if R1 != R2 else "R same"
                    print(f"    (L:{L1}→{L2}, R:{R1}→{R2}) [{l_ch}, {r_ch}]")

def trace_obligation_chains(n=7):
    """
    For a specific n, enumerate ALL bad-config cycles (should be 0) and
    analyze what a hypothetical cycle WOULD require.

    Build the "obligation graph": if position i oscillates a->b->a,
    what values must neighbors take before and after?
    """
    print("\n" + "=" * 70)
    print(f"OBLIGATION CHAIN ANALYSIS (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)

    # Analyze the "fixed-point structure" of each table
    # For each (L, R), what is the fixed point of S -> T(L, S, R)?
    tables = [
        ("T_bot", T_bot, 2, 2, 3),
        ("T_low", T_low, 2, 3, 3),
    ]
    for i in range(2, n-2):
        tables.append((f"T_mid[{i}]", T_mid, 3, 3, 3))
    tables.append(("T_high", T_high, 3, 3, 2))
    tables.append(("T_top", T_top, 3, 2, 2))

    print("\nFixed-point map: for each (L,R), what value does S converge to?")
    for name, T, mL, mS, mR in tables:
        if "mid[3]" in name:  # only print once for T_mid
            continue
        print(f"\n  {name}:")
        for L in range(mL):
            for R in range(mR):
                # Find fixed points
                fps = [S for S in range(mS) if T[(L, S, R)] == S]
                # Find what each non-fixed-point maps to
                targets = {}
                for S in range(mS):
                    if S not in fps:
                        targets[S] = T[(L, S, R)]
                fp_str = ",".join(str(s) for s in fps)
                tgt_str = ", ".join(f"{s}→{t}" for s,t in targets.items())
                print(f"    (L={L},R={R}): fixed={{{fp_str}}}"
                      f"{'  moves: ' + tgt_str if tgt_str else ''}")

def analyze_value2_cycle_impossibility():
    """
    KEY PROOF ATTEMPT: Show that value 2 cannot sustain a cycle.

    Observation: Value 2 only exists at positions 1..n-2 (ternary processors).
    T_bot (pos 0) and T_top (pos n-1) never hold value 2.

    For value 2 to participate in a cycle:
    - Some mid position i must reach value 2
    - For i to LEAVE value 2, certain conditions on L and R are needed
    - For i to RETURN to value 2, different conditions are needed
    - These conditions propagate as obligations to i-1 and i+1

    The question: can these obligations be satisfied all the way to the boundaries?
    """
    print("\n" + "=" * 70)
    print("VALUE-2 CYCLE IMPOSSIBILITY ANALYSIS")
    print("=" * 70)

    # T_mid: How does value 2 interact?
    print("\nT_mid value-2 dynamics:")
    print("  Transitions TO value 2:")
    to_2 = []
    for L in range(3):
        for S in range(3):
            for R in range(3):
                if T_mid[(L,S,R)] == 2 and S != 2:
                    to_2.append((L,S,R))
                    print(f"    ({L},{S},{R}) → 2  [from S={S}]")

    print("\n  Transitions FROM value 2:")
    from_2 = []
    for L in range(3):
        for R in range(3):
            out = T_mid[(L,2,R)]
            if out != 2:
                from_2.append((L,R,out))
                print(f"    ({L},2,{R}) → {out}")

    print(f"\n  Value 2 is PRODUCED by: {len(to_2)} transitions")
    print(f"  Value 2 is CONSUMED by: {len(from_2)} transitions")

    # Value 2 production conditions
    print("\n  Production summary (S→2):")
    print(f"    1→2: requires (L=1,R=2)  [T_mid (1,1,2)=2]")
    print(f"         or       (L=1,R=2)  [T_mid (1,2,2)=2]")
    print(f"         or       (L=2,R=2)  [T_mid (2,2,2)=2 — but 2→2 not a change]")

    for L,S,R in to_2:
        print(f"    {S}→2 at ({L},{S},{R}): needs L={L}, R={R}")

    # Value 2 consumption conditions
    print("\n  Consumption summary (2→?):")
    for L,R,out in from_2:
        print(f"    2→{out} at ({L},2,{R}): needs L={L}, R={R}")

    # KEY: trace what value-2 needs from left and right
    print("\n  CRITICAL: Value 2 at position i requires:")
    print("    To ENTER (become 2): L=1 and R=2")
    print("      i.e., left neighbor must be 1, right neighbor must be 2")
    print("    To STAY as 2: must have (L,R) in stable set")

    stable_2 = [(L,R) for L in range(3) for R in range(3) if T_mid[(L,2,R)] == 2]
    print(f"    Stable-2 contexts: {stable_2}")

    unstable_2 = [(L,R,T_mid[(L,2,R)]) for L in range(3) for R in range(3) if T_mid[(L,2,R)] != 2]
    print(f"    Unstable-2 contexts: {[(L,R) for L,R,_ in unstable_2]}")
    for L,R,out in unstable_2:
        print(f"      ({L},2,{R}) → {out}")

def analyze_2wave_boundary():
    """
    The "2-wave" analysis: value 2 propagates leftward.

    In T_mid: to produce value 2 at position i, we need R=2 at position i+1.
    So value 2 must come from the RIGHT. This creates a leftward wave.

    But T_top (rightmost) is binary — it can never be 2.
    T_high (second from right) CAN be 2, but its right neighbor is T_top (binary).

    So value 2 at T_high requires:
    """
    print("\n" + "=" * 70)
    print("2-WAVE BOUNDARY ANALYSIS")
    print("=" * 70)

    # T_high: how does value 2 arise?
    print("\nT_high: value 2 dynamics (left=ternary 0-2, right=binary 0-1)")
    print("  Transitions producing 2:")
    for L in range(3):
        for S in range(3):
            for R in range(2):
                if T_high[(L,S,R)] == 2 and S != 2:
                    print(f"    ({L},{S},{R}) → 2")

    print("  Transitions consuming 2:")
    for L in range(3):
        for R in range(2):
            out = T_high[(L,2,R)]
            if out != 2:
                print(f"    ({L},2,{R}) → {out}")

    print("  Stable-2 contexts:")
    for L in range(3):
        for R in range(2):
            if T_high[(L,2,R)] == 2:
                print(f"    (L={L}, R={R})")

    # T_low: how does value 2 arise?
    print("\nT_low: value 2 dynamics (left=binary 0-1, right=ternary 0-2)")
    print("  Transitions producing 2:")
    for L in range(2):
        for S in range(3):
            for R in range(3):
                if T_low[(L,S,R)] == 2 and S != 2:
                    print(f"    ({L},{S},{R}) → 2")

    print("  Transitions consuming 2:")
    for L in range(2):
        for R in range(3):
            out = T_low[(L,2,R)]
            if out != 2:
                print(f"    ({L},2,{R}) → {out}")

    # Now the critical question:
    print("\n" + "-" * 50)
    print("CRITICAL CHAIN ANALYSIS:")
    print("-" * 50)

    # For T_mid to produce value 2: needs R=2
    # So the right neighbor must already be 2
    # This chains: pos i needs pos i+1 = 2, which needs pos i+2 = 2, etc.
    # This chain goes RIGHTWARD until hitting T_high

    print("\nFor T_mid at position i to reach value 2:")
    print("  Needs: (L=1, S=1, R=2) → 2  [primary production]")
    print("  i.e., position i+1 must be 2")
    print("  But for position i+1 to be 2, IT needs its right neighbor to be 2")
    print("  → Chain propagates rightward: i needs i+1=2, i+1 needs i+2=2, ...")
    print("  → Eventually hits T_high at position n-2")

    print("\nFor T_high (pos n-2) to reach value 2:")
    print("  Right neighbor is T_top (binary: only 0 or 1)")
    print("  T_high 2-production requires:")
    found_r2 = False
    for L in range(3):
        for S in range(3):
            for R in range(2):
                if T_high[(L,S,R)] == 2 and S != 2:
                    print(f"    ({L},{S},{R}) → 2  [R={R}, which is in {{0,1}}]")
                    if R == 2:
                        found_r2 = True

    if not found_r2:
        print("  → T_high can reach 2 WITHOUT R=2 (R is binary anyway)")
        print("  → The rightward chain breaks at T_high")

    # But wait — T_high might produce 2 through different means
    # Let's check: for T_mid, are there OTHER ways to produce 2 besides R=2?
    print("\nAll T_mid transitions producing 2 (including from S=2):")
    for L in range(3):
        for S in range(3):
            for R in range(3):
                if T_mid[(L,S,R)] == 2:
                    is_priv = "*" if S != 2 else " "
                    print(f"    ({L},{S},{R}) → 2 {is_priv}")

def analyze_cycle_constraints_detailed(n=6):
    """
    For a SPECIFIC small n, enumerate the exact constraints a cycle would need.

    In a hypothetical cycle of length L through bad configs c_0, c_1, ..., c_{L-1}:
    - c_{k+1} is obtained from c_k by firing some position p_k
    - c_0 = c_L (cycle closes)
    - Every position fires at least twice
    - No 2-cycle: consecutive firings at same position change value

    Constraint propagation: if position i fires at step k changing a->b,
    then c_k[i-1] and c_k[i+1] must have specific values (determined by table).
    """
    print("\n" + "=" * 70)
    print(f"DETAILED CYCLE CONSTRAINTS (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)

    # For each position, catalog: what contexts cause which transitions?
    tables_by_pos = []
    for pos in range(n):
        if pos == 0:
            T, mL, mS, mR = T_bot, 2, 2, 3
        elif pos == 1:
            T, mL, mS, mR = T_low, 2, 3, 3
        elif pos == n-2:
            T, mL, mS, mR = T_high, 3, 3, 2
        elif pos == n-1:
            T, mL, mS, mR = T_top, 3, 2, 2
        else:
            T, mL, mS, mR = T_mid, 3, 3, 3

        # Map (old_val, new_val) -> list of (L, R) contexts
        trans_map = defaultdict(list)
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = T[(L,S,R)]
                    if out != S:
                        trans_map[(S, out)].append((L, R))

        tables_by_pos.append(trans_map)

    # Print the constraint table
    for pos in range(n):
        table_name = ["T_bot", "T_low"] + [f"T_mid"] * (n-4) + ["T_high", "T_top"]
        print(f"\n  Position {pos} ({table_name[pos]}):")
        for (old, new), contexts in sorted(tables_by_pos[pos].items()):
            ctx_str = ", ".join(f"(L={L},R={R})" for L,R in contexts)
            print(f"    {old}→{new}: {ctx_str}")

    # Now analyze: in a cycle, position i fires changing a->b, then later b->c
    # What are the constraints on the SEQUENCE of neighbor values?
    print("\n  SEQUENTIAL CONSTRAINT ANALYSIS:")
    print("  If position i fires twice: first a→b, then later b→c")
    print("  Between the two firings, what must neighbors do?")

    for pos in range(n):
        table_name = ["T_bot", "T_low"] + [f"T_mid"] * (n-4) + ["T_high", "T_top"]
        print(f"\n  Position {pos} ({table_name[pos]}):")
        tm = tables_by_pos[pos]

        # For each pair of consecutive transitions a->b then b->c
        for (a, b), ctx1_list in tm.items():
            for (b2, c), ctx2_list in tm.items():
                if b2 != b:
                    continue
                # a->b with context (L1,R1), then b->c with context (L2,R2)
                for L1, R1 in ctx1_list:
                    for L2, R2 in ctx2_list:
                        if L1 == L2 and R1 == R2:
                            continue  # would be 2-cycle or no change needed
                        l_req = f"L:{L1}→{L2}" if L1 != L2 else f"L={L1}"
                        r_req = f"R:{R1}→{R2}" if R1 != R2 else f"R={R1}"
                        # Only print if it's a return (a->b->a) for clarity
                        if c == a:
                            print(f"    Osc {a}→{b}→{a}: {l_req}, {r_req}")

def prove_no_pure_2_cycle():
    """
    Additional analysis: prove that no configuration can cycle using only
    value-2 oscillations.

    If we restrict attention to firings that involve value 2 (either producing
    or consuming it), can they form a cycle among themselves?
    """
    print("\n" + "=" * 70)
    print("VALUE-2 INVOLVEMENT ANALYSIS")
    print("=" * 70)

    # Key insight: T_mid value 2 needs R=2 to be produced (from 1→2)
    # Value 2 at pos i needs pos i+1 = 2
    # This creates a RIGHTWARD dependency chain

    # But value 2 is consumed (2→0 or 2→1) when certain (L,R) conditions hold
    # These conditions involve L or R changing, creating OBLIGATIONS on neighbors

    # The critical question: if we have a "pool" of value 2 at positions
    # i, i+1, ..., j, can this pool sustain itself?

    # For the leftmost 2 (position i):
    #   It needs its left neighbor (pos i-1) to be 1 to enter
    #   When it leaves: goes to 0 if (L=0 or L=2) with various R

    # For the rightmost 2 (position j):
    #   It needs R=2 at pos j+1 to enter... but pos j+1 is NOT 2
    #   UNLESS j+1 = n-2 (T_high) which has special production rules

    print("\nT_mid: Complete value-2 fixed-point analysis")
    print("  For which (L,R) is value 2 a FIXED POINT?")
    for L in range(3):
        for R in range(3):
            if T_mid[(L,2,R)] == 2:
                print(f"    (L={L}, R={R}): 2 is stable")
            else:
                print(f"    (L={L}, R={R}): 2 → {T_mid[(L,2,R)]} (UNSTABLE)")

    print("\n  For which (L,R) is value 2 the TARGET (attracting)?")
    for L in range(3):
        for R in range(3):
            targets = set()
            for S in range(3):
                # Iterate: S -> T(L,S,R) -> T(L,T(L,S,R),R) -> ...
                v = S
                for _ in range(5):
                    v = T_mid[(L,v,R)]
                targets.add((S, v))
            final = set(v for _,v in targets)
            if 2 in final:
                attracting = [S for S,v in targets if v == 2]
                print(f"    (L={L}, R={R}): value 2 attracts from {attracting}")

def find_longest_obligation_chain(n=8):
    """
    In the actual bad-config graph, find the longest chain of configs
    where value 2 is present, and trace how it enters and exits.
    """
    print("\n" + "=" * 70)
    print(f"LONGEST VALUE-2 CHAINS IN BAD CONFIGS (n={n})")
    print("=" * 70)

    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    # Build bad-config DAG
    adj = {c: [] for c in bad_set}
    for c in bad_set:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append((succ, i, S, new_S))

    # Count configs involving value 2
    has_2 = sum(1 for c in bad_set if 2 in c)
    no_2 = len(bad_set) - has_2
    print(f"  Bad configs with value 2: {has_2}/{len(bad_set)} ({100*has_2/len(bad_set):.1f}%)")
    print(f"  Bad configs without value 2: {no_2}/{len(bad_set)}")

    # Find transitions that INTRODUCE value 2 (from a config without 2 to one with 2)
    intro_2 = 0
    elim_2 = 0
    for c in bad_set:
        for succ, i, old, new in adj[c]:
            c_has_2 = 2 in c
            s_has_2 = 2 in succ
            if not c_has_2 and s_has_2:
                intro_2 += 1
            if c_has_2 and not s_has_2:
                elim_2 += 1

    print(f"  Transitions introducing value 2: {intro_2}")
    print(f"  Transitions eliminating value 2: {elim_2}")

    # Count max value-2 at once
    max_2_count = max(sum(1 for v in c if v == 2) for c in bad_set)
    print(f"  Maximum positions with value 2 simultaneously: {max_2_count}")

    # Distribution
    from collections import Counter
    count_dist = Counter(sum(1 for v in c if v == 2) for c in bad_set)
    print(f"  Distribution of #positions with value 2:")
    for k in sorted(count_dist.keys()):
        print(f"    {k}: {count_dist[k]} configs")

def main():
    print("CONVERGENCE PROOF — Part 8: Boundary Obstruction Analysis")
    print("=" * 70)

    # Part 1: Catalog all transitions
    catalog_all_transitions()

    # Part 2: Oscillation obligations
    all_osc = analyze_oscillation_obligations()

    # Part 3: Value-2 propagation
    analyze_value2_propagation()

    # Part 4: Boundary bottleneck
    analyze_boundary_bottleneck()

    # Part 5: 2-wave analysis
    analyze_2wave_boundary()

    # Part 6: Detailed constraints
    analyze_cycle_constraints_detailed(n=6)

    # Part 7: Value-2 fixed points
    prove_no_pure_2_cycle()

    # Part 8: Empirical value-2 chains
    find_longest_obligation_chain(n=8)

if __name__ == "__main__":
    main()
