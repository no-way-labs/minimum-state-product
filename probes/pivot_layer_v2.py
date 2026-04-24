"""
Focused analysis: isolated sandwiched ternary pivot at n=9 with P=2.

ms = (3,3,2,2,3,2,2,3,3), pivot=4 (ternary, ms[4]=3).
Question: which layer closes cycles with fc(pivot)=P?

The single hard case for P=2 is the "perfectly balanced" distribution:
  Both phases have (J=1, K=1, g=1, h=1).
All other distributions have a free second-neighbor (g=0 or h=0 in some phase)
which gives layer 2, or even J/K which gives layer 3.

This script:
1. Confirms the distribution analysis
2. Analyzes the balanced case in detail - is it actually reachable?
3. For P=3 (natural for ms[4]=3), checks the 9 unclosed cases
4. Determines if ordering (tightness) resolves the balanced case
"""

from itertools import product as iprod


def distribute(total, phases):
    """All ways to put total items into phases buckets (>=0 each)."""
    if phases == 1:
        yield (total,)
        return
    for k in range(total + 1):
        for rest in distribute(total - k, phases - 1):
            yield (k,) + rest


def analyze_p2():
    """P=2: pivot fires twice, 2 phases."""
    P = 2
    dists = list(distribute(2, P))  # [(0,2), (1,1), (2,0)]

    print("=" * 60)
    print("P = 2 ANALYSIS")
    print("=" * 60)
    print(f"Distributions of 2 firings into {P} phases: {dists}")
    print()

    # Classify all 3^4 = 81 combos
    layer2 = 0
    layer3 = 0
    unclosed = []

    for d_g in dists:      # left2t
        for d_J in dists:  # left_t
            for d_K in dists:  # right_t
                for d_h in dists:  # right2t
                    phases = [(d_J[i], d_K[i], d_g[i], d_h[i]) for i in range(P)]
                    # phases[i] = (J, K, g, h)

                    closed_by = None
                    for i in range(P):
                        J, K, g, h = phases[i]
                        # Layer 2: free second-neighbor + active first-neighbor
                        if g == 0 and J >= 1:
                            closed_by = 2; break
                        if h == 0 and K >= 1:
                            closed_by = 2; break

                    if closed_by is None:
                        for i in range(P):
                            J, K, g, h = phases[i]
                            # Layer 3: even first-neighbor firings >= 2
                            if J >= 2 and J % 2 == 0:
                                closed_by = 3; break
                            if K >= 2 and K % 2 == 0:
                                closed_by = 3; break

                    if closed_by == 2:
                        layer2 += 1
                    elif closed_by == 3:
                        layer3 += 1
                    else:
                        unclosed.append(phases)

    total = len(dists) ** 4
    print(f"Layer 2 (non-tight EC):    {layer2}/{total} ({100*layer2/total:.1f}%)")
    print(f"Layer 3 (binary recovery): {layer3}/{total} ({100*layer3/total:.1f}%)")
    print(f"Unclosed:                  {len(unclosed)}/{total} ({100*len(unclosed)/total:.1f}%)")
    print()

    if unclosed:
        print("Unclosed distributions:")
        for phases in unclosed:
            print(f"  Phase 0: J={phases[0][0]},K={phases[0][1]},g={phases[0][2]},h={phases[0][3]}")
            print(f"  Phase 1: J={phases[1][0]},K={phases[1][1]},g={phases[1][2]},h={phases[1][3]}")
        print()

    # Analyze the unclosed case in detail
    print("DETAILED ANALYSIS OF UNCLOSED CASE")
    print("-" * 40)
    print("Both phases: (J=1, K=1, g=1, h=1)")
    print()
    print("Each phase has exactly 4 local firings: one each of {l2t, lt, rt, r2t}")
    print("Plus non-local firings from positions {0,1,7,8} (total = 4*3 - P = 10 if P=2, but")
    print("actually total non-pivot non-local = sum(ms) - ms[pivot] - 4*2 = 23 - 3 - 8 = 12)")
    print("Wait: with P=2, pivot fires 2 times, but ms[pivot]=3.")
    print()

    # Actually, the question says P=2 meaning the pivot fires exactly 2 times.
    # This is only valid if ms[pivot]=2. With ms[pivot]=3, the pivot fires 3 times.
    # Let me note this and also check whether the balanced case can be closed
    # by ordering/tightness analysis.

    print("KEY QUESTION: In the balanced (1,1,1,1) phase, is the ordering tight or non-tight?")
    print()
    print("Tight on left means: first mover in phase is l2t, second is lt.")
    print("Non-tight means: anything else happens first.")
    print()
    print("In a phase with 4 local firings + ~6 non-local firings (~10 total),")
    print("the probability of the EXACT tight pattern is low. But CAN it happen?")
    print()
    print("YES, tight CAN happen: if the mover word starts the phase with")
    print("positions 2 then 3 (l2t then lt) with no intervening movers.")
    print()
    print("But if tight on left AND tight on right simultaneously:")
    print("  First mover = l2t (pos 2), second = lt (pos 3),")
    print("  AND first mover = r2t (pos 6), second = rt (pos 5)")
    print("This is a CONTRADICTION: the first mover can't be BOTH pos 2 and pos 6.")
    print()
    print("So at most ONE side can be tight. The other side is non-tight.")
    print()
    print("For layer 2, we need: free second-neighbor (g=0 or h=0).")
    print("In the balanced case, g=1 and h=1 in both phases, so NO free second-neighbor.")
    print("Layer 2 does NOT apply even with non-tight ordering!")
    print()

    # Check: does tightness help for a DIFFERENT layer?
    print("RESOLUTION: What closes the balanced (1,1,1,1) case?")
    print("-" * 40)
    print()
    print("Option A: The balanced case might not be REACHABLE.")
    print("  With ms[4]=3 and P=2, the pivot fires only 2 of its 3 required times.")
    print("  This violates the good cycle condition (each proc fires ms[p] times).")
    print("  So P=2 is IMPOSSIBLE for ms[4]=3.")
    print()
    print("Option B: If the question means ms[4]=2 (binary pivot, not ternary),")
    print("  then ms = (3,3,2,2,2,2,2,3,3), product = 3888.")
    print("  But then 'ternary pivot' is incorrect.")
    print()
    print("Option C: P is not the fire count but something else.")
    print()

    # Let me check P=3 (natural for ms[4]=3)
    return unclosed


def analyze_p3():
    """P=3: pivot fires 3 times (natural for ms[4]=3), 3 phases."""
    P = 3
    dists = list(distribute(2, P))

    print()
    print("=" * 60)
    print("P = 3 ANALYSIS (natural for ms[4]=3)")
    print("=" * 60)
    print(f"Distributions of 2 firings into {P} phases: {dists}")
    print(f"  = {len(dists)} options per neighbor, {len(dists)**4} total combos")
    print()

    layer1 = 0
    layer2 = 0
    layer3 = 0
    unclosed = []

    for d_g in dists:
        for d_J in dists:
            for d_K in dists:
                for d_h in dists:
                    phases = [(d_J[i], d_K[i], d_g[i], d_h[i]) for i in range(P)]

                    closed_by = None
                    # Layer 1: pigeonhole. P=3 > 2=fc(binary), so if any phase
                    # has g=0 & J>=1 or h=0 & K>=1, pigeonhole closes.
                    for i in range(P):
                        J, K, g, h = phases[i]
                        if (g == 0 and J >= 1) or (h == 0 and K >= 1):
                            closed_by = 1; break

                    if closed_by is None:
                        for i in range(P):
                            J, K, g, h = phases[i]
                            if J >= 2 and J % 2 == 0:
                                closed_by = 3; break
                            if K >= 2 and K % 2 == 0:
                                closed_by = 3; break

                    if closed_by == 1:
                        layer1 += 1
                    elif closed_by == 3:
                        layer3 += 1
                    else:
                        unclosed.append((phases, d_g, d_J, d_K, d_h))

    total = len(dists) ** 4
    print(f"Layer 1 (pigeonhole):      {layer1}/{total} ({100*layer1/total:.1f}%)")
    print(f"Layer 3 (binary recovery): {layer3}/{total} ({100*layer3/total:.1f}%)")
    print(f"Unclosed:                  {len(unclosed)}/{total} ({100*len(unclosed)/total:.1f}%)")
    print()

    if unclosed:
        print("Unclosed distributions:")
        for phases, d_g, d_J, d_K, d_h in unclosed:
            desc = " | ".join(f"J={p[0]},K={p[1]},g={p[2]},h={p[3]}" for p in phases)
            print(f"  [{desc}]")
            # Analyze: no free neighbor means g>0 whenever J>0, h>0 whenever K>0
            # AND no even J or K >= 2
            # So each active phase has J=1,K=1,g>=1,h>=1
            # With 2 firings in 3 phases: must be (0,1,1) or permutation
            # Balanced = each active phase gets exactly 1

        print()
        print(f"Pattern: all unclosed have the same structure -")
        print(f"  One empty phase (0,0,0,0) and two balanced phases (1,1,1,1)")
        print(f"  or the empty phase has some inactive neighbors.")
        print()

        # Check structure more carefully
        balanced_count = 0
        for phases, d_g, d_J, d_K, d_h in unclosed:
            active_phases = [p for p in phases if any(x > 0 for x in p)]
            if all(p == (1,1,1,1) for p in active_phases):
                balanced_count += 1

        print(f"  All-balanced active phases: {balanced_count}/{len(unclosed)}")

        # What are the non-balanced ones?
        for phases, d_g, d_J, d_K, d_h in unclosed:
            active_phases = [p for p in phases if any(x > 0 for x in p)]
            if not all(p == (1,1,1,1) for p in active_phases):
                desc = " | ".join(f"J={p[0]},K={p[1]},g={p[2]},h={p[3]}" for p in phases)
                print(f"  Non-balanced: [{desc}]")
                print(f"    d_g={d_g}, d_J={d_J}, d_K={d_K}, d_h={d_h}")

    # Now: can the balanced (1,1,1,1) phases be closed by tightness?
    print()
    print("TIGHTNESS ANALYSIS for balanced phases")
    print("-" * 40)
    print("Same logic as P=2: in a (1,1,1,1) phase, tight on left AND right")
    print("is impossible (first mover can't be both pos 2 and pos 6).")
    print("At most one side tight. The non-tight side has g=1 (not free).")
    print("Layer 2 requires g=0, so non-tight ordering doesn't help.")
    print()
    print("Layer 3 needs J=even>=2 or K=even>=2. With J=1, K=1: FAILS.")
    print()
    print("CONCLUSION: The balanced (1,1,1,1) case is NOT closed by layers 1-3.")
    print("It needs layer 4+ (e.g., tightness-based EC with g>=1, or")
    print("a different structural argument).")


def analyze_ordering_detail():
    """
    Deeper analysis: in the balanced (1,1,1,1) phase with P=2,
    what exactly happens with the ordering?

    The phase has firings of: l2t(1), lt(1), rt(1), r2t(1) = 4 local firings
    plus some number of non-local firings.

    For entry conflict, we need: at the pivot's firing (which bounds the phase),
    the pivot sees contexts (L, S, R) = (c[3], c[4], c[5]).
    The first neighbor lt (pos 3) affects L, and rt (pos 5) affects R.

    Within a phase, lt fires once and l2t fires once. The ORDER matters:
    - If l2t fires BEFORE lt: l2t changes c[2], which is the LEFT context of lt.
      When lt later fires, it sees the UPDATED c[2]. This is the "contaminated" case.
    - If lt fires BEFORE l2t: lt fires with the ORIGINAL c[2]. Clean context.

    Similarly for the right side.

    The question is whether the ordering constrains the entry conflict argument.
    """
    print()
    print("=" * 60)
    print("ORDERING DETAIL FOR BALANCED PHASE")
    print("=" * 60)
    print()

    # In a (1,1,1,1) phase, there are 4! = 24 orderings of the 4 local firings.
    # But non-local firings can interleave. Focus on the 4 local ordering.

    local_procs = ['l2t', 'lt', 'rt', 'r2t']

    from itertools import permutations
    perms = list(permutations(local_procs))

    print(f"24 orderings of local firings in a balanced phase:")
    print()

    tight_left_count = 0
    tight_right_count = 0
    tight_both_count = 0
    contaminated_left = 0  # l2t before lt
    contaminated_right = 0  # r2t before rt

    for perm in perms:
        l2t_pos = perm.index('l2t')
        lt_pos = perm.index('lt')
        rt_pos = perm.index('rt')
        r2t_pos = perm.index('r2t')

        tight_l = (l2t_pos == 0 and lt_pos == 1)
        tight_r = (r2t_pos == 0 and rt_pos == 1)
        contam_l = l2t_pos < lt_pos
        contam_r = r2t_pos < rt_pos

        if tight_l: tight_left_count += 1
        if tight_r: tight_right_count += 1
        if tight_l and tight_r: tight_both_count += 1
        if contam_l: contaminated_left += 1
        if contam_r: contaminated_right += 1

        marker = ""
        if tight_l: marker += " [TIGHT-L]"
        if tight_r: marker += " [TIGHT-R]"
        if contam_l and not tight_l: marker += " [contam-L]"
        if contam_r and not tight_r: marker += " [contam-R]"
        if not contam_l: marker += " [clean-L]"
        if not contam_r: marker += " [clean-R]"

        print(f"  {' -> '.join(perm)}{marker}")

    print()
    print(f"Tight left (l2t first, lt second): {tight_left_count}/24")
    print(f"Tight right (r2t first, rt second): {tight_right_count}/24")
    print(f"Tight BOTH (impossible): {tight_both_count}/24")
    print(f"Contaminated left (l2t before lt): {contaminated_left}/24")
    print(f"Contaminated right (r2t before rt): {contaminated_right}/24")
    print()

    # Key insight: contaminated vs clean
    # If lt fires with CLEAN left context (l2t hasn't fired yet),
    # then the left context of lt at firing time = left context at phase start.
    # This means lt's firing context is determined by the phase-start config.
    #
    # If the SAME clean context appears in two different phases,
    # but the pivot fires differently -> entry conflict at lt.

    # With P=2 phases, each phase starts right after a pivot firing.
    # The pivot changes c[4]. If lt fires with clean left (c[2] unchanged),
    # lt sees (c[1], c[2], c[3]) = same in both phases IF c[1],c[2],c[3]
    # haven't changed. But c[3] IS lt itself, and it fires once per phase...

    # Actually this gets complicated. The point is:
    # In the balanced case, layer 2's "non-tight" argument requires g=0.
    # With g=1, even non-tight ordering doesn't give a free context.

    print("CONCLUSION FOR BALANCED CASE:")
    print("  g=1 means l2t fires in EVERY phase.")
    print("  Whether l2t fires before or after lt doesn't create a FREE context.")
    print("  The second-neighbor IS active, so its value can differ between phases.")
    print("  Layer 2 (non-tight EC with free second-neighbor) does NOT apply.")
    print()
    print("  Layer 3 (binary recovery) needs J=even>=2. With J=1: FAILS.")
    print()
    print("  This balanced case needs a DIFFERENT mechanism:")
    print("  - Binary value constraint: l2t fires once in the phase,")
    print("    so it toggles (0->1 or 1->0). Combined with lt also firing once,")
    print("    the NET effect on c[3] depends on the firing order.")
    print("  - With lt binary (ms[3]=2), lt toggles c[3]. After the phase,")
    print("    c[3] has changed by 1 mod 2. Over 2 phases (P=2), c[3] changes")
    print("    twice, returning to start. Similarly for all binary neighbors.")
    print("  - The pivot (ternary, ms[4]=3) fires 2 times over 2 phases.")
    print("    With P=2, c[4] changes by 2 mod 3. After both phases: +2 mod 3.")
    print("    For a CYCLE, need +0 mod 3 over all phases, i.e., P must be")
    print("    divisible by 3. P=2 is NOT divisible by 3!")
    print()
    print("  CRITICAL INSIGHT: If ms[4]=3 (ternary), the pivot MUST fire")
    print("  a multiple of 3 times to return to its starting value.")
    print("  P=2 is IMPOSSIBLE for a ternary pivot in a good cycle!")
    print("  (Good cycles require each proc fires exactly ms[p] times.)")
    print()
    print("  Therefore: P=2 for a ternary pivot (ms[4]=3) is VACUOUSLY TRUE.")
    print("  All cycles have P=3 (or P=ms[4]=3).")


def summary():
    print()
    print("=" * 60)
    print("FINAL SUMMARY")
    print("=" * 60)
    print()
    print("For ms = (3,3,2,2,3,2,2,3,3), n=9, pivot at pos 4:")
    print()
    print("1. P=2 is IMPOSSIBLE: ms[4]=3 means the pivot fires exactly 3 times")
    print("   in any good cycle. P=2 violates the good cycle condition.")
    print()
    print("2. For P=3 (the only valid case):")
    print("   - Layer 1 (pigeonhole) closes 88.9% of distributions")
    print("     (P=3 > 2=fc(binary), so any free second-neighbor suffices)")
    print("   - Layer 3 (binary recovery) closes 10.4% more")
    print("   - 0.7% (9 distributions) remain: the 'balanced' cases where")
    print("     each active phase has (J=1,K=1,g=1,h=1)")
    print()
    print("3. The 9 unclosed P=3 cases all have structure:")
    print("   One empty phase + two balanced (1,1,1,1) phases, or")
    print("   permutations with matched left/right asymmetry.")
    print("   These need layer 4+ (ordering-based or global arguments).")
    print()
    print("4. IF the question intended ms[4]=2 (binary pivot, P=2):")
    print("   - Layer 2 closes 69.1%")
    print("   - Layer 3 closes 29.6%")
    print("   - 1 case unclosed: both phases balanced (1,1,1,1)")
    print("   - But then 'ternary pivot' is a misnomer.")


if __name__ == '__main__':
    analyze_p2()
    analyze_p3()
    analyze_ordering_detail()
    summary()
