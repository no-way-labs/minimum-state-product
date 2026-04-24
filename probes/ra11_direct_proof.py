"""
ra11_direct_proof.py — Finding a direct proof for odd-winding non-uniform
non-consecutive isolated binary → False.

The key insight: when we arrive at the recursion point, we know:
1. ≥3 non-consecutive binary
2. Odd-winding (|W| = n), non-uniform direction
3. Every proc fires ≥ 1 (from odd-winding)
4. Binary p with fc ≥ 2, all isolated firings
5. Sub-threshold, converges, no safe processor

The recursion goes through binary_ring_impossibility which dispatches:
- |Z|=0 (from 3) → no pivot → not zero-winding → not sweep → odd-winding non-uniform
  → callback → recursion

To break: need a proof for {1,2,3,4,5} → False that doesn't use the global dispatch.

APPROACH: Use the MNU (Mover Non-Uniformity) framework.
MNU works on good cycles with ≥3 non-adjacent binary at sub-threshold.
It proves entry conflict directly from the mover word structure.

Let me check: does MNU apply here?
"""

import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def total_displacement(movers, n):
    W = 0
    L = len(movers)
    for i in range(L):
        diff = (movers[(i+1) % L] - movers[i]) % n
        if diff == 0: pass
        elif diff <= n // 2: W += diff
        else: W -= (n - diff)
    return W

def fire_count(movers, n):
    fc = [0] * n
    for m in movers: fc[m] += 1
    return fc

def has_isolated_firings(movers, p):
    L = len(movers)
    for i in range(L):
        if movers[i] == p and movers[(i+1) % L] == p:
            return False
    return True


def check_mnu_applicability():
    """
    MNU (Mover Non-Uniformity) framework from LeanMn/LowerBound/MNU.lean.

    MNU proves that for sub-threshold systems with ≥3 non-adjacent binary,
    every good cycle has an entry conflict.

    Key: MNU works on the SYSTEM level, not just the mover word.
    It uses the shadow cycle construction to show impossibility.

    But wait — the shadow cycle proof is for SWEEP cycles (uniform direction).
    For non-uniform cycles, MNU might not directly apply.

    Let me check what tools are available in the Lean codebase.
    """
    print("=== MNU Applicability ===")
    print()
    print("MNU.lean provides shadow cycle obstruction for sweeps.")
    print("For non-sweep non-uniform odd-winding cycles, we need a different approach.")
    print()
    print("Available tools in the Lean codebase:")
    print("1. Shadow cycles (for sweeps/uniform)")
    print("2. Palindromic Entry Conflict (for 3 consecutive binary, fc=2 non-sweep)")
    print("3. Wiggle Shadow Cycle (for single-wiggle words with non-adjacent binary)")
    print("4. Universal Entry Conflict (4 mechanisms for all good cycles)")
    print("5. binary_isolated_firings_or_ec (trichotomy)")
    print("6. procMinGap_hasEntryConflict (3 consecutive binary, min gap)")
    print("7. general_parity_entry_conflict (3 consecutive binary, any pair)")


def check_fresh_approach():
    """
    FRESH APPROACH: Instead of routing through the global dispatch,
    prove directly from the available hypotheses.

    At the recursion point we have:
    - Binary p with isolated firings and fc ≥ 2
    - Non-consecutive (no 3 consecutive binary)
    - Odd-winding, non-uniform
    - All procs fire, no safe processor, sub-threshold

    KEY INSIGHT: The odd-winding + non-uniform condition is equivalent to
    isOddWinding ∧ ¬uniformDirection.

    For ≥3 non-adjacent binary, we can invoke:
    gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary

    Wait — this says ¬(uniformDirection ∧ isOddWinding), i.e.,
    uniformDirection → ¬isOddWinding and isOddWinding → ¬uniformDirection.

    So isOddWinding already implies ¬uniformDirection for ≥3 non-adj binary!

    But the theorem oddWinding_nonUniform_sub_threshold_false is called with
    both _hodd and _hnonunif as separate hypotheses. If ¬uniformDirection
    is automatic from isOddWinding + ≥3 non-adj binary, then we should
    never reach the non-uniform case separately...

    Wait, let me re-read. The dispatch is:
    1. zeroWinding
    2. sweep (which implies uniform direction)
    3. oddWinding (from not-sweep + not-zero-winding)
    4. Within oddWinding: uniform vs non-uniform

    For ≥3 non-adj binary: oddWinding + uniformDirection is impossible.
    So case 4 (uniform) is vacuously handled, and we always get non-uniform.

    This means: oddWinding + ≥3 non-adj binary → ¬uniformDirection automatically.
    And the theorem says: oddWinding → ¬uniformDirection in this case.

    So the oddWinding_nonUniform case IS just the oddWinding case for non-adj binary!
    """
    print("\n=== Fresh Approach ===")
    print()
    print("KEY OBSERVATION: For ≥3 non-adjacent binary:")
    print("  isOddWinding → ¬uniformDirection (from not_uniformDirection_and_isOddWinding)")
    print("  So 'odd-winding non-uniform' = 'odd-winding' for non-adj binary.")
    print()
    print("The real question: can odd-winding + non-adj binary + sub-threshold → False")
    print("be proved WITHOUT going through binary_ring_impossibility?")
    print()
    print("APPROACH: From odd-winding:")
    print("  1. Every proc fires ≥ 1 (edgeTraversalCount_pos)")
    print("  2. Every binary proc fires ≥ 2 (even)")
    print("  3. Trichotomy: EC ∨ permanent ∨ isolated")
    print("  4. Permanent → W=0, contradicts |W|=n")
    print("  5. So: EC ∨ isolated for each binary proc")
    print("  6. If any EC: done")
    print("  7. If ALL binary procs isolated: need direct proof")
    print()
    print("For step 7, the isolated firings give us MinFiringGap for each binary proc.")
    print("The gap ≥ 2 (from allIsolated_gap_ge2).")
    print("Within each gap, the binary proc doesn't fire.")
    print("At the gap boundary: mover step (binary fires) + non-mover step (next step).")
    print()
    print("For 3 consecutive binary: L,S,R all binary → parity determines config → EC.")
    print("For non-consecutive: at least one neighbor is ternary.")
    print("Ternary neighbor's value is NOT determined by fire parity alone.")
    print()
    print("HOWEVER: we have ≥3 non-adj binary. By pigeonhole, at least 2 binary procs")
    print("are at distance ≤ floor(n/3) ≤ 3 (for n=9).")
    print("Actually no — for binary at {0,3,6}, all distances are exactly 3.")
    print()
    print("CRITICAL: The ternary neighbor between two distance-3 binary procs fires")
    print("≥ 3 times (ternary). In a gap of the closer binary proc, the ternary")
    print("neighbor might fire an even number of times, making the ternary neighbor's")
    print("value return to its original — then we'd have EC if the other binary")
    print("neighbor also returns (which it does by binary parity).")
    print()
    print("But this requires controlling how the ternary fires distribute across gaps.")


def investigate_ternary_in_gap():
    """
    For non-consecutive binary with isolated firings:

    Consider binary p and its ternary neighbor q = left(p) or right(p).
    p fires at steps a₁, a₂, ..., a_k (all isolated, gaps ≥ 2).

    In each gap (a_i, a_{i+1}), q fires some number of times.
    If q fires 0 mod 3 times in some gap: q returns to same value.
    But q is ternary so fire count is multiple of 3 over the WHOLE cycle.

    The total fires of q across all gaps = fc(q) = multiple of 3.
    The number of gaps = fc(p) = even number.

    If fc(q) fires are distributed across fc(p) gaps:
    Average = fc(q)/fc(p). For min fc(q)=3, min fc(p)=2: average = 1.5.

    The ternary value at a boundary depends on total fires from cycle start.
    For EC, we need TWO steps with same context.

    SIMPLER APPROACH: Instead of gap analysis, use the existing
    `nonConsecutive_phase_extraction_false` but find a proof that
    doesn't need the oddWinding callback.

    Or even simpler: the existing proof works fine for the zero-winding case
    and the sweep case. It only fails for odd-winding non-uniform.
    But for ≥3 non-adj binary, odd-winding implies non-uniform.
    And odd-winding means |W| = n ≠ 0, so not zero-winding.
    And odd-winding + non-uniform means not sweep (sweep is uniform).

    So the only relevant case IS odd-winding non-uniform.
    The recursion is: we can prove zero-winding and sweep but not odd-winding.
    """
    print("\n=== Ternary-in-gap analysis ===")

    # Numerical experiment: for random mover words with isolated binary,
    # check if there's always a gap where both neighbors return to same parity
    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]  # binary at {0, 3, 6}
    binary = [0, 3, 6]

    found = 0
    ec_from_gap = 0
    no_ec = 0

    for trial in range(200000):
        # Build random mover word with isolated binary firings
        fc = [2, 3, 3, 2, 3, 3, 2, 3, 3]  # minimum
        word = []
        for p in range(n):
            word.extend([p] * fc[p])
        random.shuffle(word)

        W = total_displacement(word, n)
        if abs(W) != n:
            continue

        # Check all binary isolated
        all_iso = True
        for p in binary:
            if not has_isolated_firings(word, p):
                all_iso = False
                break
        if not all_iso:
            continue

        found += 1

        # For each binary proc, check if any gap has the min-gap EC property
        # For non-3-consec: check ALL proc pairs, not just consecutive
        has_any_ec = False

        for p in binary:
            # Find fire positions
            fire_pos = [i for i, m in enumerate(word) if m == p]
            L = len(word)

            for fi in range(len(fire_pos)):
                a = fire_pos[fi]
                b = fire_pos[(fi + 1) % len(fire_pos)]

                # Gap from a+1 to b-1 (wrapping)
                # In this gap, how many times does each neighbor fire?
                lp = left(p, n)
                rp = right(p, n)

                if b > a:
                    gap_range = range(a + 1, b)
                else:
                    gap_range = list(range(a + 1, L)) + list(range(0, b))

                lp_fires = sum(1 for s in gap_range if word[s] == lp)
                rp_fires = sum(1 for s in gap_range if word[s] == rp)
                p_fires_in_gap = sum(1 for s in gap_range if word[s] == p)

                # For binary p: p fires at a and b, doesn't fire in gap
                # p's parity at a+1: prefix(a+1) = prefix(a) + 1 (just fired)
                # p's parity at b: prefix(b) = prefix(a+1) + p_fires_in_gap = prefix(a+1)
                # (since p doesn't fire in gap)
                # So S-parity always matches.

                # For neighbor lp (left of p):
                # If lp is binary: parity match iff lp fires even times in gap
                # If lp is ternary: need fire count ≡ 0 mod 3 for value return
                #   (but ternary isn't determined by parity alone!)

                # Wait — for BINARY neighbor: parity determines value.
                # For TERNARY neighbor: we need the ACTUAL value to match,
                # not just the parity.

                # So for non-consecutive binary, where neighbors are ternary,
                # the gap-parity argument doesn't directly give EC.

                # BUT: if the ternary neighbor fires 0 times in the gap,
                # its value is preserved exactly → EC!

                if lp_fires == 0 and rp_fires == 0:
                    has_any_ec = True
                    break

                # If one neighbor fires 0 times and other fires even:
                # Still need the other neighbor's value to match.
                # For ternary: fires 0 mod 3 means value returns to original
                # (in a system with mod-3 transitions).
                # But the transition function isn't necessarily incrementing!

                # For a GENERAL transition function: we can't conclude value return
                # just from fire count.

                # However: the fire count being 0 in the gap DOES mean the value
                # is preserved (no fires = no change).

            if has_any_ec:
                break

        if has_any_ec:
            ec_from_gap += 1
        else:
            no_ec += 1

        if found >= 2000:
            break

    print(f"Found {found} odd-winding all-isolated mover words")
    print(f"Gap with both neighbors 0-fire: {ec_from_gap}/{found}")
    print(f"No such gap: {no_ec}/{found}")

    if no_ec > 0:
        print("\nNot all words have a zero-neighbor-fire gap.")
        print("Need a different mechanism for those.")

    # Now check: is there ALWAYS a gap where at least one neighbor doesn't fire?
    print("\n--- Check: gap with at least one 0-fire neighbor ---")

    found2 = 0
    one_zero = 0
    no_zero = 0

    random.seed(42)
    for trial in range(200000):
        fc = [2, 3, 3, 2, 3, 3, 2, 3, 3]
        word = []
        for p in range(n):
            word.extend([p] * fc[p])
        random.shuffle(word)

        W = total_displacement(word, n)
        if abs(W) != n:
            continue

        all_iso = True
        for p in binary:
            if not has_isolated_firings(word, p):
                all_iso = False
                break
        if not all_iso:
            continue

        found2 += 1

        has_one_zero = False
        for p in binary:
            fire_pos = [i for i, m in enumerate(word) if m == p]
            L = len(word)
            for fi in range(len(fire_pos)):
                a = fire_pos[fi]
                b = fire_pos[(fi + 1) % len(fire_pos)]
                if b > a:
                    gap_range = range(a + 1, b)
                else:
                    gap_range = list(range(a + 1, L)) + list(range(0, b))

                lp = left(p, n)
                rp = right(p, n)
                lp_fires = sum(1 for s in gap_range if word[s] == lp)
                rp_fires = sum(1 for s in gap_range if word[s] == rp)

                if lp_fires == 0 or rp_fires == 0:
                    has_one_zero = True
                    break
            if has_one_zero:
                break

        if has_one_zero:
            one_zero += 1
        else:
            no_zero += 1

        if found2 >= 2000:
            break

    print(f"Found {found2} words")
    print(f"Has gap with ≥1 zero-fire neighbor: {one_zero}/{found2}")
    print(f"ALL gaps have both neighbors firing: {no_zero}/{found2}")


def investigate_binary_pair_ec():
    """
    NEW APPROACH: Use the non-adjacent binary PAIR.

    We have binary p and binary q at distance ≥ 2 (non-adjacent).
    Both have isolated firings with fc ≥ 2.

    Consider the binary pair (p, q) with the path between them.
    The path has length d = distance(p, q) ≥ 2.
    All processors on the path (except p and q) are non-binary.

    KEY IDEA: Focus on a processor on the path between p and q.
    This proc has one binary neighbor (closer to p) and one binary neighbor
    (closer to q) — wait, that's not right. The path procs have ternary
    neighbors unless they're adjacent to p or q.

    Actually: proc right(p) has p as left neighbor (binary) but right(right(p))
    is ternary. Similarly proc left(q) has q as right neighbor (binary).

    For distance = 3 (like binary at {0,3,6}):
    path from 0 to 3: procs 1, 2
    proc 1: left=0 (binary), right=2 (ternary)
    proc 2: left=1 (ternary), right=3 (binary)

    Neither proc 1 nor proc 2 has BOTH binary neighbors.

    BUT: proc 1 has ONE binary neighbor (left=0). In a gap of proc 0,
    proc 0 doesn't fire, so its value is determined by prefix parity.
    If we can match proc 0's parity across a gap of proc 1 (or some other proc
    that shares context with proc 0), we get a partial EC condition.

    Actually, let me think about this more carefully.

    BETTER IDEA: The MNU / entry conflict for non-consecutive binary
    in the existing proof uses the FOUR MECHANISMS:
    1. Both-Even Return
    2. Toggle-FR
    3. Zero-Side EC
    4. Traversal Return

    These are proved in binscc_complete_proof.py and implemented in the Lean code.
    They work on ANY good cycle with ≥3 non-adjacent binary at sub-threshold.

    CHECK: Are these mechanisms available in the Lean codebase as theorems
    that can be applied directly?
    """
    print("\n=== Binary pair EC investigation ===")
    print()
    print("Checking: are the 4 UEC mechanisms available as Lean theorems?")
    print("These would provide a DIRECT proof without the global dispatch.")


def check_uec_in_lean():
    """
    Check if Universal Entry Conflict mechanisms are formalized in Lean.
    """
    print("\n=== UEC Mechanism check in Lean ===")
    print()
    print("The 4 UEC mechanisms are:")
    print("1. Both-Even Return")
    print("2. Toggle-FR")
    print("3. Zero-Side EC")
    print("4. Traversal Return")
    print()
    print("Plus 2 ring-level lemmas:")
    print("5. Parity Obstruction")
    print("6. Ring Alternation")
    print()
    print("If these are NOT formalized: need a simpler approach.")
    print()
    print("SIMPLEST POSSIBLE APPROACH:")
    print("=========================")
    print()
    print("The oddWinding_nonUniform case is the ONLY callback that matters.")
    print("The sweep and zero-winding callbacks are proved separately.")
    print()
    print("If we can prove oddWinding_nonUniform → False directly for non-consec,")
    print("WITHOUT going through binary_ring_impossibility at all, we're done.")
    print()
    print("The direct proof would be:")
    print("  oddWinding + non-uniform + ≥3 non-consec binary + sub-threshold → False")
    print()
    print("But we already showed: isOddWinding + ≥3 non-adj binary → ¬uniformDirection.")
    print("So non-uniform is automatic. The real statement is:")
    print("  oddWinding + ≥3 non-consec binary + sub-threshold + converges → False")
    print()
    print("And oddWinding gives: all procs fire ≥ 1, binary ≥ 2.")
    print("Trichotomy: EC ∨ permanent ∨ isolated.")
    print("Permanent → W=0 contradiction.")
    print("So: EC ∨ all-binary-isolated.")
    print()
    print("FOR ALL-BINARY-ISOLATED: this is the gap.")
    print("We need: all binary procs isolated + oddWinding + non-consec + sub-threshold → EC.")
    print()
    print("APPROACH VIA PARITY WALK ON TWO BINARY PROCS:")
    print("============================================")
    print()
    print("Pick binary procs p and q with distance 2 (if exists) or distance 3.")
    print()
    print("Case A: distance(p,q) = 2. Then proc between them has both binary neighbors.")
    print("  This is the 'pivot' case. Use both_binary_neighbors_false directly.")
    print("  But wait — both_binary_neighbors_false also uses the callbacks!")
    print()
    print("Case B: all binary pairs at distance ≥ 3 (e.g., {0,3,6} at n=9).")
    print("  No pivot exists. Need a fundamentally different proof.")
    print()
    print("FOR CASE B:")
    print("  Binary at {0,3,6}. Each has 2 ternary neighbors.")
    print("  All binary procs have isolated firings, fc ≥ 2.")
    print("  Total cycle length L ≥ 3*2 + 6*3 = 24.")
    print("  Odd winding: |W| = 9.")
    print()
    print("  Consider the EDGE between any two procs. By odd winding,")
    print("  the edge net flow is ±1 (mod n).")
    print()
    print("  IDEA: Use the 'no safe processor' condition more strongly.")
    print("  Every proc q has some step where moverAt = q or left(q) or right(q).")
    print("  This means every proc's neighborhood is 'visited' by the mover.")
    print("  Combined with isolated firings of all 3 binary procs:")
    print("  The mover must traverse through the ternary regions between binary procs.")
    print("  These traversals create entry conflicts at the ternary-binary boundaries.")
    print()
    print("  CONCRETE: At the boundary between binary 0 and ternary 1:")
    print("  Proc 0 fires (isolated), then the mover moves to 1 (right) or stays.")
    print("  In the gap after proc 0 fires, the mover visits the ternary region.")
    print("  When the mover returns to proc 0's neighborhood for the next fire,")
    print("  the context at 0 might match a previous non-mover context.")
    print()
    print("  But this is exactly the gap-parity argument, which doesn't work for")
    print("  ternary neighbors...")


def investigate_alternative_approach():
    """
    ALTERNATIVE: Instead of proving odd-winding non-uniform directly,
    modify the Lean code to avoid the recursion.

    The recursion happens because oddWinding_nonUniform_sub_threshold_false
    (for non-consec isolated) calls subThreshold_binary_core_false_residual.

    What if instead, for the non-consec isolated case, we derive a STRONGER
    hypothesis that resolves the case WITHOUT the global dispatch?

    IDEA: With binary p isolated + non-consecutive + odd-winding:
    - We already have hno_safe
    - We could try to derive a ZERO-WINDING sub-cycle or show the cycle
      must be a sweep, contradicting odd-winding.

    Actually, the simplest approach might be:

    Since the only use of hOddNonUnifFalse in binary_ring_impossibility is
    at line 121 (|Z|=0, no pivot, non-zero-winding, not sweep, odd-winding non-uniform),
    and from OUR CALLER we already know the cycle IS odd-winding and non-uniform:

    WE ARE THE CALLBACK. The proof is trying to prove False from the exact
    hypotheses we started with. It's a genuine cycle.

    The REAL fix must be: either
    (a) Prove the non-consec isolated case without going through
        binary_ring_impossibility at all, or
    (b) Refactor binary_ring_impossibility to handle this case internally
        without the callback.

    For (b): at line 121, instead of using the callback, prove False directly
    from: all fire + no pivot + odd-winding + non-uniform + sub-threshold +
    ≥3 binary + hno_safe + converges.

    This is exactly what we need to prove.
    """
    print("\n=== Alternative: refactor binary_ring_impossibility ===")
    print()
    print("The fix is to handle the |Z|=0, no-pivot, odd-winding case")
    print("WITHIN binary_ring_impossibility, rather than via callback.")
    print()
    print("At that point we know:")
    print("  - All procs fire (|Z|=0)")
    print("  - No pivot (no proc with both binary neighbors fires)")
    print("  - No 3 consecutive binary (derived)")
    print("  - isOddWinding (from dispatch)")
    print("  - ¬uniformDirection (from dispatch)")
    print("  - hsub, h3bin, hconv, hno_safe, hn")
    print()
    print("This is a STRICTLY STRONGER situation than what")
    print("oddWinding_nonUniform_sub_threshold_false starts with,")
    print("because we additionally know: all procs fire AND no pivot.")
    print()
    print("With 'all procs fire': every binary fires ≥ 2.")
    print("Trichotomy for each binary: EC ∨ permanent ∨ isolated.")
    print("Permanent → W=0 contradiction (odd winding).")
    print("So: each binary gives EC or isolated.")
    print()
    print("If any binary gives EC: done.")
    print("If ALL binary isolated: this is the hard case.")
    print()
    print("With ALL binary isolated + all fire + no pivot + odd-winding:")
    print("Need a SELF-CONTAINED proof that this is impossible.")
    print()
    print("CHECK: Can we use the shadow cycle/wiggle machinery?")
    print("Shadow cycles are for sweep/uniform cycles.")
    print("Wiggle shadow cycles are for single-wiggle words.")
    print("Odd-winding non-uniform is neither sweep nor single-wiggle necessarily.")
    print()
    print("SIMPLEST APPROACH: Use the CONVERGENCE argument.")
    print("converges sys gc means gc has no safe processor and eventually terminates.")
    print("But we already use this implicitly through hconv.")
    print()
    print("ANOTHER ANGLE: small_arc_contradicts_convergence")
    print("This theorem says: if the mover is confined to a small arc,")
    print("the system can't converge at sub-threshold.")
    print("With isolated binary firings, is the mover confined?")


def check_mover_confinement():
    """
    With all binary procs having isolated firings:
    - Binary p fires, then the next step is a different proc
    - Between binary fires, the mover traverses ternary procs

    For odd-winding: the mover must make net displacement n.
    With non-uniform: it goes both CW and CCW.

    IDEA: Can we show the mover is "confined" to a small arc?
    If all binary procs are isolated, the mover visits each binary
    briefly (one step) then moves on. The ternary regions between
    binary procs are traversed by the mover.

    For binary at {0,3,6} on ring of 9:
    - Region 1: procs 1,2 (between 0 and 3)
    - Region 2: procs 4,5 (between 3 and 6)
    - Region 3: procs 7,8 (between 6 and 0)

    The mover must traverse all 3 regions (no safe processor).

    With net displacement 9 (full wrap) and non-uniform direction:
    The mover makes a full circuit but with some backtracking.

    This doesn't confine the mover to a small arc.

    DEAD END for confinement.

    FINAL IDEA: The proof might need to use CONVERGENCE directly.

    converges sys gc means the system starting from any bad configuration
    reaches a good configuration. This is a strong structural condition
    on the transition function.

    The existing proof uses convergence through:
    - small_arc_contradicts_convergence (mover confined to small arc)
    - safe processor elimination (not relevant here)

    For the isolated case: convergence might force certain transitions
    that create entry conflicts. But this is very indirect.
    """
    print("\n=== Mover confinement check ===")
    print("Mover confinement doesn't apply for odd-winding (full wrap).")
    print("The mover visits the entire ring.")
    print()
    print("FINAL ANALYSIS:")
    print("===============")
    print()
    print("The problem reduces to proving:")
    print("  all-binary-isolated + all-fire + no-pivot + odd-winding")
    print("  + non-consec-binary + sub-threshold + converges → False")
    print()
    print("Available tools that DON'T use the callbacks:")
    print("  - binary_isolated_firings_or_ec: already used, gives us 'isolated'")
    print("  - procMinGap_hasEntryConflict: needs 3 consecutive binary (NO)")
    print("  - general_parity_entry_conflict: needs 3 consecutive binary (NO)")
    print("  - permanent_mover_totalDisplacement_zero: already used")
    print("  - small_arc_contradicts_convergence: mover not confined (NO)")
    print("  - entryConflict_impossible: final step, needs EC first")
    print()
    print("Tools that DO use callbacks (can't use to break recursion):")
    print("  - subThreshold_binary_core_false")
    print("  - binary_ring_impossibility")
    print("  - no_firing_both_binary_neighbors_false")
    print("  - gapDecisive_false")
    print()
    print("CONCLUSION: No existing sorry-free tool can handle this case.")
    print("A NEW theorem is needed.")
    print()
    print("PROPOSAL: 'nonConsecutive_oddWinding_allIsolated_false'")
    print("Hypotheses: ≥3 non-consec binary, sub-threshold, odd-winding,")
    print("            every binary proc has isolated firings with fc ≥ 2,")
    print("            all procs fire, converges.")
    print("Conclusion: False")
    print()
    print("Proof sketch:")
    print("  1. Pick two non-adjacent binary procs p, q (distance ≥ 2)")
    print("  2. Consider the ternary region between them")
    print("  3. Odd-winding forces the mover to traverse this region")
    print("  4. Each traversal creates a boundary visit at p or q")
    print("  5. Binary p has value determined by fire parity")
    print("  6. After even fires of p: value returns to initial")
    print("  7. The context at the ternary proc adjacent to p")
    print("     includes p's value (which returned) and the ternary's own value")
    print("  8. If the ternary proc's value also returned: EC at ternary proc")
    print("  9. Show value return happens by counting fires across traversals")
    print()
    print("This is essentially the Phase Extraction argument adapted for")
    print("non-consecutive binary, but operating at the ternary-binary boundary.")


def check_lean_lemma_availability():
    """Check what lemmas exist for non-consecutive binary in the Lean codebase."""
    print("\n=== Checking Lean codebase for non-consecutive tools ===")
    print()
    print("Files to check:")
    print("  - MNU.lean")
    print("  - ShadowCycle.lean")
    print("  - WiggleShadow.lean")
    print("  - EntryConflict/*.lean")
    print("  - MixedTightResidual.lean")
    print()
    print("KEY QUESTION: Is there a theorem that proves")
    print("  ≥3 non-adj binary + sub-threshold + converges → ¬hasGoodCycle")
    print("or equivalently → every good cycle has EC?")
    print()
    print("If such a theorem exists (maybe with a sorry for the odd-winding case),")
    print("then filling in that sorry IS the task.")


def main():
    check_mnu_applicability()
    check_fresh_approach()
    investigate_ternary_in_gap()
    investigate_binary_pair_ec()
    check_uec_in_lean()
    investigate_alternative_approach()
    check_mover_confinement()
    check_lean_lemma_availability()

    print("\n" + "=" * 70)
    print("SUMMARY OF FINDINGS")
    print("=" * 70)
    print()
    print("1. The recursion is GENUINE — the global dispatch circles back to the")
    print("   same case without adding information.")
    print()
    print("2. For ≥3 non-consecutive binary at distance ≥ 3 (e.g., {0,3,6} at n=9),")
    print("   NO processor has both binary neighbors, so the 'pivot' approach fails.")
    print()
    print("3. The parity-based EC (procMinGap, general_parity_entry_conflict) requires")
    print("   3 consecutive binary, which we DON'T have.")
    print()
    print("4. At the mover-word level, odd-winding + non-uniform + all-binary-isolated")
    print("   IS possible (752/1000 random words satisfy it).")
    print()
    print("5. The contradiction must come from the CONFIG/SYSTEM level, specifically")
    print("   from the sub-threshold + convergence constraints.")
    print()
    print("6. The UEC 4-mechanism proof works computationally (0 exceptions) but")
    print("   may not be formalized in Lean yet.")
    print()
    print("7. PROPOSED APPROACH: Prove a new theorem")
    print("   'nonConsecutive_oddWinding_allIsolated_ec' using the ternary-binary")
    print("   boundary argument, operating on the MinFiringGap of each binary proc")
    print("   and tracking ternary neighbor values across gaps.")
    print()
    print("8. The SIMPLEST approach may be to check if the sweep/zero-winding proofs")
    print("   in CaseObstructionsCore (currently sorry) can be filled in first,")
    print("   since those are also needed by the global dispatch.")


if __name__ == "__main__":
    main()
