"""
Cross-Phase EC: Edge case and cyclic wrap verification.
"""


def verify_cyclic_edge_case():
    """
    Edge case: what if the one-sided phase wraps around the cycle boundary?

    Phase from step a to step s where s < a (cyclic wrap).
    Interior: [a+1, CL) union [0, s).

    Step a+1 (mod CL): bL fires.
    Step a+2 (mod CL): far proc fires.
    Step s: t fires.

    The value preservation argument still works:
    - configVal_eq_of_noFire_between works on [a+2, s) (mod CL)
    - But in the Lean formalization, we'd need the cyclic version:
      configVal_eq_of_cyclic_noFire (proved in cyclic_phase_proof_FINAL)

    However: the Lean proof at AllNormalFormFalse2.lean works with
    the ACYCLIC version. The phases are defined using TernaryPhase
    which has a.val < s.val (linear ordering). The cyclic wrap is
    handled separately by the phase extraction infrastructure.

    So for the Lean formalization: we can always find a phase with
    length >= 2 that is NON-wrapping (a < s with s - a - 1 >= 2).
    This is because fc(t) >= 4, so there are at least 4 phases in the
    cycle, and the wrapping phase is at most 1. So at least 3 are
    non-wrapping. Among those 3, at least 1 has length >= 2 by the
    counting argument.

    Actually: the t-fire steps partition [0, CL) into fc(t) intervals.
    At most 1 wraps around. The rest are linear (a < s). Sum of lengths
    of non-wrapping phases >= sum - CL >= (CL - fc(t)) - (CL - fc(t) + 1)?

    Simpler: just use the configVal_eq_of_cyclic_noFire lemma for the
    general case. OR: pick any non-wrapping phase with length >= 2.
    Since there are >= 3 non-wrapping phases (fc(t) >= 4, at most 1 wraps),
    and their total length >= CL - fc(t) - CL/fc(t) (subtracting the wrap
    phase), some has length >= 2.

    Even simpler: fc(t) phases, total length CL - fc(t), at most 1 wrapping.
    Non-wrapping count >= fc(t) - 1 >= 3.
    Non-wrapping total length >= CL - fc(t) - (phase_max_length).
    But we don't need the exact bound. The pigeonhole already works on
    ALL phases (wrapping or not). The EC construction works for wrapping
    phases too, using the cyclic value preservation lemma.

    Bottom line: no edge case issues. The proof is clean.
    """
    print("CYCLIC EDGE CASE VERIFICATION")
    print("=" * 60)

    # Verify: with fc(t) >= 4, there exist non-wrapping phases with length >= 2
    for n in range(4, 15):
        for fc_t in range(4, 4 * n):
            # CL >= 2*fc_t + 2(n-3)
            for CL in range(max(2*n, fc_t+1), 8*n):
                if CL - 2*fc_t < 2*(n-3):
                    continue

                sum_lengths = CL - fc_t
                # At most 1 wrapping phase. Non-wrap count >= fc_t - 1.
                # Non-wrap total >= sum_lengths - CL  [wrap phase <= CL - 1]
                # Actually worst case: wrap phase has length (CL - fc_t) - (fc_t - 1)
                # when all other phases have length 1.
                # But we already know sum > fc_t, so not all can have length 1.

                # The key point: even INCLUDING wrapping, average length > 1.
                avg = sum_lengths / fc_t
                if avg <= 1:
                    print(f"  FAIL: n={n}, fc_t={fc_t}, CL={CL}, avg={avg:.2f}")
                    return False

    print("  All parameter combinations: average phase length > 1.")
    print("  Confirms some phase (wrapping or not) has length >= 2.")
    return True


def verify_nonmover_at_a_plus_2():
    """
    Verify: at step a+2, the mover is NOT t.

    In the phase from a to s:
    - Step a: t fires.
    - Step a+1: bL fires (J=1 in this phase).
    - Step a+2: some proc fires, and it's NOT t (t doesn't fire until step s).

    This is guaranteed by the phase definition: t doesn't fire in
    (a, s) = {a+1, a+2, ..., s-1}. Since a+2 < s (length >= 2),
    step a+2 is in the interior, so mover(a+2) != t.

    But: what if step a+2 fires bL or bR?
    In a J=1, K=0 phase: bL fires exactly once (at step a+1).
    So mover(a+2) != bL. And K=0 means bR doesn't fire at all.
    So mover(a+2) is a far proc. Good.
    """
    print("\nNONMOVER VERIFICATION AT STEP a+2")
    print("=" * 60)
    print("  Step a+2 is in the interior (a+1, s) since length >= 2.")
    print("  => mover(a+2) != t  (t doesn't fire in interior)")
    print("  => t is nonmover at step a+2. CONFIRMED.")
    print()
    print("  Also: mover(a+2) != bL  (J=1 exhausted at step a+1)")
    print("  Also: mover(a+2) != bR  (K=0)")
    print("  => mover(a+2) is a far proc (distance >= 2 from t).")


def verify_binary_fire_position():
    """
    Subtle point: in a one-sided phase J=1, K=0, is the single bL fire
    necessarily at step a+1 (the first interior step)?

    Answer: NOT necessarily in general. The bL fire could be at any
    interior step. BUT: for the EC argument, we just need ONE interior
    step (after the bL fire) where t is nonmover, before step s.

    If bL fires at step a+j (1 <= j <= len-1):
    Then steps a+j+1, ..., s-1 have no {bL, t, bR} fires.
    If j <= len-2 (i.e., a+j+1 exists before s):
      Triple at t constant from a+j+1 to s. EC at step a+j+1 vs step s.

    What if j = len-1 (bL fires at the very last interior step, s-1)?
    Then there's no step between bL fire and t fire.
    Triple at step s: (bL_after_fire, t_val, bR_val).
    But we need a nonmover step with the same triple. The step before
    the bL fire (s-2 or some earlier step) has bL at its PRE-fire value.
    So triple = (bL_before, t_val, bR_val) != (bL_after, t_val, bR_val)
    unless bL_before = bL_after. But bL is binary and fires, so bL_after != bL_before.

    So the bL fire at step s-1 case DOES NOT give EC from this argument.

    HOWEVER: we can use a DIFFERENT interior step. Step a+1 (first interior
    step). If bL doesn't fire at a+1: then from step a+1 to the bL fire,
    bL is constant. And from step a+1 to s: t and bR don't fire.
    But bL's value at a+1 = bL's value before fire = bL's value at step a.
    And at step s: bL's value = post-fire value. Different. So triple differs.

    The issue: if bL fires at step s-1 (last interior step), we DON'T get
    EC from the simple constant-triple argument.

    WAIT: Let me reconsider. The phase has length >= 2 and J=1, K=0.
    Interior has >= 2 steps. One of them fires bL.

    Case A: bL fires at step a+1 (first interior step).
      Then steps a+2, ..., s-1, s have constant triple. a+2 exists (len >= 2).
      EC: step a+2 (nonmover) vs step s (mover).

    Case B: bL fires at step a+j, j >= 2 (not the first).
      Then steps a+1, ..., a+j-1 have bL at pre-fire value. Steps a+j+1, ..., s
      have bL at post-fire value.

      Sub-case B1: j <= len - 2. Step a+j+1 exists before s.
        Triple at a+j+1 = triple at s. EC.

      Sub-case B2: j = len - 1. bL fires at step s-1.
        Steps a+1, ..., s-2 have bL at pre-fire value.
        Step s has bL at post-fire value.
        Pre != post (binary, fires). No constant-triple window spanning
        a nonmover and s.

        BUT: can we use step a (t fires) instead? At step a: t is mover.
        At step a+1: t is nonmover. Triple at a+1 = (bL_pre, t_val, bR_val).
        Triple at a: (bL_at_a, t_val_before_fire, bR_val). But t fires at a,
        so t_val at step a is the PRE-fire value, not the in-phase value.
        Hmm, this doesn't work directly.

        ALTERNATIVE for B2: look at step a+1 (nonmover for t) and step a (mover for t).
        At step a: t fires. Triple = (bL_pre, t_pre_val, bR_val). t_pre_val != t_val (t fires).
        At step a+1: t nonmover. Triple = (bL_pre, t_val, bR_val).
        Different t values. No EC.

        ALTERNATIVE for B2: look BACKWARDS at the previous phase.
        In the previous phase ending at step a: some steps have bL at the
        SAME post-fire value as step s. Cross-phase EC.

        Actually, let me think about this differently.

    THE FIX: We don't need the binary fire to be at step a+1. We need
    TWO steps after the binary fire, both before step s.

    Length >= 2 AND bL fires NOT at the last interior step => EC.
    Length >= 3 OR (length >= 2 AND bL fires at first interior step) => EC.

    Can ALL one-sided phases have their binary fire at the last interior step?

    Phase i: interior has steps a_i+1, ..., s_i-1. Length = s_i - a_i - 1.
    If bL fires at s_i - 1 (last step), then bL fires just before t fires at s_i.

    This is a very specific pattern: bL fires, then immediately t fires.

    Under the existing normalForm infrastructure, can we exclude this?

    ACTUALLY: I realize this IS handled. The normalForm condition says
    isNormalFormGap for each TernaryPhase. Let me check what normalForm means.
    """
    print("\nBINARY FIRE POSITION ANALYSIS")
    print("=" * 60)

    print("  Issue: in one-sided phase J=1, K=0, length >= 2,")
    print("  the binary fire might be at the LAST interior step (s-1).")
    print("  In that case, no constant-triple window exists between")
    print("  the binary fire and the t-fire at step s.")
    print()
    print("  Two fixes:")
    print("  (1) Show binary fire is NOT at the last step (from normalForm)")
    print("  (2) If length >= 3: even if binary fire is at s-1, the")
    print("      PRE-fire window [a+1, s-2] has constant triple at t")
    print("      (pre-fire bL value). Then EC between step a+1 and step a.")
    print("      WAIT: step a fires t, and step a+1 has t nonmover.")
    print("      Triple at a: (bL_pre, t_PRE, bR) where t_PRE is t before fire.")
    print("      Triple at a+1: (bL_pre, t_POST, bR) where t_POST is t after fire.")
    print("      These differ in the S component. Not an EC.")
    print()
    print("  Fix (2) fails. We need fix (1) or another approach.")
    print()
    print("  CORRECT FIX: in a one-sided phase J=1, K=0, length >= 2:")
    print("  If bL fires at step a+j where j >= 2:")
    print("    Steps a+1, ..., a+j-1 have triple (bL_pre, t_val, bR_val).")
    print("    Step a fires t. At step a: triple = (bL_pre, t_pre, bR_val).")
    print("    But t changed: t_pre != t_val. NOT an EC at step a.")
    print("    However: the PREVIOUS phase's t-fire step (call it a_prev)")
    print("    has: step a_prev fires t. Triple at a_prev: (bL_?, t_val_at_a_prev, bR_?).")
    print("    Different context in general.")
    print()
    print("  THIS IS MORE SUBTLE. Let me re-examine the argument.")


def verify_binary_fire_is_first():
    """
    CLAIM: In a one-sided phase with normalForm, the single binary fire
    is at the FIRST interior step.

    Phase from step a (t fires) to step s (t fires next).
    Interior: a+1, a+2, ..., s-1.
    J=1, K=0. One bL fire in the interior.

    Under normalForm: the phase structure constrains the order of fires.

    Actually, normalForm says:
    isNormalFormGap gc t phase means the phase is NOT isMechanismTriggering.
    This doesn't directly constrain the position of the binary fire.

    BUT: in the Lean code, the phase is TernaryPhase from a' to s where
    a' is the first interior step (not the t-fire step a). The normalForm
    condition constrains J+K <= 1.

    The POSITION of the binary fire within the interior is NOT constrained
    by normalForm. It could be anywhere.

    So: we need to handle the case where bL fires at the last interior step.

    REVISED ARGUMENT:

    In a one-sided phase J=1, K=0, length L >= 2:
    bL fires at step a+j for some 1 <= j <= L.

    Case 1: j <= L-1 (not the last step).
      Steps a+j+1, ..., s have constant triple. Step a+j+1 is nonmover
      for t. Step s is mover for t. EC.

    Case 2: j = L (last interior step = s-1).
      bL fires at step s-1, then t fires at step s.
      No constant-triple window after the bL fire.

      BUT: steps a+1, ..., s-2 have CONSTANT triple at t:
        (bL_PRE, t_val, bR_val)
      where bL_PRE is bL's value before it fires.

      At step a: t fires. After t fires, t has value t_val.
      Step a's CONFIG has t = t_val (the value AFTER the fire at step a?
      No: step a's config is the config BEFORE the fire. After the fire,
      we get step a+1's config.)

      Wait, in the Lean formalization:
      configs.get(k) is the config at step k.
      moverAt(k) is who fires at step k.
      configs.get(k+1) is the result after firing.

      So: configs.get(a) is the config BEFORE t fires at step a.
      configs.get(a+1) is the config AFTER t fires at step a.
      configs.get(a+1).t = new t value (t_val).
      configs.get(a+2).t = t_val (t doesn't fire at a+1).

      At step s: configs.get(s).t = t_val (t hasn't fired since step a).
      t fires at step s. moverAt(s) = t.

      Triple at step s: (configs.get(s).bL, configs.get(s).t, configs.get(s).bR)
        = (bL_POST, t_val, bR_val)
      where bL_POST = bL value after firing at step s-1 = step a+L.

      Triple at step a+1: (configs.get(a+1).bL, configs.get(a+1).t, configs.get(a+1).bR)
        = (bL_PRE, t_val, bR_val)
      where bL_PRE = bL value before it fires (bL hasn't fired yet at a+1).

      bL_PRE != bL_POST (binary, fires once). So triples differ. No EC
      between step a+1 and step s.

      HOWEVER: we can use the LAST step before the bL fire and the FIRST
      step after the bL fire:
      - Step s-2 (last before bL fire): triple = (bL_PRE, t_val, bR_val)
      - Step s (first after bL fire, t fires): triple = (bL_POST, t_val, bR_val)
      Different L values. No EC here either.

      So Case 2 genuinely doesn't give EC from the constant-triple argument.

      NEED DIFFERENT APPROACH FOR CASE 2.
    """
    print("\nVERIFYING: Is the binary fire always first?")
    print("=" * 60)
    print("  Answer: NO. The binary fire position is unconstrained by normalForm.")
    print("  Case 2 (binary fires last) needs separate handling.")
    print()
    print("  SOLUTION: Use pigeonhole more carefully.")
    print("  If phase has length >= 2: there are >= 2 interior steps.")
    print("  One fires bL. At least 1 fires a far proc.")
    print("  If the far proc fires AFTER bL: steps after bL fire have")
    print("  constant triple. EC.")
    print("  If the far proc fires BEFORE bL: the far proc step and the")
    print("  PREVIOUS t-fire's mover step might give cross-phase EC.")
    print()
    print("  Actually, we need length >= 3 to guarantee a step after bL")
    print("  that is not step s:")
    print("  Length 2: 2 interior steps. One is bL fire. One is far fire.")
    print("  If bL first: far is at a+2. Triple at a+2 = triple at s. EC.")
    print("  If far first: bL at a+2 = s-1. Step s has post-fire bL. No EC.")
    print()
    print("  So length >= 2 is NOT sufficient if binary fires last.")
    print("  But length >= 3 IS sufficient: at least 2 steps after bL or")
    print("  at least 1 step after bL that is not step s.")
    print()
    print("  Actually even length 2 with far-first is fine:")
    print("  Step a+1: far fires. Step a+2 = s-1: bL fires. Step s: t fires.")
    print("  Triple at a+1: (bL_PRE, t_val, bR_val). t is nonmover.")
    print("  Triple at s: (bL_POST, t_val, bR_val). t is mover.")
    print("  bL_PRE != bL_POST. No EC from step a+1 vs step s.")
    print()
    print("  But: triple at a+1 matches triple at a+2 (before bL fires)?")
    print("  Step a+1: (bL_PRE, t_val, bR_val). t nonmover.")
    print("  Step a+2: (bL_PRE, t_val, bR_val). bL fires, but config is")
    print("  BEFORE the fire. So same triple. But mover(a+2) = bL, not t.")
    print("  t is nonmover at BOTH a+1 and a+2. No EC (need mover+nonmover).")
    print()
    print("  CONCLUSION: length 2 is NOT sufficient if binary fires second.")
    print("  Need length >= 3 for guaranteed EC, or binary-fires-first.")


def compute_length_distribution():
    """
    Given that some phases might have length 2 with binary-fires-last,
    do we always have SOME phase with either:
      (a) length >= 3, or
      (b) length >= 2 with binary fires first?

    Total interior steps = CL - fc(t) >= fc(t) + 2(n-3).
    fc(t) phases, each length >= 1 (has the binary fire).
    Excess = CL - fc(t) - fc(t) = CL - 2*fc(t) >= 2(n-3) >= 2 for n >= 4.

    Excess of 2 means sum of (len_i - 1) >= 2.
    So at least 2 phases have length >= 2, or 1 phase has length >= 3.

    If 2 phases have length exactly 2 and binary fires last in both:
    Then those 2 phases each have pattern [far, bL_fire].
    The remaining phases have length 1 each (just the binary fire).

    But: sum of lengths = CL - fc(t) >= fc(t) + 2(n-3).
    With fc(t) - 2 phases of length 1 and 2 phases of length 2:
    sum = (fc(t) - 2) + 4 = fc(t) + 2.
    Need fc(t) + 2 >= fc(t) + 2(n-3). So 2 >= 2(n-3). n <= 4.

    For n >= 5: 2(n-3) >= 4 > 2. So sum >= fc(t) + 4.
    Not all can be length 1 or 2. Some phase has length >= 3!

    With length >= 3: at least 3 interior steps. 1 fires bL.
    At least 2 are far fires. If bL fires at step j:
    - If j < len: step j+1 exists, has constant triple. EC.
    - If j = len: bL fires last. But there are 2+ far fires before it.
      Steps a+1, ..., a+j-1 have constant triple (bL_PRE, t_val, bR_val).
      Step a has moverAt = t. Step a+1 has moverAt = far proc (nonmover for t).
      Triple at a: (bL_PRE, t_PREVAL, bR_val). t_PREVAL != t_val. NO EC.
      Triple at a+1: (bL_PRE, t_val, bR_val). t nonmover.

      WAIT: but we need a MOVER step for t with the same triple.
      Step s: triple = (bL_POST, t_val, bR_val). bL_POST != bL_PRE. NO.

      Hmm. Even with length >= 3, if bL fires at the very last step,
      we don't get EC from the constant-triple-at-t argument.

    I think I need to reconsider the approach entirely.
    """
    print("\nLENGTH DISTRIBUTION ANALYSIS")
    print("=" * 60)

    for n in range(4, 15):
        min_excess = 2 * (n - 3)
        print(f"  n={n}: min excess = {min_excess}")
        if min_excess <= 2:
            print(f"    Some phases might all be length <= 2")
        else:
            print(f"    Some phase has length >= 3")
            print(f"    But binary-fires-last still an issue at length 3!")

    print()
    print("  CRITICAL INSIGHT: binary-fires-last at ANY length blocks")
    print("  the simple constant-triple EC argument.")
    print("  Need a DIFFERENT approach for this case.")


def revised_approach():
    """
    REVISED APPROACH: Handle binary-fires-last separately.

    In a one-sided phase J=1, K=0 with length L:
    bL fires at interior step a+j (1 <= j <= L).

    Case A (j <= L-1): steps a+j+1, ..., s exist before next t-fire.
      After bL fires: triple at t is constant. EC between step a+j+1 and step s.

    Case B (j = L): bL fires at step s-1 (last interior step).
      No step after bL fire before t fires.

    For Case B: use the PREVIOUS phase's structure.
    Previous phase ends at step a (t fires). In the previous phase,
    the bL/bR fire pattern determines configs around step a.

    Actually, here's a simpler and CORRECT approach:

    APPROACH: Use bothEvenReturn_ec on the extended window.

    In any one-sided phase, the binary fire of bL toggles bL once (odd).
    The NEXT one-sided phase with J=1 toggles bL again. After 2 phases:
    bL has been toggled twice (even). Same for bR if K phases exist.

    Over the PAIR of phases: bL fires 2 times (even) and bR fires 0 times (even).
    bothEvenReturn_ec applies to the combined window!

    Window: from step a₁ (nonmover for t, just after first t-fire)
    through 2 consecutive phases to step s₂ (second t-fire).

    This is the cross-phase EC approach: combine 2 one-sided phases.

    Number of bL-sided phases: fc(bL) (each contributes J=1 for bL).
    Number of bR-sided phases: fc(bR) (each contributes K=1 for bR).
    fc(bL) >= 2 (binary fires even, >= 2).

    Take any 2 consecutive bL-sided phases. Between them: some bR-sided phases.
    In each bR-sided phase: bR fires once. Total bR fires between the 2
    bL-phases: some number. Total bL fires: 2 (one per bL-phase).

    Hmm, this is getting complicated. Let me think about what's simpler.

    SIMPLEST CORRECT APPROACH:

    Across ALL fc(t) phases: bL fires fc(bL) times and bR fires fc(bR) times.
    fc(bL) is even, fc(bR) is even (binary parity).

    Take the FULL cycle. Step 0: some mover. Step CL-1: wraps back.
    bothEvenReturn_ec needs a nonmover step a and a mover step s with
    a < s, t doesn't fire in [a, s), and bL and bR fire even times in [a, s).

    Can we find such (a, s)? Yes: take ANY t-fire step s. Let a be the
    step just after the PREVIOUS t-fire (so a = prev_t_fire + 1). Then
    t doesn't fire in [a, s). And bL+bR fire J+K = 1 times (one-sided phase).
    That's ODD. So bothEvenReturn_ec doesn't directly apply.

    What about 2 consecutive phases? Take a = prev_t_fire + 1 and s = next_next_t_fire.
    Then t fires once in [a, s) (at the intermediate t-fire step). So t DOES
    fire in [a, s). Can't use configVal_eq_of_noFire_between for t.

    Hmm. The issue is that t fires at phase boundaries.

    REAL SIMPLEST APPROACH:

    I was overcomplicating this. Let me re-read my original argument.

    In the original argument, the key claim was:
    "Step a+1: bL fires. Steps a+2 to s-1: only far procs fire."

    This IMPLICITLY assumed the binary fire is at step a+1. But actually
    it could be anywhere in the interior.

    The fix: REORDER. Instead of looking at the phase starting from the
    t-fire, look at the phase starting from the BINARY FIRE.

    From step a+j (bL fires) to step s (t fires):
    Steps a+j+1, ..., s-1: no {bL, t, bR} fires.
    Length of this window: s - (a+j) - 1 = L - j.

    If j < L: window has length >= 1. Step a+j+1 is nonmover for t.
    Step s is mover for t. Triple at t constant in [a+j+1, s]. EC.

    If j = L: window has length 0. No step between bL fire and t fire.

    So: if in SOME one-sided phase, the binary fire is not the last step:
    EC follows.

    Can ALL one-sided phases have binary-fires-last?

    Binary-fires-last means: moverAt(s-1) = bL (or bR), moverAt(s) = t.
    So bL fires immediately before t. In every phase.

    This is a very specific constraint. Does normalForm rule it out?
    Not directly.

    But: if bL fires at step s-1 and t fires at step s, then
    configs.get(s).bL = flipped value. The NEXT phase starts with this
    flipped value. If the next phase also has binary-fires-last, then
    bL fires at step s'-1 where s' is the next t-fire.

    Between step s and step s'-1: no bL fires (J=1 per phase, and the
    single fire is at s'-1). bL's value is constant: the flipped value
    from step s.

    Between step s-1 (bL fires) and step s'-1 (bL fires next):
    bL fires at s-1, then has constant value until s'-1, then fires again.
    bL toggles twice: back to original. Even number of fires over 2 phases.

    Hmm, the binary-fires-last pattern across consecutive phases creates
    a very constrained structure. But I don't see an immediate contradiction.

    DIFFERENT APPROACH: use fc count more carefully.

    Observation: bL fires fc(bL) times total, at positions spread across
    fc(bL) one-sided phases (one fire per bL-phase). bL toggles each time.
    After fc(bL) toggles: bL returns to original (fc(bL) even).

    Similarly for bR. Total fires at bL-phases + bR-phases = fc(t).
    fc(bL) + fc(bR) = fc(t). Both even. fc(t) even.

    Now: look at the cycle from the perspective of bL's VALUE at step s
    (just before each t-fire). Since bL toggles in each bL-phase and
    doesn't fire in bR-phases:

    At each bL-phase: bL's value at step s (the t-fire) is the post-toggle value.
    At each bR-phase: bL's value at step s is unchanged from the previous phase.

    If binary-fires-last in ALL bL-phases: at each t-fire step s, the
    config just saw bL toggle at step s-1. So bL's value at step s is fresh.

    Hmm, this is getting complicated. Let me try a completely different approach.

    APPROACH C: Look at step s-1 (bL fires) as a NONMOVER for t.
    Step s-1: bL fires, so moverAt(s-1) = bL. t is nonmover.
    Triple at t at step s-1: (bL_BEFORE_FIRE, t_val, bR_val).

    Step s: t fires, so moverAt(s) = t.
    Triple at t at step s: (bL_AFTER_FIRE, t_val, bR_val).

    bL_BEFORE != bL_AFTER (binary, fires). Different triples. No EC.

    APPROACH D: Look at the MOVER step s and NONMOVER step a.
    Step a: moverAt(a) = t. NOT nonmover. Can't use.

    APPROACH E: USE TWO PHASES.

    Phase i: t fires at step a_i, bL fires at step a_i + j_i (possibly last).
    Phase i+1: t fires at step a_{i+1} = s_i, bL fires at step a_{i+1} + j_{i+1}.

    Consider the window from step a_i + 1 to step a_{i+1} + j_{i+1}.
    In this window:
    - t fires once (at step s_i = a_{i+1}). Not a t-free window.

    Consider instead: step a_{i+1} + 1 (just after second t-fire) to
    step a_{i+2} (third t-fire).
    Wait, this is just phase i+1's interior again.

    I think the CORRECT approach is:

    CLAIM: Not all one-sided phases can have binary-fires-last.

    Consider a bL-phase where bL fires at step s-1. At step s: t fires
    with bL = post-toggle. At step s+1 (next phase interior start):
    bL has its post-toggle value.

    In the NEXT phase (s to s'): if it's a bR-phase (K=1, J=0), bL
    doesn't fire. bL's value at step s' = bL's post-toggle value from
    the previous phase.

    In the next bL-phase after that: bL fires again. If binary-fires-last:
    bL fires at step s''-1. From step s to step s''-1: bL doesn't fire.
    bL's value is constant = post-toggle from the first phase.
    At step s''-1: bL fires. New value = toggled again = original.
    At step s'': t fires with bL = original value.

    So: alternating bL values at t-fire steps (post-toggle, then after
    2 bL-phases, back to original).

    After fc(bL) bL-phases: bL back to original (fc(bL) even). Consistent.

    This doesn't give a contradiction by itself.

    APPROACH F (THE ONE THAT WORKS):

    Go back to the original argument but handle the binary-fires-last case
    by using the value BEFORE the binary fire.

    In a one-sided phase J=1, K=0, with bL firing at step a+j:

    Window [a+1, a+j): no bL, bR, or t fires (bL hasn't fired yet, t
    doesn't fire in interior, K=0). If j >= 2:
      Triple at t constant in [a+1, a+j).
      Triple at step a+1: (bL_PRE, t_val, bR_val). t is nonmover.

      But we need a MOVER step with the same triple. The mover step
      should be a t-fire. The PREVIOUS t-fire is at step a.
      Triple at step a: (bL_PRE?, t_PRE_VAL, bR_val).

      At step a: configs.get(a) has t = t_PRE_VAL (before t fires).
      t_PRE_VAL != t_val (t fires, changes value). No EC between a and a+1.

      NEXT t-fire is step s. Triple at s: (bL_POST, t_val, bR_val).
      bL_POST != bL_PRE (bL fired at a+j). No EC between a+1 and s.

      Hmm. No good mover step with triple (bL_PRE, t_val, bR_val).
      The NEXT time t fires after the pre-fire-bL region is step s,
      where bL has already been toggled.

      UNLESS: in some OTHER phase, t fires with bL = bL_PRE.

      Since bL toggles in each bL-phase: if there are fc(bL) bL-phases
      and fc(bL) is even, then exactly fc(bL)/2 have bL_POST and
      fc(bL)/2 have bL_PRE at the t-fire step.

      In a bL-phase with binary-fires-last: t-fire step sees bL_POST.
      In a bL-phase with binary-fires-first: t-fire step sees bL_POST.

      WAIT: in ALL cases, the t-fire step s is AFTER the bL fire in that
      phase. So configs.get(s).bL = bL after the fire = bL_POST. Always.

      In a bR-phase (J=0, K=1): bL doesn't fire. configs.get(s).bL = same
      as at the start of the phase = bL value inherited from the previous
      phase's end.

      So: at t-fire steps, bL alternates between post-toggle values.
      Since bL toggles fc(bL) times and fc(bL) is even, it cycles back.

    I think this analysis is getting too complicated for the pure
    constant-triple approach. Let me try a COMPLETELY DIFFERENT argument.

    APPROACH G (COUNTING EC):

    Instead of looking at constant-triple windows, use the PIGEON-HOLE
    on the TRIPLE VALUES themselves.

    Proc t has 2 * 3 * 2 = 12 possible (L, S, R) triples (bL binary, t
    ternary, bR binary). At step s (t fires): this triple is a MOVER triple.
    At other steps: NONMOVER triple.

    The cycle visits CL steps. At fc(t) of them, t is mover. At CL - fc(t),
    t is nonmover. If some mover triple equals some nonmover triple: EC.

    fc(t) mover triples from 12 possible. CL - fc(t) nonmover triples from 12.
    If fc(t) > 12 or CL - fc(t) > 12: pigeonhole gives repeated triples
    within mover or nonmover, but not necessarily cross-set.

    What if ALL 12 triples appear as mover triples? Then any nonmover step
    also has one of the 12 triples: EC.

    fc(t) >= 4 and at most 12 distinct mover triples. But fc(t) could be
    4 with 4 distinct triples. CL - fc(t) could have triples from the
    remaining 8. No forced EC from counting alone at small fc(t).

    For large n: CL >= 2n >> 12. So CL - fc(t) >> 12. Many nonmover
    triples, only 12 possible. Many repeats. But we need cross-set match.

    If fc(t) >= 7: at least 7 mover triples from 12. Nonmover has
    CL - fc(t) >= 12 or more triples from 12. By pigeonhole on the
    complement: at most 5 nonmover-only triples. But CL - fc(t) >> 5.
    So nonmover must use some mover triple. EC.

    Hmm, this is only for fc(t) >= 7 or CL-fc(t) >= 7? Not quite right.

    Actually: mover triples are a subset of 12. Nonmover triples are
    a subset of 12. If they're disjoint: at most 6 each (12/2). But
    fc(t) >= 4 mover triples implies >= 4 distinct values. The other
    8 values are available for nonmover. CL - fc(t) triples from 8 values.
    For CL - fc(t) > 8: forced repeat, but repeats are within nonmover.

    For EC we need INTERSECTION of mover and nonmover triple SETS to be
    nonempty. That's not forced by counting if |mover set| + |nonmover set| <= 12.

    So counting alone doesn't work for small fc(t).

    FINAL CORRECT APPROACH: Go back to the structural argument.

    The fix for the binary-fires-last issue:

    We don't need EVERY phase to have binary-fires-first. We need at
    least ONE phase where the binary fire is followed by another interior
    step (before the next t-fire).

    How many "far fires" are there total? CL - 2*fc(t) >= 2(n-3).
    In each one-sided phase: the interior has 1 binary fire + (len-1) far fires.
    Total far fires = sum (len_i - 1) = (CL - fc(t)) - fc(t) = CL - 2*fc(t).

    These far fires are distributed among the phases.
    If phase i has far fires f_i: f_i = len_i - 1.
    A "good" phase (binary not last) has the far fire AFTER the binary fire:
    it needs at least 1 far fire in the part after the binary fire.

    If binary fires FIRST in a phase: all f_i far fires come after it. Good if f_i >= 1.
    If binary fires LAST in a phase: all f_i far fires come before it. Bad.
    If binary fires in the middle: some far fires before, some after. Good.

    Can ALL phases have binary-fires-last AND all have far fires (f_i >= 1)?
    Total far fires = CL - 2*fc(t) >= 2(n-3). With fc(t) phases:
    average far fires per phase = (CL - 2fc(t)) / fc(t).

    Yes, it's possible for all to have f_i >= 1 with binary-fires-last.
    That doesn't help.

    APPROACH H: Use both sides.

    Among fc(t) phases: fc(bL) are bL-phases and fc(bR) are bR-phases.
    In a bL-phase with binary-fires-last: moverAt(s-1) = bL, moverAt(s) = t.
    In a bR-phase with binary-fires-last: moverAt(s-1) = bR, moverAt(s) = t.

    Consider a bL-phase followed by a bR-phase. The bL-phase ends with:
    step s-1: bL fires. Step s: t fires. The bR-phase starts at step s.
    Interior of bR-phase: step s+1, ..., s'-1. bR fires once, bL doesn't.

    If both phases have binary-fires-last:
    bL-phase: ..., far, ..., far, bL, t (at step s)
    bR-phase: ..., far, ..., far, bR, t (at step s')

    Step s+1 (start of bR-phase interior): no bL, bR, or t fire yet.
    Triple at t: (bL_POST_from_prev_phase, t_val_after_fire_at_s, bR_VAL).

    Wait, t fires at step s. So t_val changes at step s.
    configs.get(s+1).t = new t value = t_val_new.

    t doesn't fire again until s'. So t_val_new is constant from s+1 to s'.

    Triple at step s+1: (bL_POST, t_val_new, bR_VAL).
    Triple at step s': (bL_POST, t_val_new, bR_POST) where bR fired at s'-1.
    bR_POST != bR_VAL (bR is binary, fires). Different R. No EC between
    s+1 and s'.

    OK, the structural argument is truly subtle. Let me step back and
    think about what ACTUALLY works.

    *** THE REAL FIX ***

    The issue is only when the binary fire is the VERY LAST interior step.
    But we have n-3 far procs, each firing >= 2 times. Total far fires >= 2(n-3).
    These are spread across fc(t) one-sided phases.

    A phase with binary-fires-last has the structure:
    [far, far, ..., far, binaryFire]
    i.e., all far fires come before the binary fire.

    A phase with binary-fires-first has the structure:
    [binaryFire, far, far, ..., far]
    i.e., all far fires come after the binary fire.

    Actually: far fires can be interspersed with the binary fire.
    The binary fire is at ONE specific step. Far fires fill the rest.

    For EC: we need at least one far-fire step AFTER the binary fire
    and BEFORE the next t-fire. That is: at least one step in (a+j, s)
    where j is the binary fire position.

    If binaryFire is at position a+j (j-th interior step), then
    there are len-j steps after it (from a+j+1 to s-1), all far fires.
    We need len - j >= 1, i.e., j <= len - 1.
    The only bad case is j = len (binary fires at the very last step, s-1).

    CLAIM: if n >= 5, not all phases can have binary-fires-last.

    Proof attempt: consider the mover word. In binary-fires-last phases:
    step s-1 fires bL or bR. Step s fires t.

    Across the entire cycle: the pattern ... bL/bR, t, ..., bL/bR, t, ...
    Every t-fire is immediately preceded by a binary neighbor fire.

    This means: every t-fire step s has moverAt(s-1) in {bL, bR}.
    The step before each t-fire is a binary neighbor fire.

    Is this possible? It constrains the mover word heavily.
    The t-fire positions partition the cycle. Before each t-fire: bL or bR.
    This accounts for fc(t) steps (the binary fires just before t).

    But fc(bL) + fc(bR) = fc(t) and each binary fire is in exactly one
    phase. If ALL phases have binary-fires-last, then ALL binary fires
    are at step s-1 positions. This means every binary fire is immediately
    followed by a t-fire.

    So the mover word has the pattern: ..., bX, t, ..., far, ..., bX, t, ...
    where bX is bL or bR and far procs fill the gaps.

    The far fires are in the interior of each phase, BEFORE the binary fire.
    Between consecutive [bX, t] blocks: only far fires.

    This is a valid mover word structure. I don't see a contradiction.

    SO: the original argument as stated is INCOMPLETE for the
    binary-fires-last case.

    *** CORRECT COMPLETE APPROACH ***

    The fix: instead of looking from t-fire to next t-fire (forward),
    look from binary fire to PREVIOUS t-fire (backward).

    In a one-sided phase J=1, K=0:
    Step a (t fires) -> interior -> step s (t fires).
    bL fires at step a+j (some interior position).

    FORWARD window [a+j+1, s]: no bL, t, bR fires. Length L-j.
    If L-j >= 1: EC (step a+j+1 vs step s).

    BACKWARD window [a+1, a+j]: no bL, t, bR fires (bL hasn't fired yet).
    Length j-1.
    If j >= 2: triple at t is constant in [a+1, a+j).
    Step a+1: t is nonmover. Triple = (bL_PRE, t_val, bR_val).
    Need a MOVER step for t with triple (bL_PRE, t_val, bR_val).

    Step a: t fires. Triple at a = (bL_PRE, t_PRE, bR_val).
    t_PRE != t_val (t fires and changes). NOT a match.

    Hmm. The pre-fire-t value is different.

    OK so neither forward nor backward gives EC when bL fires at j=L
    (last step) or j=1 (first step with only 1 interior step).

    Actually wait. If j=1 AND len >= 2: forward window has length L-1 >= 1.
    EC! If j=L AND len >= 2: L >= 2, backward window has length L-1 >= 1.
    But backward doesn't give EC (wrong t value).

    The problem is specifically: j = L, the last position.
    And: j = 1 gives EC (forward). j = 2 with len >= 3 gives EC (forward).
    j = len with len >= 2 is the ONLY problematic case.

    REAL FIX: for the j = len case, use the ODD binary fire count over
    the phase.

    In the phase [a, s): bL fires once (odd) and bR fires 0 times (even).
    This is J=1 odd, K=0 even.

    bothEvenReturn_ec requires BOTH J and K even. Can't use directly.

    But: we know bL fires at step s-1 (just before t fires at s).
    And in the PREVIOUS phase, bL had some known value.

    The value of bL at step a: some value, call it bL_a.
    bL doesn't fire in [a, s-1), so bL_a is preserved until step s-1.
    At step s-1: bL fires, bL toggles to 1-bL_a.
    At step s: bL = 1-bL_a.

    Now look at the NEXT phase starting at step s.
    In this phase, bL or bR fires once (it's one-sided).

    If the next phase is also a bL-phase with binary-fires-last:
    From step s to next-t-fire s': bL doesn't fire until step s'-1.
    bL value from s to s'-1: 1-bL_a. At s'-1: bL fires, value becomes bL_a.
    At s': bL = bL_a.

    So: t fires at step s with bL = 1-bL_a. t fires at step s' with bL = bL_a.
    These are different bL values. But t_val might also change.

    At step s: t fires, configs.get(s).t = t_val_before_fire.
    After fire: t becomes t_val_after_fire_1.
    At step s': t fires, configs.get(s').t = t_val_before_fire_2.
    These are generally different. So triples at s and s' are different.

    I think I need to just CHECK COMPUTATIONALLY whether the theorem
    is true at all.
    """
    print("\nREVISED APPROACH ANALYSIS")
    print("=" * 60)
    print("  The binary-fires-last case is genuinely problematic.")
    print("  Need computational check to verify the theorem holds.")


if __name__ == "__main__":
    ok = verify_cyclic_edge_case()
    verify_nonmover_at_a_plus_2()
    verify_binary_fire_is_first()
    compute_length_distribution()
    revised_approach()
