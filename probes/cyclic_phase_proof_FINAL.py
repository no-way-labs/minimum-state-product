"""
DEFINITIVE PROOF SKETCH: Cyclic Phase Decomposition

Target sorry: AllNormalFormFalse2.lean:1129
  fc(L) + fc(R) <= fc(t)

Also fills: PhaseExtractionBase.lean:6693
  sparse_phase_sum_ge: fc(L) + fc(R) >= fc(t)

Together: fc(L) + fc(R) = fc(t)  [exact phase balance]

=======================================================================
RECOMMENDED APPROACH: Direct proof without gc.rotate
=======================================================================

The approach uses three facts already in the codebase:
  (F1) intervalFireCount_split (additive over sub-intervals)
  (F2) fireCount_eq_intervalFireCount_full (fc = ifc over [0, CL))
  (F3) configVal_eq_of_noFire_between (value preservation)

Plus one new fact:
  (F4) configVal_eq_of_cyclic_noFire (value preservation across boundary)

The proof works by covering ALL L/R fires with TernaryPhases.

=======================================================================
KEY NEW LEMMA: Cyclic Value Preservation
=======================================================================

Lemma (configVal_eq_of_cyclic_noFire):
  If q does not fire in [b, CL) or [0, a), i.e.:
    (∀ k, b ≤ k.val → k.val < CL → moverAt k ≠ q) ∧
    (∀ k, 0 ≤ k.val → k.val < a → moverAt k ≠ q)
  and a < b (so the "live" region is [a, b)),
  then configs.get(b) q = configs.get(a) q.

Proof:
  Step 1: configs.get(b) q = configs.get(CL-1) q  [F3, no fires in [b, CL-1)]
    Wait, need b <= CL-1. But CL-1 < CL, and q doesn't fire in [b, CL).

  Step 2: configs.get(CL-1) passes through the cycle boundary.
    nextIndex(CL-1) = 0. From gc.state_eq_of_ne_moverAt(CL-1, q, ...):
    configs.get(0) q = configs.get(CL-1) q  [if q ≠ moverAt(CL-1)]
    We need q ≠ moverAt(CL-1). We know q doesn't fire at CL-1 (from [b, CL) no-fire).
    Actually, CL-1 < CL is in the range, so moverAt(CL-1) ≠ q. Good.

    Subtlety: we need configs.get(nextIndex(CL-1)) q = configs.get(CL-1) q.
    nextIndex(CL-1) = 0. So configs.get(0) q = configs.get(CL-1) q.
    But gc.state_eq_of_ne_moverAt gives:
      configs.get(nextIndex(k)) q = configs.get(k) q  when q ≠ moverAt(k)
    So: configs.get(0) q = configs.get(CL-1) q. Good.

  Step 3: configs.get(0) q = configs.get(a) q  [F3, no fires in [0, a)]

  Chain: configs.get(b) q = configs.get(CL-1) q = configs.get(0) q = configs.get(a) q.

  Actually more careful:
  - F3 gives configs.get(b)(q) = configs.get(CL-1)(q) if no q-fire in [b, CL-1)
    (note: CL-1 is the END, so it IS checked against CL)
  - Wait, F3 signature: configVal_eq_of_noFire_between(gc, q, a, b, hab, hb_lt, hno)
    requires b < CL. So configs.get(a) q = configs.get(b) q when no q-fires in [a, b).

  For our purpose:
  - configs.get(b) q = configs.get(CL-1) q? No, we need a <= b.
    We want the opposite direction. Since b <= CL-1, and no q-fires in [b, CL-1):
    configs.get(b) q = configs.get(CL-1) q. This requires CL-1 < CL and b <= CL-1.

  Hmm, but CL-1 < CL is always true. And configVal_eq_of_noFire_between requires
  hb : b < gc.configs.length. With b = CL-1, this is b < CL. Check.
  And hab : a <= b. With a := b (our b), b := CL-1: need b <= CL-1.

  Wait, I'm confusing variable names. Let me be explicit.

  Call the theorem with (gc, q, b_orig, CL-1, b_orig <= CL-1, CL-1 < CL, no_fire).
  This gives: configs.get(b_orig) q = configs.get(CL-1) q.

  Then gc.state_eq_of_ne_moverAt(CL-1, q, q ≠ moverAt(CL-1)) gives:
    configs.get(nextIndex(CL-1)) q = configs.get(CL-1) q
    configs.get(0) q = configs.get(CL-1) q

  Then configVal_eq_of_noFire_between(gc, q, 0, a_orig, 0 <= a_orig, a_orig < CL, no_fire_in_[0, a_orig)):
    configs.get(0) q = configs.get(a_orig) q.

  Chain: configs.get(b_orig) q = configs.get(CL-1) q = configs.get(0) q = configs.get(a_orig) q.

  This is clean. About 15-20 lines of Lean.

  HOWEVER: there's a subtlety. What if b_orig = CL-1? Then the first step
  is trivial (b = CL-1, so configs.get(b) = configs.get(CL-1)).
  And what if a_orig = 0? Then the last step is trivial.
  Both edge cases work fine.

  What if CL = 1? Then b_orig = 0 = CL-1, a_orig = 0. Trivial.

=======================================================================
PROOF OF h_sparse: fc(L) + fc(R) <= fc(t)
=======================================================================

Given:
  h_phase_le1: ∀ phase : TernaryPhase gc t, J + K ≤ 1
  hfc2: fc(t) ≥ 2
  hfc_lt: fc(t) < CL

Find s_min (first t-fire) and s_max (last t-fire), s_min < s_max.

Case 1: s_min = 0.
  Then there are NO L/R fires before the first t-fire.
  The boundary contribution from [0, s_min) = [0, 0) = 0.

  All L/R fires are in [0, CL) = [s_min, CL).
  Decompose: fc(L) + fc(R) = ifc(L+R, 0, CL)
    = ifc(L+R, 0, s_1) + ifc(L+R, s_1, s_2) + ... + ifc(L+R, s_{fc-2}, s_{fc-1}) + ifc(L+R, s_{fc-1}, CL)

  Each [s_i, s_{i+1}] is an interior TernaryPhase with J+K <= 1.
  That's fc(t)-1 terms, each <= 1, so sum <= fc(t) - 1.

  Plus the LAST interval [s_{fc-1}, CL). In this interval, t doesn't fire
  (s_{fc-1} is the last t-fire). The "next" t-fire cyclically is s_0 = 0.

  We can form a TernaryPhase from any step in (s_{fc-1}, CL) to s_0 = 0?
  No: s_0 = 0 < s_{fc-1}, so a > s. Invalid.

  BUT: if s_min = 0, the wrap-around phase is [s_{fc-1}+1, CL) → step 0.
  The step at 0 has moverAt(0) = t.

  We can't form TernaryPhase(a, 0) because a > 0.

  HOWEVER, if there are no L/R fires in [s_{fc-1}, CL), then ifc(L+R, s_{fc-1}, CL) = 0,
  and fc(L) + fc(R) = sum over fc-1 interior phases <= fc - 1 <= fc. Done.

  If there IS an L/R fire at step k in (s_{fc-1}, CL), then... we need to handle it.

  Key insight: this fire at step k is AFTER the last t-fire. So k > s_{fc-1}.
  The NEXT t-fire (cyclically) is step 0 = s_min.
  We need a TernaryPhase that includes step k.

  The TernaryPhase(s_{fc-1}, s_{fc-1}+1) has a < s and covers the step right after s_{fc-1}.
  Wait, TernaryPhase needs moverAt(s) = t. Step s_{fc-1}+1 might not be a t-fire.

  Actually, TernaryPhase(a, s) requires moverAt(s) = t. So s must be a t-fire step.
  If s_{fc-1} is the LAST t-fire, there's no t-fire after it in the linear list.

  THIS IS THE CORE PROBLEM. After the last t-fire, there's no next t-fire
  in the linear list to serve as the "s" of a TernaryPhase.

Case 2: General.
  With fc(t) fires at s_0 < s_1 < ... < s_{fc-1}:
  - fc(t)-1 interior TernaryPhases: (s_0, s_1), ..., (s_{fc-2}, s_{fc-1})
  - Each has J+K <= 1
  - Interior sum = ifc(L, s_0, s_{fc-1}) + ifc(R, s_0, s_{fc-1}) <= fc-1

  Boundary = ifc(L+R, 0, s_0) + ifc(L+R, s_{fc-1}+1, CL)
  where ifc(L+R, s_{fc-1}+1, CL) counts fires of L or R AFTER the last t-fire.

  fc(L) + fc(R) = interior + boundary.

  Need: boundary <= 1 to get total <= fc.

PROVING boundary <= 1:

The boundary region [0, s_0) ∪ (s_{fc-1}, CL) has NO t-fires.
It's exactly the wrap-around gap between the last and first t-fires.

If boundary >= 2, we construct an entry conflict:

Case A: There's an L-fire at step a1 in [0, s_0) and also something else.
  Then TernaryPhase(a1, s_0) is valid (a1 < s_0, moverAt(s_0) = t, t doesn't
  fire in [a1, s_0) since a1 < s_0 = first t-fire).
  This TernaryPhase has J' + K' >= 1 (from the L-fire at a1).

  If boundary >= 2, there's ANOTHER fire in the boundary.
  But that other fire might be in (s_{fc-1}, CL), not in [a1, s_0).
  The TernaryPhase(a1, s_0) only covers [a1, s_0), missing the post-s_{fc-1} fires.

  So h_phase_le1 on this TernaryPhase gives J' + K' <= 1, which is consistent.
  Not a contradiction.

Hmm. So proving boundary <= 1 via TernaryPhase requires covering the ENTIRE
boundary with ONE TernaryPhase. But TernaryPhase can only cover a contiguous
linear interval, and the boundary is two disjoint intervals.

THIS is why we need either:
(a) Cyclic TernaryPhase, or
(b) Rotation to make the boundary contiguous, or
(c) A direct proof that boundary <= 1 using cyclic value preservation.

=======================================================================
THE ACTUAL CLEAN PROOF: Cyclic BothEvenReturn
=======================================================================

We prove: in the wrap-around region, if J+K >= 2, then hasEntryConflict.

The wrap-around region is the cyclic interval from step s_{fc-1}+1 to step s_0-1
(wrapping through CL-1 and 0). In this region, t doesn't fire.

The mover step (where t fires) is s_0 or s_{fc-1}. Both are t-fire steps.

Key: to construct an entry conflict, we need two steps a, s with a < s,
moverAt(s) = p (some processor), moverAt(a) ≠ p, and matching contexts.

For the wrap region, we have t-fires at s_0 and s_{fc-1}, with s_0 < s_{fc-1}.
We can use s_0 as the mover step and find a nonmover step BEFORE s_0.

If there's an L or R fire at step a < s_0 (in [0, s_0)):
  Form TernaryPhase(a, s_0). This is valid. Apply h_phase_le1.

If there's an L or R fire at step b in (s_{fc-1}, CL):
  We CANNOT use s_0 as mover step (b > s_0).
  We CAN use s_{fc-1} as the start of a phase... but moverAt(s_{fc-1}) = t,
  so s_{fc-1} is a mover step for t, not a nonmover.

  Actually, we can form TernaryPhase(s_{fc-1}, s_0) only if s_{fc-1} < s_0, which is FALSE.

So for fires in (s_{fc-1}, CL), we need a different approach.

APPROACH: Use b as a nonmover step for L (or R), and find a LATER mover step.
But there are no t-fire steps after s_{fc-1}. So we can't form a TernaryPhase
with b as the starting nonmover.

UNLESS: we form a TernaryPhase AT LEFT T, not at t.

Wait! The entry conflict doesn't have to be at t. It can be at L or R.

If L fires at step b in (s_{fc-1}, CL), and we want an entry conflict at L:
  We need steps a < s with moverAt(s) = L, moverAt(a) ≠ L, and matching
  (left(L), L, right(L)) contexts.

  If L fires only once in the boundary, and that's at step b, then there's
  no second L-fire to create a conflict... Actually, the entry conflict is
  between a MOVER step and a NONMOVER step for the same processor, with
  matching contexts.

OK, I think the cleanest approach really is rotation after all. Let me
reconsider.

=======================================================================
RECONSIDERED: APPROACH C (Rotation) — Minimal version
=======================================================================

Instead of building a full gc.rotate infrastructure, we prove ONE lemma:

LEMMA (wrap_phase_JK_le1):
  Given the setup of h_sparse (t fires at s_0 < s_1 < ... < s_{fc-1},
  all normal form, ¬EC), the wrap-around contribution satisfies:
    ifc(L, 0, s_0) + ifc(R, 0, s_0) + ifc(L, s_{fc-1}+1, CL) + ifc(R, s_{fc-1}+1, CL) ≤ 1

PROOF:
  By contradiction. Assume wrap_J + wrap_K >= 2.

  Sub-case 2a: wrap_J + wrap_K >= 2 and all fires are in [0, s_0).
    Then ifc(L, 0, s_0) + ifc(R, 0, s_0) >= 2.
    Pick any nonmover step a in [0, s_0) (must exist since s_0 >= 1 for fc >= 2).
    TernaryPhase(a, s_0) where a < s_0. This has J' + K' >= 2.
    Wait: J' = ifc(L, a, s_0), K' = ifc(R, a, s_0). Since a is in [0, s_0),
    J' + K' <= ifc(L, 0, s_0) + ifc(R, 0, s_0) = wrap_pre.
    But J' + K' might be < 2 if the fires are before step a.

    Take a = 0 (if moverAt(0) ≠ t): TernaryPhase(0, s_0), J' + K' = ifc(L, 0, s_0) + ifc(R, 0, s_0) = wrap_pre >= 2.
    Wait, TernaryPhase(0, s_0) has J' = ifc(L, 0, s_0) and K' = ifc(R, 0, s_0).
    But actually, J' = ifc(L, a, s) where a and s are step indices for the phase.
    The "interval" in TernaryPhase is [a, s), so ifc(L, 0, s_0) counts L-fires in steps 0, 1, ..., s_0-1.
    Wait, ifc is defined as ifc(p, a, b) = pfc(b) - pfc(a) = sum of fires in [a, b).
    And TernaryPhase.J = ifc(L, phase.a.val, phase.s.val).
    So for TernaryPhase(0, s_0): J = ifc(L, 0, s_0) = number of L-fires in [0, s_0).
    This equals our wrap_pre_J. Good.

    If moverAt(0) = t, then a = 0 is a t-fire step, so s_min = 0. But we assumed
    fires in [0, s_0), which means s_0 > 0, and s_min = s_0. Hmm, if s_min = 0
    then s_0 = 0, and [0, s_0) = empty. No fires. Contradiction with >= 2.

    So if wrap_pre >= 2, then s_0 > 0, and step 0 is a nonmover for t.
    TernaryPhase(0, s_0) is valid. h_phase_le1 gives J + K <= 1. But J + K = wrap_pre >= 2.
    Contradiction.

  Sub-case 2b: wrap_J + wrap_K >= 2 and all fires are in (s_{fc-1}, CL).
    Then ifc(L, s_{fc-1}+1, CL) + ifc(R, s_{fc-1}+1, CL) >= 2.
    We need a TernaryPhase that covers these fires.
    The next t-fire after s_{fc-1} is s_0 (cyclically). But s_0 < s_{fc-1}.
    So we can't form TernaryPhase(a, s) with a in (s_{fc-1}, CL) and s a t-fire.

    HOWEVER: we CAN form TernaryPhase(s_{fc-1}, s_0)... no, s_{fc-1} > s_0. Invalid.

    WHAT IF s_{fc-1} + 1 < CL and there's a t-fire at s_{fc-1}? Yes, moverAt(s_{fc-1}) = t.
    That's not useful because we need a LATER t-fire to be the endpoint.

    THE TRICK: the last interior TernaryPhase is (s_{fc-2}, s_{fc-1}). What about
    a TernaryPhase from some step AFTER s_{fc-2} to s_{fc-1}?

    If there's a fire at step b > s_{fc-1}:
    We form TernaryPhase(a, s_{fc-1}) where a is a nonmover step < s_{fc-1}.
    But this only covers fires in [a, s_{fc-1}), not after s_{fc-1}.

    NO EXISTING TernaryPhase CAN COVER FIRES AFTER THE LAST T-FIRE.

    This is the fundamental issue. Without rotation, fires after s_{fc-1}
    are inaccessible to TernaryPhase.

  Sub-case 2c: fires in both [0, s_0) and (s_{fc-1}, CL).
    Combine: at least one fire in [0, s_0) and at least one in (s_{fc-1}, CL).
    The [0, s_0) fire is handled by TernaryPhase(0, s_0) with J+K >= 1.
    The (s_{fc-1}, CL) fire is unhandled.
    If TernaryPhase(0, s_0) has J+K = 1 (≤ 1 from h_phase_le1), then
    fc(L)+fc(R) = interior_sum + 1 + (post-fires) >= fc-1 + 1 + 1 = fc+1 > fc.
    Wait, that's what we're trying to prove! We need fc(L)+fc(R) <= fc, not >= fc.

    Hmm. The problem is that h_phase_le1 gives J+K <= 1 for TernaryPhase(0, s_0),
    which means the [0, s_0) contribution is at most 1. The (s_{fc-1}, CL) contribution
    is at most... well, it could be anything.

OK, I'm convinced: SUB-CASE 2b IS THE HARD CASE, and it REQUIRES handling
fires after the last t-fire, which no TernaryPhase can cover.

The ONLY approaches that work for sub-case 2b:
  1. Rotation (make the last phase linear)
  2. Extend TernaryPhase to allow cyclic intervals
  3. Directly prove the mechanism arguments work cyclically

=======================================================================
FINAL RECOMMENDATION: Approach C with MINIMAL rotation
=======================================================================

Don't build full gc.rotate. Instead:

1. Prove a ONE-SHOT cyclic value preservation lemma.
2. Prove: if ifc(L, s_{fc-1}+1, CL) + ifc(R, s_{fc-1}+1, CL) >= 2,
   then hasEntryConflict gc.
3. This uses the cyclic value preservation to show that the mover context
   at step s_0 (where t fires) matches a nonmover context at some step
   in (s_{fc-1}, CL), going through the cycle boundary.

The entry conflict at t between step s_0 (mover) and step a (nonmover, a > s_{fc-1}):
  - t's value: same from step a to step CL-1 (no t fires), then same from
    step 0 to step s_0 (no t fires before s_0). By cyclic preservation:
    configs.get(a)(t) = configs.get(s_0)(t). Good.
  - L's value: if L fires even times in (a, CL) ∪ [0, s_0), then
    configs.get(a)(L) = configs.get(s_0)(L). Use binary parity across boundary.
  - R's value: similarly.

So the BothEvenReturn argument works if both L and R fire even times in the
cyclic interval (s_{fc-1}, s_0). The parity needs cyclic counting.

For ToggleFR: if L fires >= 2 times in the cyclic interval with R constant,
binary dichotomy gives two distinct L-values at nonmover steps. The mover
context at s_0 must match one. This works because the value comparisons are
point-wise (same config at same step), not interval-based.

THE CRITICAL POINT: BothEvenReturn uses configVal_eq_of_noFire_between
to show t's value is preserved. For the cyclic case, we need the cyclic
version. ToggleFR uses configVal_eq_of_noFire_between for t AND for R
(showing R is constant). For the cyclic case, we need cyclic versions of both.

The cyclic configVal_eq is the KEY NEW INFRASTRUCTURE.

Once we have it, the mechanism proofs carry over nearly verbatim:
  - BothEvenReturn: replace configVal_eq_of_noFire_between with cyclic version
  - ToggleFR: same replacement
  - The binary_config_eq_of_even_intervalFireCount also needs a cyclic version
    (even fires => same value across the cycle boundary)

=======================================================================
CONCRETE LEAN PROOF SKETCH
=======================================================================

--- New file: CyclicPhase.lean (~100 lines) ---

-- Cyclic value preservation: if q doesn't fire in [b, CL) or [0, a),
-- then config(b)(q) = config(a)(q).
theorem configVal_eq_of_cyclic_noFire
    (gc : GoodCycle sys) (q : Fin sys.rs.n) (a b : Nat)
    (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (hab : a < b)  -- a < b, so the "no fire" region wraps: [b, CL) ∪ [0, a)
    (hno_post : ∀ k : Fin gc.configs.length,
      b ≤ k.val → gc.moverAt k ≠ q)
    (hno_pre : ∀ k : Fin gc.configs.length,
      k.val < a → gc.moverAt k ≠ q)
    : (gc.configs.get ⟨b, hb⟩) q = (gc.configs.get ⟨a, ha⟩) q := by
  -- Step 1: config(b)(q) = config(CL-1)(q) by no-fire in [b, CL-1]
  -- (uses existing configVal_eq_of_noFire_between)

  -- Step 2: config(CL-1)(q) = config(0)(q) by gc.state_eq_of_ne_moverAt at CL-1
  -- (q doesn't fire at CL-1 since CL-1 >= b and hno_post)

  -- Step 3: config(0)(q) = config(a)(q) by no-fire in [0, a)
  -- (uses existing configVal_eq_of_noFire_between)
  sorry -- (~15 lines of Lean)

-- Cyclic binary parity: if p is binary and fires an even number of times
-- in the cyclic interval [b, CL) ∪ [0, a), then config(b)(p) = config(a)(p).
theorem binary_config_eq_of_cyclic_even_fire
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2)
    (a b : Nat) (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (heven : Even (gc.intervalFireCount p b gc.configs.length +
                    gc.intervalFireCount p 0 a))
    : (gc.configs.get ⟨b, hb⟩) p = (gc.configs.get ⟨a, ha⟩) p := by
  sorry -- (~20 lines, chain through boundary using binary_stateAfter_val_eq)

-- Wrap-around BothEvenReturn: entry conflict when L and R both fire even
-- times in the cyclic interval [s_{fc-1}+1, CL) ∪ [0, s_0).
theorem cyclic_bothEvenReturn_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (s_first s_last : Fin gc.configs.length)
    (h_first_lt : s_first.val < s_last.val)
    (h_first_mover : gc.moverAt s_first = t)
    (h_last_mover : gc.moverAt s_last = t)
    (h_no_t_wrap : ∀ k : Fin gc.configs.length,
      s_last.val < k.val → gc.moverAt k ≠ t)
    (h_no_t_pre : ∀ k : Fin gc.configs.length,
      k.val < s_first.val → gc.moverAt k ≠ t)
    (hbL : sys.rs.m (left t) = 2)
    (hbR : sys.rs.m (right t) = 2)
    -- Nonmover step in the wrap region
    (a : Fin gc.configs.length)
    (ha_in_wrap : a.val > s_last.val ∨ a.val < s_first.val)
    (ha_nonmover : gc.moverAt a ≠ t)
    -- L fires even, R fires even in wrap
    (hJ_even : Even (gc.intervalFireCount (left t) (s_last.val + 1) gc.configs.length +
                      gc.intervalFireCount (left t) 0 s_first.val))
    (hK_even : Even (gc.intervalFireCount (right t) (s_last.val + 1) gc.configs.length +
                      gc.intervalFireCount (right t) 0 s_first.val))
    : hasEntryConflict gc := by
  sorry -- (~25 lines, use cyclic value preservation + cyclic binary parity)

-- Similarly: cyclic ToggleFR for one-sided >= 2 in the wrap.
-- And: cyclic cross-neighbor EC for mixed J >= 1, K >= 1 in the wrap.

-- THE MAIN LEMMA: wrap contribution <= 1.
theorem wrap_phase_JK_le1
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfc_ge2 : gc.fireCount t ≥ 2)
    (hfc_lt : gc.fireCount t < gc.configs.length)
    (hall_normal : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hnoEC : ¬hasEntryConflict gc)
    -- s_first, s_last are the first and last t-fire steps
    (s_first s_last : Fin gc.configs.length)
    (h_first_mover : gc.moverAt s_first = t)
    (h_last_mover : gc.moverAt s_last = t)
    (h_first_lt : s_first.val < s_last.val)
    (h_first_min : ∀ k : Fin gc.configs.length, k.val < s_first.val → gc.moverAt k ≠ t)
    (h_last_max : ∀ k : Fin gc.configs.length, s_last.val < k.val → gc.moverAt k ≠ t)
    : gc.intervalFireCount (left t) 0 s_first.val +
      gc.intervalFireCount (right t) 0 s_first.val +
      gc.intervalFireCount (left t) (s_last.val + 1) gc.configs.length +
      gc.intervalFireCount (right t) (s_last.val + 1) gc.configs.length ≤ 1 := by
  -- By contradiction: assume wrap J+K >= 2.
  -- Case split: both even? -> cyclic_bothEvenReturn_ec -> EC -> contradiction
  -- One-sided >= 2? -> cyclic ToggleFR -> EC -> contradiction
  -- Mixed J >= 1, K >= 1? -> cyclic cross-neighbor EC -> contradiction
  sorry -- (~30 lines, mirrors the h_phase_le1 case analysis)

-- THE TARGET: fill the sorry at AllNormalFormFalse2.lean:1129.
-- fc(L) + fc(R) = interior_sum + wrap_sum.
-- interior_sum <= fc(t) - 1 (from h_phase_le1 over fc-1 interior phases).
-- wrap_sum <= 1 (from wrap_phase_JK_le1).
-- So fc(L) + fc(R) <= fc(t) - 1 + 1 = fc(t).
-- ~10 lines combining intervalFireCount_split + wrap_phase_JK_le1.
"""

print("Proof sketch complete. See the code comments above for the full plan.")
print()
print("SUMMARY OF LEAN WORK:")
print("  1. configVal_eq_of_cyclic_noFire: ~15 lines")
print("  2. binary_config_eq_of_cyclic_even_fire: ~20 lines")
print("  3. cyclic_bothEvenReturn_ec: ~25 lines")
print("  4. cyclic_toggleFR_ec (+ symmetric): ~30 lines")
print("  5. cyclic_cross_neighbor_ec: ~20 lines")
print("  6. wrap_phase_JK_le1: ~30 lines")
print("  7. h_sparse proof body: ~10 lines")
print("  Total: ~150 lines new Lean code")
print()
print("DEPENDENCIES:")
print("  - configVal_eq_of_noFire_between (existing)")
print("  - gc.state_eq_of_ne_moverAt (existing)")
print("  - binary_config_eq_of_even_intervalFireCount (existing)")
print("  - intervalFireCount_split (existing)")
print("  - fireCount_eq_intervalFireCount_full (existing)")
print("  - normalForm_gap_constraint (existing)")
print()
print("NO NEW IMPORTS NEEDED. All new code goes in one file.")
