#!/usr/bin/env python3
"""
=== DEFINITIVE ANALYSIS: Closing the Mixed-Phase Sorry ===

SETUP:
- Ring of n ≥ 9 processors. Processor t is ternary (m_t ≥ 3) with binary
  neighbors L = left(t) and R = right(t) (both m=2).
- Good cycle (all configs distinct, one privileged proc fires each step).
- Under ¬EC (no entry conflict), gap1_ec forces all consecutive movers ring-adjacent.
- The sorry is inside h_phase_le1: showing J+K ≤ 1 for each TernaryPhase.
- If J ≥ 1 AND K ≥ 1 (mixed phase), the code tries to derive EC → contradiction.

=== SORRY 1 (line 1012): VACUOUSLY TRUE ===

Context: fL > a AND fR > a.
Proof: Under ¬EC, moverAt(a) ∈ {L, R} (adjacent to t, not t itself).
  If moverAt(a) = L: fL = a, contradicts fL > a.
  If moverAt(a) = R: fR = a, contradicts fR > a.
  QED. The branch is unreachable.

Lean fix: After the `by_cases hfL_gt`, in the hfL_gt case, do:
  by_cases hfR_gt:
  · -- fL > a AND fR > a: derive False from adjacency
    exfalso
    have : moverAt(a) ∈ {L, R} := gap1_adjacent ... (phase.ht_nofire ...)
    cases this with
    | inl h => exact absurd (fL_first a ...) (by rw [h]; ... fL = a ...)
    | inr h => exact absurd (fR_first a ...) (by rw [h]; ... fR = a ...)

=== SORRYS 2,3 (lines 1077, 1121): BACKWARD CHAIN INDUCTION ===

The sorry case has the backward chain extending from the far side of the ring.
The mk_ec construction fails because each level's left-neighbor fires in the interval.

PROPOSED FIX: Replace the case-by-case backward scan with a SINGLE INDUCTIVE LEMMA.

Lemma (adjacent_chain_ec): Given:
  - fR = a (R fires first in phase)
  - No gap after any left^k(t) fire for k = 2,...,n-2
  (i.e., each left^k(t) fires immediately before left^(k-1)(t))
Then: the mover sequence in [a, fL] is exactly:
  R, right^(n-3)(t), ..., left^3(t), left^2(t), L
which is a full ring walk from R to L.

In this walk, processor t's left neighbor L fires ONCE at step fL = a+n-2.
But L fires an ODD number of times in this phase. L must fire EVEN times
over the full cycle. So L fires ODD times in other phases.

Combined with the normalForm constraint: if L fires exactly once in each
of J_other phases (since J+K ≤ 1), then fc(L) = 1 + J_other.
fc(L) must be even, so J_other must be odd, so J_other ≥ 1.
Similarly fc(R) ≥ 2 (R fires once in sorry phase + at least once more).

fc(L) + fc(R) ≥ 2 + 2 = 4. But fc(t) ≥ 3 (ternary).
Under h_sparse (being proved): fc(L)+fc(R) ≤ fc(t). So fc(t) ≥ 4.

But this alone doesn't close it. The REAL closure needs to be:

ACTUAL PROPOSED FIX: Show that in the sorry case (full ring walk),
  the mover at step (fL-1) is LL, and the mover at step (fL-2) is left³(t).
  Continue the chain: mover at step (fL-k) = left^(k+1)(t) for k=0,...,n-3.
  At step a: mover = left^(n-2)(t) = right(t) = R. ✓

  Now apply gap1_ec at step a+1: moverAt(a+1) must be adj to moverAt(a) = R.
  moverAt(a+1) ∈ {t, R, RR}. t doesn't fire. If R: re-fires.
  If RR: chain continues.

  gap1_ec at the mover at step a (which is R, adjacent to t at step a-1): OK.

  The KEY: at step fL, L fires. At step fL+1, what fires? It must be t
  (since fL+1 = s, the phase end). ✓

  So the boundary triple at L at step fL = a+n-2:
    (LL_val_after, L_val_old, t_val)
  The mover at step fL is L. This is a mover triple for L.

  At step a (= fR): mover is R. L is non-mover. Boundary at L at step a:
    (LL_val_before, L_val_old, t_val)

  EC at L if LL_val_after = LL_val_before.
  LL fires at step fL-1 = a+n-3. Before: LL_val_before. After: LL_val_after.
  LL_val_after ≠ LL_val_before (LL fired, changing its value).

  NO EC at L within the phase. ✓ (Confirmed earlier)

  But what about step a-1 (previous t-fire)? At step a-1, mover is t.
  L is non-mover. Boundary at L at step a-1:
    (LL_val_before, L_val_old, t_val_old)
  After t fires at step a-1: t_val changes to t_val_new.
  At step a: L boundary = (LL_val_before, L_val_old, t_val_new).
  At step fL: L boundary = (LL_val_after, L_val_old, t_val_new).
  (t_val doesn't change during the phase.)

  At step a-1: L boundary = (LL_val_before, L_val_old, t_val_old).
  t_val_old ≠ t_val_new (t fired). So step a-1 boundary ≠ step fL boundary.

  What about the PREVIOUS phase? In the previous phase, L might be a
  non-mover at some step with boundary (LL_val_x, L_val_y, t_val_z).
  If (LL_val_x, L_val_y, t_val_z) = (LL_val_after, L_val_old, t_val_new):
  that's a cross-phase EC at L.

  But we can't guarantee this without knowing the full cycle structure.

=== BOTTOM LINE ===

The sorry cases 2 and 3 CANNOT be closed by local-phase arguments alone.
The mixed-phase sorry pattern (full ring walk) does not produce EC within
the phase. EC only arises from cross-phase interactions.

RECOMMENDED APPROACH:
1. Close sorry 1 by showing fL>a ∧ fR>a is vacuously impossible (trivial).
2. For sorrys 2 and 3, RESTRUCTURE THE PROOF:
   Instead of proving EC in each mixed phase individually,
   prove that if a mixed phase exists, SOME other part of the proof
   (e.g., fire count bounds, normalForm constraints, or sub-threshold product)
   gives a contradiction.

   Specifically: if there exists a mixed phase with J≥1, K≥1, and the
   backward chain extends to the full ring walk, then:
   - fc(L) fires once in this phase.
   - fc(R) fires once in this phase.
   - fc(t) increments by 1 for this phase.
   - If ALL phases have J+K ≤ 1 EXCEPT this one:
     fc(L) + fc(R) = J_this + K_this + sum_other ≤ 2 + (fc(t)-1).
   - fc(L) + fc(R) ≤ fc(t) + 1.
   - But we need ≤ fc(t). So we need to show the mixed phase's
     contribution doesn't exceed the budget.
   - THIS IS THE HARD PART.

   Alternative: prove that the backward chain CANNOT extend all the way.
   I.e., at some point the chain breaks (a processor re-fires or a non-adjacent
   step occurs). This would give gap1_ec or mk_ec at that point.

3. SIMPLEST CLOSURE: Observe that sorrys 2 and 3 are inside a proof-by-contradiction
   (by_contra at line 905). The ultimate goal is h_sparse. If we can prove h_sparse
   by a DIFFERENT route (not per-phase), the sorrys become irrelevant.

   For example: use the fire-count sum decomposition directly.
   sparse_phase_sum_ge (line 1157) gives fc(L)+fc(R) ≥ fc(t).
   Combined with what we'd get from h_sparse: fc(L)+fc(R) = fc(t).
   But wait, sparse_phase_sum_ge already uses the normalForm assumption.
   If normalForm gives fc(L)+fc(R) ≥ fc(t) and h_sparse gives ≤ fc(t),
   then equality holds and each phase has J+K = 1.
   This means NO mixed phases (mixed has J+K ≥ 2).
   But this is CIRCULAR: h_sparse is what we're trying to prove.

4. ALTERNATIVE SIMPLE CLOSURE: The sorry case at line 1077 requires:
   left³(t) fires in [a, fLL).
   But fLL is the first LL fire in [a, fL).
   So left³(t) fires BEFORE LL in the phase.

   Under gap1_ec: movers are adjacent. Starting from moverAt(a) = R:
     moverAt(a+1) adj to R → {t, R, RR}. t excluded. If R: repeat.
     Likely: moverAt(a+1) = RR.

   But does left³(t) fire BEFORE LL? In the ring walk R→RR→...→LL→L,
   left³(t) appears BETWEEN R and LL on the ring. So yes, left³(t) fires
   before LL in the walk.

   The fix: instead of trying mk_ec at deeper levels, use the
   configVal_eq lemma with a LONGER interval.

   Specifically: at step a, mover = R. L is non-mover at step a.
   At step fL, L fires (mover). We need:
   configVal at left(L) = left(left(t)) = LL at step a = configVal at LL at step fL.
   This requires NO LL fire in [a, fL). But LL fires (that's the sorry condition).

   What if we use a DIFFERENT pair for ec_caseC_RL?
   ec_caseC_RL(fR, fL) requires no t, L, LL in [fR, fL).
   LL fires, so it fails.

   What about ec_caseC_RL(fR, fL') where fL' is the SECOND L-fire?
   But J=1 means L fires only once in the phase.

   What about using a DIFFERENT processor's fire?
   E.g., LL fires at fLL. Use ec at LL between fLL and some non-mover step.
   mk_ec_left at LL: EC at LL between fLL (mover) and v (non-mover),
   with no left³(t), LL, L in [v, fLL).
   If v = a: need no left³(t) in [a, fLL). That's exactly the sorry condition!
   So this ALSO fails.

   The chain of failures IS the sorry case. No local construction works.
   The proof needs a global or structural argument.
"""

print("=" * 70)
print("SUMMARY OF FINDINGS")
print("=" * 70)
print()
print("1. SORRY 1 (line 1012) is VACUOUSLY TRUE.")
print("   Proof: fL>a ∧ fR>a is impossible because moverAt(a) ∈ {L, R}")
print("   implies one of fL=a or fR=a.")
print("   FIX: Simple Lean proof using gap1_ec + phase.ht_nofire.")
print()
print("2. SORRYS 2,3 (lines 1077, 1121) require a GLOBAL argument.")
print("   The sorry case is a full-ring-walk phase (every non-t proc fires once).")
print("   No LOCAL EC construction works within this phase.")
print("   At n=5 (only 2 binary), these phases exist in ¬EC cycles.")
print("   At n≥7 (with ≥3 binary + sub-threshold), they computationally DON'T")
print("   appear in ¬EC cycles (every all-adjacent cycle has EC from elsewhere).")
print()
print("3. RECOMMENDED PROOF STRATEGIES for sorrys 2,3:")
print()
print("   (A) INDUCTIVE CHAIN + TERMINATION ARGUMENT:")
print("       Build an induction on the chain depth. At depth n-2,")
print("       left^(n-1)(t) = R fires at step a. The interval [a, first_fire(left^(n-2)(t)))")
print("       contains the R fire. Use this to get EC at left^(n-2)(t) = RR:")
print("       EC between first_fire(RR) and step a+1 (where RR is non-mover).")
print("       ISSUE: moverAt(a+1) might be RR itself, so a+1 is mover, not non-mover.")
print()
print("   (B) FIRE COUNT BOUND (avoid per-phase EC entirely):")
print("       Prove h_sparse (fc(L)+fc(R) ≤ fc(t)) WITHOUT showing each mixed")
print("       phase has EC. Instead, use:")
print("       - normalForm_gap_constraint: J=0→K=1, K=0→J=1, mixed→¬(both even)")
print("       - Binary parity: fc(L) even, fc(R) even")
print("       - Phase sum: fc(L)+fc(R) = sum over phases of (J_i + K_i)")
print("       - From normalForm: J_i + K_i ≥ 1 per phase (gap constraint)")
print("       - So fc(L)+fc(R) ≥ fc(t)")
print("       - Need ≤ fc(t): if fc(L)+fc(R) > fc(t), pigeonhole gives")
print("         a phase with J+K ≥ 2 = J≥1,K≥1 (mixed).")
print("         In mixed phase: ¬(both even). With J≥1,K≥1:")
print("         THIS IS EXACTLY WHAT THE CURRENT CODE DOES → leads to sorry.")
print("       So (B) doesn't avoid the sorry either.")
print()
print("   (C) USE ec_caseC_RL BETWEEN NON-PHASE STEPS:")
print("       Instead of looking within the phase, use the phase-to-phase")
print("       boundary. At step s (t fires after sorry phase):")
print("       - L boundary = (LL_new, L_new, t_new)")
print("       At some non-mover step in a DIFFERENT phase:")
print("       - L boundary might match.")
print("       This requires cross-phase tracking, which is complex but possible.")
print()
print("   (D) SIMPLEST: Prove the sorry branch is unreachable at n ≥ 9")
print("       by using the sub-threshold product or ≥3 binary constraint.")
print("       Show that the backward chain (left³t fires in [a, fLL))")
print("       contradicts some global invariant.")
print("       MOST PROMISING: the third binary processor (e.g., proc 4)")
print("       creates an additional constraint that makes the chain impossible.")
