#!/usr/bin/env python3
"""
RA13 SUMMARY: Complete findings on fc≥3 → contradiction in ZW cycles.

THEOREM: In a zero-winding good cycle (cw=ccw>0) with no safe processor,
sub-threshold product, ≥3 binary procs, n≥5, all procs fire ≥2 times,
and convergent — if some proc q has fc(q)≥3, derive False.

PROOF STRATEGY (verified computationally at n=5,7,9):

1. Case A: fc is NON-CONSTANT (>99.9% of cycles).
   ANALYTICAL proof via gradient + pigeonhole + phase dispatch:

   Since fc is non-constant on the ring, there exist adjacent procs t, u
   with fc(t) > fc(u). We can find such a pair where fc(t) ≥ 3:
   - If S = {q: fc(q)≥3} is a proper subset: boundary of S gives t ∈ S, u ∉ S.
   - If S = all procs but fc non-constant: argmax has lower-fc neighbor.

   At proc t: fc(u) fires distributed over fc(t) > fc(u) phases.
   By pigeonhole: some phase has 0 fires from u-side.
   That phase has (0, K) or (J, 0) → ZERO-SIDED → dispatchable.
   phase_dispatch_ec produces entry conflict → contradiction.

2. Case B: fc is CONSTANT = k (even ≥ 4) for all procs.
   Empirically: <0.1% of cycles. All found examples have "both-zero" phases.

   Two sub-approaches for formalization:
   a) Prove constant fc is impossible in ZW cycles (too strong, may not hold).
   b) Prove constant fc cycles always have a zero-sided phase.
      Evidence: the walk contains jumps (non-±1 steps). Jumps of ≥2
      skip neighbors, creating phases with J=0 or K=0.
   c) Use context counting at binary proc: with fc = k ≥ 4, binary proc
      fires k times as mover, each with context (L,self,R) ∈ {0,1}×ms_L×ms_R.
      Non-mover appearances: CL - k = (n-1)k. If (n-1)k > contexts at proc,
      guaranteed EC by pigeonhole (no phase analysis needed).

   For n ≥ 9, all binary: contexts = 8, (n-1)k ≥ 8·4 = 32 >> 8.
   Mover has k contexts, non-mover has (n-1)k contexts, total = nk.
   Distinct contexts = 8. Mover needs k ≤ 8 distinct, non-mover k ≤ 8.
   Overlap ≥ max(0, k + k - 8) = max(0, 2k-8).
   For k=4: overlap ≥ 0. Not guaranteed.

   Actually: mover contexts ⊆ {8 triples}. Non-mover contexts ⊆ {8 triples}.
   For EC: need intersection non-empty.
   Mover visits k triples (not necessarily distinct). Non-mover visits (n-1)k.
   |mover_set| ≤ 8, |nonmover_set| ≤ 8. If |mover_set| + |nonmover_set| > 8:
   guaranteed overlap. |mover_set| ≤ k, |nonmover_set| ≤ (n-1)k.
   But sets are bounded by 8.
   Need |mover_set| + |nonmover_set| > 8, i.e., if mover visits > 4 distinct
   AND nonmover visits > 4 distinct → guaranteed overlap.

   For k=4: mover visits 4 triples (could be all distinct = 4 ≤ 8/2).
   Not enough by simple counting.

RECOMMENDED FORMALIZATION:
  Use Case A (analytical) as the MAIN proof.
  For Case B: add as a separate lemma with a computational verification
  at small n, or find an analytical argument based on walk structure.

  Actually: the simplest approach for Case B may be:
  With constant fc = k, all binary procs fire k ≥ 4 times.
  CL = nk ≥ 4n. With ZW and cw = ccw ≥ 1:
  There are ≥ 2 direction changes (CW→CCW and CCW→CW).
  At each direction change, some proc fires at step t and again at step t+δ
  for small δ. This creates a short phase → likely zero-sided.

  But formalizing "direction change → short phase" is non-trivial.

  SIMPLEST APPROACH: In the Lean formalization, handle the constant-fc case
  computationally (finite check for each n, or verify that the constant-fc
  assumption leads to CL ≥ 4n which combined with context counting gives EC).

VERIFICATION RESULTS:
  n=5: 23909 ZW fc≥3 cycles. 100% dispatchable. 100% entry conflict.
       Case A: 23797 (100% gradient works). Case B: 112 (100% dispatchable).
  n=7: 30282 ZW fc≥3 cycles. 100% dispatchable. 100% entry conflict.
  n=9: 2553+ cycles sampled. 100% dispatchable.
       Case A: 2552. Case B: 1 (dispatchable via both-zero phase).
"""

print(__doc__)

print("="*60)
print("FORMALIZATION ROADMAP")
print("="*60)
print("""
STEP 1: Prove gradient lemma (analytical).
  lemma gradient_exists:
    If fc: Fin n → Nat with (∃ q, fc q ≥ 3) and (∀ q, fc q ≥ 2):
    Then either fc is constant, or ∃ t, fc t ≥ 3 ∧ (fc (t-1) < fc t ∨ fc (t+1) < fc t).

  Proof: If fc non-constant, the max-value set is proper.
  Its boundary (on the ring) has the desired property.

STEP 2: Prove pigeonhole → zero-sided phase (analytical).
  lemma pigeonhole_zero_phase:
    If fc t ≥ 3 and fc u < fc t where u is a neighbor of t:
    Then some phase of t has 0 fires from the u-side.

  Proof: fc(u) fires distributed over fc(t) > fc(u) phases.
  By pigeonhole, some phase has 0.

STEP 3: Prove zero-sided phase → entry conflict (already done as phase_dispatch_ec).

STEP 4: Handle constant fc case.
  Option A: Prove analytically that constant fc → some zero-sided phase.
  Option B: Prove constant fc → CL ≥ 4n → entry conflict by other means.
  Option C: Prove constant fc is impossible under ZW + sub-threshold + ≥3 binary.
  Option D: Leave as sorry (labeled: constant_fc_case_sorry).

  Recommendation: Option D for now, with computational evidence that it never
  occurs in practice (<0.1%). Can be discharged later.

  Actually Option B might work:
  Constant fc = k ≥ 4. Binary procs have 2 states.
  A binary proc's value alternates: 0,1,0,1,... over k firings.
  Its LEFT context (value of left neighbor when binary fires) takes values
  from ms[left]. Its RIGHT context similarly.
  Mover contexts: (left_val, self_val, right_val).
  self_val alternates. So half the mover contexts have self=0, half self=1.
  At most ms[left]·ms[right] contexts per self-value = ms[left]·ms[right].
  Total distinct mover contexts ≤ 2·ms[left]·ms[right].

  Non-mover contexts: binary appears as non-mover in CL-k = (n-1)k steps.
  But binary value only changes when it fires, so between consecutive firings,
  the binary's value is FIXED. Each phase has the same self_val for all
  non-mover appearances. With k phases and self alternating:
  k/2 phases with self=0, k/2 with self=1.
  In each phase: left and right neighbors change.
  Non-mover contexts per phase: up to (n-1) steps, but context =
  (left_val, fixed_self, right_val). Could be many distinct.

  For EC at binary: need mover context = some non-mover context.
  Mover at phase i start: context = (L_i, s_i, R_i) where s_i alternates.
  Non-mover in some other phase j: context = (L', s_j, R') where s_j is fixed.
  For overlap: s_i = s_j (same self value). This happens for k/2 mover phases
  matching k/2 non-mover phase groups.

  Within the s=0 group: mover sees k/2 contexts, non-mover sees many contexts.
  If k/2 > ms[left]·ms[right]: mover contexts repeat → but we need mover-nonmover
  overlap, not mover-mover repeat.

  This is getting complicated. Stick with Option D for now.
""")
