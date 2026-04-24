/-
  PhaseExtraction.lean — Top-level phase extraction assembly

  Wires phase analysis into the binary ring impossibility chain:
  binary_ring_impossibility → both_binary_neighbors_false →
  subThreshold_binary_core_false → nonConsecutive_phase_extraction_false.

  Cycle-type callbacks (sweep/zero-winding/odd-winding) are passed as
  explicit parameters to break the import cycle with CaseObstructions.
-/
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase
import LeanMn.LowerBound.Archive.EntryConflict.AllNormalFormFalse
import LeanMn.LowerBound.Archive.CaseObstructionsCore

namespace LeanMn

variable {sys : System}

/-- **Residual impossibility for sub-threshold binary rings.**
    Reduced via firing support analysis. Three branches:

    1. |Z| ≥ 3 (3+ non-firing procs): closed by `zeroSet_ge3_impossible`.
    2. |Z| = 0 (all procs fire): dispatched via
       `exists_mechanism_phase_of_fullSupport_pivot` (one sorry in
       `allNormalForm_false` for the counting contradiction).
    3. |Z| ∈ {1, 2} (some proc doesn't fire → zero winding proved):
       - CW > 0 derived from zero winding + hno_safe (trapped mover argument).
       - Sub-case (a): 3 consecutive binary — sorry (proved downstream in
         ConsecutiveBinaryEC.lean / BoundaryShadowEntry.lean, but circular import
         through GlobalMinGap prevents calling from here).
       - Sub-case (b): non-consecutive binary — sorry (4-mechanism universal EC). -/
private theorem binary_ring_impossibility
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9) (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    -- Parametric proofs for |Z|∈{1,2} cases (provided by caller to break import cycle).
    -- The consecutive case is proved in ConsecutiveBinaryEC.lean (not importable here).
    -- The non-consecutive case is proved later in this file (top-to-bottom ordering).
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    -- The sweep and odd-winding callbacks are needed for the |Z|=0 pivot
    -- normal-form case (non-zero-winding) and the no-pivot case.
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False := by
  -- Case split on the size of the zero set
  by_cases hZ : (zeroSet gc).card ≥ 3
  · exact zeroSet_ge3_impossible gc _hno_safe (by omega) hZ
  · -- |Z| ≤ 2: at most 2 non-firing processors.
    by_cases hZ0 : (zeroSet gc).card = 0
    · -- |Z| = 0: all processors fire.
      have hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0 := by
        intro p
        by_contra h; push_neg at h
        have hmem : p ∈ zeroSet gc := by simp [zeroSet]; omega
        have := Finset.card_pos.mpr ⟨p, hmem⟩; omega
      -- Split on pivot existence
      by_cases hpivot : ∃ t : Fin sys.rs.n,
          sys.rs.m (left t) = 2 ∧ sys.rs.m (right t) = 2
      · -- Pivot exists + all fire: phase extraction at the pivot.
        obtain ⟨t, hbL, hbR⟩ := hpivot
        have hfc2 := fireCount_ge_2_of_pos gc t (hfull t)
        have hfc_lt := fireCount_lt_length_of_hno_safe gc
          (show sys.rs.n ≥ 5 by omega) _hno_safe t
        -- Classical case split: either ALL phases are normal form, or some
        -- phase triggers a mechanism (entry conflict → done).
        by_cases hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase
        · -- All phases normal form: use allNormalForm_false (1 sorry for phase analysis)
          exact allNormalForm_false gc _hn _hconv _hno_safe _hsub _h3bin t hbL hbR
            hfull hfc2 hfc_lt hall
        · -- Some phase is mechanism-triggering
          push_neg at hall
          obtain ⟨phase_mech, hmech_neg⟩ := hall
          simp only [isNormalFormGap, not_not] at hmech_neg
          exact entryConflict_impossible gc
            (phase_dispatch_ec gc t phase_mech hbL hbR hmech_neg)
      · -- No pivot + all fire: no proc has both binary neighbors.
        have hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i := by
          intro h3consec
          obtain ⟨i, hbin_i, _hbin_ri, hbin_rri⟩ := h3consec
          have hbL : sys.rs.m (left (right i)) = 2 := by
            rw [left_right_eq_self]
            exact hbin_i
          exact hpivot ⟨right i, hbL, hbin_rri⟩
        by_cases hzero : gc.zeroWinding
        · have _hcw_pos : 0 < gc.cwStepCount := by
            by_contra hcw_not_pos
            push_neg at hcw_not_pos
            have hcw0 : gc.cwStepCount = 0 := by omega
            have hccw0 : gc.ccwStepCount = 0 :=
              gc.cwStepCount_eq_ccwStepCount_of_zeroWinding hzero ▸ hcw0
            have hcw_all : ∀ p : Fin sys.rs.n, gc.cwMoveCountAt p = 0 := by
              intro p
              have hle : gc.cwMoveCountAt p ≤ gc.cwStepCount :=
                gc.cwStepCount_eq_sum_cwMoveCountAt ▸
                  Finset.single_le_sum (fun q _ => Nat.zero_le _) (Finset.mem_univ p)
              omega
            have hccw_all : ∀ p : Fin sys.rs.n, gc.ccwMoveCountAt p = 0 := by
              intro p
              have hle : gc.ccwMoveCountAt p ≤ gc.ccwStepCount :=
                gc.ccwStepCount_eq_sum_ccwMoveCountAt ▸
                  Finset.single_le_sum (fun q _ => Nat.zero_le _) (Finset.mem_univ p)
              omega
            have hL := gc.configs_length_pos
            set k₀ : Fin gc.configs.length := ⟨0, hL⟩
            set p₀ := gc.moverAt k₀
            exact trapped_contradicts_hno_safe gc (by omega) p₀
              (hcw_all p₀) (hccw_all p₀) k₀ rfl _hno_safe
          exact hNonConsecZW hzero _hcw_pos hnoncons
        · -- Non-zero-winding, no pivot, all fire: dispatch on cycle type
          by_cases hsweep : gc.isSweep
          · exact hSweepFalse hsweep
          · rcases gc.zeroWinding_or_isOddWinding_of_not_sweep hsweep with hzw | hodd
            · exact (hzero hzw).elim
            · by_cases hunif : gc.uniformDirection
              · exact (gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary _h3bin)
                  ⟨hunif, hodd⟩
              · exact hOddNonUnifFalse hodd hunif
    · -- |Z| ≥ 1: some processor doesn't fire → zero winding.
      have hZ_pos : 0 < (zeroSet gc).card := by omega
      obtain ⟨q, hq_mem⟩ := Finset.card_pos.mp hZ_pos
      have hfc_q : gc.fireCount q = 0 := by simp [zeroSet] at hq_mem; exact hq_mem
      have _hzw : gc.zeroWinding := zeroWinding_of_fc_zero gc q hfc_q
      -- Step 1: Derive cwStepCount > 0 from zero winding + hno_safe.
      -- If cwStepCount = 0: zero winding gives ccwStepCount = 0 too,
      -- so all steps are stays. The mover stays forever at one position,
      -- making processors at ring distance ≥ 3 safe (contradicts hno_safe).
      have _hcw_pos : 0 < gc.cwStepCount := by
        by_contra hcw_not_pos
        push_neg at hcw_not_pos
        have hcw0 : gc.cwStepCount = 0 := by omega
        have hccw0 : gc.ccwStepCount = 0 :=
          gc.cwStepCount_eq_ccwStepCount_of_zeroWinding _hzw ▸ hcw0
        -- All cwMoveCountAt and ccwMoveCountAt are 0
        have hcw_all : ∀ p : Fin sys.rs.n, gc.cwMoveCountAt p = 0 := by
          intro p
          have hle : gc.cwMoveCountAt p ≤ gc.cwStepCount :=
            gc.cwStepCount_eq_sum_cwMoveCountAt ▸
              Finset.single_le_sum (fun q _ => Nat.zero_le _) (Finset.mem_univ p)
          omega
        have hccw_all : ∀ p : Fin sys.rs.n, gc.ccwMoveCountAt p = 0 := by
          intro p
          have hle : gc.ccwMoveCountAt p ≤ gc.ccwStepCount :=
            gc.ccwStepCount_eq_sum_ccwMoveCountAt ▸
              Finset.single_le_sum (fun q _ => Nat.zero_le _) (Finset.mem_univ p)
          omega
        -- Pick any initial step; the mover is trapped there forever.
        have hL := gc.configs_length_pos
        set k₀ : Fin gc.configs.length := ⟨0, hL⟩
        set p₀ := gc.moverAt k₀
        exact trapped_contradicts_hno_safe gc (by omega) p₀
          (hcw_all p₀) (hccw_all p₀) k₀ rfl _hno_safe
      -- Step 2: Case split on 3 consecutive binary.
      by_cases h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i
      · -- CONSECUTIVE: use parametric proof from caller.
        exact hConsecZW _hzw _hcw_pos h3consec
      · -- NON-CONSECUTIVE: use parametric proof from caller.
          exact hNonConsecZW _hzw _hcw_pos h3consec

/-- Shared wrapper for `binary_ring_impossibility` with explicit callbacks.

    The 4 callbacks break the import cycle: they are proved in
    CaseObstructions.lean and threaded through from callers there.
    This avoids PhaseExtraction needing to import CaseObstructions. -/
private theorem binary_ring_impossibility_residual
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9) (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False := by
  exact binary_ring_impossibility gc hn hconv hno_safe hsub h3bin
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- Shared downstream callback bundle for callers that sit above the import
    cycle. This localizes the remaining cycle-type residue to one theorem. -/
private theorem binary_ring_impossibility_residual_callbacks
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9) (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs) :
    (gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) ∧
    (gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) ∧
    (gc.isSweep → False) ∧
    (gc.isOddWinding → ¬gc.uniformDirection → False) := by
  /-
    These are exactly the downstream facts that `PhaseExtraction` cannot
    import directly without recreating the
    `PhaseExtraction -> GlobalMinGap -> CaseObstructions` cycle.
  -/
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero hcw_pos h3consec
    exact zeroWinding_consecutive_false gc hn hconv hno_safe hsub h3bin
      hzero hcw_pos h3consec
  · intro hzero hcw_pos hnoncons
    exact zeroWinding_nonConsecutive_false gc hn hconv hno_safe hsub h3bin
      hzero hcw_pos hnoncons
  · intro hsweep
    exact archive_sweep_false gc hn hconv hno_safe hsub h3bin hsweep
  · intro hodd hnonunif
    exact oddWinding_nonUniform_false gc hn hconv hno_safe hsub h3bin
      hodd hnonunif

/-- **Phase dispatch for a processor with both binary neighbors.**
    Given t with m(left t) = 2, m(right t) = 2, fireCount ≥ 2, fireCount < L,
    and hno_safe + n ≥ 7 + converges: derive False.

    This theorem is placed BEFORE `neighbor_fires_at_prev_step_ec` and
    `palindromic_phase_ec` so that `neighbor_fires_at_prev_step_ec` can call it,
    breaking the former circular dependency.

    Routes through phase_dispatch_ec for mechanism-triggering phases.
    The normal-form residual delegates to `binary_ring_impossibility`. -/
theorem both_binary_neighbors_false
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9) (hconv : converges sys gc)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfc_ge2 : gc.fireCount t ≥ 2)
    (hfc_lt : gc.fireCount t < gc.configs.length)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False := by
  by_cases hmt : sys.rs.m t ≥ 3
  · -- Ternary pivot case: t is sandwiched between two binary neighbors.
    -- Extract a ternary phase and dispatch on mechanism type.
    obtain ⟨phase, _⟩ := exists_ternaryPhase gc t hfc_ge2 hfc_lt
    by_cases hmech : let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
                     let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
                     (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)
    · exact entryConflict_impossible gc (phase_dispatch_ec gc t phase hbL hbR hmech)
    · -- Normal form: no mechanism triggers for this phase.
      -- Delegates to binary_ring_impossibility with explicit callbacks.
      exact binary_ring_impossibility_residual gc hn hconv hno_safe hsub h3bin
        hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
  · -- Binary middle case: t is binary (m t = 2), left t is binary, right t is binary.
    -- This gives three consecutive binary processors: (left t, t, right t).
    -- Delegate to binary_ring_impossibility_residual which handles this
    -- via the hConsecZW callback for the consecutive binary case.
    exact binary_ring_impossibility_residual gc hn hconv hno_safe hsub h3bin
      hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- **Helper: neighbor fires at prev step**.
    When the last neighbor fire in [a, s) is at step s-1 (i.e., the step
    immediately before the mover step s for t), there is no room to place
    a nonmover step between the fire and s. This helper consolidates the
    5 sub-cases of `palindromic_phase_ec` where this occurs.

    The hypothesis `hprev_neighbor` says some neighbor (left or right of t)
    fires at the step immediately before s. All other hypotheses come from
    the outer `palindromic_phase_ec` context.

    **Now sorry-free**: derives False from `both_binary_neighbors_false`
    (defined above), then uses `exfalso` to produce `hasEntryConflict`. -/
private theorem neighbor_fires_at_prev_step_ec
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2)
    (_hbR : sys.rs.m (right t) = 2)
    (phase : TernaryPhase gc t)
    (_hnormal : let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
               let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
               ¬((Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)))
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hn : sys.rs.n ≥ 9)
    (_hconv : converges sys gc)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False)
    (prev : Fin gc.configs.length)
    (hprev_succ : prev.val + 1 = phase.s.val)
    (hprev_neighbor : gc.moverAt prev = left t ∨ gc.moverAt prev = right t) :
    hasEntryConflict gc := by
  exfalso
  have hfc_pos : gc.fireCount t > 0 :=
    fireCount_pos_of_moverAt_eq gc t phase.s phase.hs_mover
  exact both_binary_neighbors_false gc _hn _hconv t _hbL _hbR
    (fireCount_ge_2_of_pos gc t hfc_pos)
    (fireCount_lt_length_of_hno_safe gc (by omega : sys.rs.n ≥ 5) _hno_safe t)
    _hno_safe _hsub _h3bin hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- **Palindromic EC**: For a processor t with both binary neighbors,
    if some phase is in normal form (no mechanism triggers),
    then hasEntryConflict gc.

    The argument: the palindromic structure of the mover word forces
    matching (L,S,R) contexts at mover and non-mover steps. Between
    a CW non-mover step (when right(t) fires) and a CCW mover step
    (when t fires), the values at t, left(t), right(t) return to the
    same state from binary parity and cycle closure. -/
theorem palindromic_phase_ec
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2)
    (_hbR : sys.rs.m (right t) = 2)
    (phase : TernaryPhase gc t)
    (_hnormal : let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
               let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
               ¬((Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)))
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hn : sys.rs.n ≥ 9)
    (_hconv : converges sys gc)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    hasEntryConflict gc := by
  -- The normal form has: ¬BothEven ∧ ¬ToggleFR-L ∧ ¬ToggleFR-R.
  -- This means: (J odd ∨ K odd) ∧ (J<2 ∨ K>0) ∧ (J>0 ∨ K<2).
  -- Cases by J and K size:
  set J := gc.intervalFireCount (left t) phase.a.val phase.s.val with hJ_def
  set K := gc.intervalFireCount (right t) phase.a.val phase.s.val with hK_def
  -- Extract normal form constraints
  have h_not_be : ¬(Even J ∧ Even K) := fun h => _hnormal (Or.inl h)
  have h_not_tl : ¬(J ≥ 2 ∧ K = 0) := fun h => _hnormal (Or.inr (Or.inl h))
  have h_not_tr : ¬(J = 0 ∧ K ≥ 2) := fun h => _hnormal (Or.inr (Or.inr h))
  by_cases hJ2 : J ≥ 2
  · -- J ≥ 2: left(t) fires ≥ 2 in phase. K ≥ 1 (from h_not_be: K can't be 0
    -- when J is even; from h_not_tl: K ≠ 0 when J ≥ 2).
    have hK_pos : K ≥ 1 := by
      by_contra hK0; push_neg at hK0
      interval_cases K
      exact h_not_tl ⟨hJ2, rfl⟩
    -- Extract two consecutive left fires with distinct values,
    -- and use the first right fire as singleton for Traversal Return.
    -- Case A/B argument at the LAST left fire in [a, s):
    -- Find the last left fire step k_max. At config k_max+1:
    -- Case A: left(t) privileged → intervalFireCount > J (left fires again). Contradiction!
    -- Case B: left(t) not privileged → EC with first left fire (same context, different status).
    -- Find the last left(t) fire step in [a, s)
    let fireSetL := (Finset.univ : Finset (Fin gc.configs.length)).filter
      (fun k => phase.a.val ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = left t)
    have hneL : fireSetL.Nonempty := by
      obtain ⟨k, hka, hkb, hkm⟩ := exists_fire_step_in_interval gc (left t)
        (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) (by omega)
      exact ⟨k, by simp [fireSetL]; exact ⟨hka, hkb, hkm⟩⟩
    obtain ⟨k_max, hk_mem, hk_max⟩ := Finset.exists_max_image fireSetL Fin.val hneL
    simp [fireSetL] at hk_mem
    obtain ⟨hka, hkb, hkm⟩ := hk_mem
    -- k_max is the last left fire in [a, s). After k_max: no more left fires before s.
    have hno_more_left : ∀ j : Fin gc.configs.length,
        k_max.val < j.val → j.val < phase.s.val → gc.moverAt j ≠ left t := by
      intro j hj1 hj2 hjm
      have : j ∈ fireSetL := by simp [fireSetL]; exact ⟨by omega, hj2, hjm⟩
      have := hk_max j this; omega
    -- Case A/B: is left(t) privileged at config k_max+1?
    -- Config k_max+1 exists (k_max < s ≤ configs.length - 1, so k_max + 1 < configs.length)
    have hk1_lt : k_max.val + 1 < gc.configs.length := by omega
    -- At config k_max+1: left(t) = flipped value. Context at left(t):
    -- (val(ll, k_max+1), flipped_val, val(t, k_max+1))
    -- left(t) ≠ t (ring topology, n ≥ 4)
    have hlt_ne_t : left t ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [left_val] at this
      have hn := sys.rs.n_ge_4; have ht := t.isLt
      by_cases h0 : t.val = 0
      · rw [h0] at this; simp at this; omega
      · rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this; omega
    -- Case split: is left(t) privileged at config k_max+1?
    by_cases hpriv_next : privileged sys (gc.configs.get ⟨k_max.val + 1, hk1_lt⟩) (left t)
    · -- CASE A: left(t) IS privileged at k_max+1.
      -- But no more left fires in (k_max, s). And k_max+1 ≤ s.
      -- If k_max+1 < s: moverAt(k_max+1) can't be t (ht_nofire) and can't be left(t)
      --   (no more left fires). But left(t) is privileged → someone else is mover →
      --   TWO privileged → unique_privileged contradiction.
      -- If k_max+1 = s: moverAt(s) = t. left(t) also privileged. t ≠ left(t).
      --   TWO privileged → contradiction.
      exfalso
      have hk1_le_s : k_max.val + 1 ≤ phase.s.val := by omega
      by_cases hk1_eq_s : k_max.val + 1 = phase.s.val
      · -- k_max+1 = s: both t and left(t) privileged at s → contradicts unique_privileged
        have hs_config : (⟨k_max.val + 1, hk1_lt⟩ : Fin gc.configs.length) = phase.s :=
          Fin.ext hk1_eq_s
        rw [hs_config] at hpriv_next
        have ht_priv : privileged sys (gc.configs.get phase.s) t := by
          have := gc.moverAt_privileged phase.s; rwa [phase.hs_mover] at this
        have h1 := gc.moverAt_unique phase.s (left t) hpriv_next  -- left t = moverAt s
        have h2 := gc.moverAt_unique phase.s t ht_priv            -- t = moverAt s
        exact hlt_ne_t (h1.trans h2.symm)
      · -- k_max+1 < s: left(t) privileged but can't be the mover
        have hk1_lt_s : k_max.val + 1 < phase.s.val := by omega
        have hstep : Fin.mk (k_max.val + 1) hk1_lt = ⟨k_max.val + 1, hk1_lt⟩ := rfl
        -- moverAt(k_max+1) ≠ left(t) (no more left fires after k_max)
        have hne_left : gc.moverAt ⟨k_max.val + 1, hk1_lt⟩ ≠ left t :=
          hno_more_left ⟨k_max.val + 1, hk1_lt⟩
            (show k_max.val < k_max.val + 1 by omega) hk1_lt_s
        -- But left(t) is privileged → left(t) = moverAt(k_max+1) by uniqueness
        have heq := gc.moverAt_unique ⟨k_max.val + 1, hk1_lt⟩ (left t) hpriv_next
        exact hne_left heq.symm
    · -- CASE B: left(t) NOT privileged at k_max+1.
      -- Between k_max+1 and s: no left fires, no t fires.
      -- val_L and val_T are constant in [k_max+1, s].
      -- Strategy: find a nonmover step for t in [k_max+1, s) where val_R matches val_R(s).
      -- Since right(t) is binary, this holds when right fires even times in [step, s).
      have hk_lt_s : k_max.val < phase.s.val := hkb
      -- No t fires in [k_max+1, s)
      have ht_nofire_km : ∀ k : Fin gc.configs.length,
          k_max.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t := by
        intro k hk1 hk2; exact phase.ht_nofire k (by omega) hk2
      -- No left fires in [k_max+1, s)
      have hL_nofire_km : ∀ k : Fin gc.configs.length,
          k_max.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
        intro k hk1 hk2; exact hno_more_left k (by omega) hk2
      -- Compute right fire count in [k_max+1, s)
      set K_rem := gc.intervalFireCount (right t) (k_max.val + 1) phase.s.val
      -- Find the last right(t) fire in [k_max+1, s) if K_rem > 0
      -- Strategy: if K_rem = 0 or K_rem even, EC via k_max+1.
      --           if K_rem odd ≥ 1, find last right fire r_last;
      --             if r_last < s-1: EC via r_last+1.
      --             if r_last = s-1: need alternative.
      by_cases hkm_eq_s1 : k_max.val + 1 = phase.s.val
      · -- k_max+1 = s: left fires at k_max = s-1, t fires at s.
        exact neighbor_fires_at_prev_step_ec gc t _hbL _hbR phase _hnormal _hno_safe _hn _hconv _hsub _h3bin
              hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
              k_max hkm_eq_s1 (Or.inl hkm)
      · -- k_max+1 < s: there's at least one step in (k_max, s) for a nonmover.
        have hkm1_lt_s : k_max.val + 1 < phase.s.val := by omega
        -- Step k_max+1 is NOT a t-fire
        have hkm1_ne_t : gc.moverAt ⟨k_max.val + 1, hk1_lt⟩ ≠ t :=
          ht_nofire_km ⟨k_max.val + 1, hk1_lt⟩ le_rfl hkm1_lt_s
        by_cases hKrem_even : Even K_rem
        · -- K_rem even: right fires even times in [k_max+1, s).
          -- val_R preserved from k_max+1 to s. val_L and val_T also preserved.
          -- EC between s (mover) and k_max+1 (nonmover).
          refine ⟨phase.s, ⟨k_max.val + 1, hk1_lt⟩, t, phase.hs_mover, hkm1_ne_t, ?_, ?_, ?_⟩
          · -- val_L preserved: no left fires in [k_max+1, s)
            exact (configVal_eq_of_noFire_between gc (left t) (k_max.val + 1) phase.s.val
              (Nat.le_of_lt hkm1_lt_s) phase.s.isLt hL_nofire_km).symm
          · -- val_T preserved: no t fires in [k_max+1, s)
            exact (configVal_eq_of_noFire_between gc t (k_max.val + 1) phase.s.val
              (Nat.le_of_lt hkm1_lt_s) phase.s.isLt ht_nofire_km).symm
          · -- val_R preserved: right fires even times
            exact (binary_config_eq_of_even_intervalFireCount gc (right t) _hbR
              (k_max.val + 1) phase.s.val (Nat.le_of_lt hkm1_lt_s)
              phase.s.isLt hKrem_even).symm
        · -- K_rem odd: find last right fire in [k_max+1, s).
          -- K_rem ≥ 1 (odd and not even → K_rem ≥ 1)
          have hKrem_pos : K_rem ≥ 1 := by
            by_contra h; push_neg at h
            have : K_rem = 0 := by omega
            exact hKrem_even ⟨0, by omega⟩
          -- Find the last right fire
          let fireSetR_km := (Finset.univ : Finset (Fin gc.configs.length)).filter
            (fun k => k_max.val + 1 ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = right t)
          have hneR_km : fireSetR_km.Nonempty := by
            obtain ⟨k, hka, hkb', hkm'⟩ := exists_fire_step_in_interval gc (right t)
              (by omega : k_max.val + 1 ≤ phase.s.val)
              (Nat.le_of_lt phase.s.isLt) hKrem_pos
            exact ⟨k, by simp [fireSetR_km]; exact ⟨hka, hkb', hkm'⟩⟩
          obtain ⟨r_last, hr_mem, hr_max⟩ := Finset.exists_max_image fireSetR_km Fin.val hneR_km
          simp [fireSetR_km] at hr_mem
          obtain ⟨hra, hrb, hrm⟩ := hr_mem
          -- r_last is the last right fire in [k_max+1, s).
          have hno_more_right_km : ∀ j : Fin gc.configs.length,
              r_last.val < j.val → j.val < phase.s.val → gc.moverAt j ≠ right t := by
            intro j hj1 hj2 hjm
            have : j ∈ fireSetR_km := by simp [fireSetR_km]; exact ⟨by omega, hj2, hjm⟩
            have := hr_max j this; omega
          by_cases hr_eq_s1 : r_last.val + 1 = phase.s.val
          · -- Last right fire at s-1.
            exact neighbor_fires_at_prev_step_ec gc t _hbL _hbR phase _hnormal _hno_safe _hn _hconv _hsub _h3bin
              hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
              r_last hr_eq_s1 (Or.inr hrm)
          · -- r_last+1 < s: no right fires in [r_last+1, s).
            -- No left fires, no t fires. All 3 context values match → EC.
            have hra' : k_max.val + 1 ≤ r_last.val := hra
            have hrl1_lt_s : r_last.val + 1 < phase.s.val := by omega
            have hrl1_lt : r_last.val + 1 < gc.configs.length := by
              have := phase.s.isLt; omega
            have hrl1_ge_km : k_max.val + 1 ≤ r_last.val + 1 := by omega
            have hrl1_ne_t : gc.moverAt ⟨r_last.val + 1, hrl1_lt⟩ ≠ t :=
              ht_nofire_km ⟨r_last.val + 1, hrl1_lt⟩ hrl1_ge_km hrl1_lt_s
            -- No right fires in [r_last+1, s)
            have hR_nofire_rl : ∀ k : Fin gc.configs.length,
                r_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
              intro k hk1 hk2; exact hno_more_right_km k (by omega) hk2
            -- No left fires in [r_last+1, s)
            have hL_nofire_rl : ∀ k : Fin gc.configs.length,
                r_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
              intro k hk1 hk2; exact hL_nofire_km k (by omega) hk2
            -- No t fires in [r_last+1, s)
            have ht_nofire_rl : ∀ k : Fin gc.configs.length,
                r_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t := by
              intro k hk1 hk2; exact ht_nofire_km k (by omega) hk2
            refine ⟨phase.s, ⟨r_last.val + 1, hrl1_lt⟩, t, phase.hs_mover, hrl1_ne_t, ?_, ?_, ?_⟩
            · exact (configVal_eq_of_noFire_between gc (left t) (r_last.val + 1) phase.s.val
                (Nat.le_of_lt hrl1_lt_s) phase.s.isLt hL_nofire_rl).symm
            · exact (configVal_eq_of_noFire_between gc t (r_last.val + 1) phase.s.val
                (Nat.le_of_lt hrl1_lt_s) phase.s.isLt ht_nofire_rl).symm
            · exact (configVal_eq_of_noFire_between gc (right t) (r_last.val + 1) phase.s.val
                (Nat.le_of_lt hrl1_lt_s) phase.s.isLt hR_nofire_rl).symm
  · push_neg at hJ2; -- J ≤ 1
    by_cases hK2 : K ≥ 2
    · -- K ≥ 2: symmetric to J ≥ 2 case
      have hJ_pos : J ≥ 1 := by
        by_contra hJ0; push_neg at hJ0
        interval_cases J
        exact h_not_tr ⟨rfl, hK2⟩
      -- Symmetric Case A/B argument with right(t) instead of left(t)
      -- Find the last right(t) fire step in [a, s)
      let fireSetR := (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k => phase.a.val ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = right t)
      have hneR : fireSetR.Nonempty := by
        obtain ⟨k, hka, hkb, hkm⟩ := exists_fire_step_in_interval gc (right t)
          (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) (by omega)
        exact ⟨k, by simp [fireSetR]; exact ⟨hka, hkb, hkm⟩⟩
      obtain ⟨k_max, hk_mem, hk_max⟩ := Finset.exists_max_image fireSetR Fin.val hneR
      simp [fireSetR] at hk_mem
      obtain ⟨hka, hkb, hkm⟩ := hk_mem
      have hno_more_right : ∀ j : Fin gc.configs.length,
          k_max.val < j.val → j.val < phase.s.val → gc.moverAt j ≠ right t := by
        intro j hj1 hj2 hjm
        have : j ∈ fireSetR := by simp [fireSetR]; exact ⟨by omega, hj2, hjm⟩
        have := hk_max j this; omega
      have hk1_lt : k_max.val + 1 < gc.configs.length := by omega
      -- right(t) ≠ t (from n ≥ 4)
      have hrt_ne_t : right t ≠ t := by
        intro h; have hval := congrArg Fin.val h
        simp only [right, Fin.val_mk] at hval
        have hn := sys.rs.n_ge_4; have ht := t.isLt
        by_cases htop : t.val + 1 < sys.rs.n
        · rw [Nat.mod_eq_of_lt htop] at hval; omega
        · have : t.val = sys.rs.n - 1 := by omega
          rw [this, show sys.rs.n - 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hval
          omega
      -- Case A: right(t) privileged at k_max+1 → unique_privileged contradiction
      by_cases hpriv_next : privileged sys (gc.configs.get ⟨k_max.val + 1, hk1_lt⟩) (right t)
      · exfalso
        by_cases hk1_eq_s : k_max.val + 1 = phase.s.val
        · -- k_max+1 = s: both t and right(t) privileged
          have hs_config : (⟨k_max.val + 1, hk1_lt⟩ : Fin gc.configs.length) = phase.s :=
            Fin.ext hk1_eq_s
          rw [hs_config] at hpriv_next
          have ht_priv : privileged sys (gc.configs.get phase.s) t := by
            have := gc.moverAt_privileged phase.s; rwa [phase.hs_mover] at this
          have h1 := gc.moverAt_unique phase.s (right t) hpriv_next
          have h2 := gc.moverAt_unique phase.s t ht_priv
          exact hrt_ne_t (h1.trans h2.symm)
        · -- k_max+1 < s: right(t) privileged but not the mover
          have hk1_lt_s : k_max.val + 1 < phase.s.val := by omega
          have hne_right : gc.moverAt ⟨k_max.val + 1, hk1_lt⟩ ≠ right t :=
            hno_more_right ⟨k_max.val + 1, hk1_lt⟩
              (show k_max.val < k_max.val + 1 by omega) hk1_lt_s
          have heq := gc.moverAt_unique ⟨k_max.val + 1, hk1_lt⟩ (right t) hpriv_next
          exact hne_right heq.symm
      · -- Case B: right(t) NOT privileged at k_max+1. Entry conflict.
        -- Symmetric to J≥2 Case B: between k_max+1 and s, no right fires, no t fires.
        -- val_R and val_T constant. Find nonmover step where val_L also matches.
        have hk_lt_s : k_max.val < phase.s.val := hkb
        have ht_nofire_km : ∀ k : Fin gc.configs.length,
            k_max.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t := by
          intro k hk1 hk2; exact phase.ht_nofire k (by omega) hk2
        have hR_nofire_km : ∀ k : Fin gc.configs.length,
            k_max.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
          intro k hk1 hk2; exact hno_more_right k (by omega) hk2
        set J_rem := gc.intervalFireCount (left t) (k_max.val + 1) phase.s.val
        by_cases hkm_eq_s1 : k_max.val + 1 = phase.s.val
        · -- k_max+1 = s: right fires at k_max = s-1
          exact neighbor_fires_at_prev_step_ec gc t _hbL _hbR phase _hnormal _hno_safe _hn _hconv _hsub _h3bin
              hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
              k_max hkm_eq_s1 (Or.inr hkm)
        · have hkm1_lt_s : k_max.val + 1 < phase.s.val := by omega
          have hkm1_ne_t : gc.moverAt ⟨k_max.val + 1, hk1_lt⟩ ≠ t :=
            ht_nofire_km ⟨k_max.val + 1, hk1_lt⟩ le_rfl hkm1_lt_s
          by_cases hJrem_even : Even J_rem
          · -- J_rem even: val_L preserved → EC
            refine ⟨phase.s, ⟨k_max.val + 1, hk1_lt⟩, t, phase.hs_mover, hkm1_ne_t, ?_, ?_, ?_⟩
            · exact (binary_config_eq_of_even_intervalFireCount gc (left t) _hbL
                (k_max.val + 1) phase.s.val (Nat.le_of_lt hkm1_lt_s)
                phase.s.isLt hJrem_even).symm
            · exact (configVal_eq_of_noFire_between gc t (k_max.val + 1) phase.s.val
                (Nat.le_of_lt hkm1_lt_s) phase.s.isLt ht_nofire_km).symm
            · exact (configVal_eq_of_noFire_between gc (right t) (k_max.val + 1) phase.s.val
                (Nat.le_of_lt hkm1_lt_s) phase.s.isLt hR_nofire_km).symm
          · -- J_rem odd: find last left fire
            have hJrem_pos : J_rem ≥ 1 := by
              by_contra h; push_neg at h
              have : J_rem = 0 := by omega
              exact hJrem_even ⟨0, by omega⟩
            let fireSetL_km := (Finset.univ : Finset (Fin gc.configs.length)).filter
              (fun k => k_max.val + 1 ≤ k.val ∧ k.val < phase.s.val ∧ gc.moverAt k = left t)
            have hneL_km : fireSetL_km.Nonempty := by
              obtain ⟨k, hka, hkb', hkm'⟩ := exists_fire_step_in_interval gc (left t)
                (by omega : k_max.val + 1 ≤ phase.s.val)
                (Nat.le_of_lt phase.s.isLt) hJrem_pos
              exact ⟨k, by simp [fireSetL_km]; exact ⟨hka, hkb', hkm'⟩⟩
            obtain ⟨l_last, hl_mem, hl_max⟩ := Finset.exists_max_image fireSetL_km Fin.val hneL_km
            simp [fireSetL_km] at hl_mem
            obtain ⟨hla, hlb, hlm⟩ := hl_mem
            have hno_more_left_km : ∀ j : Fin gc.configs.length,
                l_last.val < j.val → j.val < phase.s.val → gc.moverAt j ≠ left t := by
              intro j hj1 hj2 hjm
              have : j ∈ fireSetL_km := by simp [fireSetL_km]; exact ⟨by omega, hj2, hjm⟩
              have := hl_max j this; omega
            by_cases hl_eq_s1 : l_last.val + 1 = phase.s.val
            · -- last left fire at s-1
              exact neighbor_fires_at_prev_step_ec gc t _hbL _hbR phase _hnormal _hno_safe _hn _hconv _hsub _h3bin
                hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
                l_last hl_eq_s1 (Or.inl hlm)
            · have hla' : k_max.val + 1 ≤ l_last.val := hla
              have hll1_lt_s : l_last.val + 1 < phase.s.val := by omega
              have hll1_lt : l_last.val + 1 < gc.configs.length := by
                have := phase.s.isLt; omega
              have hll1_ge_km : k_max.val + 1 ≤ l_last.val + 1 := by omega
              have hll1_ne_t : gc.moverAt ⟨l_last.val + 1, hll1_lt⟩ ≠ t :=
                ht_nofire_km ⟨l_last.val + 1, hll1_lt⟩ hll1_ge_km hll1_lt_s
              have hL_nofire_ll : ∀ k : Fin gc.configs.length,
                  l_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
                intro k hk1 hk2; exact hno_more_left_km k (by omega) hk2
              have hR_nofire_ll : ∀ k : Fin gc.configs.length,
                  l_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
                intro k hk1 hk2; exact hR_nofire_km k (by omega) hk2
              have ht_nofire_ll : ∀ k : Fin gc.configs.length,
                  l_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t := by
                intro k hk1 hk2; exact ht_nofire_km k (by omega) hk2
              refine ⟨phase.s, ⟨l_last.val + 1, hll1_lt⟩, t, phase.hs_mover, hll1_ne_t, ?_, ?_, ?_⟩
              · exact (configVal_eq_of_noFire_between gc (left t) (l_last.val + 1) phase.s.val
                  (Nat.le_of_lt hll1_lt_s) phase.s.isLt hL_nofire_ll).symm
              · exact (configVal_eq_of_noFire_between gc t (l_last.val + 1) phase.s.val
                  (Nat.le_of_lt hll1_lt_s) phase.s.isLt ht_nofire_ll).symm
              · exact (configVal_eq_of_noFire_between gc (right t) (l_last.val + 1) phase.s.val
                  (Nat.le_of_lt hll1_lt_s) phase.s.isLt hR_nofire_ll).symm
    · push_neg at hK2 -- K ≤ 1
      -- J ≤ 1 and K ≤ 1. (0,0) excluded by h_not_be (both even).
      -- So (J,K) ∈ {(0,1), (1,0), (1,1)}.
      -- Strategy: find the last neighbor fire in [a, s). After that fire,
      -- no neighbor fires. val_L, val_T, val_R all constant → EC if there's
      -- a nonmover step for t between the last fire and s.
      -- The "last fire" is the max of the last left fire and last right fire.
      -- If the last fire is at step s-1: no intermediate step → sorry.
      -- If the last fire is before s-1: EC.
      have hJK_sum_pos : J + K ≥ 1 := by
        by_contra h; push_neg at h
        have hJ0 : J = 0 := by omega
        have hK0 : K = 0 := by omega
        exact h_not_be ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩
      -- Combine: find the last step in [a, s) that fires left(t) or right(t)
      let fireSetLR := (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k => phase.a.val ≤ k.val ∧ k.val < phase.s.val ∧
          (gc.moverAt k = left t ∨ gc.moverAt k = right t))
      have hneLR : fireSetLR.Nonempty := by
        -- J + K ≥ 1 means there's at least one left or right fire in [a, s)
        by_cases hJ_pos : J ≥ 1
        · obtain ⟨k, hka, hkb', hkm'⟩ := exists_fire_step_in_interval gc (left t)
            (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hJ_pos
          exact ⟨k, by simp [fireSetLR]; exact ⟨hka, hkb', Or.inl hkm'⟩⟩
        · push_neg at hJ_pos
          have hK_pos : K ≥ 1 := by omega
          obtain ⟨k, hka, hkb', hkm'⟩ := exists_fire_step_in_interval gc (right t)
            (Nat.le_of_lt phase.ha_lt_s) (Nat.le_of_lt phase.s.isLt) hK_pos
          exact ⟨k, by simp [fireSetLR]; exact ⟨hka, hkb', Or.inr hkm'⟩⟩
      obtain ⟨lr_last, hlr_mem, hlr_max⟩ := Finset.exists_max_image fireSetLR Fin.val hneLR
      simp [fireSetLR] at hlr_mem
      obtain ⟨hlra, hlrb, hlrm⟩ := hlr_mem
      -- No left or right fires after lr_last in [lr_last+1, s)
      have hno_more_lr : ∀ j : Fin gc.configs.length,
          lr_last.val < j.val → j.val < phase.s.val →
          gc.moverAt j ≠ left t ∧ gc.moverAt j ≠ right t := by
        intro j hj1 hj2
        constructor
        · intro hjm
          have : j ∈ fireSetLR := by simp [fireSetLR]; exact ⟨by omega, hj2, Or.inl hjm⟩
          have := hlr_max j this; omega
        · intro hjm
          have : j ∈ fireSetLR := by simp [fireSetLR]; exact ⟨by omega, hj2, Or.inr hjm⟩
          have := hlr_max j this; omega
      by_cases hlr_eq_s1 : lr_last.val + 1 = phase.s.val
      · -- Last neighbor fire at s-1.
        exact neighbor_fires_at_prev_step_ec gc t _hbL _hbR phase _hnormal _hno_safe _hn _hconv _hsub _h3bin
              hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
              lr_last hlr_eq_s1 hlrm
      · -- lr_last+1 < s: no neighbor fires in [lr_last+1, s).
        -- No left, no right, no t fires → all context preserved → EC.
        have hlra' : phase.a.val ≤ lr_last.val := hlra
        have hlr1_lt_s : lr_last.val + 1 < phase.s.val := by omega
        have hlr1_lt : lr_last.val + 1 < gc.configs.length := by
          have := phase.s.isLt; omega
        have hlr1_ge_a : phase.a.val ≤ lr_last.val + 1 := by omega
        have hlr1_ne_t : gc.moverAt ⟨lr_last.val + 1, hlr1_lt⟩ ≠ t :=
          phase.ht_nofire ⟨lr_last.val + 1, hlr1_lt⟩ hlr1_ge_a hlr1_lt_s
        -- Helpers for noFire in [lr_last+1, s)
        have hL_nofire_lr : ∀ k : Fin gc.configs.length,
            lr_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
          intro k hk1 hk2; exact (hno_more_lr k (by omega) hk2).1
        have hR_nofire_lr : ∀ k : Fin gc.configs.length,
            lr_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
          intro k hk1 hk2; exact (hno_more_lr k (by omega) hk2).2
        have ht_nofire_lr : ∀ k : Fin gc.configs.length,
            lr_last.val + 1 ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ t := by
          intro k hk1 hk2; exact phase.ht_nofire k (by omega) hk2
        refine ⟨phase.s, ⟨lr_last.val + 1, hlr1_lt⟩, t, phase.hs_mover, hlr1_ne_t, ?_, ?_, ?_⟩
        · exact (configVal_eq_of_noFire_between gc (left t) (lr_last.val + 1) phase.s.val
            (Nat.le_of_lt hlr1_lt_s) phase.s.isLt hL_nofire_lr).symm
        · exact (configVal_eq_of_noFire_between gc t (lr_last.val + 1) phase.s.val
            (Nat.le_of_lt hlr1_lt_s) phase.s.isLt ht_nofire_lr).symm
        · exact (configVal_eq_of_noFire_between gc (right t) (lr_last.val + 1) phase.s.val
            (Nat.le_of_lt hlr1_lt_s) phase.s.isLt hR_nofire_lr).symm

/-- Callback-free wrapper around `palindromic_phase_ec`.

    Higher-level files use this wrapper to route the all-normal residual
    through the single shared callback bundle above instead of carrying
    three separate callback stubs. -/
theorem palindromic_phase_ec_residual
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    (_hbL : sys.rs.m (left t) = 2)
    (_hbR : sys.rs.m (right t) = 2)
    (phase : TernaryPhase gc t)
    (_hnormal : let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
               let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
               ¬((Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)))
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hn : sys.rs.n ≥ 9)
    (_hconv : converges sys gc)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs) :
    hasEntryConflict gc := by
  obtain ⟨hConsecZW, hNonConsecZW, hSweepFalse, hOddNonUnifFalse⟩ :=
    binary_ring_impossibility_residual_callbacks gc _hn _hconv _hno_safe _hsub _h3bin
  exact palindromic_phase_ec gc t _hbL _hbR phase _hnormal _hno_safe _hn _hconv _hsub _h3bin
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-! ### Step 6: Helpers for subThreshold_binary_core_false -/

-- Note: both_binary_neighbors_false is now defined earlier (before neighbor_fires_at_prev_step_ec)
-- to break the circular dependency. See "Step 5d" above.

/-- If fc(p) = 0, then moverAt(k) ≠ p for all steps k. -/
theorem neverMover_of_fc_zero_local (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p = 0) (k : Fin gc.configs.length) :
    gc.moverAt k ≠ p := by
  intro hmov
  have hpos := fireCount_pos_of_moverAt_eq gc p k hmov
  omega

/-- If fc(i) = fc(right i) = fc(right(right i)) = 0, then right(i) is a
    safe processor, contradicting hno_safe. -/
theorem three_neverFire_safe_local (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hfc_i : gc.fireCount i = 0)
    (hfc_ri : gc.fireCount (right i) = 0)
    (hfc_rri : gc.fireCount (right (right i)) = 0)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False := by
  apply hno_safe
  refine ⟨right i, fun k => ⟨?_, ?_, ?_⟩⟩
  · exact neverMover_of_fc_zero_local gc (right i) hfc_ri k
  · rw [left_right_eq_self]; exact neverMover_of_fc_zero_local gc i hfc_i k
  · exact neverMover_of_fc_zero_local gc (right (right i)) hfc_rri k

private theorem no_firing_both_binary_neighbors_false
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hno_pivot : ¬∃ t : Fin sys.rs.n,
      sys.rs.m (left t) = 2 ∧ sys.rs.m (right t) = 2 ∧ gc.fireCount t > 0)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False := by
  -- _hno_pivot: for all t, if both neighbors binary then fc(t) = 0
  -- Reformulate: any proc with both binary neighbors never fires
  have hpivot_fc0 : ∀ t : Fin sys.rs.n,
      sys.rs.m (left t) = 2 → sys.rs.m (right t) = 2 → gc.fireCount t = 0 := by
    intro t hL hR
    by_contra hne
    apply _hno_pivot
    exact ⟨t, hL, hR, by omega⟩
  -- From _hno_safe: every proc's neighborhood is visited by the mover
  -- Use hno_safe_visit (from BinaryRightCrossing.lean):
  --   ∀ q, ∃ k, moverAt k = q ∨ moverAt k = left q ∨ moverAt k = right q
  --
  -- Proof strategy:
  -- The hypotheses _hno_pivot + _hno_safe + _h3bin + _hn + _hsub + _hconv
  -- are jointly contradictory. The key argument depends on the binary
  -- placement structure:
  --
  -- Case 1 (≥5 consecutive binary): inner 3 procs all have both binary
  --   neighbors → fc=0 → three_neverFire_safe → contradiction with _hno_safe.
  --
  -- Case 2 (exactly 3-4 consecutive binary with outer endpoints non-binary):
  --   The middle procs have fc=0, but outer binary procs fire without having
  --   both binary neighbors. Zero-winding structure (from caller context) forces
  --   the mover to traverse through the binary group, creating edge crossings
  --   that generate an entry conflict. This case requires the caller to provide
  --   zero-winding or waterfall structure directly.
  --
  -- Case 3 (non-consecutive, all gaps ≥ 2): no proc has both binary neighbors,
  --   _hno_pivot is vacuously true. This case should be routed through the
  --   shadow cycle / wiggle approach rather than phase extraction.
  --
  -- Currently only Case 1 is handled; Cases 2-3 require architectural changes
  -- to the caller (CaseObstructions.lean / GlobalMinGap.lean) to route through
  -- the correct proof strategy for each binary placement pattern.
  -- Delegates to the single shared residual theorem.
  exact binary_ring_impossibility_residual gc _hn _hconv _hno_safe _hsub _h3bin
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-! ### Step 6b: Core obstruction theorem -/

/-- **Core obstruction**: ≥3 binary + sub-threshold + no safe processor + converges ⟹ False.

    Strategy: find a processor t with both binary neighbors that fires (fc > 0).
    If found: fc ≥ 2 (fireCount_ne_one), fc < L (from hno_safe), extract
    TernaryPhase, dispatch to phase_dispatch_ec or palindromic_phase_ec.
    If not found: delegate to no_firing_both_binary_neighbors_false. -/
theorem subThreshold_binary_core_false
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False := by
  by_cases hpivot : ∃ t : Fin sys.rs.n,
      sys.rs.m (left t) = 2 ∧ sys.rs.m (right t) = 2 ∧ gc.fireCount t > 0
  · obtain ⟨t, hbL, hbR, hfc_pos⟩ := hpivot
    exact both_binary_neighbors_false gc _hn _hconv t hbL hbR
      (fireCount_ge_2_of_pos gc t hfc_pos)
      (fireCount_lt_length_of_hno_safe gc (by omega : sys.rs.n ≥ 5) _hno_safe t) _hno_safe
      _hsub _h3bin hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
  · exact no_firing_both_binary_neighbors_false gc _hn _hsub _h3bin _hconv
      _hno_safe hpivot hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- Callback-free wrapper around `subThreshold_binary_core_false`. -/
theorem subThreshold_binary_core_false_residual
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False := by
  obtain ⟨hConsecZW, hNonConsecZW, hSweepFalse, hOddNonUnifFalse⟩ :=
    binary_ring_impossibility_residual_callbacks gc _hn _hconv _hno_safe _hsub _h3bin
  exact subThreshold_binary_core_false gc _hn _hsub _h3bin _hconv _hno_safe
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-! ### Step 7: Main theorems -/

/-- **Non-consecutive binary => False.** -/
theorem gapDecisive_false
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False :=
  subThreshold_binary_core_false gc _hn _hsub _h3bin _hconv _hno_safe
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- **Non-consecutive binary with sub-threshold implies False.** -/
theorem nonConsecutive_phase_extraction_false
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (hsub : subThreshold sys.rs)
    (h3bin : hasGe3Binary sys.rs)
    (hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False :=
  gapDecisive_false gc hn hsub h3bin hnoncons hconv hno_safe
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

end LeanMn
