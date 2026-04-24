/-
  PhaseExtractionClean.lean — Phase extraction assembly WITHOUT AllNormalFormFalse

  Replaces PhaseExtraction.lean's dependency on AllNormalFormFalse (8300-line monolith)
  with AllNormalFormFalse2 (626-line clean rewrite), breaking the import cycle.

  Does NOT import:
    - PhaseExtraction.lean
    - CaseObstructions.lean
    - CaseObstructionsCore.lean
    - AllNormalFormFalse.lean

  Provides `subThreshold_binary_core_false_clean` with the same callback signature
  as `subThreshold_binary_core_false` (PhaseExtraction.lean).
-/
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase
import LeanMn.LowerBound.Archive.EntryConflict.AllNormalFormFalse2

namespace LeanMn

variable {sys : System}

/-- **Binary ring impossibility (clean version).**
    Same as `binary_ring_impossibility` in PhaseExtraction.lean but uses
    `allNormalForm_false2` (AllNormalFormFalse2.lean) instead of `allNormalForm_false`.

    Key change: when all phases are normal form at a pivot t, we case-split on
    whether m(t) ≥ 3 (ternary → allNormalForm_false2) or m(t) = 2 (binary →
    three consecutive binary → delegate to hConsecZW callback). -/
private theorem binary_ring_impossibility_clean
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9) (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False := by
  -- Case split on the size of the zero set
  by_cases hZ : (zeroSet gc).card ≥ 3
  · exact zeroSet_ge3_impossible gc _hno_safe (by omega) hZ
  · by_cases hZ0 : (zeroSet gc).card = 0
    · -- |Z| = 0: all processors fire.
      have hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0 := by
        intro p
        by_contra h; push_neg at h
        have hmem : p ∈ zeroSet gc := by simp [zeroSet]; omega
        have := Finset.card_pos.mpr ⟨p, hmem⟩; omega
      -- Split on pivot existence
      by_cases hpivot : ∃ t : Fin sys.rs.n,
          sys.rs.m (left t) = 2 ∧ sys.rs.m (right t) = 2
      · obtain ⟨t, hbL, hbR⟩ := hpivot
        have hfc2 := fireCount_ge_2_of_pos gc t (hfull t)
        have hfc_lt := fireCount_lt_length_of_hno_safe gc
          (show sys.rs.n ≥ 5 by omega) _hno_safe t
        by_cases hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase
        · -- All phases normal form: case split on m(t) ≥ 3
          by_cases hmt : sys.rs.m t ≥ 3
          · -- Ternary pivot: use allNormalForm_false2
            exact allNormalForm_false2 gc _hn _hconv _hno_safe _hsub _h3bin
              t hbL hbR hmt hfull hfc2 hfc_lt hall
          · -- m(t) < 3 → m(t) = 2 (since m ≥ 2 always) → three consecutive binary
            -- left(t) binary, t binary, right(t) binary
            push_neg at hmt
            have hmt2 : sys.rs.m t = 2 := by
              have := sys.rs.m_pos t; omega
            -- Derive: three consecutive binary at (left t)
            have h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i := by
              refine ⟨left t, ?_, ?_, ?_⟩
              · -- isBinary (left t)
                exact hbL
              · -- isBinary (right (left t)) = isBinary t
                simp [isBinary, right_left_eq_self]; exact hmt2
              · -- isBinary (right (right (left t))) = isBinary (right t)
                simp [right_left_eq_self]; exact hbR
            -- Need zero winding to call hConsecZW.
            -- But we're in |Z|=0 branch (all fire), not necessarily zero winding.
            -- Route through the non-zero-winding dispatch instead.
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
              exact hConsecZW hzero _hcw_pos h3consec
            · -- Non-zero-winding: dispatch on cycle type
              by_cases hsweep : gc.isSweep
              · exact hSweepFalse hsweep
              · rcases gc.zeroWinding_or_isOddWinding_of_not_sweep hsweep with hzw | hodd
                · exact (hzero hzw).elim
                · by_cases hunif : gc.uniformDirection
                  · exact (gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary _h3bin)
                      ⟨hunif, hodd⟩
                  · exact hOddNonUnifFalse hodd hunif
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
        · -- Non-zero-winding, no pivot, all fire
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
      have _hcw_pos : 0 < gc.cwStepCount := by
        by_contra hcw_not_pos
        push_neg at hcw_not_pos
        have hcw0 : gc.cwStepCount = 0 := by omega
        have hccw0 : gc.ccwStepCount = 0 :=
          gc.cwStepCount_eq_ccwStepCount_of_zeroWinding _hzw ▸ hcw0
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
      by_cases h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i
      · exact hConsecZW _hzw _hcw_pos h3consec
      · exact hNonConsecZW _hzw _hcw_pos h3consec

/-- Wrapper for `binary_ring_impossibility_clean` with explicit callbacks. -/
private theorem binary_ring_impossibility_residual_clean
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
  exact binary_ring_impossibility_clean gc hn hconv hno_safe hsub h3bin
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- **Phase dispatch for a processor with both binary neighbors (clean version).**
    Same as `both_binary_neighbors_false` in PhaseExtraction.lean but routes
    through `allNormalForm_false2` instead of `allNormalForm_false`. -/
theorem both_binary_neighbors_false_clean
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
  · -- Ternary pivot case
    obtain ⟨phase, _⟩ := exists_ternaryPhase gc t hfc_ge2 hfc_lt
    by_cases hmech : let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
                     let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
                     (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)
    · exact entryConflict_impossible gc (phase_dispatch_ec gc t phase hbL hbR hmech)
    · exact binary_ring_impossibility_residual_clean gc hn hconv hno_safe hsub h3bin
        hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
  · -- Binary middle case: delegates to callbacks
    exact binary_ring_impossibility_residual_clean gc hn hconv hno_safe hsub h3bin
      hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- **No-firing-pivot case (clean version).**
    When no processor with both binary neighbors fires, delegate to callbacks. -/
private theorem no_firing_both_binary_neighbors_false_clean
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
  exact binary_ring_impossibility_residual_clean gc _hn _hconv _hno_safe _hsub _h3bin
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- **Core obstruction (clean version)**: ≥3 binary + sub-threshold + no safe processor + converges ⟹ False.
    Uses `allNormalForm_false2` (AllNormalFormFalse2.lean) instead of `allNormalForm_false`. -/
theorem subThreshold_binary_core_false_clean
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
    exact both_binary_neighbors_false_clean gc _hn _hconv t hbL hbR
      (fireCount_ge_2_of_pos gc t hfc_pos)
      (fireCount_lt_length_of_hno_safe gc (by omega : sys.rs.n ≥ 5) _hno_safe t) _hno_safe
      _hsub _h3bin hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse
  · exact no_firing_both_binary_neighbors_false_clean gc _hn _hsub _h3bin _hconv
      _hno_safe hpivot hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

end LeanMn
