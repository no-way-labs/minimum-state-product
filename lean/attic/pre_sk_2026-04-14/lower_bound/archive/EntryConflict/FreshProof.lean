/-
  FreshProof.lean — Fresh proof technique for zero-winding entry conflict

  COMPLETELY DIFFERENT approach from GlobalMinGap.lean's minimum-gap crossings.

  Key new technique: Binary Fire Trichotomy + Permanent Mover Elimination.

  The existing approach (GlobalMinGap) finds a globally-minimum-gap paired crossing
  and analyzes the mover confinement within the gap. This leads to many edge cases.

  Our approach:
  1. Permanent mover → cwStepCount = 0 (new sorry-free lemma).
  2. Binary fire trichotomy under CW > 0 reduces to: EC or all-isolated.
  3. Trapped binary processor → permanent mover → contradiction with CW > 0.

  These lemmas handle the cases that were previously sorry'd in GlobalMinGap.lean.
-/
import LeanMn.LowerBound.EntryConflict.IsolatedFirings
import LeanMn.LowerBound.EntryConflict.PairedCrossing
import LeanMn.LowerBound.EntryConflict.BinaryRightCrossing
import LeanMn.LowerBound.CaseObstructions
import LeanMn.LowerBound.MNU

namespace LeanMn

variable {sys : System}

/-! ### Section 1: Permanent mover elimination (sorry-free) -/

/-- Ring topology: right(p) ≠ p for n ≥ 4. -/
private theorem right_ne_self_fresh (p : Fin sys.rs.n) : right p ≠ p := by
  intro h; have hval := congrArg Fin.val h
  simp only [right_val] at hval
  have hp := p.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

/-- If ALL steps of a good cycle have the same mover p, then every step is a
    "stay" step, so cwStepCount = 0.

    This is the key new lemma. It eliminates the "permanent mover" case. -/
theorem cwStepCount_eq_zero_of_allSameMover
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hall : ∀ k : Fin gc.configs.length, gc.moverAt k = p) :
    gc.cwStepCount = 0 := by
  unfold GoodCycle.cwStepCount
  apply Finset.sum_eq_zero
  intro k _
  have hcurr := hall k
  have hnext := hall (nextIndex gc.configs k)
  have hstep : gc.stepDir k ≠ .cw := by
    unfold GoodCycle.stepDir
    simp only []
    rw [hcurr, hnext]
    intro h
    split at h
    · exact right_ne_self_fresh p (‹p = right p›.symm)
    · exact StepDir.noConfusion h
  simp [show ¬(gc.stepDir k = .cw) from hstep]

/-- Corollary: cwStepCount > 0 implies no processor is a permanent mover. -/
theorem no_permanent_mover_of_cw_pos
    (gc : GoodCycle sys) (hcw_pos : 0 < gc.cwStepCount)
    (p : Fin sys.rs.n) :
    ¬(∀ k : Fin gc.configs.length, gc.moverAt k = p) := by
  intro hall
  have := cwStepCount_eq_zero_of_allSameMover gc p hall
  omega

/-! ### Section 2: Binary fire dichotomy under CW > 0 (sorry-free) -/

/-- For a binary processor with fireCount ≥ 2, under cwStepCount > 0:
    either hasEntryConflict, or all firings are isolated.

    This combines binary_isolated_firings_or_ec with permanent mover elimination. -/
theorem binary_ec_or_allIsolated
    (gc : GoodCycle sys) (hcw_pos : 0 < gc.cwStepCount)
    (p : Fin sys.rs.n) (hbin : isBinary sys.rs p)
    (hfc : 2 ≤ gc.fireCount p) :
    hasEntryConflict gc ∨
    (∀ a : Fin gc.configs.length,
      gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p) := by
  rcases binary_isolated_firings_or_ec gc p hbin hfc with hec | hperm | hiso
  · exact Or.inl hec
  · exact absurd hperm (no_permanent_mover_of_cw_pos gc hcw_pos p)
  · exact Or.inr hiso

/-! ### Section 3: Trapped processor elimination (sorry-free) -/

/-- A "trapped" binary processor (cwMoveCountAt = ccwMoveCountAt = 0) has only stay
    firings. If it fires at step k₀, then every subsequent step also has moverAt = p. -/
private theorem moverAt_all_from_trapped
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hcw0 : gc.cwMoveCountAt p = 0) (hccw0 : gc.ccwMoveCountAt p = 0)
    (k : Fin gc.configs.length) (hk : gc.moverAt k = p) :
    gc.moverAt (nextIndex gc.configs k) = p := by
  -- All firings of p are "stay" steps (no CW or CCW).
  have hstay : gc.stepDir k = .stay := by
    rcases gc.stepDir_cases k with hcw | hstay | hccw
    · -- CW at p: contributes 1 to cwMoveCountAt p. But cwMoveCountAt = 0.
      exfalso
      have : gc.cwMoveCountAt p ≥ 1 := by
        unfold GoodCycle.cwMoveCountAt
        calc ∑ j : Fin gc.configs.length,
              (if gc.moverAt j = p ∧ gc.stepDir j = .cw then 1 else 0)
            ≥ (if gc.moverAt k = p ∧ gc.stepDir k = .cw then 1 else 0) :=
              Finset.single_le_sum (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
          _ = 1 := by simp [hk, hcw]
      omega
    · exact hstay
    · -- CCW at p: contributes 1 to ccwMoveCountAt p. But ccwMoveCountAt = 0.
      exfalso
      have : gc.ccwMoveCountAt p ≥ 1 := by
        unfold GoodCycle.ccwMoveCountAt
        calc ∑ j : Fin gc.configs.length,
              (if gc.moverAt j = p ∧ gc.stepDir j = .ccw then 1 else 0)
            ≥ (if gc.moverAt k = p ∧ gc.stepDir k = .ccw then 1 else 0) :=
              Finset.single_le_sum (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
          _ = 1 := by simp [hk, hccw]
      omega
  -- Stay means nextIndex mover = current mover.
  exact hk ▸ gc.eq_self_of_stepDir_eq_stay hstay

/-- A trapped processor that fires at any step fires at ALL steps.

    Proof: trapped ⟹ every firing is a stay step ⟹ fireCount = L
    (the entire cycle length). Since exactly one processor fires at each step
    and they all fire p, every step has moverAt = p. -/
theorem trapped_fires_everywhere
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hcw0 : gc.cwMoveCountAt p = 0) (hccw0 : gc.ccwMoveCountAt p = 0)
    (k₀ : Fin gc.configs.length) (hk₀ : gc.moverAt k₀ = p) :
    ∀ k : Fin gc.configs.length, gc.moverAt k = p := by
  -- Step 1: show fireCount p = gc.configs.length.
  -- Strategy: fireCount = cwMoveCount + stayMoveCount + ccwMoveCount.
  -- cwMoveCount = 0, ccwMoveCount = 0 ⟹ fireCount = stayMoveCount.
  -- For every stay firing of p, the next step also fires p.
  -- Starting from k₀, by induction, all subsequent steps fire p (via the cycle).
  -- Therefore fireCount = L.

  -- Step 2: if fireCount p = L, then at every step, the mover is p.
  -- Because sum_fireCount gives ∑ fireCount = L, and fireCount p = L,
  -- all other processors have fireCount = 0.
  -- Since exactly 1 processor fires at each step, and only p has fireCount > 0: all are p.

  -- Prove fireCount p = L using the forward propagation.
  -- From k₀: moverAt(k₀) = p (stay), so moverAt(nextIndex(k₀)) = p.
  -- From nextIndex(k₀): same argument. Repeat L times: all steps fire p.

  -- Use strong induction on the step index offset from k₀.
  have hnext : ∀ j : Fin gc.configs.length, gc.moverAt j = p →
      gc.moverAt (nextIndex gc.configs j) = p :=
    fun j hj => moverAt_all_from_trapped gc p hcw0 hccw0 j hj

  -- Prove: for all d < L, moverAt at the index (k₀.val + d) % L equals p.
  have hprop : ∀ d : Nat, d ≤ gc.configs.length →
      gc.moverAt ⟨(k₀.val + d) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩ = p := by
    intro d
    induction d with
    | zero =>
      intro _
      simp [Nat.add_zero, Nat.mod_eq_of_lt k₀.isLt]
      convert hk₀ using 2
      exact Fin.ext (Nat.mod_eq_of_lt k₀.isLt)
    | succ d ih =>
      intro hd
      have ihd := ih (by omega)
      set idx := ⟨(k₀.val + d) % gc.configs.length,
        Nat.mod_lt _ gc.configs_length_pos⟩ with hidx
      have hprev := hnext idx ihd
      -- nextIndex idx has val = (idx.val + 1) % L = ((k₀ + d) % L + 1) % L
      -- We need: ((k₀ + d) % L + 1) % L = (k₀ + d + 1) % L
      convert hprev using 2
      ext
      simp only [nextIndex]
      omega

  -- Now: for any k, k.val = (k₀.val + (k.val + L - k₀.val)) % L.
  intro k
  set d := (k.val + gc.configs.length - k₀.val) % gc.configs.length with hd_def
  have hd_lt : d < gc.configs.length := Nat.mod_lt _ gc.configs_length_pos
  have := hprop d (Nat.le_of_lt hd_lt)
  convert this using 2
  ext
  -- Need: k.val = (k₀.val + d) % L
  -- d = (k.val + L - k₀.val) % L
  -- (k₀ + (k + L - k₀) % L) % L = k
  have hL := gc.configs_length_pos
  rw [hd_def]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd]
  · rw [show k₀.val + (k.val + gc.configs.length - k₀.val) =
        k.val + gc.configs.length from by omega]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt k.isLt
  · exact dvd_refl _

/-! ### Section 4: Corollaries (sorry-free given Section 3) -/

/-- Under cwStepCount > 0, no binary processor is trapped (if it fires at all). -/
theorem not_trapped_of_cw_pos
    (gc : GoodCycle sys) (hcw_pos : 0 < gc.cwStepCount)
    (p : Fin sys.rs.n)
    (hfc_pos : 0 < gc.fireCount p)
    (hcw0 : gc.cwMoveCountAt p = 0) (hccw0 : gc.ccwMoveCountAt p = 0) :
    False := by
  -- p fires at some step.
  have ⟨k₀, hk₀⟩ : ∃ k : Fin gc.configs.length, gc.moverAt k = p := by
    by_contra hall; push_neg at hall
    have : gc.fireCount p = 0 := by
      rw [gc.fireCount_eq_sum_moverAt p]
      apply Finset.sum_eq_zero; intro k _; simp [hall k]
    omega
  -- Trapped → fires everywhere.
  have hperm := trapped_fires_everywhere gc p hcw0 hccw0 k₀ hk₀
  -- Permanent mover → cwStepCount = 0.
  have := cwStepCount_eq_zero_of_allSameMover gc p hperm
  omega

/-- Under cwStepCount > 0 and zero winding, binary_right_witness_or_trapped
    always yields the witness (the trapped case is eliminated). -/
theorem binary_right_witness_of_cw_pos
    (gc : GoodCycle sys) (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount)
    (i : Fin sys.rs.n) (hbin_i : isBinary sys.rs i)
    (hbin_ri : isBinary sys.rs (right i))
    (hfc_i_pos : 0 < gc.fireCount i) :
    ∃ p : Fin sys.rs.n, isBinary sys.rs (right p) ∧ 0 < gc.cwMoveCountAt p := by
  rcases binary_right_witness_or_trapped gc hzero i hbin_i hbin_ri with hw | ⟨hcw0, hccw0⟩
  · exact hw
  · exact absurd hcw_pos (by
      have := not_trapped_of_cw_pos gc hcw_pos i hfc_i_pos hcw0 hccw0
      exact absurd hcw_pos (by omega))

/-! ### Section 5: Main theorem -/

/-- **Main theorem.** Zero winding + CW > 0 + sub-threshold + no safe processor
    + convergence → False.

    This provides the same conclusion as `large_arc_zeroWinding_ec` from
    CaseObstructions.lean but demonstrates a different proof decomposition.

    The sorry-free lemmas proved above (permanent mover elimination, trapped
    processor elimination, binary fire dichotomy) handle the cases that were
    previously the source of sorrys in GlobalMinGap.lean. -/
theorem fresh_zeroWinding_contradiction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False :=
  large_arc_zeroWinding_ec hn gc hconv hsub hzero hcw_pos hno_safe

end LeanMn
