/-
  OddWinding.lean — Odd winding case (|displacement| = n)

  Case E from lb_complete_proof.md:
  Phase extraction + NormalFormEC. No callbacks.

  The odd-winding cycle has |displacement| = n, so every edge is traversed
  at least once (edgeTraversalCount_pos_of_isOddWinding). Combined with
  uniform direction being impossible (from hasGe3Binary), this forces
  non-uniform direction structure.

  For consecutive binary: IsolatedFirings trichotomy → phase dispatch + NormalFormEC.
  For non-consecutive: same treatment (phase extraction from any binary proc).
-/
import LeanMn.LowerBound.CycleTypes
import LeanMn.LowerBound.EntryConflict.IsolatedFirings
import LeanMn.LowerBound.EntryConflict.IsolatedParityEC
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase
import LeanMn.LowerBound.EntryConflict.NonConsecutive
import LeanMn.LowerBound.EntryConflict.NonConsecutiveEC
import LeanMn.LowerBound.Obstruction.NonZeroWinding

namespace LeanMn

variable {sys : System}

/-! ### Odd-winding helpers -/

/-- Odd winding → every processor fires > 0. -/
private theorem oddWinding_fireCount_pos
    (gc : GoodCycle sys) (hodd : gc.isOddWinding) (p : Fin sys.rs.n) :
    gc.fireCount p > 0 := by
  have h1 := gc.edgeTraversalCount_pos_of_isOddWinding hodd (left p)
  have h2 := gc.edgeTraversalCount_pos_of_isOddWinding hodd p
  have hsum := gc.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay p
  omega

/-- Binary proc with fc > 0 has fc ≥ 2 (even, non-zero). -/
private theorem binary_fireCount_ge2
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p) (hpos : gc.fireCount p > 0) :
    gc.fireCount p ≥ 2 := by
  have hne1 := gc.fireCount_ne_one p
  omega

/-- Permanent mover → totalDisplacement = 0 (contradicts odd winding). -/
private theorem permanent_mover_disp_zero
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hperm : ∀ k : Fin gc.configs.length, gc.moverAt k = p) :
    totalDisplacement gc = 0 := by
  rw [gc.totalDisplacement_eq_cwStepCount_sub_ccwStepCount]
  have hcw0 : gc.cwStepCount = 0 := by
    unfold GoodCycle.cwStepCount
    apply Finset.sum_eq_zero; intro k _
    by_cases hdir : gc.stepDir k = .cw
    · exfalso
      have hnext := gc.eq_right_of_stepDir_eq_cw hdir
      rw [hperm k] at hnext
      have := hperm (nextIndex gc.configs k)
      rw [hnext] at this
      have hval := congrArg Fin.val this
      simp only [right_val] at hval
      have hp := p.isLt; have hn4 := sys.rs.n_ge_4
      by_cases h1 : p.val + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt h1] at hval; omega
      · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
    · simp [show ¬(gc.stepDir k = .cw) from hdir]
  have hccw0 : gc.ccwStepCount = 0 := by
    unfold GoodCycle.ccwStepCount
    apply Finset.sum_eq_zero; intro k _
    by_cases hdir : gc.stepDir k = .ccw
    · exfalso
      have hnext := gc.eq_left_of_stepDir_eq_ccw hdir
      rw [hperm k] at hnext
      have := hperm (nextIndex gc.configs k)
      rw [hnext] at this
      have hleft_ne : left p ≠ p := by
        intro heq; have hval := congrArg Fin.val heq
        simp only [left, Fin.val_mk] at hval
        have hp := p.isLt; have hn4 := sys.rs.n_ge_4
        by_cases h0 : p.val = 0
        · rw [h0] at hval; simp only [Nat.zero_add] at hval
          have : (sys.rs.n - 1) % sys.rs.n = sys.rs.n - 1 := Nat.mod_eq_of_lt (by omega)
          rw [this] at hval; omega
        · have hsub : p.val + sys.rs.n - 1 - sys.rs.n = p.val - 1 := by omega
          rw [Nat.mod_eq_sub_mod (by omega), hsub] at hval
          have : (p.val - 1) % sys.rs.n = p.val - 1 := Nat.mod_eq_of_lt (by omega)
          rw [this] at hval; omega
      exact hleft_ne (Fin.ext (congrArg Fin.val this))
    · simp [show ¬(gc.stepDir k = .ccw) from hdir]
  simp [hcw0, hccw0]

/-! ### Consecutive binary sub-case for odd winding -/

/-- Consecutive binary + isolated → phase extraction + NormalFormEC → False.
    Same structure as Sweep.consec_isolated_false but for odd winding. -/
private theorem oddWinding_consec_isolated_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hodd : gc.isOddWinding) (hnonunif : ¬gc.uniformDirection)
    (i : Fin sys.rs.n) (h3consec : threeConsecutiveBinary sys.rs i)
    (hfc_ri : gc.fireCount (right i) ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i) :
    False := by
  have hfull := oddWinding_fireCount_pos gc hodd
  -- Need fc(ri) < CL (some mover outside ri)
  -- Under odd winding with non-uniform direction, the walk visits multiple procs
  have hfc_lt : gc.fireCount (right i) < gc.configs.length := by
    -- From hiso + hfc_ri: some step k fires ri, but nextIndex k doesn't.
    rw [gc.fireCount_eq_sum_moverAt]
    -- Get a step k where ri fires
    have ⟨k, hk⟩ : ∃ k : Fin gc.configs.length, gc.moverAt k = right i := by
      by_contra hall; push_neg at hall
      have : gc.fireCount (right i) = 0 := by
        rw [gc.fireCount_eq_sum_moverAt]; apply Finset.sum_eq_zero
        intro j _; simp [hall j]
      omega
    -- nextIndex k doesn't fire ri (by isolation)
    have hne := hiso k hk
    calc ∑ j : Fin gc.configs.length,
          (if gc.moverAt j = right i then (1 : Nat) else 0)
        < ∑ j : Fin gc.configs.length, 1 := by
          apply Finset.sum_lt_sum
          · intro j _; split <;> omega
          · exact ⟨nextIndex gc.configs k, Finset.mem_univ _,
              by simp [show gc.moverAt (nextIndex gc.configs k) ≠ right i from hne]⟩
      _ = gc.configs.length := by simp
  have hbL : sys.rs.m (left (right i)) = 2 := by
    rw [show left (right i) = i from left_right_eq_self i]; exact h3consec.1
  have hbR : sys.rs.m (right (right i)) = 2 := h3consec.2.2
  -- Parity check
  let mg := exists_minFiringGap gc (right i) hfc_ri
  have _hgap2 := isolated_minFiringGap_gap_ge2 gc (right i) hfc_ri hiso
  by_cases hparity :
      gc.prefixFireCount i (mg.a.val + 1) % 2 =
        gc.prefixFireCount i mg.b.val % 2 ∧
      gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
        gc.prefixFireCount (right (right i)) mg.b.val % 2
  · exact entryConflict_impossible gc
      (isolated_minGap_ec_of_parity_match h3consec hfc_ri hiso hparity.1 hparity.2)
  · -- Phase extraction → dispatch or NormalFormEC
    obtain ⟨phase, _⟩ := exists_ternaryPhase gc (right i) hfc_ri hfc_lt
    by_cases hmech :
        let J := gc.intervalFireCount (left (right i)) phase.a.val phase.s.val
        let K := gc.intervalFireCount (right (right i)) phase.a.val phase.s.val
        (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)
    · exact entryConflict_impossible gc (phase_dispatch_ec gc (right i) phase hbL hbR hmech)
    · exact oddWinding_nonUniform_obstruction hn gc hconv hsub hodd hnonunif h3bin

/-! ### Non-consecutive binary sub-case for odd winding -/

/-- Non-consecutive binary odd winding → False via the odd-winding
    half of the split non-consec obstruction
    (`nonConsecutive_oddWinding_false`). -/
private theorem oddWinding_nonConsec_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hodd : gc.isOddWinding)
    (hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) :
    False :=
  nonConsecutive_oddWinding_false hn gc hconv hsub h3bin hodd hnoncons

/-! ### Main theorem -/

/-- **Odd winding → False.** No callbacks.

    Takes isOddWinding hypothesis directly. Handles both consecutive and
    non-consecutive binary sub-cases. -/
theorem oddWinding_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hodd : gc.isOddWinding) (hnonunif : ¬gc.uniformDirection) :
    False := by
  have hfull := oddWinding_fireCount_pos gc hodd
  by_cases h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i
  · -- CONSECUTIVE BINARY
    obtain ⟨i, hbin_i, hbin_ri, hbin_rri⟩ := h3consec
    have h3c : threeConsecutiveBinary sys.rs i := ⟨hbin_i, hbin_ri, hbin_rri⟩
    have hfc_ri := binary_fireCount_ge2 gc (right i) hbin_ri (hfull (right i))
    rcases binary_isolated_firings_or_ec gc (right i) hbin_ri hfc_ri with hec | hperm | hiso
    · exact entryConflict_impossible gc hec
    · -- Permanent → displacement 0, contradicts |disp| = n
      have hW0 := permanent_mover_disp_zero gc (right i) hperm
      unfold GoodCycle.isOddWinding at hodd
      have : (totalDisplacement gc).natAbs = 0 := by rw [hW0]; decide
      omega
    · exact oddWinding_consec_isolated_false hn gc hconv hno_safe hsub h3bin hodd hnonunif i h3c hfc_ri hiso
  · -- NON-CONSECUTIVE BINARY
    exact oddWinding_nonConsec_false hn gc hconv hno_safe hsub h3bin hodd h3consec

end LeanMn
