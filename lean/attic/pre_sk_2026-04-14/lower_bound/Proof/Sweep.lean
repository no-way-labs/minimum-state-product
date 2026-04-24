/-
  Sweep.lean — Sweep case (|displacement| ≥ 2n)

  Case D from lb_complete_proof.md:
  - D1 (consecutive binary): IsolatedFirings trichotomy → phase dispatch + NormalFormEC
  - D2 (non-consecutive binary): direct contradiction via `nonConsecutive_false`

  No callbacks. Each sub-case terminates with a contradiction.
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

/-! ### Sweep helpers -/

/-- Sweep → |edgeNetFlow| ≥ 2 at every edge. -/
private theorem sweep_edgeNetFlow_ge2
    (gc : GoodCycle sys) (hsweep : gc.isSweep) (p : Fin sys.rs.n) :
    Int.natAbs (gc.edgeNetFlow p) ≥ 2 := by
  unfold GoodCycle.isSweep at hsweep
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow p, Int.natAbs_mul] at hsweep
  have hn4 := sys.rs.n_ge_4
  have : Int.natAbs (↑sys.rs.n : Int) = sys.rs.n := by simp
  rw [this] at hsweep
  by_contra hlt; push_neg at hlt
  have hle : Int.natAbs (gc.edgeNetFlow p) ≤ 1 := by omega
  have : sys.rs.n * Int.natAbs (gc.edgeNetFlow p) ≤ sys.rs.n * 1 :=
    Nat.mul_le_mul_left sys.rs.n hle
  omega

/-- Sweep → fireCount ≥ 2 for every processor. -/
private theorem sweep_fireCount_ge2
    (gc : GoodCycle sys) (hsweep : gc.isSweep) (p : Fin sys.rs.n) :
    gc.fireCount p ≥ 2 := by
  have hflow := sweep_edgeNetFlow_ge2 gc hsweep p
  by_cases hpos : gc.edgeNetFlow p ≥ 0
  · have hge2 : gc.edgeNetFlow p ≥ 2 := by omega
    unfold GoodCycle.edgeNetFlow at hge2
    have hcw_ge2 : gc.cwMoveCountAt p ≥ 2 := by omega
    have hpart := gc.fireCount_eq_moveCount_partition p
    omega
  · push_neg at hpos
    have hle : gc.edgeNetFlow p ≤ -2 := by omega
    unfold GoodCycle.edgeNetFlow at hle
    have hflow_left : gc.edgeNetFlow (left p) = gc.edgeNetFlow p :=
      gc.edgeNetFlow_constant p (left p)
    have hle' : gc.edgeNetFlow (left p) ≤ -2 := by omega
    unfold GoodCycle.edgeNetFlow at hle'
    have hrlp : right (left p) = p := by simpa using right_left_eq_self p
    rw [hrlp] at hle'
    have hccw_ge2 : gc.ccwMoveCountAt p ≥ 2 := by omega
    have hpart := gc.fireCount_eq_moveCount_partition p
    omega

/-- Permanent mover → totalDisplacement = 0. -/
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

/-! ### Consecutive binary sub-case

For 3 consecutive binary at i, ri, rri:
1. Trichotomy at ri: EC / permanent / isolated
2. Permanent contradicts sweep (displacement 0 vs ≥ 2n)
3. Isolated: parity check → EC or phase extraction
4. Phase extraction: dispatch or NormalFormEC -/

/-- For n ≥ 6, there exists a processor outside the 5-neighborhood {li, i, ri, rri, rrri}. -/
private theorem exists_outside_triple_neighborhood
    (hn : sys.rs.n ≥ 6) (i : Fin sys.rs.n) :
    ∃ q : Fin sys.rs.n,
      q ≠ left i ∧ q ≠ i ∧ q ≠ right i ∧
      q ≠ right (right i) ∧ q ≠ right (right (right i)) := by
  by_contra hall
  push_neg at hall
  have hcover :
      ∀ x : Fin sys.rs.n,
        x = left i ∨ x = i ∨ x = right i ∨
          x = right (right i) ∨ x = right (right (right i)) := by
    intro x
    by_cases hx_li : x = left i
    · exact Or.inl hx_li
    · by_cases hx_i : x = i
      · exact Or.inr (Or.inl hx_i)
      · by_cases hx_ri : x = right i
        · exact Or.inr (Or.inr (Or.inl hx_ri))
        · by_cases hx_rri : x = right (right i)
          · exact Or.inr (Or.inr (Or.inr (Or.inl hx_rri)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (hall x hx_li hx_i hx_ri hx_rri))))
  have hsub :
      (Finset.univ : Finset (Fin sys.rs.n)) ⊆
        ({left i, i, right i, right (right i), right (right (right i))} :
          Finset (Fin sys.rs.n)) := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcover x
  have hle := Finset.card_le_card hsub
  rw [Finset.card_fin] at hle
  have h5 :
      ({left i, i, right i, right (right i), right (right (right i))} :
        Finset (Fin sys.rs.n)).card ≤ 5 := by
    let S₁ : Finset (Fin sys.rs.n) := {left i}
    let S₂ : Finset (Fin sys.rs.n) := {i}
    let S₃ : Finset (Fin sys.rs.n) := {right i}
    let S₄ : Finset (Fin sys.rs.n) := {right (right i)}
    let S₅ : Finset (Fin sys.rs.n) := {right (right (right i))}
    let U₁₂ : Finset (Fin sys.rs.n) := S₁ ∪ S₂
    let U₁₂₃ : Finset (Fin sys.rs.n) := U₁₂ ∪ S₃
    let U₁₂₃₄ : Finset (Fin sys.rs.n) := U₁₂₃ ∪ S₄
    let U : Finset (Fin sys.rs.n) := U₁₂₃₄ ∪ S₅
    have hsub5 :
        ({left i, i, right i, right (right i), right (right (right i))} :
          Finset (Fin sys.rs.n)) ⊆ U := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [U, U₁₂₃₄, U₁₂₃, U₁₂, S₁, S₂, S₃, S₄, S₅,
          Finset.mem_singleton]
    calc ({left i, i, right i, right (right i), right (right (right i))} :
          Finset (Fin sys.rs.n)).card
        ≤ U.card :=
            Finset.card_le_card hsub5
      _ ≤ U₁₂₃₄.card + S₅.card := by
            simpa [U, U₁₂₃₄, S₅] using Finset.card_union_le U₁₂₃₄ S₅
      _ ≤ (U₁₂₃.card + S₄.card) + S₅.card := by
            linarith [Finset.card_union_le U₁₂₃ S₄]
      _ ≤ ((U₁₂.card + S₃.card) + S₄.card) + S₅.card := by
            linarith [Finset.card_union_le U₁₂ S₃]
      _ ≤ (((S₁.card + S₂.card) + S₃.card) + S₄.card) + S₅.card := by
            linarith [Finset.card_union_le S₁ S₂]
      _ = 5 := by simp [S₁, S₂, S₃, S₄, S₅]
  omega

/-- Safe processor from mover confinement to triple. -/
private theorem safe_from_mover_triple
    (hn : sys.rs.n ≥ 6) (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hsubset : ∀ k : Fin gc.configs.length,
      gc.moverAt k = i ∨ gc.moverAt k = right i ∨ gc.moverAt k = right (right i)) :
    ∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q := by
  obtain ⟨q, hq_li, hq_i, hq_ri, hq_rri, hq_r3⟩ :=
    exists_outside_triple_neighborhood hn i
  refine ⟨q, ?_⟩
  intro k
  rcases hsubset k with hmov | hmov | hmov
  · refine ⟨?_, ?_, ?_⟩
    · intro hq
      exact hq_i (by calc q = gc.moverAt k := hq.symm
        _ = i := hmov)
    · intro hlq; exact hq_ri (by
        calc q = right (left q) := by simp [right_left_eq_self]
          _ = right (gc.moverAt k) := by rw [hlq]
          _ = right i := by rw [hmov])
    · intro hrq; exact hq_li (by
        calc q = left (right q) := by simp [left_right_eq_self]
          _ = left (gc.moverAt k) := by rw [hrq]
          _ = left i := by rw [hmov])
  · refine ⟨?_, ?_, ?_⟩
    · intro hq
      exact hq_ri (by calc q = gc.moverAt k := hq.symm
        _ = right i := hmov)
    · intro hlq; exact hq_rri (by
        calc q = right (left q) := by simp [right_left_eq_self]
          _ = right (gc.moverAt k) := by rw [hlq]
          _ = right (right i) := by rw [hmov])
    · intro hrq; exact hq_i (by
        calc q = left (right q) := by simp [left_right_eq_self]
          _ = left (gc.moverAt k) := by rw [hrq]
          _ = left (right i) := by rw [hmov]
          _ = i := by simp [left_right_eq_self])
  · refine ⟨?_, ?_, ?_⟩
    · intro hq
      exact hq_rri (by calc q = gc.moverAt k := hq.symm
        _ = right (right i) := hmov)
    · intro hlq; exact hq_r3 (by
        calc q = right (left q) := by simp [right_left_eq_self]
          _ = right (gc.moverAt k) := by rw [hlq]
          _ = right (right (right i)) := by rw [hmov])
    · intro hrq; exact hq_ri (by
        calc q = left (right q) := by simp [left_right_eq_self]
          _ = left (gc.moverAt k) := by rw [hrq]
          _ = left (right (right i)) := by rw [hmov]
          _ = right i := by simp [left_right_eq_self])

/-- Consecutive binary with isolated firings at ri → False.
    Phase extraction + dispatch + NormalFormEC. NO CALLBACKS. -/
private theorem consec_isolated_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hsweep : gc.isSweep)
    (i : Fin sys.rs.n) (h3consec : threeConsecutiveBinary sys.rs i)
    (hfc_ri : gc.fireCount (right i) ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = right i → gc.moverAt (nextIndex gc.configs a) ≠ right i) :
    False := by
  -- Every processor fires > 0 (under sweep, fc ≥ 2; or under safe-proc negation + fairness)
  have hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0 := by
    intro p
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair p
    have hmov : gc.moverAt k = p := by
      rw [← hj]; exact (gc.moverAt_unique k j hpriv).symm
    rw [gc.fireCount_eq_sum_moverAt]
    have h2 := Finset.single_le_sum
      (f := fun i : Fin gc.configs.length =>
        if gc.moverAt i = p then (1 : Nat) else 0)
      (fun i _ => by simp only []; split_ifs <;> omega) (Finset.mem_univ k)
    simp only [hmov, ite_true] at h2; omega
  -- Safe processor contradiction via hfull
  -- Mover confinement: if all movers in {i, ri, rri}, safe proc exists, contradicts hno_safe
  by_cases hsubset : ∀ k : Fin gc.configs.length,
      gc.moverAt k = i ∨ gc.moverAt k = right i ∨ gc.moverAt k = right (right i)
  · obtain ⟨q, hq⟩ := safe_from_mover_triple (by omega) gc i hsubset
    exact hno_safe ⟨q, hq⟩
  · push_neg at hsubset
    obtain ⟨k_out, hk_ni, hk_nri, hk_nrri⟩ := hsubset
    -- Some mover outside triple → fc(ri) < CL
    have hfc_lt : gc.fireCount (right i) < gc.configs.length := by
      rw [gc.fireCount_eq_sum_moverAt]
      calc ∑ j : Fin gc.configs.length,
            (if gc.moverAt j = right i then (1 : Nat) else 0)
          < ∑ j : Fin gc.configs.length, 1 := by
            apply Finset.sum_lt_sum
            · intro j _; split <;> omega
            · exact ⟨k_out, Finset.mem_univ k_out, by simp [hk_nri]⟩
        _ = gc.configs.length := by simp
    -- Binary neighbors of ri
    have hbL : sys.rs.m (left (right i)) = 2 := by
      rw [show left (right i) = i from left_right_eq_self i]; exact h3consec.1
    have hbR : sys.rs.m (right (right i)) = 2 := h3consec.2.2
    -- MinFiringGap for ri
    let mg := exists_minFiringGap gc (right i) hfc_ri
    have hgap2 := isolated_minFiringGap_gap_ge2 gc (right i) hfc_ri hiso
    -- Parity check
    by_cases hparity :
        gc.prefixFireCount i (mg.a.val + 1) % 2 =
          gc.prefixFireCount i mg.b.val % 2 ∧
        gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
          gc.prefixFireCount (right (right i)) mg.b.val % 2
    · -- Even parity → EC
      exact entryConflict_impossible gc
        (isolated_minGap_ec_of_parity_match h3consec hfc_ri hiso hparity.1 hparity.2)
    · -- Odd parity → phase extraction
      -- Extract TernaryPhase for ri
      obtain ⟨phase, _⟩ := exists_ternaryPhase gc (right i) hfc_ri hfc_lt
      -- Try dispatchable mechanisms first
      by_cases hmech :
          let J := gc.intervalFireCount (left (right i)) phase.a.val phase.s.val
          let K := gc.intervalFireCount (right (right i)) phase.a.val phase.s.val
          (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)
      · exact entryConflict_impossible gc (phase_dispatch_ec gc (right i) phase hbL hbR hmech)
      · exact sweep_obstruction hn gc hconv hsub hsweep h3bin

/-! ### Main theorem -/

/-- **Sweep → False.** No callbacks.

    Consecutive: IsolatedFirings trichotomy + phase dispatch + NormalFormEC.
    Non-consecutive: reuse the direct `nonConsecutive_false` theorem. -/
theorem sweep_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hsweep : gc.isSweep) :
    False := by
  have hfc2 : ∀ p : Fin sys.rs.n, gc.fireCount p ≥ 2 := sweep_fireCount_ge2 gc hsweep
  by_cases h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i
  · -- CONSECUTIVE BINARY
    obtain ⟨i, hbin_i, hbin_ri, hbin_rri⟩ := h3consec
    have h3c : threeConsecutiveBinary sys.rs i := ⟨hbin_i, hbin_ri, hbin_rri⟩
    have hfc_ri := hfc2 (right i)
    rcases binary_isolated_firings_or_ec gc (right i) hbin_ri hfc_ri with hec | hperm | hiso
    · exact entryConflict_impossible gc hec
    · -- Permanent mover → displacement 0, contradicts sweep
      have hW0 := permanent_mover_disp_zero gc (right i) hperm
      unfold GoodCycle.isSweep at hsweep
      have : (totalDisplacement gc).natAbs = 0 := by rw [hW0]; decide
      omega
    · exact consec_isolated_false hn gc hconv hno_safe hsub h3bin hsweep i h3c hfc_ri hiso
  · -- NON-CONSECUTIVE BINARY
    exact nonConsecutive_sweep_false hn gc hconv hsub h3bin hsweep h3consec

end LeanMn
