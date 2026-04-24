/-
  FireCountNe.lean — fireCount ≠ 1 lemma

  Extracted from CaseObstructions.lean to break the circular dependency:
    CaseObstructions → NestedFirings → CaseObstructions
  This file only imports CycleTypes, so it can be imported by NestedFirings
  without creating a cycle.
-/
import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

/-! ### Helpers -/

private theorem stateAfter_length_eq (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.stateAfter p gc.configs.length = gc.stateAfter p 0 := by
  -- stateAfter p L: L ≥ L so stateAfter_of_ge gives configs[firstIndex] p
  -- stateAfter p 0: 0 < L so stateAfter_of_lt gives configs[⟨0,...⟩] p
  -- firstIndex.val = 0 by definition (but private), so both point to configs[0]
  -- Use native_decide or prove through intermediate steps
  have h1 := gc.stateAfter_of_ge p (le_refl gc.configs.length)
  have h2 := gc.stateAfter_of_lt p gc.configs_length_pos
  rw [h1, h2]; rfl

/-- If p doesn't fire at step m, its stateAfter is preserved. -/
private theorem stateAfter_step_preserved (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (m : Nat) (hm : m < gc.configs.length) (hne : gc.moverAt ⟨m, hm⟩ ≠ p) :
    gc.stateAfter p (m + 1) = gc.stateAfter p m := by
  have hval := gc.state_eq_of_ne_moverAt ⟨m, hm⟩ p (Ne.symm hne)
  -- hval : configs.get(nextIndex m) p = configs.get(m) p
  by_cases hm1 : m + 1 < gc.configs.length
  · rw [gc.stateAfter_of_lt p hm1, gc.stateAfter_of_lt p hm]
    have hnext : nextIndex gc.configs ⟨m, hm⟩ = ⟨m + 1, hm1⟩ :=
      Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hm1])
    rw [← hnext]; exact hval
  · have hm1_eq : m + 1 = gc.configs.length := by omega
    rw [show m + 1 = gc.configs.length from hm1_eq, stateAfter_length_eq gc,
        gc.stateAfter_of_lt p gc.configs_length_pos, gc.stateAfter_of_lt p hm]
    have hnext : nextIndex gc.configs ⟨m, hm⟩ = ⟨0, gc.configs_length_pos⟩ :=
      Fin.ext (by simp [nextIndex, hm1_eq, Nat.mod_self])
    rw [← hnext]; exact hval

/-- If p doesn't fire in [a, b), stateAfter is preserved. -/
private theorem stateAfter_range_preserved (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hno : ∀ (j : Fin gc.configs.length), a ≤ j.val → j.val < b → gc.moverAt j ≠ p) :
    gc.stateAfter p b = gc.stateAfter p a := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; rfl
  | succ b ih =>
    by_cases hab' : a = b + 1
    · subst hab'; rfl
    · have hab2 : a ≤ b := by omega
      have hblt : b < gc.configs.length := by omega
      have hstep := stateAfter_step_preserved gc p b hblt
        (hno ⟨b, hblt⟩ hab2 (Nat.lt_succ_self b))
      rw [hstep]
      exact ih (by omega) (by omega)
        (fun j haj hjb => hno j haj (by omega))

/-- p fires at step k: stateAfter changes. -/
private theorem stateAfter_changes_at_fire (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Nat) (hk : k < gc.configs.length) (hmov : gc.moverAt ⟨k, hk⟩ = p) :
    gc.stateAfter p (k + 1) ≠ gc.stateAfter p k := by
  by_cases hk1 : k + 1 < gc.configs.length
  · rw [gc.stateAfter_of_lt p hk1, gc.stateAfter_of_lt p hk]
    have hnext : nextIndex gc.configs ⟨k, hk⟩ = ⟨k + 1, hk1⟩ :=
      Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hk1])
    rw [← hnext, ← hmov]; exact gc.state_ne_at_moverAt ⟨k, hk⟩
  · rw [show k + 1 = gc.configs.length from by omega, stateAfter_length_eq gc,
        gc.stateAfter_of_lt p gc.configs_length_pos, gc.stateAfter_of_lt p hk]
    have hnext : nextIndex gc.configs ⟨k, hk⟩ = ⟨0, gc.configs_length_pos⟩ :=
      Fin.ext (by simp [nextIndex, show k + 1 = gc.configs.length from by omega, Nat.mod_self])
    rw [← hnext, ← hmov]; exact gc.state_ne_at_moverAt ⟨k, hk⟩

/-! ### fireCount ≠ 1 -/

theorem GoodCycle.fireCount_ne_one (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.fireCount p ≠ 1 := by
  intro hone
  -- There exists a step where p fires
  have hexists : ∃ k : Fin gc.configs.length, gc.moverAt k = p := by
    by_contra hall; push_neg at hall
    have : gc.fireCount p = 0 := by
      unfold GoodCycle.fireCount GoodCycle.prefixFireCount
      apply Finset.sum_eq_zero; intro k hk
      rw [gc.fireIndicator_of_lt p (Finset.mem_range.mp hk)]
      simp [show gc.moverAt ⟨k, Finset.mem_range.mp hk⟩ ≠ p from hall _]
    omega
  obtain ⟨⟨k, hklt⟩, hkp⟩ := hexists
  -- k is the unique fire step (since fireCount = 1)
  have huniq : ∀ j : Fin gc.configs.length, gc.moverAt j = p → j.val = k := by
    intro ⟨j, hjlt⟩ hjp; by_contra hne
    have hge2 : gc.fireCount p ≥ 2 := by
      unfold GoodCycle.fireCount GoodCycle.prefixFireCount
      have hmem_k : k ∈ Finset.range gc.configs.length := Finset.mem_range.mpr hklt
      have herase := Finset.sum_erase_add
        (Finset.range gc.configs.length) (fun i => gc.fireIndicator p i) hmem_k
      have hmem_j : j ∈ (Finset.range gc.configs.length).erase k := by
        rw [Finset.mem_erase]; exact ⟨hne, Finset.mem_range.mpr hjlt⟩
      have _herase2 := Finset.sum_erase_add
        ((Finset.range gc.configs.length).erase k) (fun i => gc.fireIndicator p i) hmem_j
      have hnn : ∀ i ∈ ((Finset.range gc.configs.length).erase k).erase j,
          0 ≤ gc.fireIndicator p i := by
        intro i _; unfold GoodCycle.fireIndicator; split_ifs <;> omega
      have hk1 : gc.fireIndicator p k = 1 := by
        rw [gc.fireIndicator_of_lt p hklt]; simp [hkp]
      have hj1 : gc.fireIndicator p j = 1 := by
        rw [gc.fireIndicator_of_lt p hjlt]; simp [hjp]
      linarith [Finset.sum_nonneg hnn]
    omega
  have hno : ∀ j, j ≠ k → (hj : j < gc.configs.length) → gc.moverAt ⟨j, hj⟩ ≠ p :=
    fun j hne hj hmov => absurd (huniq ⟨j, hj⟩ hmov) hne
  -- Chain: stateAfter(k) = stateAfter(0) = stateAfter(L) = stateAfter(k+1)
  have hbefore := stateAfter_range_preserved gc p 0 k (Nat.zero_le k) (by omega)
    (fun j haj hjk => by
      have hjne : j.val ≠ k := by omega
      exact hno j.val hjne j.isLt)
  have hafter := stateAfter_range_preserved gc p (k + 1) gc.configs.length (by omega) le_rfl
    (fun j hkj hjL => by
      have hjne : j.val ≠ k := by omega
      exact hno j.val hjne j.isLt)
  have hclosure := stateAfter_length_eq gc p
  have hfire := stateAfter_changes_at_fire gc p k hklt hkp
  -- stateAfter(k+1) = stateAfter(L) = stateAfter(0) = stateAfter(k) → contradiction
  exact hfire (by rw [← hafter, hclosure, hbefore])

end LeanMn
