import LeanMn.SmallN.M6SystemFront
import LeanMn.LowerBound.EntryConflict.IsolatedFirings
import LeanMn.LowerBound.EntryConflict.BinaryParity

namespace LeanMn

variable {sys : System}

theorem allNormal_phase_right_or_left_before_t
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t) :
    gc.moverAt ⟨phase.s.val - 1,
        by
          have := phase.ha_lt_s
          have := phase.s.isLt
          omega⟩ = left t ∨
      gc.moverAt ⟨phase.s.val - 1,
        by
          have := phase.ha_lt_s
          have := phase.s.isLt
          omega⟩ = right t :=
  allNormal_phase_prev_is_neighbor gc t hall phase

theorem allNormal_one_sided_counts
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase) :
    (gc.intervalFireCount (left t) phase.a.val phase.s.val = 0 →
      gc.intervalFireCount (right t) phase.a.val phase.s.val = 1) ∧
    (gc.intervalFireCount (right t) phase.a.val phase.s.val = 0 →
      gc.intervalFireCount (left t) phase.a.val phase.s.val = 1) := by
  exact ⟨(normalForm_gap_constraint gc t phase hnorm).1,
    (normalForm_gap_constraint gc t phase hnorm).2.1⟩

theorem allNormal_phase_neighbor_sum_pos'
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hnorm : isNormalFormGap gc t phase) :
    1 ≤
      gc.intervalFireCount (left t) phase.a.val phase.s.val +
      gc.intervalFireCount (right t) phase.a.val phase.s.val :=
  normalForm_phase_neighbor_sum_pos gc t phase hnorm

theorem allNormal_phase_prev_left_of_right_count_zero
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hK0 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 0) :
    gc.moverAt ⟨phase.s.val - 1,
        by
          have := phase.ha_lt_s
          have := phase.s.isLt
          omega⟩ = left t := by
  let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  have hprev_val : prev.val = phase.s.val - 1 := rfl
  have hs_pos : 0 < phase.s.val := by
    exact lt_of_le_of_lt (Nat.zero_le phase.a.val) phase.ha_lt_s
  have hs1 : phase.a.val + 1 ≤ phase.s.val := Nat.succ_le_of_lt phase.ha_lt_s
  have hprev_ge_a : phase.a.val ≤ prev.val := by
    rw [hprev_val]
    omega
  have hprev_lt_s : prev.val < phase.s.val := by
    rw [hprev_val]
    omega
  rcases allNormal_phase_right_or_left_before_t gc t hall phase with hL | hR
  · simpa [prev] using hL
  · have hsingle : gc.intervalFireCount (right t) prev.val (prev.val + 1) = 1 := by
      rw [intervalFireCount_single gc (right t) prev.isLt]
      simp [prev, hR]
    have hsplit := intervalFireCount_split gc (right t)
      (a := phase.a.val) (c := prev.val) (b := phase.s.val)
      hprev_ge_a (Nat.le_of_lt hprev_lt_s)
    have hs_eq : prev.val + 1 = phase.s.val := by
      rw [hprev_val]
      omega
    have htail1 : gc.intervalFireCount (right t) prev.val phase.s.val = 1 := by
      simpa [hs_eq] using hsingle
    omega

theorem allNormal_phase_prev_right_of_left_count_zero
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hJ0 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 0) :
    gc.moverAt ⟨phase.s.val - 1,
        by
          have := phase.ha_lt_s
          have := phase.s.isLt
          omega⟩ = right t := by
  let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  have hprev_val : prev.val = phase.s.val - 1 := rfl
  have hs_pos : 0 < phase.s.val := by
    exact lt_of_le_of_lt (Nat.zero_le phase.a.val) phase.ha_lt_s
  have hs1 : phase.a.val + 1 ≤ phase.s.val := Nat.succ_le_of_lt phase.ha_lt_s
  have hprev_ge_a : phase.a.val ≤ prev.val := by
    rw [hprev_val]
    omega
  have hprev_lt_s : prev.val < phase.s.val := by
    rw [hprev_val]
    omega
  rcases allNormal_phase_right_or_left_before_t gc t hall phase with hL | hR
  · have hsingle : gc.intervalFireCount (left t) prev.val (prev.val + 1) = 1 := by
      rw [intervalFireCount_single gc (left t) prev.isLt]
      simp [prev, hL]
    have hsplit := intervalFireCount_split gc (left t)
      (a := phase.a.val) (c := prev.val) (b := phase.s.val)
      hprev_ge_a (Nat.le_of_lt hprev_lt_s)
    have hs_eq : prev.val + 1 = phase.s.val := by
      rw [hprev_val]
      omega
    have htail1 : gc.intervalFireCount (left t) prev.val phase.s.val = 1 := by
      simpa [hs_eq] using hsingle
    omega
  · simpa [prev] using hR

theorem m6_binary_sandwich_residue_with_phase
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        gc.fireCount t ≥ 2 ∧
        gc.fireCount t < gc.configs.length ∧
        (∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase) ∧
        ∃ _phase : TernaryPhase gc t, True := by
  exact valid_reduces_to_ternary_binary_sandwich_allNormal_with_phase_of_binaryCount_five
    sys hvalid hn hcount

theorem m6_binary_sandwich_residue_has_localized_len1_suffix
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        ∃ phase : TernaryPhase gc t,
          phase.s.val = phase.a.val + 1 ∧
          (gc.moverAt phase.a = left t ∨ gc.moverAt phase.a = right t) ∧
          ∀ k : Fin gc.configs.length,
            phase.a.val ≤ k.val → k.val < phase.s.val →
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) := by
  rcases m6_binary_sandwich_residue_with_phase sys hvalid hn hcount with
    ⟨gc, hconv, t, hmt, hbL, hbR, _hfc2, _hfc_lt, hall, phase0, _⟩
  rcases normal_phase_has_localized_short_suffix_or_ec gc t hall phase0 with hec | hshort
  · exact False.elim (entryConflict_impossible gc hec)
  · rcases hshort with ⟨phase1, _hs, hlen1, hstart, hlocal⟩
    exact ⟨gc, hconv, t, hmt, hbL, hbR, phase1, hlen1, hstart, hlocal⟩

theorem m6_binary_sandwich_residue_has_len1_suffix
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        ∃ phase : TernaryPhase gc t,
          phase.s.val = phase.a.val + 1 ∧
          (gc.moverAt phase.a = left t ∨ gc.moverAt phase.a = right t) := by
  rcases m6_binary_sandwich_residue_has_localized_len1_suffix sys hvalid hn hcount with
    ⟨gc, hconv, t, hmt, hbL, hbR, phase, hlen1, hstart, _hlocal⟩
  exact ⟨gc, hconv, t, hmt, hbL, hbR, phase, hlen1, hstart⟩

private theorem left_ne_right_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left t ≠ right t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  have hval' : (t.val + 6 - 1) % 6 = (t.val + 1) % 6 := by
    simpa [left_val, right_val, hn] using hval
  omega

private theorem right_ne_left_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right t ≠ left t := by
  intro h
  exact left_ne_right_of_n_eq_six hn t h.symm

private theorem left_ne_self_of_n_eq_six_local
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left t ≠ t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, hn] at hval
  omega

private theorem right_ne_self_of_n_eq_six_local
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right t ≠ t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [right_val, hn] at hval
  omega

private theorem left_ne_right2_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left t ≠ right (right t) := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn] at hval
  omega

private theorem left2_ne_right_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left t) ≠ right t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn] at hval
  omega

private theorem left2_ne_right2_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left t) ≠ right (right t) := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn] at hval
  omega

private theorem right2_ne_left_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right (right t) ≠ left t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn] at hval
  omega

private theorem left2_ne_self_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left t) ≠ t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, hn] at hval
  omega

private theorem left2_ne_left_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left t) ≠ left t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, hn] at hval
  omega

private theorem right2_ne_self_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right (right t) ≠ t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [right_val, hn] at hval
  omega

private theorem right2_ne_right_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right (right t) ≠ right t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [right_val, hn] at hval
  omega

private theorem right3_ne_right_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right (right (right t)) ≠ right t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [right_val, hn] at hval
  omega

private theorem right3_ne_right2_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right (right (right t)) ≠ right (right t) := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [right_val, hn] at hval
  omega

private theorem right3_ne_self_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    right (right (right t)) ≠ t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [right_val, hn] at hval
  omega

private theorem left3_ne_left2_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ left (left t) := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, hn] at hval
  omega

private theorem left3_ne_self_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, hn] at hval
  omega

private theorem left3_ne_left_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ left t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, hn] at hval
  omega

private theorem left3_ne_right_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ right t := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn] at hval
  omega

private theorem left3_ne_right2_of_n_eq_six
    (hn : sys.rs.n = 6) (t : Fin sys.rs.n) :
    left (left (left t)) ≠ right (right t) := by
  intro h
  have hval := congrArg Fin.val h
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn] at hval
  omega

private theorem binary_left3_isolated_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left3 : isBinary sys.rs (left (left (left t)))) :
    ∀ a : Fin gc.configs.length,
      gc.moverAt a = left (left (left t)) →
      gc.moverAt (nextIndex gc.configs a) ≠ left (left (left t)) := by
  have hfc_pos : 0 < gc.fireCount (left (left (left t))) :=
    fireCount_pos_of_goodCycle gc _
  have hfc2 : gc.fireCount (left (left (left t))) ≥ 2 :=
    fireCount_ge_2_of_pos gc _ hfc_pos
  rcases binary_isolated_firings_or_ec gc (left (left (left t))) hbin_left3 hfc2 with
    hec | hall | hiso
  · exact False.elim (entryConflict_impossible gc hec)
  · exfalso
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair t
    have hmov_t : gc.moverAt k = t := by
      rw [← hj]
      exact (gc.moverAt_unique k j hpriv).symm
    exact left3_ne_self_of_n_eq_six hn6 t (by
      calc
        left (left (left t)) = gc.moverAt k := (hall k).symm
        _ = t := hmov_t)
  · exact hiso

private theorem binary_right3_isolated_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right3 : isBinary sys.rs (right (right (right t)))) :
    ∀ a : Fin gc.configs.length,
      gc.moverAt a = right (right (right t)) →
      gc.moverAt (nextIndex gc.configs a) ≠ right (right (right t)) := by
  have hbin_left3 : isBinary sys.rs (left (left (left t))) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hbin_right3
  intro a ha
  have hiso :=
    binary_left3_isolated_n6 gc t hn6 hbin_left3 a
      (by simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using ha)
  intro hnext
  exact hiso (by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hnext)

private theorem binary_left2_isolated_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t))) :
    ∀ a : Fin gc.configs.length,
      gc.moverAt a = left (left t) →
      gc.moverAt (nextIndex gc.configs a) ≠ left (left t) := by
  have hfc_pos : 0 < gc.fireCount (left (left t)) := fireCount_pos_of_goodCycle gc _
  have hfc2 : gc.fireCount (left (left t)) ≥ 2 := fireCount_ge_2_of_pos gc _ hfc_pos
  rcases binary_isolated_firings_or_ec gc (left (left t)) hbin_left2 hfc2 with hec | hall | hiso
  · exact False.elim (entryConflict_impossible gc hec)
  · exfalso
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair t
    have hmov_t : gc.moverAt k = t := by
      rw [← hj]
      exact (gc.moverAt_unique k j hpriv).symm
    exact left2_ne_self_of_n_eq_six hn6 t (by
      calc
        left (left t) = gc.moverAt k := (hall k).symm
        _ = t := hmov_t)
  · exact hiso

private theorem binary_right2_isolated_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t))) :
    ∀ a : Fin gc.configs.length,
      gc.moverAt a = right (right t) →
      gc.moverAt (nextIndex gc.configs a) ≠ right (right t) := by
  have hfc_pos : 0 < gc.fireCount (right (right t)) := fireCount_pos_of_goodCycle gc _
  have hfc2 : gc.fireCount (right (right t)) ≥ 2 := fireCount_ge_2_of_pos gc _ hfc_pos
  rcases binary_isolated_firings_or_ec gc (right (right t)) hbin_right2 hfc2 with hec | hall | hiso
  · exact False.elim (entryConflict_impossible gc hec)
  · exfalso
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair t
    have hmov_t : gc.moverAt k = t := by
      rw [← hj]
      exact (gc.moverAt_unique k j hpriv).symm
    exact right2_ne_self_of_n_eq_six hn6 t (by
      calc
        right (right t) = gc.moverAt k := (hall k).symm
        _ = t := hmov_t)
  · exact hiso

private theorem binary_left1_isolated_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left1 : isBinary sys.rs (left t)) :
    ∀ a : Fin gc.configs.length,
      gc.moverAt a = left t →
      gc.moverAt (nextIndex gc.configs a) ≠ left t := by
  have hfc_pos : 0 < gc.fireCount (left t) := fireCount_pos_of_goodCycle gc _
  have hfc2 : gc.fireCount (left t) ≥ 2 := fireCount_ge_2_of_pos gc _ hfc_pos
  rcases binary_isolated_firings_or_ec gc (left t) hbin_left1 hfc2 with hec | hall | hiso
  · exact False.elim (entryConflict_impossible gc hec)
  · exfalso
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair t
    have hmov_t : gc.moverAt k = t := by
      rw [← hj]
      exact (gc.moverAt_unique k j hpriv).symm
    exact left_ne_self_of_n_eq_six_local hn6 t (by
      calc
        left t = gc.moverAt k := (hall k).symm
        _ = t := hmov_t)
  · exact hiso

private theorem binary_right1_isolated_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right1 : isBinary sys.rs (right t)) :
    ∀ a : Fin gc.configs.length,
      gc.moverAt a = right t →
      gc.moverAt (nextIndex gc.configs a) ≠ right t := by
  have hfc_pos : 0 < gc.fireCount (right t) := fireCount_pos_of_goodCycle gc _
  have hfc2 : gc.fireCount (right t) ≥ 2 := fireCount_ge_2_of_pos gc _ hfc_pos
  rcases binary_isolated_firings_or_ec gc (right t) hbin_right1 hfc2 with hec | hall | hiso
  · exact False.elim (entryConflict_impossible gc hec)
  · exfalso
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair t
    have hmov_t : gc.moverAt k = t := by
      rw [← hj]
      exact (gc.moverAt_unique k j hpriv).symm
    exact right_ne_self_of_n_eq_six_local hn6 t (by
      calc
        right t = gc.moverAt k := (hall k).symm
        _ = t := hmov_t)
  · exact hiso

private theorem binary_step_flip_val
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : isBinary sys.rs p)
    (k : Fin gc.configs.length) (hmov : gc.moverAt k = p) :
    ((gc.configs.get (nextIndex gc.configs k)) p).val =
      (((gc.configs.get k) p).val + 1) % 2 := by
  have hp_eq_two : sys.rs.m p = 2 := by
    simpa [isBinary] using hbin
  have hne := gc.state_ne_at_moverAt k
  rw [hmov] at hne
  have hcurr_lt0 : ((gc.configs.get k) p).val < sys.rs.m p := ((gc.configs.get k) p).isLt
  have hnext_lt0 :
      ((gc.configs.get (nextIndex gc.configs k)) p).val < sys.rs.m p :=
    ((gc.configs.get (nextIndex gc.configs k)) p).isLt
  have hcurr_lt : ((gc.configs.get k) p).val < 2 := by
    omega
  have hnext_lt : ((gc.configs.get (nextIndex gc.configs k)) p).val < 2 := by
    omega
  have hne_val :
      ((gc.configs.get (nextIndex gc.configs k)) p).val ≠
        ((gc.configs.get k) p).val := by
    intro hval
    exact hne (Fin.ext hval)
  omega

private theorem exists_prevIndex
    (gc : GoodCycle sys) (j : Fin gc.configs.length) :
    ∃ prev : Fin gc.configs.length, nextIndex gc.configs prev = j := by
  by_cases h0 : j.val = 0
  · let prev : Fin gc.configs.length := ⟨gc.configs.length - 1, by
      have := gc.configs_length_pos
      omega⟩
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      have hlen_pos : 0 < gc.configs.length := gc.configs_length_pos
      have hmod : (gc.configs.length - 1 + 1) % gc.configs.length = 0 := by
        have hlen : gc.configs.length - 1 + 1 = gc.configs.length := by omega
        rw [hlen, Nat.mod_self]
      simpa [nextIndex, prev, h0] using hmod
    exact ⟨prev, hnext_eq⟩
  · let prev : Fin gc.configs.length := ⟨j.val - 1, by
      have := j.isLt
      omega⟩
    have hprev_succ : prev.val + 1 = j.val := by
      dsimp [prev]
      omega
    have hnext_eq : nextIndex gc.configs prev = j := by
      apply Fin.ext
      simp [nextIndex, prev, hprev_succ, Nat.mod_eq_of_lt j.isLt]
    exact ⟨prev, hnext_eq⟩

private theorem noFire_of_intervalFireCount_zero_local
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    {a b : Nat} (hab : a ≤ b) (_hb : b ≤ gc.configs.length)
    (hzero : gc.intervalFireCount p a b = 0) :
    ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.moverAt k ≠ p := by
  intro k hka hkb hmov
  have hone : gc.intervalFireCount p k.val (k.val + 1) = 1 := by
    rw [intervalFireCount_single gc p k.isLt]
    simp [hmov]
  have hsplit1 := intervalFireCount_split gc p (show a ≤ k.val from hka)
    (show k.val ≤ b by omega)
  have hsplit2 := intervalFireCount_split gc p (show k.val ≤ k.val + 1 by omega)
    (show k.val + 1 ≤ b by omega)
  rw [hsplit1, hsplit2, hone] at hzero
  omega

private theorem opposite_binary_of_ternary_pivot_binaryCount_five
    (hn6 : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5)
    (t : Fin sys.rs.n)
    (hmt : sys.rs.m t ≥ 3) :
    isBinary sys.rs (left (left (left t))) := by
  rcases existsUnique_nonbinary_of_binaryCount_five sys.rs hn6 hcount with
    ⟨u, hu, hu_unique⟩
  have htu : t = u := by
    apply hu_unique
    intro hbin
    have : sys.rs.m t = 2 := hbin
    omega
  by_contra hnb
  have hoppu : left (left (left t)) = u := hu_unique _ hnb
  exact left3_ne_self_of_n_eq_six hn6 t (hoppu.trans htu.symm)

private theorem opposite_binary_right_of_ternary_pivot_binaryCount_five
    (hn6 : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5)
    (t : Fin sys.rs.n)
    (hmt : sys.rs.m t ≥ 3) :
    isBinary sys.rs (right (right (right t))) := by
  simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using
    opposite_binary_of_ternary_pivot_binaryCount_five
      (sys := sys) hn6 hcount t hmt

private theorem left2_binary_of_ternary_pivot_binaryCount_five
    (hn6 : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5)
    (t : Fin sys.rs.n)
    (hmt : sys.rs.m t ≥ 3) :
    isBinary sys.rs (left (left t)) := by
  rcases existsUnique_nonbinary_of_binaryCount_five sys.rs hn6 hcount with
    ⟨u, hu, hu_unique⟩
  have htu : t = u := by
    apply hu_unique
    intro hbin
    have : sys.rs.m t = 2 := hbin
    omega
  by_contra hnb
  have hll_u : left (left t) = u := hu_unique _ hnb
  exact left2_ne_self_of_n_eq_six hn6 t (hll_u.trans htu.symm)

private theorem right2_binary_of_ternary_pivot_binaryCount_five
    (hn6 : sys.rs.n = 6)
    (hcount : binaryCount sys.rs = 5)
    (t : Fin sys.rs.n)
    (hmt : sys.rs.m t ≥ 3) :
    isBinary sys.rs (right (right t)) := by
  rcases existsUnique_nonbinary_of_binaryCount_five sys.rs hn6 hcount with
    ⟨u, hu, hu_unique⟩
  have htu : t = u := by
    apply hu_unique
    intro hbin
    have : sys.rs.m t = 2 := hbin
    omega
  by_contra hnb
  have hrr_u : right (right t) = u := hu_unique _ hnb
  exact right2_ne_self_of_n_eq_six hn6 t (hrr_u.trans htu.symm)

theorem len1_phase_left_counts
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hn : sys.rs.n = 6)
    (hlen1 : phase.s.val = phase.a.val + 1)
    (haL : gc.moverAt phase.a = left t) :
    gc.intervalFireCount (left t) phase.a.val phase.s.val = 1 ∧
      gc.intervalFireCount (right t) phase.a.val phase.s.val = 0 := by
  constructor
  · rw [hlen1, intervalFireCount_single gc (left t) phase.a.isLt]
    simp [haL]
  · rw [hlen1, intervalFireCount_single gc (right t) phase.a.isLt]
    simp [haL, left_ne_right_of_n_eq_six hn t]

theorem len1_phase_right_counts
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hn : sys.rs.n = 6)
    (hlen1 : phase.s.val = phase.a.val + 1)
    (haR : gc.moverAt phase.a = right t) :
    gc.intervalFireCount (left t) phase.a.val phase.s.val = 0 ∧
      gc.intervalFireCount (right t) phase.a.val phase.s.val = 1 := by
  constructor
  · rw [hlen1, intervalFireCount_single gc (left t) phase.a.isLt]
    simp [haR, right_ne_left_of_n_eq_six hn t]
  · rw [hlen1, intervalFireCount_single gc (right t) phase.a.isLt]
    simp [haR]

theorem m6_binary_sandwich_residue_has_one_sided_len1_suffix
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        ∃ phase : TernaryPhase gc t,
          (gc.moverAt phase.a = left t ∧
            gc.intervalFireCount (left t) phase.a.val phase.s.val = 1 ∧
            gc.intervalFireCount (right t) phase.a.val phase.s.val = 0) ∨
          (gc.moverAt phase.a = right t ∧
            gc.intervalFireCount (left t) phase.a.val phase.s.val = 0 ∧
            gc.intervalFireCount (right t) phase.a.val phase.s.val = 1) := by
  rcases m6_binary_sandwich_residue_has_len1_suffix sys hvalid hn hcount with
    ⟨gc, hconv, t, hmt, hbL, hbR, phase, hlen1, hstart⟩
  cases hstart with
  | inl hL =>
      have hcounts := len1_phase_left_counts gc t phase hn hlen1 hL
      exact ⟨gc, hconv, t, hmt, hbL, hbR, phase, Or.inl ⟨hL, hcounts.1, hcounts.2⟩⟩
  | inr hR =>
      have hcounts := len1_phase_right_counts gc t phase hn hlen1 hR
      exact ⟨gc, hconv, t, hmt, hbL, hbR, phase, Or.inr ⟨hR, hcounts.1, hcounts.2⟩⟩

theorem phase_all_local5_or_last_opposite_of_n_eq_six
    (gc : GoodCycle sys) (t : Fin sys.rs.n) (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6) :
    (∀ k : Fin gc.configs.length,
      phase.a.val ≤ k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) ∨
    (∃ a0 : Fin gc.configs.length,
      phase.a.val ≤ a0.val ∧
      a0.val < phase.s.val ∧
      gc.moverAt a0 = left (left (left t)) ∧
      ∀ k : Fin gc.configs.length,
        a0.val < k.val → k.val < phase.s.val →
        gc.moverAt k = left (left t) ∨
        gc.moverAt k = left t ∨
        gc.moverAt k = right t ∨
        gc.moverAt k = right (right t)) := by
  rcases phase_last_outside_or_all_local gc t phase with hall | hout
  · exact Or.inl hall
  · rcases hout with ⟨a0, ha0_ge_a, ha0_lt_s, ha0_nll, ha0_nl, ha0_nt, ha0_nr, ha0_nrr, htail⟩
    have ha0_opp : gc.moverAt a0 = left (left (left t)) := by
      apply eq_left3_of_not_local5_of_n_eq_six sys.rs hn6 (gc.moverAt a0) t
      · exact ha0_nt
      · exact ha0_nl
      · exact ha0_nll
      · exact ha0_nr
      · exact ha0_nrr
    exact Or.inr ⟨a0, ha0_ge_a, ha0_lt_s, ha0_opp, htail⟩

theorem allNormal_last_opposite_not_final
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (a0 : Fin gc.configs.length)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_opp : gc.moverAt a0 = left (left (left t))) :
    a0.val + 1 < phase.s.val := by
  by_contra hnot
  have hs_eq : a0.val + 1 = phase.s.val := by
    omega
  let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  have ha0_eq_prev : a0 = prev := by
    apply Fin.ext
    dsimp [prev]
    omega
  rcases allNormal_phase_right_or_left_before_t gc t hall phase with hL | hR
  · have : left (left (left t)) = left t := by
      calc
        left (left (left t)) = gc.moverAt a0 := ha0_opp.symm
        _ = gc.moverAt prev := by simpa [ha0_eq_prev]
        _ = left t := by simpa [prev] using hL
    exact left3_ne_left_of_n_eq_six hn6 t this
  · have : left (left (left t)) = right t := by
      calc
        left (left (left t)) = gc.moverAt a0 := ha0_opp.symm
        _ = gc.moverAt prev := by simpa [ha0_eq_prev]
        _ = right t := by simpa [prev] using hR
    exact left3_ne_right_of_n_eq_six hn6 t this

theorem allNormal_last_opposite_next_is_second_neighbor
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (a0 : Fin gc.configs.length)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_opp : gc.moverAt a0 = left (left (left t)))
    (htail_local : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    ∃ a1 : Fin gc.configs.length,
      nextIndex gc.configs a0 = a1 ∧
      a1.val < phase.s.val ∧
      (gc.moverAt a1 = left (left t) ∨ gc.moverAt a1 = right (right t)) := by
  have ha1_lt_s_nat : a0.val + 1 < phase.s.val :=
    allNormal_last_opposite_not_final gc t hall phase hn6 a0 ha0_lt_s ha0_opp
  let a1 : Fin gc.configs.length := ⟨a0.val + 1, by
    have := phase.s.isLt
    omega⟩
  have hnext : nextIndex gc.configs a0 = a1 := by
    apply Fin.ext
    simp [nextIndex, a1]
    exact Nat.mod_eq_of_lt a1.isLt
  have ha1_gt : a0.val < a1.val := by
    simp [a1]
  have ha1_lt_s : a1.val < phase.s.val := by
    simpa [a1] using ha1_lt_s_nat
  have ha1_local5 :
      gc.moverAt a1 = left (left t) ∨
      gc.moverAt a1 = left t ∨
      gc.moverAt a1 = right t ∨
      gc.moverAt a1 = right (right t) :=
    htail_local a1 ha1_gt ha1_lt_s
  have hnext_local := gc.next_mover_is_local a0
  rw [hnext, ha0_opp] at hnext_local
  rcases hnext_local with hleft | hself | hright
  · refine ⟨a1, hnext, ha1_lt_s, Or.inr ?_⟩
    simpa [left4_eq_right2_of_n_eq_six sys.rs hn6 t] using hleft
  · exfalso
    have ha1_opp : gc.moverAt a1 = left (left (left t)) := by
      simpa using hself
    rcases ha1_local5 with ha1ll | ha1l | ha1r | ha1rr
    · exact left3_ne_left2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt a1 := ha1_opp.symm
          _ = left (left t) := ha1ll)
    · exact left3_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt a1 := ha1_opp.symm
          _ = left t := ha1l)
    · exact left3_ne_right_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt a1 := ha1_opp.symm
          _ = right t := ha1r)
    · exact left3_ne_right2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt a1 := ha1_opp.symm
          _ = right (right t) := ha1rr)
  · refine ⟨a1, hnext, ha1_lt_s, Or.inl ?_⟩
    simpa [right_left_eq_self] using hright

theorem allNormal_last_opposite_tail_one_sided
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_opp : gc.moverAt a0 = left (left (left t)))
    (htail_local : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    (∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) ∨
    (∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) := by
  rcases allNormal_last_opposite_next_is_second_neighbor gc t hall phase hn6 a0
      ha0_lt_s ha0_opp htail_local with ⟨a1, hnext, ha1_lt_s, ha1_side⟩
  have hnext_val : a1.val = a0.val + 1 := by
    have hEq := congrArg Fin.val hnext
    have ha1_lt_len : a0.val + 1 < gc.configs.length := by
      have := phase.s.isLt
      omega
    simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
    exact hEq.symm
  have ha1_gt_a0 : a0.val < a1.val := by
    rw [hnext_val]
    omega
  cases ha1_side with
  | inl ha1_ll =>
      left
      intro k hk1 hk2
      by_cases hgood : gc.moverAt k = left (left t) ∨ gc.moverAt k = left t
      · exact hgood
      · let badSet : Finset (Fin gc.configs.length) :=
          (Finset.univ : Finset (Fin gc.configs.length)).filter
            (fun j =>
              a1.val ≤ j.val ∧ j.val < phase.s.val ∧
              (gc.moverAt j = right t ∨ gc.moverAt j = right (right t)))
        have ha1_le_k : a1.val ≤ k.val := by
          have : a0.val + 1 = a1.val := hnext_val.symm
          omega
        have hk_bad : gc.moverAt k = right t ∨ gc.moverAt k = right (right t) := by
          rcases htail_local k hk1 hk2 with hkll | hkl | hkr | hkrr
          · exact False.elim (hgood (Or.inl hkll))
          · exact False.elim (hgood (Or.inr hkl))
          · exact Or.inl hkr
          · exact Or.inr hkrr
        have hk_mem : k ∈ badSet := by
          refine Finset.mem_filter.mpr ?_
          exact ⟨Finset.mem_univ k, ⟨ha1_le_k, hk2, hk_bad⟩⟩
        obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val ⟨k, hk_mem⟩
        have ha1_le_j : a1.val ≤ j.val := by
          simp [badSet] at hj_mem
          exact hj_mem.1
        have hj_lt_s : j.val < phase.s.val := by
          simp [badSet] at hj_mem
          exact hj_mem.2.1
        have hj_bad : gc.moverAt j = right t ∨ gc.moverAt j = right (right t) := by
          simp [badSet] at hj_mem
          exact hj_mem.2.2
        have hj_ne_a1 : j ≠ a1 := by
          intro hEq
          rcases hj_bad with hjr | hjrr
          · exact left2_ne_right_of_n_eq_six hn6 t (by
              calc
                left (left t) = gc.moverAt a1 := ha1_ll.symm
                _ = gc.moverAt j := by simpa [hEq]
                _ = right t := hjr)
          · exact left2_ne_right2_of_n_eq_six hn6 t (by
              calc
                left (left t) = gc.moverAt a1 := ha1_ll.symm
                _ = gc.moverAt j := by simpa [hEq]
                _ = right (right t) := hjrr)
        have hj_gt_a1 : a1.val < j.val := by
          have hneq : a1.val ≠ j.val := by
            intro hEq
            exact hj_ne_a1 (Fin.ext hEq.symm)
          omega
        let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
        have hprev_ge_a1 : a1.val ≤ prev.val := by
          dsimp [prev]
          omega
        have hprev_gt_a0 : a0.val < prev.val := by
          omega
        have hprev_lt_s : prev.val < phase.s.val := by
          dsimp [prev]
          omega
        have hprev_next : nextIndex gc.configs prev = j := by
          apply Fin.ext
          have hsucc : prev.val + 1 = j.val := by
            dsimp [prev]
            omega
          simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
        have hprev_good : gc.moverAt prev = left (left t) ∨ gc.moverAt prev = left t := by
          by_cases hprev_eq : prev = a1
          · exact Or.inl (by simpa [hprev_eq] using ha1_ll)
          · rcases htail_local prev hprev_gt_a0 hprev_lt_s with hll | hl | hr | hrr
            · exact Or.inl hll
            · exact Or.inr hl
            · exfalso
              have hprev_mem : prev ∈ badSet := by
                refine Finset.mem_filter.mpr ?_
                exact ⟨Finset.mem_univ prev, ⟨hprev_ge_a1, hprev_lt_s, Or.inl hr⟩⟩
              have := hj_min prev hprev_mem
              have hprev_lt_j : prev.val < j.val := by
                dsimp [prev]
                omega
              omega
            · exfalso
              have hprev_mem : prev ∈ badSet := by
                refine Finset.mem_filter.mpr ?_
                exact ⟨Finset.mem_univ prev, ⟨hprev_ge_a1, hprev_lt_s, Or.inr hrr⟩⟩
              have := hj_min prev hprev_mem
              have hprev_lt_j : prev.val < j.val := by
                dsimp [prev]
                omega
              omega
        have hnext_local := gc.next_mover_is_local prev
        rw [hprev_next] at hnext_local
        rcases hprev_good with hprev_ll | hprev_l
        · rcases hnext_local with hleft | hself | hright
          · have hj_l3 : gc.moverAt j = left (left (left t)) := by
              simpa [hprev_ll] using hleft
            have hj_gt_a0 : a0.val < j.val := by
              omega
            exfalso
            rcases htail_local j hj_gt_a0 hj_lt_s with hjll | hjl | hjr | hjrr
            · exact left3_ne_left2_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_l3.symm
                  _ = left (left t) := hjll)
            · exact left3_ne_left_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_l3.symm
                  _ = left t := hjl)
            · exact left3_ne_right_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_l3.symm
                  _ = right t := hjr)
            · exact left3_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_l3.symm
                  _ = right (right t) := hjrr)
          · have hj_ll : gc.moverAt j = left (left t) := by
              simpa [hprev_ll] using hself
            exfalso
            rcases hj_bad with hjr | hjrr
            · exact left2_ne_right_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hj_ll.symm
                  _ = right t := hjr)
            · exact left2_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hj_ll.symm
                  _ = right (right t) := hjrr)
          · have hj_l : gc.moverAt j = left t := by
              simpa [hprev_ll] using hright
            rcases hj_bad with hjr | hjrr
            · exact False.elim (left_ne_right_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hj_l.symm
                  _ = right t := hjr))
            · exact False.elim (left_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hj_l.symm
                  _ = right (right t) := hjrr))
        · rcases hnext_local with hleft | hself | hright
          · have hj_ll : gc.moverAt j = left (left t) := by
              simpa [hprev_l] using hleft
            rcases hj_bad with hjr | hjrr
            · exact False.elim (left2_ne_right_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hj_ll.symm
                  _ = right t := hjr))
            · exact False.elim (left2_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hj_ll.symm
                  _ = right (right t) := hjrr))
          · have hj_l : gc.moverAt j = left t := by
              simpa [hprev_l] using hself
            rcases hj_bad with hjr | hjrr
            · exact False.elim (left_ne_right_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hj_l.symm
                  _ = right t := hjr))
            · exact False.elim (left_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hj_l.symm
                  _ = right (right t) := hjrr))
          · exfalso
            exact phase.ht_nofire j (le_trans ha0_ge_a (by omega)) hj_lt_s
              (by simpa [hprev_l] using hright)
  | inr ha1_rr =>
      right
      intro k hk1 hk2
      by_cases hgood : gc.moverAt k = right t ∨ gc.moverAt k = right (right t)
      · exact hgood
      · let badSet : Finset (Fin gc.configs.length) :=
          (Finset.univ : Finset (Fin gc.configs.length)).filter
            (fun j =>
              a1.val ≤ j.val ∧ j.val < phase.s.val ∧
              (gc.moverAt j = left (left t) ∨ gc.moverAt j = left t))
        have ha1_le_k : a1.val ≤ k.val := by
          have : a0.val + 1 = a1.val := hnext_val.symm
          omega
        have hk_bad : gc.moverAt k = left (left t) ∨ gc.moverAt k = left t := by
          rcases htail_local k hk1 hk2 with hkll | hkl | hkr | hkrr
          · exact Or.inl hkll
          · exact Or.inr hkl
          · exact False.elim (hgood (Or.inl hkr))
          · exact False.elim (hgood (Or.inr hkrr))
        have hk_mem : k ∈ badSet := by
          refine Finset.mem_filter.mpr ?_
          exact ⟨Finset.mem_univ k, ⟨ha1_le_k, hk2, hk_bad⟩⟩
        obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image badSet Fin.val ⟨k, hk_mem⟩
        have ha1_le_j : a1.val ≤ j.val := by
          simp [badSet] at hj_mem
          exact hj_mem.1
        have hj_lt_s : j.val < phase.s.val := by
          simp [badSet] at hj_mem
          exact hj_mem.2.1
        have hj_bad : gc.moverAt j = left (left t) ∨ gc.moverAt j = left t := by
          simp [badSet] at hj_mem
          exact hj_mem.2.2
        have hj_ne_a1 : j ≠ a1 := by
          intro hEq
          rcases hj_bad with hjll | hjl
          · exact left2_ne_right2_of_n_eq_six hn6 t (by
              calc
                left (left t) = gc.moverAt j := hjll.symm
                _ = gc.moverAt a1 := by simpa [hEq]
                _ = right (right t) := ha1_rr)
          · exact left_ne_right2_of_n_eq_six hn6 t (by
              calc
                left t = gc.moverAt j := hjl.symm
                _ = gc.moverAt a1 := by simpa [hEq]
                _ = right (right t) := ha1_rr)
        have hj_gt_a1 : a1.val < j.val := by
          have hneq : a1.val ≠ j.val := by
            intro hEq
            exact hj_ne_a1 (Fin.ext hEq.symm)
          omega
        let prev : Fin gc.configs.length := ⟨j.val - 1, by omega⟩
        have hprev_ge_a1 : a1.val ≤ prev.val := by
          dsimp [prev]
          omega
        have hprev_gt_a0 : a0.val < prev.val := by
          omega
        have hprev_lt_s : prev.val < phase.s.val := by
          dsimp [prev]
          omega
        have hprev_next : nextIndex gc.configs prev = j := by
          apply Fin.ext
          have hsucc : prev.val + 1 = j.val := by
            dsimp [prev]
            omega
          simp [nextIndex, prev, hsucc, Nat.mod_eq_of_lt j.isLt]
        have hprev_good : gc.moverAt prev = right t ∨ gc.moverAt prev = right (right t) := by
          by_cases hprev_eq : prev = a1
          · exact Or.inr (by simpa [hprev_eq] using ha1_rr)
          · rcases htail_local prev hprev_gt_a0 hprev_lt_s with hll | hl | hr | hrr
            · exfalso
              have hprev_mem : prev ∈ badSet := by
                refine Finset.mem_filter.mpr ?_
                exact ⟨Finset.mem_univ prev, ⟨hprev_ge_a1, hprev_lt_s, Or.inl hll⟩⟩
              have := hj_min prev hprev_mem
              have hprev_lt_j : prev.val < j.val := by
                dsimp [prev]
                omega
              omega
            · exfalso
              have hprev_mem : prev ∈ badSet := by
                refine Finset.mem_filter.mpr ?_
                exact ⟨Finset.mem_univ prev, ⟨hprev_ge_a1, hprev_lt_s, Or.inr hl⟩⟩
              have := hj_min prev hprev_mem
              have hprev_lt_j : prev.val < j.val := by
                dsimp [prev]
                omega
              omega
            · exact Or.inl hr
            · exact Or.inr hrr
        have hnext_local := gc.next_mover_is_local prev
        rw [hprev_next] at hnext_local
        rcases hprev_good with hprev_r | hprev_rr
        · rcases hnext_local with hleft | hself | hright
          · exfalso
            exact phase.ht_nofire j (le_trans ha0_ge_a (by omega)) hj_lt_s
              (by simpa [hprev_r] using hleft)
          · have hj_r : gc.moverAt j = right t := by
              simpa [hprev_r] using hself
            rcases hj_bad with hjll | hjl
            · exact False.elim (left2_ne_right_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hjll.symm
                  _ = right t := hj_r))
            · exact False.elim (left_ne_right_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hjl.symm
                  _ = right t := hj_r))
          · have hj_rr : gc.moverAt j = right (right t) := by
              simpa [hprev_r] using hright
            rcases hj_bad with hjll | hjl
            · exact False.elim (left2_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hjll.symm
                  _ = right (right t) := hj_rr))
            · exact False.elim (left_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hjl.symm
                  _ = right (right t) := hj_rr))
        · rcases hnext_local with hleft | hself | hright
          · have hj_r : gc.moverAt j = right t := by
              simpa [hprev_rr] using hleft
            rcases hj_bad with hjll | hjl
            · exact False.elim (left2_ne_right_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hjll.symm
                  _ = right t := hj_r))
            · exact False.elim (left_ne_right_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hjl.symm
                  _ = right t := hj_r))
          · have hj_rr : gc.moverAt j = right (right t) := by
              simpa [hprev_rr] using hself
            rcases hj_bad with hjll | hjl
            · exact False.elim (left2_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left (left t) = gc.moverAt j := hjll.symm
                  _ = right (right t) := hj_rr))
            · exact False.elim (left_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left t = gc.moverAt j := hjl.symm
                  _ = right (right t) := hj_rr))
          · have hj_opp : gc.moverAt j = left (left (left t)) := by
              simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t, hprev_rr] using hright
            have hj_gt_a0 : a0.val < j.val := by
              omega
            exfalso
            rcases htail_local j hj_gt_a0 hj_lt_s with hjll | hjl | hjr | hjrr
            · exact left3_ne_left2_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_opp.symm
                  _ = left (left t) := hjll)
            · exact left3_ne_left_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_opp.symm
                  _ = left t := hjl)
            · exact left3_ne_right_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_opp.symm
                  _ = right t := hjr)
            · exact left3_ne_right2_of_n_eq_six hn6 t (by
                calc
                  left (left (left t)) = gc.moverAt j := hj_opp.symm
                  _ = right (right t) := hjrr)

theorem allNormal_last_opposite_tail_tight
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_opp : gc.moverAt a0 = left (left (left t)))
    (htail_local : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    (∃ a1 : Fin gc.configs.length,
      nextIndex gc.configs a0 = a1 ∧
      a1.val < phase.s.val ∧
      gc.moverAt a1 = left (left t) ∧
      (∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) ∧
      gc.intervalFireCount (left t) a1.val phase.s.val = 1 ∧
      gc.intervalFireCount (right t) a1.val phase.s.val = 0) ∨
    (∃ a1 : Fin gc.configs.length,
      nextIndex gc.configs a0 = a1 ∧
      a1.val < phase.s.val ∧
      gc.moverAt a1 = right (right t) ∧
      (∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < phase.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) ∧
      gc.intervalFireCount (left t) a1.val phase.s.val = 0 ∧
      gc.intervalFireCount (right t) a1.val phase.s.val = 1) := by
  rcases allNormal_last_opposite_next_is_second_neighbor gc t hall phase hn6 a0
      ha0_lt_s ha0_opp htail_local with ⟨a1, hnext, ha1_lt_s, ha1_side⟩
  have hnext_val : a1.val = a0.val + 1 := by
    have hEq := congrArg Fin.val hnext
    have ha1_lt_len : a0.val + 1 < gc.configs.length := by
      have := phase.s.isLt
      omega
    simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
    exact hEq.symm
  have ha1_gt_a0 : a0.val < a1.val := by
    rw [hnext_val]
    omega
  rcases allNormal_last_opposite_tail_one_sided gc t hall phase hn6 a0
      ha0_ge_a ha0_lt_s ha0_opp htail_local with hleft_tail | hright_tail
  · rcases ha1_side with ha1_ll | ha1_rr
    · left
      have hleft_tail' : ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < phase.s.val →
          gc.moverAt k = left (left t) ∨ gc.moverAt k = left t := by
        intro k hk1 hk2
        by_cases hk_eq : k = a1
        · exact Or.inl (by simpa [hk_eq] using ha1_ll)
        · have hk_gt_a0 : a0.val < k.val := by
            have hneq : a1.val ≠ k.val := by
              intro hEq
              exact hk_eq (Fin.ext hEq.symm)
            omega
          exact hleft_tail k hk_gt_a0 hk2
      have ha1_nonmover : gc.moverAt a1 ≠ t := by
        rw [ha1_ll]
        exact left2_ne_self_of_n_eq_six hn6 t
      let suffix_phase : TernaryPhase gc t :=
        { a := a1, s := phase.s, ha_lt_s := ha1_lt_s, hs_mover := phase.hs_mover,
          ha_nonmover := ha1_nonmover,
          ht_nofire := by
            intro k hk1 hk2
            exact phase.ht_nofire k (le_trans ha0_ge_a (by omega)) hk2 }
      have hnorm : isNormalFormGap gc t suffix_phase := hall suffix_phase
      have hK0 : gc.intervalFireCount (right t) a1.val phase.s.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire (gc := gc) (p := right t)
          (a := a1.val) (b := phase.s.val) (Nat.le_of_lt ha1_lt_s) (Nat.le_of_lt phase.s.isLt)
        intro k hk1 hk2
        by_cases hk_eq : k = a1
        · rw [hk_eq, ha1_ll]
          exact left2_ne_right_of_n_eq_six hn6 t
        · rcases hleft_tail' k hk1 hk2 with hkll | hkl
          · intro hkr
            exact left2_ne_right_of_n_eq_six hn6 t (by
              calc
                left (left t) = gc.moverAt k := hkll.symm
                _ = right t := hkr)
          · intro hkr
            exact left_ne_right_of_n_eq_six hn6 t (by
              calc
                left t = gc.moverAt k := hkl.symm
                _ = right t := hkr)
      have hJ1 : gc.intervalFireCount (left t) a1.val phase.s.val = 1 :=
        (normalForm_gap_constraint gc t suffix_phase hnorm).2.1 hK0
      exact ⟨a1, hnext, ha1_lt_s, ha1_ll, hleft_tail', hJ1, hK0⟩
    · exfalso
      rcases hleft_tail a1 ha1_gt_a0 ha1_lt_s with ha1_ll | ha1_l
      · exact left2_ne_right2_of_n_eq_six hn6 t (by
          calc
            left (left t) = gc.moverAt a1 := ha1_ll.symm
            _ = right (right t) := ha1_rr)
      · exact left_ne_right2_of_n_eq_six hn6 t (by
          calc
            left t = gc.moverAt a1 := ha1_l.symm
            _ = right (right t) := ha1_rr)
  · rcases ha1_side with ha1_ll | ha1_rr
    · exfalso
      rcases hright_tail a1 ha1_gt_a0 ha1_lt_s with ha1_r | ha1_rr
      · exact left2_ne_right_of_n_eq_six hn6 t (by
          calc
            left (left t) = gc.moverAt a1 := ha1_ll.symm
            _ = right t := ha1_r)
      · exact left2_ne_right2_of_n_eq_six hn6 t (by
          calc
            left (left t) = gc.moverAt a1 := ha1_ll.symm
            _ = right (right t) := ha1_rr)
    · right
      have hright_tail' : ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < phase.s.val →
          gc.moverAt k = right t ∨ gc.moverAt k = right (right t) := by
        intro k hk1 hk2
        by_cases hk_eq : k = a1
        · exact Or.inr (by simpa [hk_eq] using ha1_rr)
        · have hk_gt_a0 : a0.val < k.val := by
            have hneq : a1.val ≠ k.val := by
              intro hEq
              exact hk_eq (Fin.ext hEq.symm)
            omega
          exact hright_tail k hk_gt_a0 hk2
      have ha1_nonmover : gc.moverAt a1 ≠ t := by
        rw [ha1_rr]
        exact right2_ne_self_of_n_eq_six hn6 t
      let suffix_phase : TernaryPhase gc t :=
        { a := a1, s := phase.s, ha_lt_s := ha1_lt_s, hs_mover := phase.hs_mover,
          ha_nonmover := ha1_nonmover,
          ht_nofire := by
            intro k hk1 hk2
            exact phase.ht_nofire k (le_trans ha0_ge_a (by omega)) hk2 }
      have hnorm : isNormalFormGap gc t suffix_phase := hall suffix_phase
      have hJ0 : gc.intervalFireCount (left t) a1.val phase.s.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire (gc := gc) (p := left t)
          (a := a1.val) (b := phase.s.val) (Nat.le_of_lt ha1_lt_s) (Nat.le_of_lt phase.s.isLt)
        intro k hk1 hk2
        by_cases hk_eq : k = a1
        · rw [hk_eq, ha1_rr]
          intro hleft
          exact left_ne_right2_of_n_eq_six hn6 t hleft.symm
        · rcases hright_tail' k hk1 hk2 with hkr | hkrr
          · intro hleft
            exact right_ne_left_of_n_eq_six hn6 t (by
              calc
                right t = gc.moverAt k := hkr.symm
                _ = left t := hleft)
          · intro hleft
            exact left_ne_right2_of_n_eq_six hn6 t (by
              calc
                left t = gc.moverAt k := hleft.symm
                _ = right (right t) := hkrr)
      have hK1 : gc.intervalFireCount (right t) a1.val phase.s.val = 1 :=
        (normalForm_gap_constraint gc t suffix_phase hnorm).1 hJ0
      exact ⟨a1, hnext, ha1_lt_s, ha1_rr, hright_tail', hJ0, hK1⟩

theorem allNormal_last_opposite_tail_word
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (a0 : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_opp : gc.moverAt a0 = left (left (left t)))
    (htail_local : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val →
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)) :
    (∃ a1 prev : Fin gc.configs.length,
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      gc.moverAt a1 = left (left t) ∧
      gc.moverAt prev = left t ∧
      ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
    (∃ a1 prev : Fin gc.configs.length,
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      gc.moverAt a1 = right (right t) ∧
      gc.moverAt prev = right t ∧
      ∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t)) := by
  rcases allNormal_last_opposite_tail_tight gc t hall phase hn6 a0
      ha0_ge_a ha0_lt_s ha0_opp htail_local with hleft | hright
  · rcases hleft with ⟨a1, hnext, ha1_lt_s, ha1_ll, htail1, hJ1, hK0⟩
    have hnext_val : a1.val = a0.val + 1 := by
      have hEq := congrArg Fin.val hnext
      have ha1_lt_len : a0.val + 1 < gc.configs.length := by
        have := phase.s.isLt
        omega
      simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
      exact hEq.symm
    let suffix_phase : TernaryPhase gc t :=
      { a := a1, s := phase.s, ha_lt_s := ha1_lt_s, hs_mover := phase.hs_mover,
        ha_nonmover := by
          rw [ha1_ll]
          exact left2_ne_self_of_n_eq_six hn6 t,
        ht_nofire := by
          intro k hk1 hk2
          have ha1_gt_a0 : a0.val < a1.val := by
            rw [hnext_val]
            omega
          have hk_gt_a0 : a0.val < k.val := lt_of_lt_of_le ha1_gt_a0 hk1
          exact phase.ht_nofire k (le_trans ha0_ge_a (Nat.le_of_lt hk_gt_a0)) hk2 }
    let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
      have := phase.ha_lt_s
      have := phase.s.isLt
      omega⟩
    have hprev_succ : prev.val + 1 = phase.s.val := by
      dsimp [prev]
      omega
    have hprev_left : gc.moverAt prev = left t := by
      exact allNormal_phase_prev_left_of_right_count_zero gc t hall suffix_phase hK0
    have ha1_lt_prev : a1.val < prev.val := by
      by_contra hnot
      have hEq : a1 = prev := by
        apply Fin.ext
        omega
      exact left2_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left t) = gc.moverAt a1 := ha1_ll.symm
          _ = gc.moverAt prev := by simpa [hEq]
          _ = left t := by simpa [hEq] using hprev_left)
    have hprev_single : gc.intervalFireCount (left t) prev.val phase.s.val = 1 := by
      simpa [hprev_succ, hprev_left] using
        (intervalFireCount_single gc (left t) prev.isLt)
    have hsplit_prev := intervalFireCount_split gc (left t)
      (a := a1.val) (c := prev.val) (b := phase.s.val)
      (Nat.le_of_lt ha1_lt_prev) (Nat.le_of_lt (by
        have := phase.s.isLt
        omega : prev.val < phase.s.val))
    have hleft_before_zero : gc.intervalFireCount (left t) a1.val prev.val = 0 := by
      omega
    have hno_left_before_prev :
        ∀ k : Fin gc.configs.length, a1.val ≤ k.val → k.val < prev.val → gc.moverAt k ≠ left t := by
      intro k hk1 hk2 hkL
      have hsingle : gc.intervalFireCount (left t) k.val (k.val + 1) = 1 := by
        rw [intervalFireCount_single gc (left t) k.isLt]
        simp [hkL]
      have hsplit1 := intervalFireCount_split gc (left t)
        (a := a1.val) (c := k.val) (b := prev.val) hk1 (Nat.le_of_lt hk2)
      have hsplit2 := intervalFireCount_split gc (left t)
        (a := k.val) (c := k.val + 1) (b := prev.val) (by omega) (by omega)
      rw [hsplit1, hsplit2, hsingle] at hleft_before_zero
      omega
    left
    refine ⟨a1, prev, hnext, hprev_succ, ha1_ll, hprev_left, ?_⟩
    intro k hk1 hk2
    rcases htail1 k hk1 (lt_trans hk2 (by
      have := phase.s.isLt
      dsimp [prev]
      omega)) with hkll | hkl
    · exact hkll
    · exfalso
      exact hno_left_before_prev k hk1 hk2 hkl
  · rcases hright with ⟨a1, hnext, ha1_lt_s, ha1_rr, htail1, hJ0, hK1⟩
    have hnext_val : a1.val = a0.val + 1 := by
      have hEq := congrArg Fin.val hnext
      have ha1_lt_len : a0.val + 1 < gc.configs.length := by
        have := phase.s.isLt
        omega
      simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
      exact hEq.symm
    let suffix_phase : TernaryPhase gc t :=
      { a := a1, s := phase.s, ha_lt_s := ha1_lt_s, hs_mover := phase.hs_mover,
        ha_nonmover := by
          rw [ha1_rr]
          exact right2_ne_self_of_n_eq_six hn6 t,
        ht_nofire := by
          intro k hk1 hk2
          have ha1_gt_a0 : a0.val < a1.val := by
            rw [hnext_val]
            omega
          have hk_gt_a0 : a0.val < k.val := lt_of_lt_of_le ha1_gt_a0 hk1
          exact phase.ht_nofire k (le_trans ha0_ge_a (Nat.le_of_lt hk_gt_a0)) hk2 }
    let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
      have := phase.ha_lt_s
      have := phase.s.isLt
      omega⟩
    have hprev_succ : prev.val + 1 = phase.s.val := by
      dsimp [prev]
      omega
    have hprev_right : gc.moverAt prev = right t := by
      exact allNormal_phase_prev_right_of_left_count_zero gc t hall suffix_phase hJ0
    have ha1_lt_prev : a1.val < prev.val := by
      by_contra hnot
      have hEq : a1 = prev := by
        apply Fin.ext
        omega
      exact right2_ne_right_of_n_eq_six hn6 t (by
        calc
          right (right t) = gc.moverAt a1 := ha1_rr.symm
          _ = gc.moverAt prev := by simpa [hEq]
          _ = right t := by simpa [hEq] using hprev_right)
    have hprev_single : gc.intervalFireCount (right t) prev.val phase.s.val = 1 := by
      simpa [hprev_succ, hprev_right] using
        (intervalFireCount_single gc (right t) prev.isLt)
    have hsplit_prev := intervalFireCount_split gc (right t)
      (a := a1.val) (c := prev.val) (b := phase.s.val)
      (Nat.le_of_lt ha1_lt_prev) (Nat.le_of_lt (by
        have := phase.s.isLt
        omega : prev.val < phase.s.val))
    have hright_before_zero : gc.intervalFireCount (right t) a1.val prev.val = 0 := by
      omega
    have hno_right_before_prev :
        ∀ k : Fin gc.configs.length, a1.val ≤ k.val → k.val < prev.val → gc.moverAt k ≠ right t := by
      intro k hk1 hk2 hkR
      have hsingle : gc.intervalFireCount (right t) k.val (k.val + 1) = 1 := by
        rw [intervalFireCount_single gc (right t) k.isLt]
        simp [hkR]
      have hsplit1 := intervalFireCount_split gc (right t)
        (a := a1.val) (c := k.val) (b := prev.val) hk1 (Nat.le_of_lt hk2)
      have hsplit2 := intervalFireCount_split gc (right t)
        (a := k.val) (c := k.val + 1) (b := prev.val) (by omega) (by omega)
      rw [hsplit1, hsplit2, hsingle] at hright_before_zero
      omega
    right
    refine ⟨a1, prev, hnext, hprev_succ, ha1_rr, hprev_right, ?_⟩
    intro k hk1 hk2
    rcases htail1 k hk1 (lt_trans hk2 (by
      have := phase.s.isLt
      dsimp [prev]
      omega)) with hkr | hkrr
    · exfalso
      exact hno_right_before_prev k hk1 hk2 hkr
    · exact hkrr

theorem left3_started_normal_phase_has_last_opposite_tail_word
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (hstart_left3 : gc.moverAt phase.a = left (left (left t))) :
    ∃ a0 a1 prev : Fin gc.configs.length,
      phase.a.val ≤ a0.val ∧
      a0.val < phase.s.val ∧
      gc.moverAt a0 = left (left (left t)) ∧
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      ((gc.moverAt a1 = left (left t) ∧
        gc.moverAt prev = left t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
       (gc.moverAt a1 = right (right t) ∧
        gc.moverAt prev = right t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t))) := by
  rcases phase_all_local5_or_last_opposite_of_n_eq_six gc t phase hn6 with hall_local | hlast
  · exfalso
    rcases hall_local phase.a (Nat.le_refl _) phase.ha_lt_s with hll | hl | hr | hrr
    · exact left3_ne_left2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = left (left t) := hll)
    · exact left3_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = left t := hl)
    · exact left3_ne_right_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = right t := hr)
    · exact left3_ne_right2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = right (right t) := hrr)
  · rcases hlast with ⟨a0, ha0_ge_a, ha0_lt_s, ha0_opp, htail⟩
    rcases allNormal_last_opposite_tail_word gc t hall phase hn6 a0
        ha0_ge_a ha0_lt_s ha0_opp htail with hleft | hright
    · rcases hleft with ⟨a1, prev, hnext, hprev_succ, ha1_ll, hprev_l, hword⟩
      exact ⟨a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hnext, hprev_succ,
        Or.inl ⟨ha1_ll, hprev_l, hword⟩⟩
    · rcases hright with ⟨a1, prev, hnext, hprev_succ, ha1_rr, hprev_r, hword⟩
      exact ⟨a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hnext, hprev_succ,
        Or.inr ⟨ha1_rr, hprev_r, hword⟩⟩

theorem left3_started_normal_phase_has_last_left3_tail_word
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (hstart_left3 : gc.moverAt phase.a = left (left (left t))) :
    ∃ a0 a1 prev : Fin gc.configs.length,
      phase.a.val ≤ a0.val ∧
      a0.val < phase.s.val ∧
      gc.moverAt a0 = left (left (left t)) ∧
      (∀ k : Fin gc.configs.length,
        a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t))) ∧
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      ((gc.moverAt a1 = left (left t) ∧
        gc.moverAt prev = left t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
       (gc.moverAt a1 = right (right t) ∧
        gc.moverAt prev = right t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t))) := by
  rcases phase_all_local5_or_last_opposite_of_n_eq_six gc t phase hn6 with hall_local | hlast
  · exfalso
    rcases hall_local phase.a (Nat.le_refl _) phase.ha_lt_s with hll | hl | hr | hrr
    · exact left3_ne_left2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = left (left t) := hll)
    · exact left3_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = left t := hl)
    · exact left3_ne_right_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = right t := hr)
    · exact left3_ne_right2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase.a := hstart_left3.symm
          _ = right (right t) := hrr)
  · rcases hlast with ⟨a0, ha0_ge_a, ha0_lt_s, ha0_opp, htail⟩
    have hno_later_left3 : ∀ k : Fin gc.configs.length,
        a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t)) := by
      intro k hk1 hk2 hk
      rcases htail k hk1 hk2 with hkll | hkl | hkr | hkrr
      · exact left3_ne_left2_of_n_eq_six hn6 t (by
          calc
            left (left (left t)) = gc.moverAt k := hk.symm
            _ = left (left t) := hkll)
      · exact left3_ne_left_of_n_eq_six hn6 t (by
          calc
            left (left (left t)) = gc.moverAt k := hk.symm
            _ = left t := hkl)
      · exact left3_ne_right_of_n_eq_six hn6 t (by
          calc
            left (left (left t)) = gc.moverAt k := hk.symm
            _ = right t := hkr)
      · exact left3_ne_right2_of_n_eq_six hn6 t (by
          calc
            left (left (left t)) = gc.moverAt k := hk.symm
            _ = right (right t) := hkrr)
    rcases allNormal_last_opposite_tail_word gc t hall phase hn6 a0
        ha0_ge_a ha0_lt_s ha0_opp htail with hleft | hright
    · rcases hleft with ⟨a1, prev, hnext, hprev_succ, ha1_ll, hprev_l, hword⟩
      exact ⟨a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later_left3, hnext, hprev_succ,
        Or.inl ⟨ha1_ll, hprev_l, hword⟩⟩
    · rcases hright with ⟨a1, prev, hnext, hprev_succ, ha1_rr, hprev_r, hword⟩
      exact ⟨a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later_left3, hnext, hprev_succ,
        Or.inr ⟨ha1_rr, hprev_r, hword⟩⟩

theorem right3_started_normal_phase_has_last_opposite_tail_word
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (hstart_right3 : gc.moverAt phase.a = right (right (right t))) :
    ∃ a0 a1 prev : Fin gc.configs.length,
      phase.a.val ≤ a0.val ∧
      a0.val < phase.s.val ∧
      gc.moverAt a0 = left (left (left t)) ∧
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      ((gc.moverAt a1 = left (left t) ∧
        gc.moverAt prev = left t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
       (gc.moverAt a1 = right (right t) ∧
        gc.moverAt prev = right t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t))) := by
  have hstart_left3 : gc.moverAt phase.a = left (left (left t)) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hstart_right3
  exact left3_started_normal_phase_has_last_opposite_tail_word
    gc t hall phase hn6 hstart_left3

theorem left3_started_phase_has_last_left3_tail_word_from_local6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (_hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t,
      phase.a = j1 ∧
      ∃ a0 a1 prev : Fin gc.configs.length,
        phase.a.val ≤ a0.val ∧
        a0.val < phase.s.val ∧
        gc.moverAt a0 = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t))) ∧
        nextIndex gc.configs a0 = a1 ∧
        prev.val + 1 = phase.s.val ∧
        ((gc.moverAt a1 = left (left t) ∧
          gc.moverAt prev = left t ∧
          ∀ k : Fin gc.configs.length,
            a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
         (gc.moverAt a1 = right (right t) ∧
          gc.moverAt prev = right t ∧
          ∀ k : Fin gc.configs.length,
            a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t))) := by
  have hj1_nonmover : gc.moverAt j1 ≠ t := by
    rw [hj1_left3]
    exact left3_ne_self_of_n_eq_six hn6 t
  rcases exists_ternaryPhase_starting_at gc t j1 hj1_nonmover hafter with ⟨phase, hphasea⟩
  rcases left3_started_normal_phase_has_last_left3_tail_word gc t hall phase hn6 (by
      simpa [hphasea] using hj1_left3) with
    ⟨a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hbranch⟩
  exact ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hbranch⟩

theorem right3_started_phase_has_last_right3_tail_word_from_local6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t,
      phase.a = j1 ∧
      ∃ a0 a1 prev : Fin gc.configs.length,
        phase.a.val ≤ a0.val ∧
        a0.val < phase.s.val ∧
        gc.moverAt a0 = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t))) ∧
        nextIndex gc.configs a0 = a1 ∧
        prev.val + 1 = phase.s.val ∧
        ((gc.moverAt a1 = left (left t) ∧
          gc.moverAt prev = left t ∧
          ∀ k : Fin gc.configs.length,
            a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
         (gc.moverAt a1 = right (right t) ∧
          gc.moverAt prev = right t ∧
          ∀ k : Fin gc.configs.length,
            a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t))) := by
  have hj1_left3 : gc.moverAt j1 = left (left (left t)) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hj1_right3
  rcases left3_started_phase_has_last_left3_tail_word_from_local6
      gc t hall hn6 j1 hj1_left3
      (by
        intro k hk
        rcases hj_tail k hk with hkll | hkl | hkt | hkr | hkrr | hk3
        · exact Or.inr (Or.inl hkll)
        · exact Or.inr (Or.inr (Or.inl hkl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hkt)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkr))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hkrr))))
        · exact Or.inl (by simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hk3))
      hafter with
    ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hbranch⟩
  exact ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hbranch⟩

theorem left3_in_phase_before_canonical_suffix_start
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (_hn6 : sys.rs.n = 6)
    (a0 a1 _prev : Fin gc.configs.length)
    (_ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (_ha0_opp : gc.moverAt a0 = left (left (left t)))
    (hno_later : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t)))
    (hnext : nextIndex gc.configs a0 = a1)
    (k_out : Fin gc.configs.length)
    (_hk_phase : phase.a.val < k_out.val)
    (hk_lt_s : k_out.val < phase.s.val)
    (hk_left3 : gc.moverAt k_out = left (left (left t))) :
    k_out.val < a1.val := by
  have ha1_val : a1.val = a0.val + 1 := by
    have hEq := congrArg Fin.val hnext
    have ha1_lt_len : a0.val + 1 < gc.configs.length := by
      have := phase.s.isLt
      omega
    simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
    exact hEq.symm
  by_contra hnot
  have ha0_lt_kout : a0.val < k_out.val := by
    rw [ha1_val] at hnot
    omega
  exact hno_later k_out ha0_lt_kout hk_lt_s hk_left3

theorem right3_in_phase_before_canonical_suffix_start
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (a0 a1 prev : Fin gc.configs.length)
    (ha0_ge_a : phase.a.val ≤ a0.val)
    (ha0_lt_s : a0.val < phase.s.val)
    (ha0_opp : gc.moverAt a0 = left (left (left t)))
    (hno_later : ∀ k : Fin gc.configs.length,
      a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t)))
    (hnext : nextIndex gc.configs a0 = a1)
    (k_out : Fin gc.configs.length)
    (hk_phase : phase.a.val < k_out.val)
    (hk_lt_s : k_out.val < phase.s.val)
    (hk_right3 : gc.moverAt k_out = right (right (right t))) :
    k_out.val < a1.val := by
  have hk_left3 : gc.moverAt k_out = left (left (left t)) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hk_right3
  exact left3_in_phase_before_canonical_suffix_start gc t phase hn6 a0 a1 prev
    ha0_ge_a ha0_lt_s ha0_opp hno_later hnext k_out hk_phase hk_lt_s hk_left3

theorem left3_started_phase_later_left3_before_suffix_start_from_local6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t,
      phase.a = j1 ∧
      ∃ a0 a1 prev : Fin gc.configs.length,
        phase.a.val ≤ a0.val ∧
        a0.val < phase.s.val ∧
        gc.moverAt a0 = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t))) ∧
        nextIndex gc.configs a0 = a1 ∧
        prev.val + 1 = phase.s.val ∧
        (∀ k_out : Fin gc.configs.length,
          phase.a.val < k_out.val → k_out.val < phase.s.val →
          gc.moverAt k_out = left (left (left t)) → k_out.val < a1.val) := by
  rcases left3_started_phase_has_last_left3_tail_word_from_local6
      gc t hall hn6 j1 hj1_left3 hj_tail hafter with
    ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, _hbranch⟩
  refine ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, ?_⟩
  intro k_out hk_phase hk_lt_s hk_left3
  exact left3_in_phase_before_canonical_suffix_start gc t phase hn6 a0 a1 prev
    ha0_ge_a ha0_lt_s ha0_opp hno_later hnext k_out hk_phase hk_lt_s hk_left3

theorem right3_started_phase_later_right3_before_suffix_start_from_local6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t,
      phase.a = j1 ∧
      ∃ a0 a1 prev : Fin gc.configs.length,
        phase.a.val ≤ a0.val ∧
        a0.val < phase.s.val ∧
        gc.moverAt a0 = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          a0.val < k.val → k.val < phase.s.val → gc.moverAt k ≠ left (left (left t))) ∧
        nextIndex gc.configs a0 = a1 ∧
        prev.val + 1 = phase.s.val ∧
        (∀ k_out : Fin gc.configs.length,
          phase.a.val < k_out.val → k_out.val < phase.s.val →
          gc.moverAt k_out = right (right (right t)) → k_out.val < a1.val) := by
  rcases right3_started_phase_has_last_right3_tail_word_from_local6
      gc t hall hn6 j1 hj1_right3 hj_tail hafter with
    ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, _hbranch⟩
  refine ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, ?_⟩
  intro k_out hk_phase hk_lt_s hk_right3
  exact right3_in_phase_before_canonical_suffix_start gc t phase hn6 a0 a1 prev
    ha0_ge_a ha0_lt_s ha0_opp hno_later hnext k_out hk_phase hk_lt_s hk_right3

theorem left_terminal_far_suffix_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (k_out : Fin gc.configs.length)
    (hkout_lt_s : k_out.val < phase.s.val)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    False := by
  rcases hterm phase.s hkout_lt_s with hs_ll | hs_l
  · exact left2_ne_self_of_n_eq_six hn6 t (by
        calc
          left (left t) = gc.moverAt phase.s := hs_ll.symm
          _ = t := phase.hs_mover)
  · exact left_ne_self_of_n_eq_six_local hn6 t (by
        calc
          left t = gc.moverAt phase.s := hs_l.symm
          _ = t := phase.hs_mover)

theorem right_terminal_far_suffix_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (hn6 : sys.rs.n = 6)
    (k_out : Fin gc.configs.length)
    (hkout_lt_s : k_out.val < phase.s.val)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    False := by
  rcases hterm phase.s hkout_lt_s with hs_r | hs_rr
  · exact right_ne_self_of_n_eq_six_local hn6 t (by
        calc
          right t = gc.moverAt phase.s := hs_r.symm
          _ = t := phase.hs_mover)
  · exact right2_ne_self_of_n_eq_six hn6 t (by
        calc
          right (right t) = gc.moverAt phase.s := hs_rr.symm
          _ = t := phase.hs_mover)

theorem left3_started_phase_ends_before_terminal_left3_tail
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase : TernaryPhase gc t, phase.a = j1 ∧ phase.s.val ≤ k_out.val := by
  rcases left3_started_phase_has_last_left3_tail_word_from_local6
      gc t hall hn6 j1 hj1_left3 hj_tail hafter with
    ⟨phase, hphasea, _a0, _a1, _prev, _ha0_ge_a, _ha0_lt_s, _ha0_opp, _hno_later, _hnext, _hprev_succ, _hbranch⟩
  by_cases hk_lt_s : k_out.val < phase.s.val
  · exfalso
    exact left_terminal_far_suffix_false_n6 gc t phase hn6 k_out hk_lt_s hterm
  · exact ⟨phase, hphasea, Nat.le_of_not_gt hk_lt_s⟩

theorem right3_started_phase_ends_before_terminal_right3_tail
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase : TernaryPhase gc t, phase.a = j1 ∧ phase.s.val ≤ k_out.val := by
  rcases right3_started_phase_has_last_right3_tail_word_from_local6
      gc t hall hn6 j1 hj1_right3 hj_tail hafter with
    ⟨phase, hphasea, _a0, _a1, _prev, _ha0_ge_a, _ha0_lt_s, _ha0_opp, _hno_later, _hnext, _hprev_succ, _hbranch⟩
  by_cases hk_lt_s : k_out.val < phase.s.val
  · exfalso
    exact right_terminal_far_suffix_false_n6 gc t phase hn6 k_out hk_lt_s hterm
  · exact ⟨phase, hphasea, Nat.le_of_not_gt hk_lt_s⟩

theorem left_same_terminal_after_reduction_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    False := by
  have hafter_j1 : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t := by
    rcases hafter with ⟨s, hs_gt, hs_t⟩
    exact ⟨s, lt_trans hj1_lt_kout hs_gt, hs_t⟩
  rcases left3_started_phase_ends_before_terminal_left3_tail gc t hall hn6 j1 k_out
      hj1_left3 hkout_left3 hj_tail hafter_j1 hterm with ⟨phase, hphasea, hs_le_kout⟩
  have hs_gt_j1 : j1.val < phase.s.val := by
    simpa [hphasea] using phase.ha_lt_s
  exact hno_t_to_kout phase.s hs_gt_j1 hs_le_kout phase.hs_mover

theorem right_same_terminal_after_reduction_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    False := by
  have hafter_j1 : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t := by
    rcases hafter with ⟨s, hs_gt, hs_t⟩
    exact ⟨s, lt_trans hj1_lt_kout hs_gt, hs_t⟩
  rcases right3_started_phase_ends_before_terminal_right3_tail gc t hall hn6 j1 k_out
      hj1_right3 hkout_right3 hj_tail hafter_j1 hterm with ⟨phase, hphasea, hs_le_kout⟩
  have hs_gt_j1 : j1.val < phase.s.val := by
    simpa [hphasea] using phase.ha_lt_s
  exact hno_t_to_kout phase.s hs_gt_j1 hs_le_kout phase.hs_mover

theorem left3_started_phase_terminal_tail_false_from_local6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    False :=
  left_same_terminal_after_reduction_n6 gc t hall hn6 j1 k_out
    hj1_left3 hj1_lt_kout hkout_left3 hj_tail hno_t_to_kout hafter hterm

theorem right3_started_phase_terminal_tail_false_from_local6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    False :=
  right_same_terminal_after_reduction_n6 gc t hall hn6 j1 k_out
    hj1_right3 hj1_lt_kout hkout_right3 hj_tail hno_t_to_kout hafter hterm

theorem left_terminal_tail_first_after_opp_forced_left2_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (k_out k1 : Fin gc.configs.length)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hkout_lt_k1 : k_out.val < k1.val)
    (hnext : nextIndex gc.configs k_out = k1)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    gc.moverAt k1 = left (left t) := by
  rcases hterm k1 hkout_lt_k1 with hk1_left2 | hk1_left
  · exact hk1_left2
  · have hlocal := gc.next_mover_is_local k_out
    rw [hnext, hkout_left3] at hlocal
    rcases hlocal with hleft | hself | hright
    · exfalso
      have hk1_right2 : gc.moverAt k1 = right (right t) := by
        simpa [left4_eq_right2_of_n_eq_six sys.rs hn6 t] using hleft
      exact right2_ne_left_of_n_eq_six hn6 t (by
        exact hk1_right2.symm.trans hk1_left)
    · exfalso
      exact left3_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt k1 := by simpa using hself.symm
          _ = left t := hk1_left)
    · exfalso
      have hk1_left2 : gc.moverAt k1 = left (left t) := by
        simpa [right_left_eq_self] using hright
      exact left2_ne_left_of_n_eq_six hn6 t (by
        exact hk1_left2.symm.trans hk1_left)

theorem right_terminal_tail_first_after_opp_forced_right2_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (k_out k1 : Fin gc.configs.length)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hkout_lt_k1 : k_out.val < k1.val)
    (hnext : nextIndex gc.configs k_out = k1)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    gc.moverAt k1 = right (right t) := by
  rcases hterm k1 hkout_lt_k1 with hk1_right | hk1_right2
  · have hlocal := gc.next_mover_is_local k_out
    rw [hnext, hkout_right3] at hlocal
    rcases hlocal with hleft | hself | hright
    · exfalso
      have hk1_right2' : gc.moverAt k1 = right (right t) := by
        simpa using hleft
      exact right2_ne_right_of_n_eq_six hn6 t (by
        exact hk1_right2'.symm.trans hk1_right)
    · exfalso
      exact right3_ne_right_of_n_eq_six hn6 t (by
        calc
          right (right (right t)) = gc.moverAt k1 := by simpa using hself.symm
          _ = right t := hk1_right)
    · exfalso
      have hk1_left2 : gc.moverAt k1 = left (left t) := by
        simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t, right4_eq_left2_of_n_eq_six sys.rs hn6 t] using hright
      exact left2_ne_right_of_n_eq_six hn6 t (by
        exact hk1_left2.symm.trans hk1_right)
  · exact hk1_right2

theorem left_terminal_tail_next_after_left2_forced_left_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (k_out k1 k2 : Fin gc.configs.length)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hk1_left2 : gc.moverAt k1 = left (left t))
    (hnext : nextIndex gc.configs k1 = k2)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    gc.moverAt k2 = left t := by
  rcases hterm k2 hkout_lt_k2 with hk2_left2 | hk2_left
  · have hiso := binary_left2_isolated_n6 gc t hn6 hbin_left2 k1 hk1_left2
    exact False.elim (hiso (by simpa [hnext] using hk2_left2))
  · exact hk2_left

theorem left_terminal_tail_next_after_left_forced_left2_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left1 : isBinary sys.rs (left t))
    (k_out k1 k2 : Fin gc.configs.length)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hk1_left : gc.moverAt k1 = left t)
    (hnext : nextIndex gc.configs k1 = k2)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    gc.moverAt k2 = left (left t) := by
  rcases hterm k2 hkout_lt_k2 with hk2_left2 | hk2_left
  · exact hk2_left2
  · have hiso := binary_left1_isolated_n6 gc t hn6 hbin_left1 k1 hk1_left
    exact False.elim (hiso (by simpa [hnext] using hk2_left))

theorem right_terminal_tail_next_after_right2_forced_right_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (k_out k1 k2 : Fin gc.configs.length)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hk1_right2 : gc.moverAt k1 = right (right t))
    (hnext : nextIndex gc.configs k1 = k2)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    gc.moverAt k2 = right t := by
  rcases hterm k2 hkout_lt_k2 with hk2_right | hk2_right2
  · exact hk2_right
  · have hiso := binary_right2_isolated_n6 gc t hn6 hbin_right2 k1 hk1_right2
    exact False.elim (hiso (by simpa [hnext] using hk2_right2))

theorem right_terminal_tail_next_after_right_forced_right2_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right1 : isBinary sys.rs (right t))
    (k_out k1 k2 : Fin gc.configs.length)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hk1_right : gc.moverAt k1 = right t)
    (hnext : nextIndex gc.configs k1 = k2)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    gc.moverAt k2 = right (right t) := by
  rcases hterm k2 hkout_lt_k2 with hk2_right | hk2_right2
  · have hiso := binary_right1_isolated_n6 gc t hn6 hbin_right1 k1 hk1_right
    exact False.elim (hiso (by simpa [hnext] using hk2_right))
  · exact hk2_right2

theorem left_terminal_tail_two_steps_forced_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (hbin_left1 : isBinary sys.rs (left t))
    (k_out k1 k2 k3 : Fin gc.configs.length)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hkout_lt_k3 : k_out.val < k3.val)
    (hk1_left2 : gc.moverAt k1 = left (left t))
    (hnext12 : nextIndex gc.configs k1 = k2)
    (hnext23 : nextIndex gc.configs k2 = k3)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    gc.moverAt k2 = left t ∧ gc.moverAt k3 = left (left t) := by
  have hk2_left := left_terminal_tail_next_after_left2_forced_left_n6
    gc t hn6 hbin_left2 k_out k1 k2 hkout_lt_k2 hk1_left2 hnext12 hterm
  have hk3_left2 := left_terminal_tail_next_after_left_forced_left2_n6
    gc t hn6 hbin_left1 k_out k2 k3 hkout_lt_k3 hk2_left hnext23 hterm
  exact ⟨hk2_left, hk3_left2⟩

theorem right_terminal_tail_two_steps_forced_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (hbin_right1 : isBinary sys.rs (right t))
    (k_out k1 k2 k3 : Fin gc.configs.length)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hkout_lt_k3 : k_out.val < k3.val)
    (hk1_right2 : gc.moverAt k1 = right (right t))
    (hnext12 : nextIndex gc.configs k1 = k2)
    (hnext23 : nextIndex gc.configs k2 = k3)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    gc.moverAt k2 = right t ∧ gc.moverAt k3 = right (right t) := by
  have hk2_right := right_terminal_tail_next_after_right2_forced_right_n6
    gc t hn6 hbin_right2 k_out k1 k2 hkout_lt_k2 hk1_right2 hnext12 hterm
  have hk3_right2 := right_terminal_tail_next_after_right_forced_right2_n6
    gc t hn6 hbin_right1 k_out k2 k3 hkout_lt_k3 hk2_right hnext23 hterm
  exact ⟨hk2_right, hk3_right2⟩

theorem left_terminal_tail_three_step_prefix_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (hbin_left1 : isBinary sys.rs (left t))
    (k_out k1 k2 k3 : Fin gc.configs.length)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hkout_lt_k1 : k_out.val < k1.val)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hkout_lt_k3 : k_out.val < k3.val)
    (hnext01 : nextIndex gc.configs k_out = k1)
    (hnext12 : nextIndex gc.configs k1 = k2)
    (hnext23 : nextIndex gc.configs k2 = k3)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    gc.moverAt k1 = left (left t) ∧
    gc.moverAt k2 = left t ∧
    gc.moverAt k3 = left (left t) := by
  have hk1_left2 := left_terminal_tail_first_after_opp_forced_left2_n6
    gc t hn6 k_out k1 hkout_left3 hkout_lt_k1 hnext01 hterm
  have htwo := left_terminal_tail_two_steps_forced_n6
    gc t hn6 hbin_left2 hbin_left1 k_out k1 k2 k3
    hkout_lt_k2 hkout_lt_k3 hk1_left2 hnext12 hnext23 hterm
  exact ⟨hk1_left2, htwo.1, htwo.2⟩

theorem right_terminal_tail_three_step_prefix_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (hbin_right1 : isBinary sys.rs (right t))
    (k_out k1 k2 k3 : Fin gc.configs.length)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hkout_lt_k1 : k_out.val < k1.val)
    (hkout_lt_k2 : k_out.val < k2.val)
    (hkout_lt_k3 : k_out.val < k3.val)
    (hnext01 : nextIndex gc.configs k_out = k1)
    (hnext12 : nextIndex gc.configs k1 = k2)
    (hnext23 : nextIndex gc.configs k2 = k3)
    (hterm : ∀ k : Fin gc.configs.length,
      k_out.val < k.val → gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    gc.moverAt k1 = right (right t) ∧
    gc.moverAt k2 = right t ∧
    gc.moverAt k3 = right (right t) := by
  have hk1_right2 := right_terminal_tail_first_after_opp_forced_right2_n6
    gc t hn6 k_out k1 hkout_right3 hkout_lt_k1 hnext01 hterm
  have htwo := right_terminal_tail_two_steps_forced_n6
    gc t hn6 hbin_right2 hbin_right1 k_out k1 k2 k3
    hkout_lt_k2 hkout_lt_k3 hk1_right2 hnext12 hnext23 hterm
  exact ⟨hk1_right2, htwo.1, htwo.2⟩

theorem left_same_prefix_suffix_position_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t, ∃ a0 a1 prev : Fin gc.configs.length,
      phase.a = j1 ∧
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      k_out.val < a1.val := by
  have hafter_j1 : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t := by
    rcases hafter with ⟨s, hs_gt, hs_t⟩
    exact ⟨s, lt_trans hj1_lt_kout hs_gt, hs_t⟩
  rcases left3_started_phase_later_left3_before_suffix_start_from_local6
      gc t hall hn6 j1 hj1_left3 hj_tail hafter_j1 with
    ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hpos⟩
  have hkout_lt_s : k_out.val < phase.s.val := by
    by_contra hnot
    have hs_le_kout : phase.s.val ≤ k_out.val := by omega
    have hs_gt_j1 : j1.val < phase.s.val := by
      simpa [hphasea] using phase.ha_lt_s
    exact hno_t_to_kout phase.s hs_gt_j1 hs_le_kout phase.hs_mover
  have hk_phase : phase.a.val < k_out.val := by
    simpa [hphasea] using hj1_lt_kout
  exact ⟨phase, a0, a1, prev, hphasea, hnext, hprev_succ,
    hpos k_out hk_phase hkout_lt_s hkout_left3⟩

theorem right_same_prefix_suffix_position_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t, ∃ a0 a1 prev : Fin gc.configs.length,
      phase.a = j1 ∧
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      k_out.val < a1.val := by
  rcases right3_started_phase_later_right3_before_suffix_start_from_local6
      gc t hall hn6 j1 hj1_right3 hj_tail
      (by
        rcases hafter with ⟨s, hs_gt, hs_t⟩
        exact ⟨s, lt_trans hj1_lt_kout hs_gt, hs_t⟩) with
    ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hpos⟩
  have hkout_lt_s : k_out.val < phase.s.val := by
    by_contra hnot
    have hs_le_kout : phase.s.val ≤ k_out.val := by omega
    have hs_gt_j1 : j1.val < phase.s.val := by
      simpa [hphasea] using phase.ha_lt_s
    exact hno_t_to_kout phase.s hs_gt_j1 hs_le_kout phase.hs_mover
  have hk_phase : phase.a.val < k_out.val := by
    simpa [hphasea] using hj1_lt_kout
  exact ⟨phase, a0, a1, prev, hphasea, hnext, hprev_succ,
    hpos k_out hk_phase hkout_lt_s hkout_right3⟩

theorem left_same_prefix_tail_word_position_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t, ∃ a0 a1 prev : Fin gc.configs.length,
      phase.a = j1 ∧
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      k_out.val < a1.val ∧
      ((gc.moverAt a1 = left (left t) ∧
        gc.moverAt prev = left t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
       (gc.moverAt a1 = right (right t) ∧
        gc.moverAt prev = right t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t))) := by
  have hafter_j1 : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t := by
    rcases hafter with ⟨s, hs_gt, hs_t⟩
    exact ⟨s, lt_trans hj1_lt_kout hs_gt, hs_t⟩
  rcases left3_started_phase_has_last_left3_tail_word_from_local6
      gc t hall hn6 j1 hj1_left3 hj_tail hafter_j1 with
    ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hbranch⟩
  have hkout_lt_s : k_out.val < phase.s.val := by
    by_contra hnot
    have hs_le_kout : phase.s.val ≤ k_out.val := by omega
    have hs_gt_j1 : j1.val < phase.s.val := by
      simpa [hphasea] using phase.ha_lt_s
    exact hno_t_to_kout phase.s hs_gt_j1 hs_le_kout phase.hs_mover
  have hk_phase : phase.a.val < k_out.val := by
    simpa [hphasea] using hj1_lt_kout
  have hkout_lt_a1 := left3_in_phase_before_canonical_suffix_start gc t phase hn6
    a0 a1 prev ha0_ge_a ha0_lt_s ha0_opp hno_later hnext k_out hk_phase hkout_lt_s hkout_left3
  exact ⟨phase, a0, a1, prev, hphasea, hnext, hprev_succ, hkout_lt_a1, hbranch⟩

theorem right_same_prefix_tail_word_position_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) :
    ∃ phase : TernaryPhase gc t, ∃ a0 a1 prev : Fin gc.configs.length,
      phase.a = j1 ∧
      nextIndex gc.configs a0 = a1 ∧
      prev.val + 1 = phase.s.val ∧
      k_out.val < a1.val ∧
      ((gc.moverAt a1 = left (left t) ∧
        gc.moverAt prev = left t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
       (gc.moverAt a1 = right (right t) ∧
        gc.moverAt prev = right t ∧
        ∀ k : Fin gc.configs.length,
          a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t))) := by
  have hafter_j1 : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t := by
    rcases hafter with ⟨s, hs_gt, hs_t⟩
    exact ⟨s, lt_trans hj1_lt_kout hs_gt, hs_t⟩
  rcases right3_started_phase_has_last_right3_tail_word_from_local6
      gc t hall hn6 j1 hj1_right3 hj_tail hafter_j1 with
    ⟨phase, hphasea, a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev_succ, hbranch⟩
  have hkout_lt_s : k_out.val < phase.s.val := by
    by_contra hnot
    have hs_le_kout : phase.s.val ≤ k_out.val := by omega
    have hs_gt_j1 : j1.val < phase.s.val := by
      simpa [hphasea] using phase.ha_lt_s
    exact hno_t_to_kout phase.s hs_gt_j1 hs_le_kout phase.hs_mover
  have hk_phase : phase.a.val < k_out.val := by
    simpa [hphasea] using hj1_lt_kout
  have hkout_lt_a1 := right3_in_phase_before_canonical_suffix_start gc t phase hn6
    a0 a1 prev ha0_ge_a ha0_lt_s ha0_opp hno_later hnext k_out hk_phase hkout_lt_s hkout_right3
  exact ⟨phase, a0, a1, prev, hphasea, hnext, hprev_succ, hkout_lt_a1, hbranch⟩

theorem left3_start_predecessor_only_second_neighbor_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left3 : isBinary sys.rs (left (left (left t))))
    (j1 : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t))) :
    ∃ prev : Fin gc.configs.length,
      nextIndex gc.configs prev = j1 ∧
      (gc.moverAt prev = left (left t) ∨ gc.moverAt prev = right (right t)) := by
  by_cases h0 : j1.val = 0
  · let prev : Fin gc.configs.length := ⟨gc.configs.length - 1, by
      have := gc.configs_length_pos
      omega⟩
    have hnext_eq : nextIndex gc.configs prev = j1 := by
      apply Fin.ext
      have hj1_zero : j1.val = 0 := h0
      have hlen_pos : 0 < gc.configs.length := gc.configs_length_pos
      have hmod : (gc.configs.length - 1 + 1) % gc.configs.length = 0 := by
        have hlen : gc.configs.length - 1 + 1 = gc.configs.length := by omega
        rw [hlen, Nat.mod_self]
      simpa [nextIndex, prev, hj1_zero] using hmod
    have hnext_local :
        left (left (left t)) = left (gc.moverAt prev) ∨
        left (left (left t)) = gc.moverAt prev ∨
        left (left (left t)) = right (gc.moverAt prev) := by
      simpa [hnext_eq, hj1_left3] using gc.next_mover_is_local prev
    rcases hnext_local with hleft | hself | hright
    · refine ⟨prev, hnext_eq, Or.inl ?_⟩
      have : left (left t) = gc.moverAt prev := by
        have := congrArg right (show left (left (left t)) = left (gc.moverAt prev) by simpa using hleft)
        simpa [right_left_eq_self] using this
      simpa using this.symm
    · have hprev_left3 : gc.moverAt prev = left (left (left t)) := by
        simpa using hself.symm
      have hiso := binary_left3_isolated_n6 gc t hn6 hbin_left3 prev hprev_left3
      exact False.elim (hiso (by simpa [hnext_eq] using hj1_left3))
    · refine ⟨prev, hnext_eq, Or.inr ?_⟩
      have : right (right t) = gc.moverAt prev := by
        have := congrArg left (show left (left (left t)) = right (gc.moverAt prev) by simpa using hright)
        simpa [left4_eq_right2_of_n_eq_six sys.rs hn6 t, left_right_eq_self] using this
      simpa using this.symm
  · let prev : Fin gc.configs.length := ⟨j1.val - 1, by
      have := j1.isLt
      omega⟩
    have hprev_succ : prev.val + 1 = j1.val := by
      dsimp [prev]
      omega
    have hnext_eq : nextIndex gc.configs prev = j1 := by
      apply Fin.ext
      simp [nextIndex, prev, hprev_succ, Nat.mod_eq_of_lt j1.isLt]
    have hnext_local :
        left (left (left t)) = left (gc.moverAt prev) ∨
        left (left (left t)) = gc.moverAt prev ∨
        left (left (left t)) = right (gc.moverAt prev) := by
      simpa [hnext_eq, hj1_left3] using gc.next_mover_is_local prev
    rcases hnext_local with hleft | hself | hright
    · refine ⟨prev, hnext_eq, Or.inl ?_⟩
      have : left (left t) = gc.moverAt prev := by
        have := congrArg right (show left (left (left t)) = left (gc.moverAt prev) by simpa using hleft)
        simpa [right_left_eq_self] using this
      simpa using this.symm
    · have hprev_left3 : gc.moverAt prev = left (left (left t)) := by
        simpa using hself.symm
      have hiso := binary_left3_isolated_n6 gc t hn6 hbin_left3 prev hprev_left3
      exact False.elim (hiso (by simpa [hnext_eq] using hj1_left3))
    · refine ⟨prev, hnext_eq, Or.inr ?_⟩
      have : right (right t) = gc.moverAt prev := by
        have := congrArg left (show left (left (left t)) = right (gc.moverAt prev) by simpa using hright)
        simpa [left4_eq_right2_of_n_eq_six sys.rs hn6 t, left_right_eq_self] using this
      simpa using this.symm

theorem right3_start_predecessor_only_second_neighbor_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right3 : isBinary sys.rs (right (right (right t))))
    (j1 : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t))) :
    ∃ prev : Fin gc.configs.length,
      nextIndex gc.configs prev = j1 ∧
      (gc.moverAt prev = left (left t) ∨ gc.moverAt prev = right (right t)) := by
  have hbin_left3 : isBinary sys.rs (left (left (left t))) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hbin_right3
  have hj1_left3 : gc.moverAt j1 = left (left (left t)) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hj1_right3
  exact left3_start_predecessor_only_second_neighbor_n6 gc t hn6 hbin_left3 j1 hj1_left3

theorem first_later_left3_predecessor_second_neighbor_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ left (left (left t))) :
    ∃ prev : Fin gc.configs.length,
      prev.val + 1 = k_out.val ∧
      (prev = j1 ∨ gc.moverAt prev = left (left t) ∨ gc.moverAt prev = right (right t)) := by
  let prev : Fin gc.configs.length := ⟨k_out.val - 1, by
    have := k_out.isLt
    omega⟩
  have hprev_succ : prev.val + 1 = k_out.val := by
    dsimp [prev]
    omega
  have hnext_eq : nextIndex gc.configs prev = k_out := by
    apply Fin.ext
    simp [nextIndex, prev, hprev_succ]
    exact Nat.mod_eq_of_lt k_out.isLt
  have hnext_local := gc.next_mover_is_local prev
  rw [hnext_eq] at hnext_local
  rcases hnext_local with hleft | hself | hright
  · refine ⟨prev, hprev_succ, Or.inr (Or.inl ?_)⟩
    have : left (left t) = gc.moverAt prev := by
      have := congrArg right (show left (left (left t)) = left (gc.moverAt prev) by
        simpa [hkout_left3] using hleft)
      simpa [right_left_eq_self] using this
    simpa using this.symm
  ·
    have hprev_left3 : gc.moverAt prev = left (left (left t)) := by
      simpa [hkout_left3] using hself.symm
    have hprev_eq_j1 : prev = j1 := by
      by_contra hne
      have hprev_gt_j1 : j1.val < prev.val := by
        dsimp [prev]
        have hneq : prev.val ≠ j1.val := by
          intro hval
          exact hne (Fin.ext hval)
        omega
      exact hfirst prev hprev_gt_j1 (by
        dsimp [prev]
        omega) hprev_left3
    exact ⟨prev, hprev_succ, Or.inl hprev_eq_j1⟩
  · refine ⟨prev, hprev_succ, Or.inr (Or.inr ?_)⟩
    have : right (right t) = gc.moverAt prev := by
      have := congrArg left (show left (left (left t)) = right (gc.moverAt prev) by
        simpa [hkout_left3] using hright)
      simpa [left4_eq_right2_of_n_eq_six sys.rs hn6 t, left_right_eq_self] using this
    simpa using this.symm

theorem first_later_right3_predecessor_second_neighbor_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ right (right (right t))) :
    ∃ prev : Fin gc.configs.length,
      prev.val + 1 = k_out.val ∧
      (prev = j1 ∨ gc.moverAt prev = left (left t) ∨ gc.moverAt prev = right (right t)) := by
  have hj1_left3 : gc.moverAt j1 = left (left (left t)) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hj1_right3
  have hkout_left3 : gc.moverAt k_out = left (left (left t)) := by
    simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hkout_right3
  rcases first_later_left3_predecessor_second_neighbor_n6 gc t hn6 j1 k_out
      hj1_lt_kout hj1_left3 hkout_left3
      (by
        intro k hk1 hk2 hk
        exact hfirst k hk1 hk2 (by
          simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hk)) with
    ⟨prev, hprev_succ, hprev_side⟩
  exact ⟨prev, hprev_succ, hprev_side⟩

theorem first_later_left3_predecessor_only_second_neighbor_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left3 : isBinary sys.rs (left (left (left t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ left (left (left t))) :
    ∃ prev : Fin gc.configs.length,
      prev.val + 1 = k_out.val ∧
      (gc.moverAt prev = left (left t) ∨ gc.moverAt prev = right (right t)) := by
  rcases first_later_left3_predecessor_second_neighbor_n6 gc t hn6 j1 k_out
      hj1_lt_kout hj1_left3 hkout_left3 hfirst with
    ⟨prev, hprev_succ, hprev_side⟩
  rcases hprev_side with hprev_eq_j1 | hprev_left2 | hprev_right2
  · have hkout_val : k_out.val = j1.val + 1 := by
      simpa [hprev_eq_j1] using hprev_succ.symm
    have hj1_succ_lt_len : j1.val + 1 < gc.configs.length := by
      exact lt_of_eq_of_lt hkout_val.symm k_out.isLt
    have hnext : nextIndex gc.configs j1 = k_out := by
      apply Fin.ext
      simp [nextIndex, Nat.mod_eq_of_lt hj1_succ_lt_len, hkout_val]
    have hiso := binary_left3_isolated_n6 gc t hn6 hbin_left3 j1 hj1_left3
    exact False.elim (hiso (by simpa [hnext] using hkout_left3))
  · exact ⟨prev, hprev_succ, Or.inl hprev_left2⟩
  · exact ⟨prev, hprev_succ, Or.inr hprev_right2⟩

theorem first_later_right3_predecessor_only_second_neighbor_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right3 : isBinary sys.rs (right (right (right t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ right (right (right t))) :
    ∃ prev : Fin gc.configs.length,
      prev.val + 1 = k_out.val ∧
      (gc.moverAt prev = left (left t) ∨ gc.moverAt prev = right (right t)) := by
  rcases first_later_right3_predecessor_second_neighbor_n6 gc t hn6 j1 k_out
      hj1_lt_kout hj1_right3 hkout_right3 hfirst with
    ⟨prev, hprev_succ, hprev_side⟩
  rcases hprev_side with hprev_eq_j1 | hprev_left2 | hprev_right2
  · have hkout_val : k_out.val = j1.val + 1 := by
      simpa [hprev_eq_j1] using hprev_succ.symm
    have hj1_succ_lt_len : j1.val + 1 < gc.configs.length := by
      exact lt_of_eq_of_lt hkout_val.symm k_out.isLt
    have hnext : nextIndex gc.configs j1 = k_out := by
      apply Fin.ext
      simp [nextIndex, Nat.mod_eq_of_lt hj1_succ_lt_len, hkout_val]
    have hiso := binary_right3_isolated_n6 gc t hn6 hbin_right3 j1 hj1_right3
    exact False.elim (hiso (by simpa [hnext] using hkout_right3))
  · exact ⟨prev, hprev_succ, Or.inl hprev_left2⟩
  · exact ⟨prev, hprev_succ, Or.inr hprev_right2⟩

theorem first_later_left3_not_immediate_restart_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left3 : isBinary sys.rs (left (left (left t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ left (left (left t))) :
    j1.val + 1 < k_out.val := by
  rcases first_later_left3_predecessor_only_second_neighbor_n6
      gc t hn6 hbin_left3 j1 k_out hj1_lt_kout hj1_left3 hkout_left3 hfirst with
    ⟨prev, hprev_succ, hprev_side⟩
  have hprev_ne_j1 : prev ≠ j1 := by
    intro hEq
    rcases hprev_side with hprev_left2 | hprev_right2
    · exact left3_ne_left2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt prev := by rw [hEq]
          _ = left (left t) := hprev_left2)
    · exact left3_ne_right2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt prev := by rw [hEq]
          _ = right (right t) := hprev_right2)
  have hneqv : prev.val ≠ j1.val := by
    intro hval
    exact hprev_ne_j1 (Fin.ext hval)
  omega

theorem first_later_right3_not_immediate_restart_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right3 : isBinary sys.rs (right (right (right t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_lt_kout : j1.val < k_out.val)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ right (right (right t))) :
    j1.val + 1 < k_out.val := by
  rcases first_later_right3_predecessor_only_second_neighbor_n6
      gc t hn6 hbin_right3 j1 k_out hj1_lt_kout hj1_right3 hkout_right3 hfirst with
    ⟨prev, hprev_succ, hprev_side⟩
  have hprev_ne_j1 : prev ≠ j1 := by
    intro hEq
    have hj1_left3 : gc.moverAt j1 = left (left (left t)) := by
      simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hj1_right3
    rcases hprev_side with hprev_left2 | hprev_right2
    ·
      exact left3_ne_left2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt prev := by rw [hEq]
          _ = left (left t) := hprev_left2)
    · exact left3_ne_right2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt prev := by rw [hEq]
          _ = right (right t) := hprev_right2)
  have hneqv : prev.val ≠ j1.val := by
    intro hval
    exact hprev_ne_j1 (Fin.ext hval)
  omega

theorem left_continuation_phase_counts_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (phase0 : TernaryPhase gc t)
    (hstart_left3 : gc.moverAt phase0.a = left (left (left t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase0.a.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 1 ∧
    gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 0 := by
  have hK0 : gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 0 := by
    apply intervalFireCount_eq_zero_of_noFire gc (right t)
      (Nat.le_of_lt phase0.ha_lt_s) (Nat.le_of_lt phase0.s.isLt)
    intro k hk_ge hk_lt
    by_cases hk_eq : k = phase0.a
    · subst hk_eq
      intro hk
      exact left3_ne_right_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase0.a := hstart_left3.symm
          _ = right t := hk)
    · have hk_gt : phase0.a.val < k.val := by
        have hneqv : k.val ≠ phase0.a.val := by
          intro hval
          exact hk_eq (Fin.ext hval)
        omega
      rcases hphase_branch k hk_gt hk_lt with hk | hk
      · intro hkr
        exact left2_ne_right_of_n_eq_six hn6 t (Eq.trans hk.symm hkr)
      · intro hkr
        exact left_ne_right_of_n_eq_six hn6 t (Eq.trans hk.symm hkr)
  have hnorm0 : isNormalFormGap gc t phase0 := hall phase0
  have hJ1 : gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 1 := by
    exact (normalForm_gap_constraint gc t phase0 hnorm0).2.1 hK0
  exact ⟨hJ1, hK0⟩

theorem right_continuation_phase_counts_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (phase0 : TernaryPhase gc t)
    (hstart_right3 : gc.moverAt phase0.a = right (right (right t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase0.a.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 0 ∧
    gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 1 := by
  have hJ0 : gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 0 := by
    apply intervalFireCount_eq_zero_of_noFire gc (left t)
      (Nat.le_of_lt phase0.ha_lt_s) (Nat.le_of_lt phase0.s.isLt)
    intro k hk_ge hk_lt
    by_cases hk_eq : k = phase0.a
    · subst hk_eq
      have hstart_left3 : gc.moverAt phase0.a = left (left (left t)) := by
        simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hstart_right3
      intro hk
      exact left3_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt phase0.a := hstart_left3.symm
          _ = left t := hk)
    · have hk_gt : phase0.a.val < k.val := by
        have hneqv : k.val ≠ phase0.a.val := by
          intro hval
          exact hk_eq (Fin.ext hval)
        omega
      rcases hphase_branch k hk_gt hk_lt with hk | hk
      · intro hkl
        exact right_ne_left_of_n_eq_six hn6 t (Eq.trans hk.symm hkl)
      · intro hkl
        exact right2_ne_left_of_n_eq_six hn6 t (Eq.trans hk.symm hkl)
  have hnorm0 : isNormalFormGap gc t phase0 := hall phase0
  have hK1 : gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 1 := by
    exact (normalForm_gap_constraint gc t phase0 hnorm0).1 hJ0
  exact ⟨hJ0, hK1⟩

theorem left_continuation_len2_suffix_or_ec_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (phase0 : TernaryPhase gc t)
    (hstart_left3 : gc.moverAt phase0.a = left (left (left t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase0.a.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t)
    (hlong : phase0.a.val + 2 < phase0.s.val) :
    hasEntryConflict gc ∨
    ∃ aL prevL : Fin gc.configs.length,
      phase0.a.val < aL.val ∧
      aL.val + 2 = phase0.s.val ∧
      gc.moverAt aL = left (left t) ∧
      prevL.val = aL.val + 1 ∧
      gc.moverAt prevL = left t := by
  have hJ1K0 :=
    left_continuation_phase_counts_n6 gc t hall hn6 phase0 hstart_left3 hphase_branch
  let aL : Fin gc.configs.length := ⟨phase0.s.val - 2, by
    have := phase0.s.isLt
    omega⟩
  have haL_eq : phase0.s.val = aL.val + 2 := by
    dsimp [aL]
    omega
  have haL_lt_s : aL.val < phase0.s.val := by
    dsimp [aL]
    omega
  have haL_ge_a : phase0.a.val ≤ aL.val := by
    dsimp [aL]
    omega
  have haL_nonmover : gc.moverAt aL ≠ t := phase0.ht_nofire aL haL_ge_a haL_lt_s
  let phaseL2 : TernaryPhase gc t := {
    a := aL
    s := phase0.s
    ha_lt_s := haL_lt_s
    hs_mover := phase0.hs_mover
    ha_nonmover := haL_nonmover
    ht_nofire := by
      intro k hk1 hk2
      exact phase0.ht_nofire k (le_trans haL_ge_a hk1) hk2
  }
  have hnormL2 : isNormalFormGap gc t phaseL2 := hall phaseL2
  have hK0L2 : gc.intervalFireCount (right t) phaseL2.a.val phaseL2.s.val = 0 := by
    apply intervalFireCount_eq_zero_of_noFire gc (right t)
      (Nat.le_of_lt phaseL2.ha_lt_s) (Nat.le_of_lt phaseL2.s.isLt)
    intro k hk_ge hk_lt
    exact noFire_of_intervalFireCount_zero_local gc (right t)
      (show phase0.a.val ≤ phase0.s.val by omega)
      (Nat.le_of_lt phase0.s.isLt) hJ1K0.2 k (le_trans haL_ge_a hk_ge) hk_lt
  have hJ1L2 : gc.intervalFireCount (left t) phaseL2.a.val phaseL2.s.val = 1 := by
    exact (normalForm_gap_constraint gc t phaseL2 hnormL2).2.1 hK0L2
  have hlen2L2 : phaseL2.s.val = phaseL2.a.val + 2 := by
    dsimp [phaseL2, aL]
    omega
  rcases one_sided_left_len2_start_ll_or_ec gc t phaseL2 hnormL2 hJ1L2 hK0L2 hlen2L2 with
    hec | haL_left2
  · exact Or.inl hec
  · let prevL : Fin gc.configs.length := ⟨phaseL2.s.val - 1, by
      have := phaseL2.ha_lt_s
      have := phaseL2.s.isLt
      omega⟩
    have hprevL_eq : prevL.val = aL.val + 1 := by
      dsimp [prevL, aL, phaseL2]
      omega
    have hprevL_left : gc.moverAt prevL = left t := by
      simpa [prevL] using
        allNormal_phase_prev_left_of_right_count_zero gc t hall phaseL2 hK0L2
    exact Or.inr ⟨aL, prevL, by
      dsimp [aL]
      omega, by simpa [haL_eq], haL_left2, hprevL_eq, hprevL_left⟩

theorem right_continuation_len2_suffix_or_ec_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (phase0 : TernaryPhase gc t)
    (hstart_right3 : gc.moverAt phase0.a = right (right (right t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase0.a.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t))
    (hlong : phase0.a.val + 2 < phase0.s.val) :
    hasEntryConflict gc ∨
    ∃ aR prevR : Fin gc.configs.length,
      phase0.a.val < aR.val ∧
      aR.val + 2 = phase0.s.val ∧
      gc.moverAt aR = right (right t) ∧
      prevR.val = aR.val + 1 ∧
      gc.moverAt prevR = right t := by
  have hJ0K1 :=
    right_continuation_phase_counts_n6 gc t hall hn6 phase0 hstart_right3 hphase_branch
  let aR : Fin gc.configs.length := ⟨phase0.s.val - 2, by
    have := phase0.s.isLt
    omega⟩
  have haR_eq : phase0.s.val = aR.val + 2 := by
    dsimp [aR]
    omega
  have haR_lt_s : aR.val < phase0.s.val := by
    dsimp [aR]
    omega
  have haR_ge_a : phase0.a.val ≤ aR.val := by
    dsimp [aR]
    omega
  have haR_nonmover : gc.moverAt aR ≠ t := phase0.ht_nofire aR haR_ge_a haR_lt_s
  let phaseR2 : TernaryPhase gc t := {
    a := aR
    s := phase0.s
    ha_lt_s := haR_lt_s
    hs_mover := phase0.hs_mover
    ha_nonmover := haR_nonmover
    ht_nofire := by
      intro k hk1 hk2
      exact phase0.ht_nofire k (le_trans haR_ge_a hk1) hk2
  }
  have hnormR2 : isNormalFormGap gc t phaseR2 := hall phaseR2
  have hJ0R2 : gc.intervalFireCount (left t) phaseR2.a.val phaseR2.s.val = 0 := by
    apply intervalFireCount_eq_zero_of_noFire gc (left t)
      (Nat.le_of_lt phaseR2.ha_lt_s) (Nat.le_of_lt phaseR2.s.isLt)
    intro k hk_ge hk_lt
    exact noFire_of_intervalFireCount_zero_local gc (left t)
      (show phase0.a.val ≤ phase0.s.val by omega)
      (Nat.le_of_lt phase0.s.isLt) hJ0K1.1 k (le_trans haR_ge_a hk_ge) hk_lt
  have hK1R2 : gc.intervalFireCount (right t) phaseR2.a.val phaseR2.s.val = 1 := by
    exact (normalForm_gap_constraint gc t phaseR2 hnormR2).1 hJ0R2
  have hlen2R2 : phaseR2.s.val = phaseR2.a.val + 2 := by
    dsimp [phaseR2, aR]
    omega
  rcases one_sided_right_len2_start_rr_or_ec gc t phaseR2 hnormR2 hJ0R2 hK1R2 hlen2R2 with
    hec | haR_right2
  · exact Or.inl hec
  · let prevR : Fin gc.configs.length := ⟨phaseR2.s.val - 1, by
      have := phaseR2.ha_lt_s
      have := phaseR2.s.isLt
      omega⟩
    have hprevR_eq : prevR.val = aR.val + 1 := by
      dsimp [prevR, aR, phaseR2]
      omega
    have hprevR_right : gc.moverAt prevR = right t := by
      simpa [prevR] using
        allNormal_phase_prev_right_of_left_count_zero gc t hall phaseR2 hJ0R2
    exact Or.inr ⟨aR, prevR, by
      dsimp [aR]
      omega, by simpa [haR_eq], haR_right2, hprevR_eq, hprevR_right⟩

theorem left_same_prefix_shared_end_tail_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase1 : TernaryPhase gc t, ∃ a1 prev1 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      k_out.val < a1.val ∧
      a1.val < phase1.s.val ∧
      gc.moverAt a1 = left (left t) ∧
      prev1.val + 1 = phase1.s.val ∧
      gc.moverAt prev1 = left t ∧
      (∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < prev1.val → gc.moverAt k = left (left t)) := by
  rcases left_continuation_len2_suffix_or_ec_n6 gc t hall hn6 phase0
      (by simpa [hphase0a] using hkout_left3)
      (by
        intro k hk1 hk2
        exact hphase_branch k (by simpa [hphase0a] using hk1) hk2)
      (by simpa [hphase0a] using hlong) with
    hec | ⟨aL, prevL, hkout_lt_aL, haL_eq, haL_left2, hprevL_eq, hprevL_left⟩
  · exact False.elim (entryConflict_impossible gc hec)
  · have hafter_j1 : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t := by
      exact ⟨phase0.s, by
        have hs_gt_kout : k_out.val < phase0.s.val := by
          simpa [hphase0a] using phase0.ha_lt_s
        exact lt_trans hj1_lt_kout hs_gt_kout, phase0.hs_mover⟩
    rcases left3_started_phase_has_last_left3_tail_word_from_local6
      gc t hall hn6 j1 hj1_left3 hj_tail hafter_j1 with
      ⟨phase1, hphase1a, a0, a1, prev1, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev1_succ, hbranch⟩
    have hkout_lt_s : k_out.val < phase1.s.val := by
      by_contra hnot
      have hs_le_kout : phase1.s.val ≤ k_out.val := by omega
      have hs_gt_j1 : j1.val < phase1.s.val := by
        simpa [hphase1a] using phase1.ha_lt_s
      exact hno_t_to_kout phase1.s hs_gt_j1 hs_le_kout phase1.hs_mover
    have hk_phase : phase1.a.val < k_out.val := by
      simpa [hphase1a] using hj1_lt_kout
    have hkout_lt_a1 := left3_in_phase_before_canonical_suffix_start gc t phase1 hn6
      a0 a1 prev1 ha0_ge_a ha0_lt_s ha0_opp hno_later hnext k_out hk_phase hkout_lt_s hkout_left3
    have ha1_lt_phase1s : a1.val < phase1.s.val := by
      have ha1_val : a1.val = a0.val + 1 := by
        have hEq := congrArg Fin.val hnext
        have ha1_lt_len : a0.val + 1 < gc.configs.length := by
          have := phase1.s.isLt
          omega
        simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
        exact hEq.symm
      have ha1_ne_phase1s : a1 ≠ phase1.s := by
        intro hEq
        rcases hbranch with hleft | hright
        · rcases hleft with ⟨ha1_left2, _hprev1_left, _hword⟩
          exact left2_ne_self_of_n_eq_six hn6 t (by
            calc
              left (left t) = gc.moverAt a1 := ha1_left2.symm
              _ = gc.moverAt phase1.s := by rw [hEq]
              _ = t := phase1.hs_mover)
        · rcases hright with ⟨ha1_right2, _hprev1_right, _hword⟩
          exact right2_ne_self_of_n_eq_six hn6 t (by
            calc
              right (right t) = gc.moverAt a1 := ha1_right2.symm
              _ = gc.moverAt phase1.s := by rw [hEq]
              _ = t := phase1.hs_mover)
      have ha1_le_phase1s : a1.val ≤ phase1.s.val := by
        rw [ha1_val]
        omega
      have hneqv : a1.val ≠ phase1.s.val := by
        intro hval
        exact ha1_ne_phase1s (Fin.ext hval)
      exact lt_of_le_of_ne ha1_le_phase1s hneqv
    have hphase1s_eq_phase0s : phase1.s = phase0.s := by
      apply Fin.ext
      by_contra hneq
      have hlt_or_gt : phase1.s.val < phase0.s.val ∨ phase0.s.val < phase1.s.val := by
        omega
      rcases hlt_or_gt with hs1_lt_s0 | hs0_lt_s1
      · exact phase0.ht_nofire phase1.s
          (by
            have hkout_le_phase1s : k_out.val ≤ phase1.s.val := by
              exact Nat.le_of_lt (lt_trans hkout_lt_a1 ha1_lt_phase1s)
            simpa [hphase0a] using hkout_le_phase1s)
          hs1_lt_s0 phase1.hs_mover
      · exact phase1.ht_nofire phase0.s
          (by
            have hj1_le_phase0s : j1.val ≤ phase0.s.val := by
              have hs_gt_kout : k_out.val < phase0.s.val := by
                simpa [hphase0a] using phase0.ha_lt_s
              exact Nat.le_of_lt (lt_trans hj1_lt_kout hs_gt_kout)
            simpa [hphase1a] using hj1_le_phase0s)
          hs0_lt_s1 phase0.hs_mover
    rcases hbranch with hleft | hright
    · rcases hleft with ⟨ha1_left2, hprev1_left, hword⟩
      exact ⟨phase1, a1, prev1, hphase1a, hphase1s_eq_phase0s,
        hkout_lt_a1, ha1_lt_phase1s, ha1_left2, hprev1_succ, hprev1_left, hword⟩
    · rcases hright with ⟨ha1_right2, hprev1_right, _hword⟩
      have hprevL_succ : prevL.val + 1 = phase0.s.val := by
        rw [hprevL_eq]
        omega
      have hprev1_eq_prevL : prev1 = prevL := by
        apply Fin.ext
        rw [hphase1s_eq_phase0s] at hprev1_succ
        omega
      exact False.elim (left_ne_right_of_n_eq_six hn6 t (by
        calc
          left t = gc.moverAt prevL := hprevL_left.symm
          _ = gc.moverAt prev1 := by rw [hprev1_eq_prevL]
          _ = right t := hprev1_right))

theorem right_same_prefix_shared_end_tail_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase1 : TernaryPhase gc t, ∃ a1 prev1 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      k_out.val < a1.val ∧
      a1.val < phase1.s.val ∧
      gc.moverAt a1 = right (right t) ∧
      prev1.val + 1 = phase1.s.val ∧
      gc.moverAt prev1 = right t ∧
      (∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < prev1.val → gc.moverAt k = right (right t)) := by
  rcases right_continuation_len2_suffix_or_ec_n6 gc t hall hn6 phase0
      (by simpa [hphase0a] using hkout_right3)
      (by
        intro k hk1 hk2
        exact hphase_branch k (by simpa [hphase0a] using hk1) hk2)
      (by simpa [hphase0a] using hlong) with
    hec | ⟨aR, prevR, hkout_lt_aR, haR_eq, haR_right2, hprevR_eq, hprevR_right⟩
  · exact False.elim (entryConflict_impossible gc hec)
  · have hafter_j1 : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t := by
      exact ⟨phase0.s, by
        have hs_gt_kout : k_out.val < phase0.s.val := by
          simpa [hphase0a] using phase0.ha_lt_s
        exact lt_trans hj1_lt_kout hs_gt_kout, phase0.hs_mover⟩
    rcases right3_started_phase_has_last_right3_tail_word_from_local6
      gc t hall hn6 j1 hj1_right3 hj_tail hafter_j1 with
      ⟨phase1, hphase1a, a0, a1, prev1, ha0_ge_a, ha0_lt_s, ha0_opp, hno_later, hnext, hprev1_succ, hbranch⟩
    have hkout_lt_s : k_out.val < phase1.s.val := by
      by_contra hnot
      have hs_le_kout : phase1.s.val ≤ k_out.val := by omega
      have hs_gt_j1 : j1.val < phase1.s.val := by
        simpa [hphase1a] using phase1.ha_lt_s
      exact hno_t_to_kout phase1.s hs_gt_j1 hs_le_kout phase1.hs_mover
    have hk_phase : phase1.a.val < k_out.val := by
      simpa [hphase1a] using hj1_lt_kout
    have hkout_lt_a1 := right3_in_phase_before_canonical_suffix_start gc t phase1 hn6
      a0 a1 prev1 ha0_ge_a ha0_lt_s ha0_opp hno_later hnext k_out hk_phase hkout_lt_s hkout_right3
    have ha1_lt_phase1s : a1.val < phase1.s.val := by
      have ha1_val : a1.val = a0.val + 1 := by
        have hEq := congrArg Fin.val hnext
        have ha1_lt_len : a0.val + 1 < gc.configs.length := by
          have := phase1.s.isLt
          omega
        simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
        exact hEq.symm
      have ha1_ne_phase1s : a1 ≠ phase1.s := by
        intro hEq
        rcases hbranch with hleft | hright
        · rcases hleft with ⟨ha1_left2, _hprev1_left, _hword⟩
          exact left2_ne_self_of_n_eq_six hn6 t (by
            calc
              left (left t) = gc.moverAt a1 := ha1_left2.symm
              _ = gc.moverAt phase1.s := by rw [hEq]
              _ = t := phase1.hs_mover)
        · rcases hright with ⟨ha1_right2, _hprev1_right, _hword⟩
          exact right2_ne_self_of_n_eq_six hn6 t (by
            calc
              right (right t) = gc.moverAt a1 := ha1_right2.symm
              _ = gc.moverAt phase1.s := by rw [hEq]
              _ = t := phase1.hs_mover)
      have ha1_le_phase1s : a1.val ≤ phase1.s.val := by
        rw [ha1_val]
        omega
      have hneqv : a1.val ≠ phase1.s.val := by
        intro hval
        exact ha1_ne_phase1s (Fin.ext hval)
      exact lt_of_le_of_ne ha1_le_phase1s hneqv
    have hphase1s_eq_phase0s : phase1.s = phase0.s := by
      apply Fin.ext
      by_contra hneq
      have hlt_or_gt : phase1.s.val < phase0.s.val ∨ phase0.s.val < phase1.s.val := by
        omega
      rcases hlt_or_gt with hs1_lt_s0 | hs0_lt_s1
      · exact phase0.ht_nofire phase1.s
          (by
            have hkout_le_phase1s : k_out.val ≤ phase1.s.val := by
              exact Nat.le_of_lt (lt_trans hkout_lt_a1 ha1_lt_phase1s)
            simpa [hphase0a] using hkout_le_phase1s)
          hs1_lt_s0 phase1.hs_mover
      · exact phase1.ht_nofire phase0.s
          (by
            have hj1_le_phase0s : j1.val ≤ phase0.s.val := by
              have hs_gt_kout : k_out.val < phase0.s.val := by
                simpa [hphase0a] using phase0.ha_lt_s
              exact Nat.le_of_lt (lt_trans hj1_lt_kout hs_gt_kout)
            simpa [hphase1a] using hj1_le_phase0s)
          hs0_lt_s1 phase0.hs_mover
    rcases hbranch with hleft | hright
    · rcases hleft with ⟨ha1_left2, hprev1_left, _hword⟩
      have hprevR_succ : prevR.val + 1 = phase0.s.val := by
        rw [hprevR_eq]
        omega
      have hprev1_eq_prevR : prev1 = prevR := by
        apply Fin.ext
        rw [hphase1s_eq_phase0s] at hprev1_succ
        omega
      exact False.elim (right_ne_left_of_n_eq_six hn6 t (by
        calc
          right t = gc.moverAt prevR := hprevR_right.symm
          _ = gc.moverAt prev1 := by rw [hprev1_eq_prevR]
          _ = left t := hprev1_left))
    · rcases hright with ⟨ha1_right2, hprev1_right, hword⟩
      exact ⟨phase1, a1, prev1, hphase1a, hphase1s_eq_phase0s,
        hkout_lt_a1, ha1_lt_phase1s, ha1_right2, hprev1_succ, hprev1_right, hword⟩

theorem left_same_prefix_shared_end_same_prev_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase1 : TernaryPhase gc t, ∃ a1 prevL : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      k_out.val < a1.val ∧
      a1.val < phase1.s.val ∧
      gc.moverAt a1 = left (left t) ∧
      prevL.val + 1 = phase1.s.val ∧
      gc.moverAt prevL = left t ∧
      (∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < prevL.val → gc.moverAt k = left (left t)) := by
  rcases left_continuation_len2_suffix_or_ec_n6 gc t hall hn6 phase0
      (by simpa [hphase0a] using hkout_left3)
      (by
        intro k hk1 hk2
        exact hphase_branch k (by simpa [hphase0a] using hk1) hk2)
      (by simpa [hphase0a] using hlong) with
    hec | ⟨aL, prevL, _hkout_lt_aL, _haL_eq, _haL_left2, hprevL_eq, hprevL_left⟩
  · exact False.elim (entryConflict_impossible gc hec)
  · rcases left_same_prefix_shared_end_tail_word_n6 gc t hall hn6 j1 k_out
      hj1_left3 hj1_lt_kout hkout_left3 hj_tail hno_t_to_kout
      phase0 hphase0a hlong hphase_branch with
      ⟨phase1, a1, prev1, hphase1a, hphase1s, hkout_lt_a1, ha1_lt_phase1s,
        ha1_left2, hprev1_succ, hprev1_left, hword⟩
    have hprevL_succ : prevL.val + 1 = phase0.s.val := by
      rw [hprevL_eq]
      omega
    have hprev1_eq_prevL : prev1 = prevL := by
      apply Fin.ext
      rw [hphase1s] at hprev1_succ
      omega
    exact ⟨phase1, a1, prevL, hphase1a, hphase1s, hkout_lt_a1, ha1_lt_phase1s, ha1_left2,
      by simpa [hprev1_eq_prevL] using hprev1_succ,
      by simpa [hprev1_eq_prevL] using hprev1_left,
      by
        intro k hk1 hk2
        exact hword k hk1 (by simpa [hprev1_eq_prevL] using hk2)⟩

theorem right_same_prefix_shared_end_same_prev_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase1 : TernaryPhase gc t, ∃ a1 prevR : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      k_out.val < a1.val ∧
      a1.val < phase1.s.val ∧
      gc.moverAt a1 = right (right t) ∧
      prevR.val + 1 = phase1.s.val ∧
      gc.moverAt prevR = right t ∧
      (∀ k : Fin gc.configs.length,
        a1.val ≤ k.val → k.val < prevR.val → gc.moverAt k = right (right t)) := by
  rcases right_continuation_len2_suffix_or_ec_n6 gc t hall hn6 phase0
      (by simpa [hphase0a] using hkout_right3)
      (by
        intro k hk1 hk2
        exact hphase_branch k (by simpa [hphase0a] using hk1) hk2)
      (by simpa [hphase0a] using hlong) with
    hec | ⟨aR, prevR, _hkout_lt_aR, _haR_eq, _haR_right2, hprevR_eq, hprevR_right⟩
  · exact False.elim (entryConflict_impossible gc hec)
  · rcases right_same_prefix_shared_end_tail_word_n6 gc t hall hn6 j1 k_out
      hj1_right3 hj1_lt_kout hkout_right3 hj_tail hno_t_to_kout
      phase0 hphase0a hlong hphase_branch with
      ⟨phase1, a1, prev1, hphase1a, hphase1s, hkout_lt_a1, ha1_lt_phase1s,
        ha1_right2, hprev1_succ, hprev1_right, hword⟩
    have hprevR_succ : prevR.val + 1 = phase0.s.val := by
      rw [hprevR_eq]
      omega
    have hprev1_eq_prevR : prev1 = prevR := by
      apply Fin.ext
      rw [hphase1s] at hprev1_succ
      omega
    exact ⟨phase1, a1, prevR, hphase1a, hphase1s, hkout_lt_a1, ha1_lt_phase1s, ha1_right2,
      by simpa [hprev1_eq_prevR] using hprev1_succ,
      by simpa [hprev1_eq_prevR] using hprev1_right,
      by
        intro k hk1 hk2
        exact hword k hk1 (by simpa [hprev1_eq_prevR] using hk2)⟩

theorem left_same_prefix_short_phase_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    {j1 : Fin gc.configs.length}
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (phase1 : TernaryPhase gc t)
    (hphase1a : phase1.a = j1)
    (hJ1 : gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 1)
    (hK0 : gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 0)
    (hnot_long : ¬ phase1.a.val + 2 < phase1.s.val) :
    False := by
  have hnorm1 : isNormalFormGap gc t phase1 := hall phase1
  by_cases hlen1 : phase1.s.val = phase1.a.val + 1
  · rcases normal_len1_phase_starts_at_neighbor gc t phase1 hnorm1 hlen1 with hL | hR
    · exact left3_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt phase1.a := by rw [hphase1a]
          _ = left t := hL)
    · exact left3_ne_right_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt phase1.a := by rw [hphase1a]
          _ = right t := hR)
  · have hlen2 : phase1.s.val = phase1.a.val + 2 := by
      have hsucc_le : phase1.a.val + 1 ≤ phase1.s.val := Nat.succ_le_of_lt phase1.ha_lt_s
      omega
    rcases one_sided_left_len2_start_ll_or_ec gc t phase1 hnorm1 hJ1 hK0 hlen2 with hec | hll
    · exact entryConflict_impossible gc hec
    · exact left3_ne_left2_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt phase1.a := by rw [hphase1a]
          _ = left (left t) := hll)

theorem right_same_prefix_short_phase_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    {j1 : Fin gc.configs.length}
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (phase1 : TernaryPhase gc t)
    (hphase1a : phase1.a = j1)
    (hJ0 : gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 0)
    (hK1 : gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 1)
    (hnot_long : ¬ phase1.a.val + 2 < phase1.s.val) :
    False := by
  have hnorm1 : isNormalFormGap gc t phase1 := hall phase1
  by_cases hlen1 : phase1.s.val = phase1.a.val + 1
  · rcases normal_len1_phase_starts_at_neighbor gc t phase1 hnorm1 hlen1 with hL | hR
    · have hj1_left3 : gc.moverAt j1 = left (left (left t)) := by
        simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t] using hj1_right3
      exact left3_ne_left_of_n_eq_six hn6 t (by
        calc
          left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
          _ = gc.moverAt phase1.a := by rw [hphase1a]
          _ = left t := hL)
    · exact right3_ne_right_of_n_eq_six hn6 t (by
        calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = gc.moverAt phase1.a := by rw [hphase1a]
          _ = right t := hR)
  · have hlen2 : phase1.s.val = phase1.a.val + 2 := by
      have hsucc_le : phase1.a.val + 1 ≤ phase1.s.val := Nat.succ_le_of_lt phase1.ha_lt_s
      omega
    rcases one_sided_right_len2_start_rr_or_ec gc t phase1 hnorm1 hJ0 hK1 hlen2 with hec | hrr
    · exact entryConflict_impossible gc hec
    · exact right2_ne_right_of_n_eq_six hn6 (right t) (by
        calc
          right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
          _ = gc.moverAt phase1.a := by rw [hphase1a]
          _ = right (right t) := hrr)

theorem left_opp_started_one_sided_exact_len3_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (phase : TernaryPhase gc t)
    (hstart_left3 : gc.moverAt phase.a = left (left (left t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ a1 prev : Fin gc.configs.length,
      nextIndex gc.configs phase.a = a1 ∧
      prev.val = a1.val + 1 ∧
      prev.val + 1 = phase.s.val ∧
      gc.moverAt a1 = left (left t) ∧
      gc.moverAt prev = left t := by
  have hJ1K0 := left_continuation_phase_counts_n6 gc t hall hn6 phase hstart_left3 hphase_branch
  have hlong : phase.a.val + 2 < phase.s.val := by
    by_contra hnot_long
    exact left_same_prefix_short_phase_false_n6 gc t hall hn6 hstart_left3 phase rfl
      hJ1K0.1 hJ1K0.2 hnot_long
  let a1 : Fin gc.configs.length := ⟨phase.a.val + 1, by
    have := phase.s.isLt
    omega⟩
  let a2 : Fin gc.configs.length := ⟨phase.a.val + 2, by
    have := phase.s.isLt
    omega⟩
  have hnext1 : nextIndex gc.configs phase.a = a1 := by
    apply Fin.ext
    simp [nextIndex, a1]
    exact Nat.mod_eq_of_lt a1.isLt
  have hnext2 : nextIndex gc.configs a1 = a2 := by
    apply Fin.ext
    simp [nextIndex, a1, a2]
    exact Nat.mod_eq_of_lt a2.isLt
  have ha1_gt_a : phase.a.val < a1.val := by
    dsimp [a1]
    omega
  have ha1_lt_s : a1.val < phase.s.val := by
    dsimp [a1]
    omega
  have ha2_gt_a : phase.a.val < a2.val := by
    dsimp [a2]
    omega
  have ha2_lt_s : a2.val < phase.s.val := by
    dsimp [a2]
    omega
  have ha1_left2 : gc.moverAt a1 = left (left t) := by
    rcases hphase_branch a1 ha1_gt_a ha1_lt_s with ha1_left2 | ha1_left
    · exact ha1_left2
    · have hlocal := gc.next_mover_is_local phase.a
      rw [hnext1, hstart_left3] at hlocal
      rcases hlocal with hleft | hself | hright
      · exfalso
        have ha1_right2 : gc.moverAt a1 = right (right t) := by
          simpa [left4_eq_right2_of_n_eq_six sys.rs hn6 t] using hleft
        exact right2_ne_left_of_n_eq_six hn6 t (ha1_right2.symm.trans ha1_left)
      · exfalso
        exact left3_ne_left_of_n_eq_six hn6 t (by
          calc
            left (left (left t)) = gc.moverAt a1 := by simpa using hself.symm
            _ = left t := ha1_left)
      · exfalso
        have ha1_left2' : gc.moverAt a1 = left (left t) := by
          simpa [right_left_eq_self] using hright
        exact left2_ne_left_of_n_eq_six hn6 t (ha1_left2'.symm.trans ha1_left)
  have ha2_left : gc.moverAt a2 = left t := by
    rcases hphase_branch a2 ha2_gt_a ha2_lt_s with ha2_left2 | ha2_left
    · have hiso := binary_left2_isolated_n6 gc t hn6 hbin_left2 a1 ha1_left2
      exact False.elim (hiso (by simpa [hnext2] using ha2_left2))
    · exact ha2_left
  let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  have hprev_succ : prev.val + 1 = phase.s.val := by
    dsimp [prev]
    omega
  have hprev_left : gc.moverAt prev = left t := by
    exact allNormal_phase_prev_left_of_right_count_zero gc t hall phase hJ1K0.2
  have ha2_eq_prev : a2 = prev := by
    by_cases hEq : a2 = prev
    · exact hEq
    have ha2_le_prev : a2.val ≤ prev.val := by
      dsimp [a2, prev]
      omega
    have hneqv : a2.val ≠ prev.val := by
      intro hval
      exact hEq (Fin.ext hval)
    have ha2_lt_prev : a2.val < prev.val := lt_of_le_of_ne ha2_le_prev hneqv
    have hsingle_a2 : gc.intervalFireCount (left t) a2.val (a2.val + 1) = 1 := by
      rw [intervalFireCount_single gc (left t) a2.isLt]
      simp [ha2_left]
    have hsingle_prev : gc.intervalFireCount (left t) prev.val (prev.val + 1) = 1 := by
      rw [intervalFireCount_single gc (left t) prev.isLt]
      simp [hprev_left]
    have hsingle_prev_tail : gc.intervalFireCount (left t) prev.val phase.s.val = 1 := by
      simpa [hprev_succ] using hsingle_prev
    have hsplit1 := intervalFireCount_split gc (left t)
      (a := phase.a.val) (c := a2.val) (b := phase.s.val)
      (by dsimp [a2]; omega) (Nat.le_of_lt (by dsimp [a2]; omega))
    have hsplit2 := intervalFireCount_split gc (left t)
      (a := a2.val) (c := a2.val + 1) (b := phase.s.val)
      (by omega) (by omega)
    have hsplit3 := intervalFireCount_split gc (left t)
      (a := a2.val + 1) (c := prev.val) (b := phase.s.val)
      (by omega) (Nat.le_of_lt (by dsimp [prev]; omega))
    have htwo : 2 ≤ gc.intervalFireCount (left t) phase.a.val phase.s.val := by
      rw [hsplit1, hsplit2, hsplit3, hsingle_a2, hsingle_prev_tail]
      omega
    omega
  have hprev_eq : prev.val = a1.val + 1 := by
    have hval : a2.val = prev.val := congrArg Fin.val ha2_eq_prev
    dsimp [a1, a2] at hval ⊢
    omega
  exact ⟨a1, prev, hnext1, hprev_eq, hprev_succ, ha1_left2, hprev_left⟩

theorem right_opp_started_one_sided_exact_len3_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (phase : TernaryPhase gc t)
    (hstart_right3 : gc.moverAt phase.a = right (right (right t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ a1 prev : Fin gc.configs.length,
      nextIndex gc.configs phase.a = a1 ∧
      prev.val = a1.val + 1 ∧
      prev.val + 1 = phase.s.val ∧
      gc.moverAt a1 = right (right t) ∧
      gc.moverAt prev = right t := by
  have hJ0K1 := right_continuation_phase_counts_n6 gc t hall hn6 phase hstart_right3 hphase_branch
  have hlong : phase.a.val + 2 < phase.s.val := by
    by_contra hnot_long
    exact right_same_prefix_short_phase_false_n6 gc t hall hn6 hstart_right3 phase rfl
      hJ0K1.1 hJ0K1.2 hnot_long
  let a1 : Fin gc.configs.length := ⟨phase.a.val + 1, by
    have := phase.s.isLt
    omega⟩
  let a2 : Fin gc.configs.length := ⟨phase.a.val + 2, by
    have := phase.s.isLt
    omega⟩
  have hnext1 : nextIndex gc.configs phase.a = a1 := by
    apply Fin.ext
    simp [nextIndex, a1]
    exact Nat.mod_eq_of_lt a1.isLt
  have hnext2 : nextIndex gc.configs a1 = a2 := by
    apply Fin.ext
    simp [nextIndex, a1, a2]
    exact Nat.mod_eq_of_lt a2.isLt
  have ha1_gt_a : phase.a.val < a1.val := by
    dsimp [a1]
    omega
  have ha1_lt_s : a1.val < phase.s.val := by
    dsimp [a1]
    omega
  have ha2_gt_a : phase.a.val < a2.val := by
    dsimp [a2]
    omega
  have ha2_lt_s : a2.val < phase.s.val := by
    dsimp [a2]
    omega
  have ha1_right2 : gc.moverAt a1 = right (right t) := by
    rcases hphase_branch a1 ha1_gt_a ha1_lt_s with ha1_right | ha1_right2
    · have hlocal := gc.next_mover_is_local phase.a
      rw [hnext1, hstart_right3] at hlocal
      rcases hlocal with hleft | hself | hright
      · exfalso
        have ha1_right2' : gc.moverAt a1 = right (right t) := by
          simpa using hleft
        exact right2_ne_right_of_n_eq_six hn6 t (ha1_right2'.symm.trans ha1_right)
      · exfalso
        exact right3_ne_right_of_n_eq_six hn6 t (by
          calc
            right (right (right t)) = gc.moverAt a1 := by simpa using hself.symm
            _ = right t := ha1_right)
      · exfalso
        have ha1_left2 : gc.moverAt a1 = left (left t) := by
          simpa [left3_eq_right3_of_n_eq_six sys.rs hn6 t,
            right4_eq_left2_of_n_eq_six sys.rs hn6 t] using hright
        exact left2_ne_right_of_n_eq_six hn6 t (ha1_left2.symm.trans ha1_right)
    · exact ha1_right2
  have ha2_right : gc.moverAt a2 = right t := by
    rcases hphase_branch a2 ha2_gt_a ha2_lt_s with ha2_right | ha2_right2
    · exact ha2_right
    · have hiso := binary_right2_isolated_n6 gc t hn6 hbin_right2 a1 ha1_right2
      exact False.elim (hiso (by simpa [hnext2] using ha2_right2))
  let prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
    have := phase.ha_lt_s
    have := phase.s.isLt
    omega⟩
  have hprev_succ : prev.val + 1 = phase.s.val := by
    dsimp [prev]
    omega
  have hprev_right : gc.moverAt prev = right t := by
    exact allNormal_phase_prev_right_of_left_count_zero gc t hall phase hJ0K1.1
  have ha2_eq_prev : a2 = prev := by
    by_cases hEq : a2 = prev
    · exact hEq
    have ha2_le_prev : a2.val ≤ prev.val := by
      dsimp [a2, prev]
      omega
    have hneqv : a2.val ≠ prev.val := by
      intro hval
      exact hEq (Fin.ext hval)
    have ha2_lt_prev : a2.val < prev.val := lt_of_le_of_ne ha2_le_prev hneqv
    have hsingle_a2 : gc.intervalFireCount (right t) a2.val (a2.val + 1) = 1 := by
      rw [intervalFireCount_single gc (right t) a2.isLt]
      simp [ha2_right]
    have hsingle_prev : gc.intervalFireCount (right t) prev.val (prev.val + 1) = 1 := by
      rw [intervalFireCount_single gc (right t) prev.isLt]
      simp [hprev_right]
    have hsingle_prev_tail : gc.intervalFireCount (right t) prev.val phase.s.val = 1 := by
      simpa [hprev_succ] using hsingle_prev
    have hsplit1 := intervalFireCount_split gc (right t)
      (a := phase.a.val) (c := a2.val) (b := phase.s.val)
      (by dsimp [a2]; omega) (Nat.le_of_lt (by dsimp [a2]; omega))
    have hsplit2 := intervalFireCount_split gc (right t)
      (a := a2.val) (c := a2.val + 1) (b := phase.s.val)
      (by omega) (by omega)
    have hsplit3 := intervalFireCount_split gc (right t)
      (a := a2.val + 1) (c := prev.val) (b := phase.s.val)
      (by omega) (Nat.le_of_lt (by dsimp [prev]; omega))
    have htwo : 2 ≤ gc.intervalFireCount (right t) phase.a.val phase.s.val := by
      rw [hsplit1, hsplit2, hsplit3, hsingle_a2, hsingle_prev_tail]
      omega
    omega
  have hprev_eq : prev.val = a1.val + 1 := by
    have hval : a2.val = prev.val := congrArg Fin.val ha2_eq_prev
    dsimp [a1, a2] at hval ⊢
    omega
  exact ⟨a1, prev, hnext1, hprev_eq, hprev_succ, ha1_right2, hprev_right⟩

theorem left_opp_started_one_sided_len3_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (phase : TernaryPhase gc t)
    (hstart_left3 : gc.moverAt phase.a = left (left (left t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    phase.s.val = phase.a.val + 3 := by
  rcases left_opp_started_one_sided_exact_len3_n6
      gc t hall hn6 hbin_left2 phase hstart_left3 hphase_branch with
    ⟨a1, prev, hnext1, hprev_eq, hprev_succ, _ha1_left2, _hprev_left⟩
  have ha1_eq : a1.val = phase.a.val + 1 := by
    have hEq := congrArg Fin.val hnext1
    have ha1_lt_len : phase.a.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt phase.ha_lt_s) phase.s.isLt
    simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
    exact hEq.symm
  omega

theorem right_opp_started_one_sided_len3_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (phase : TernaryPhase gc t)
    (hstart_right3 : gc.moverAt phase.a = right (right (right t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    phase.s.val = phase.a.val + 3 := by
  rcases right_opp_started_one_sided_exact_len3_n6
      gc t hall hn6 hbin_right2 phase hstart_right3 hphase_branch with
    ⟨a1, prev, hnext1, hprev_eq, hprev_succ, _ha1_right2, _hprev_right⟩
  have ha1_eq : a1.val = phase.a.val + 1 := by
    have hEq := congrArg Fin.val hnext1
    have ha1_lt_len : phase.a.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt phase.ha_lt_s) phase.s.isLt
    simp [nextIndex, Nat.mod_eq_of_lt ha1_lt_len] at hEq
    exact hEq.symm
  omega

theorem left_opp_started_one_sided_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (phase : TernaryPhase gc t)
    (hstart_left3 : gc.moverAt phase.a = left (left (left t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ a1 a2 : Fin gc.configs.length,
      nextIndex gc.configs phase.a = a1 ∧
      nextIndex gc.configs a1 = a2 ∧
      a2.val + 1 = phase.s.val ∧
      gc.moverAt a1 = left (left t) ∧
      gc.moverAt a2 = left t := by
  rcases left_opp_started_one_sided_exact_len3_n6
      gc t hall hn6 hbin_left2 phase hstart_left3 hphase_branch with
    ⟨a1, a2, hnext1, ha2_eq, ha2_succ, ha1_left2, ha2_left⟩
  have ha2_succ_lt_len : a1.val + 1 < gc.configs.length := by
    rw [← ha2_eq]
    exact a2.isLt
  have hnext2 : nextIndex gc.configs a1 = a2 := by
    apply Fin.ext
    simp [nextIndex, Nat.mod_eq_of_lt ha2_succ_lt_len, ha2_eq]
  exact ⟨a1, a2, hnext1, hnext2, ha2_succ, ha1_left2, ha2_left⟩

theorem right_opp_started_one_sided_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (phase : TernaryPhase gc t)
    (hstart_right3 : gc.moverAt phase.a = right (right (right t)))
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        phase.a.val < k.val → k.val < phase.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ a1 a2 : Fin gc.configs.length,
      nextIndex gc.configs phase.a = a1 ∧
      nextIndex gc.configs a1 = a2 ∧
      a2.val + 1 = phase.s.val ∧
      gc.moverAt a1 = right (right t) ∧
      gc.moverAt a2 = right t := by
  rcases right_opp_started_one_sided_exact_len3_n6
      gc t hall hn6 hbin_right2 phase hstart_right3 hphase_branch with
    ⟨a1, a2, hnext1, ha2_eq, ha2_succ, ha1_right2, ha2_right⟩
  have ha2_succ_lt_len : a1.val + 1 < gc.configs.length := by
    rw [← ha2_eq]
    exact a2.isLt
  have hnext2 : nextIndex gc.configs a1 = a2 := by
    apply Fin.ext
    simp [nextIndex, Nat.mod_eq_of_lt ha2_succ_lt_len, ha2_eq]
  exact ⟨a1, a2, hnext1, hnext2, ha2_succ, ha1_right2, ha2_right⟩

theorem left_same_prefix_shared_end_exact_suffix_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase1 : TernaryPhase gc t, ∃ a1 prevL : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      a1.val = k_out.val + 1 ∧
      prevL.val = k_out.val + 2 ∧
      prevL.val + 1 = phase1.s.val ∧
      gc.moverAt a1 = left (left t) ∧
      gc.moverAt prevL = left t := by
  rcases left_same_prefix_shared_end_same_prev_n6
      gc t hall hn6 j1 k_out hj1_left3 hj1_lt_kout hkout_left3 hj_tail
      hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, a1, prevL, hphase1a, hphase1s, hkout_lt_a1, ha1_lt_phase1s,
      ha1_left2, hprevL_succ, hprevL_left, hword⟩
  rcases left_opp_started_one_sided_word_n6
      gc t hall hn6 hbin_left2 phase0
      (by simpa [hphase0a] using hkout_left3)
      (by
        intro k hk1 hk2
        exact hphase_branch k (by simpa [hphase0a] using hk1) hk2) with
    ⟨b1, b2, hb1, hb2, hb2_succ, hb1_left2, hb2_left⟩
  have hb1_val : b1.val = k_out.val + 1 := by
    have hEq := congrArg Fin.val hb1
    have hkout_succ_lt_len : k_out.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt (by simpa [hphase0a] using phase0.ha_lt_s)) phase0.s.isLt
    simp [hphase0a, nextIndex, Nat.mod_eq_of_lt hkout_succ_lt_len] at hEq
    exact hEq.symm
  have hs_eq : phase0.s.val = k_out.val + 3 := by
    rw [← hb2_succ]
    have hb2_val : b2.val = b1.val + 1 := by
      have hEq := congrArg Fin.val hb2
      have hb1_succ_lt_len : b1.val + 1 < gc.configs.length := by
        rw [hb1_val]
        exact lt_of_le_of_lt (show k_out.val + 2 ≤ phase0.s.val by omega) phase0.s.isLt
      simp [nextIndex, Nat.mod_eq_of_lt hb1_succ_lt_len] at hEq
      exact hEq.symm
    omega
  have hprevL_val : prevL.val = k_out.val + 2 := by
    rw [hphase1s] at hprevL_succ
    rw [hs_eq] at hprevL_succ
    omega
  have ha1_ne_prevL : a1 ≠ prevL := by
    intro hEq
    exact left2_ne_left_of_n_eq_six hn6 t (by
      calc
        left (left t) = gc.moverAt a1 := ha1_left2.symm
        _ = gc.moverAt prevL := by rw [hEq]
        _ = left t := hprevL_left)
  have ha1_val : a1.val = k_out.val + 1 := by
    have ha1_lt_prevsucc : a1.val < prevL.val + 1 := by
      rw [hprevL_succ]
      exact ha1_lt_phase1s
    omega
  exact ⟨phase1, a1, prevL, hphase1a, hphase1s, ha1_val, hprevL_val, hprevL_succ, ha1_left2, hprevL_left⟩

theorem right_same_prefix_shared_end_exact_suffix_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase1 : TernaryPhase gc t, ∃ a1 prevR : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      a1.val = k_out.val + 1 ∧
      prevR.val = k_out.val + 2 ∧
      prevR.val + 1 = phase1.s.val ∧
      gc.moverAt a1 = right (right t) ∧
      gc.moverAt prevR = right t := by
  rcases right_same_prefix_shared_end_same_prev_n6
      gc t hall hn6 j1 k_out hj1_right3 hj1_lt_kout hkout_right3 hj_tail
      hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, a1, prevR, hphase1a, hphase1s, hkout_lt_a1, ha1_lt_phase1s,
      ha1_right2, hprevR_succ, hprevR_right, hword⟩
  rcases right_opp_started_one_sided_word_n6
      gc t hall hn6 hbin_right2 phase0
      (by simpa [hphase0a] using hkout_right3)
      (by
        intro k hk1 hk2
        exact hphase_branch k (by simpa [hphase0a] using hk1) hk2) with
    ⟨b1, b2, hb1, hb2, hb2_succ, hb1_right2, hb2_right⟩
  have hb1_val : b1.val = k_out.val + 1 := by
    have hEq := congrArg Fin.val hb1
    have hkout_succ_lt_len : k_out.val + 1 < gc.configs.length := by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt (by simpa [hphase0a] using phase0.ha_lt_s)) phase0.s.isLt
    simp [hphase0a, nextIndex, Nat.mod_eq_of_lt hkout_succ_lt_len] at hEq
    exact hEq.symm
  have hs_eq : phase0.s.val = k_out.val + 3 := by
    rw [← hb2_succ]
    have hb2_val : b2.val = b1.val + 1 := by
      have hEq := congrArg Fin.val hb2
      have hb1_succ_lt_len : b1.val + 1 < gc.configs.length := by
        rw [hb1_val]
        exact lt_of_le_of_lt (show k_out.val + 2 ≤ phase0.s.val by omega) phase0.s.isLt
      simp [nextIndex, Nat.mod_eq_of_lt hb1_succ_lt_len] at hEq
      exact hEq.symm
    omega
  have hprevR_val : prevR.val = k_out.val + 2 := by
    rw [hphase1s] at hprevR_succ
    rw [hs_eq] at hprevR_succ
    omega
  have ha1_ne_prevR : a1 ≠ prevR := by
    intro hEq
    exact right2_ne_right_of_n_eq_six hn6 t (by
      calc
        right (right t) = gc.moverAt a1 := ha1_right2.symm
        _ = gc.moverAt prevR := by rw [hEq]
        _ = right t := hprevR_right)
  have ha1_val : a1.val = k_out.val + 1 := by
    have ha1_lt_prevsucc : a1.val < prevR.val + 1 := by
      rw [hprevR_succ]
      exact ha1_lt_phase1s
    omega
  exact ⟨phase1, a1, prevR, hphase1a, hphase1s, ha1_val, hprevR_val, hprevR_succ, ha1_right2, hprevR_right⟩

theorem left_same_prefix_shared_end_length3_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase1 : TernaryPhase gc t,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      phase1.s.val = k_out.val + 3 := by
  rcases left_same_prefix_shared_end_exact_suffix_n6
      gc t hall hn6 hbin_left2 j1 k_out hj1_left3 hj1_lt_kout hkout_left3
      hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, a1, prevL, hphase1a, hphase1s, hprevL_val, hprevL_succ, _hkout_lt_a1,
      _ha1_left2, _hprevL_left⟩
  have hs_val : phase1.s.val = k_out.val + 3 := by
    omega
  exact ⟨phase1, hphase1a, hphase1s, hs_val⟩

theorem right_same_prefix_shared_end_length3_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase1 : TernaryPhase gc t,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      phase1.s.val = k_out.val + 3 := by
  rcases right_same_prefix_shared_end_exact_suffix_n6
      gc t hall hn6 hbin_right2 j1 k_out hj1_right3 hj1_lt_kout hkout_right3
      hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, a1, prevR, hphase1a, hphase1s, hprevR_val, hprevR_succ, _hkout_lt_a1,
      _ha1_right2, _hprevR_right⟩
  have hs_val : phase1.s.val = k_out.val + 3 := by
    omega
  exact ⟨phase1, hphase1a, hphase1s, hs_val⟩

theorem left_same_prefix_shared_end_terminal_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase1 : TernaryPhase gc t, ∃ k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      k2.val + 1 = phase1.s.val ∧
      gc.moverAt k1 = left (left t) ∧
      gc.moverAt k2 = left t := by
  rcases left_same_prefix_shared_end_exact_suffix_n6
      gc t hall hn6 hbin_left2 j1 k_out hj1_left3 hj1_lt_kout hkout_left3
      hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, a1, prevL, hphase1a, hphase1s, ha1_val, hprevL_val, hprevL_succ,
      ha1_left2, hprevL_left⟩
  have hkout_succ_lt_len : k_out.val + 1 < gc.configs.length := by
    exact lt_of_eq_of_lt ha1_val.symm a1.isLt
  have hnext01 : nextIndex gc.configs k_out = a1 := by
    apply Fin.ext
    simp [nextIndex, Nat.mod_eq_of_lt hkout_succ_lt_len, ha1_val]
  have ha1_succ_lt_len : a1.val + 1 < gc.configs.length := by
    have : a1.val + 1 = prevL.val := by omega
    exact lt_of_eq_of_lt this prevL.isLt
  have hnext12 : nextIndex gc.configs a1 = prevL := by
    have hprevL_eq_a1succ : prevL.val = a1.val + 1 := by
      omega
    apply Fin.ext
    simp [nextIndex, Nat.mod_eq_of_lt ha1_succ_lt_len, hprevL_eq_a1succ]
  exact ⟨phase1, a1, prevL, hphase1a, hphase1s, hnext01, hnext12, hprevL_succ, ha1_left2, hprevL_left⟩

theorem right_same_prefix_shared_end_terminal_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase1 : TernaryPhase gc t, ∃ k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      k2.val + 1 = phase1.s.val ∧
      gc.moverAt k1 = right (right t) ∧
      gc.moverAt k2 = right t := by
  rcases right_same_prefix_shared_end_exact_suffix_n6
      gc t hall hn6 hbin_right2 j1 k_out hj1_right3 hj1_lt_kout hkout_right3
      hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, a1, prevR, hphase1a, hphase1s, ha1_val, hprevR_val, hprevR_succ,
      ha1_right2, hprevR_right⟩
  have hkout_succ_lt_len : k_out.val + 1 < gc.configs.length := by
    exact lt_of_eq_of_lt ha1_val.symm a1.isLt
  have hnext01 : nextIndex gc.configs k_out = a1 := by
    apply Fin.ext
    simp [nextIndex, Nat.mod_eq_of_lt hkout_succ_lt_len, ha1_val]
  have ha1_succ_lt_len : a1.val + 1 < gc.configs.length := by
    have : a1.val + 1 = prevR.val := by omega
    exact lt_of_eq_of_lt this prevR.isLt
  have hnext12 : nextIndex gc.configs a1 = prevR := by
    have hprevR_eq_a1succ : prevR.val = a1.val + 1 := by
      omega
    apply Fin.ext
    simp [nextIndex, Nat.mod_eq_of_lt ha1_succ_lt_len, hprevR_eq_a1succ]
  exact ⟨phase1, a1, prevR, hphase1a, hphase1s, hnext01, hnext12, hprevR_succ, ha1_right2, hprevR_right⟩

theorem left_first_later_shared_end_five_step_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (hbin_left3 : isBinary sys.rs (left (left (left t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      (gc.moverAt prev0 = left (left t) ∨ gc.moverAt prev0 = right (right t)) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = left (left t) ∧
      gc.moverAt k2 = left t ∧
      k2.val + 1 = phase1.s.val := by
  rcases first_later_left3_predecessor_only_second_neighbor_n6
      gc t hn6 hbin_left3 j1 k_out hj1_lt_kout hj1_left3 hkout_left3 hfirst with
    ⟨prev0, hprev0_succ, hprev0_side⟩
  rcases left_same_prefix_shared_end_terminal_word_n6
      gc t hall hn6 hbin_left2 j1 k_out hj1_left3 hj1_lt_kout hkout_left3
      hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, k1, k2, hphase1a, hphase1s, hnext01, hnext12, hk2_succ, hk1_left2, hk2_left⟩
  exact ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_side,
    hnext01, hnext12, hk1_left2, hk2_left, hk2_succ⟩

theorem right_first_later_shared_end_five_step_word_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (hbin_right3 : isBinary sys.rs (right (right (right t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      (gc.moverAt prev0 = left (left t) ∨ gc.moverAt prev0 = right (right t)) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = right (right t) ∧
      gc.moverAt k2 = right t ∧
      k2.val + 1 = phase1.s.val := by
  rcases first_later_right3_predecessor_only_second_neighbor_n6
      gc t hn6 hbin_right3 j1 k_out hj1_lt_kout hj1_right3 hkout_right3 hfirst with
    ⟨prev0, hprev0_succ, hprev0_side⟩
  rcases right_same_prefix_shared_end_terminal_word_n6
      gc t hall hn6 hbin_right2 j1 k_out hj1_right3 hj1_lt_kout hkout_right3
      hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, k1, k2, hphase1a, hphase1s, hnext01, hnext12, hk2_succ, hk1_right2, hk2_right⟩
  exact ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_side,
    hnext01, hnext12, hk1_right2, hk2_right, hk2_succ⟩

theorem left_first_later_shared_end_same_or_cross_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (hbin_left3 : isBinary sys.rs (left (left (left t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    (∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      gc.moverAt prev0 = left (left t) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = left (left t) ∧
      gc.moverAt k2 = left t ∧
      k2.val + 1 = phase1.s.val) ∨
    (∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      gc.moverAt prev0 = right (right t) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = left (left t) ∧
      gc.moverAt k2 = left t ∧
      k2.val + 1 = phase1.s.val) := by
  rcases left_first_later_shared_end_five_step_word_n6
      gc t hall hn6 hbin_left2 hbin_left3 j1 k_out hj1_left3 hj1_lt_kout
      hkout_left3 hfirst hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_side,
      hnext01, hnext12, hk1_left2, hk2_left, hk2_succ⟩
  rcases hprev0_side with hprev0_left2 | hprev0_right2
  · exact Or.inl ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_left2,
      hnext01, hnext12, hk1_left2, hk2_left, hk2_succ⟩
  · exact Or.inr ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_right2,
      hnext01, hnext12, hk1_left2, hk2_left, hk2_succ⟩

theorem right_first_later_shared_end_same_or_cross_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (hbin_right3 : isBinary sys.rs (right (right (right t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    (∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      gc.moverAt prev0 = left (left t) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = right (right t) ∧
      gc.moverAt k2 = right t ∧
      k2.val + 1 = phase1.s.val) ∨
    (∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      gc.moverAt prev0 = right (right t) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = right (right t) ∧
      gc.moverAt k2 = right t ∧
      k2.val + 1 = phase1.s.val) := by
  rcases right_first_later_shared_end_five_step_word_n6
      gc t hall hn6 hbin_right2 hbin_right3 j1 k_out hj1_right3 hj1_lt_kout
      hkout_right3 hfirst hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with
    ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_side,
      hnext01, hnext12, hk1_right2, hk2_right, hk2_succ⟩
  rcases hprev0_side with hprev0_left2 | hprev0_right2
  · exact Or.inl ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_left2,
      hnext01, hnext12, hk1_right2, hk2_right, hk2_succ⟩
  · exact Or.inr ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ, hprev0_right2,
      hnext01, hnext12, hk1_right2, hk2_right, hk2_succ⟩

/-
/-
/-
theorem left_same_side_five_step_word_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (prev0 k_out k1 k2 : Fin gc.configs.length)
    (hprev0_left2 : gc.moverAt prev0 = left (left t))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hk1_left2 : gc.moverAt k1 = left (left t))
    (hk2_left1 : gc.moverAt k2 = left t)
    (hprev0_succ : prev0.val + 1 = k_out.val)
    (hnext01 : nextIndex gc.configs k_out = k1)
    (hnext12 : nextIndex gc.configs k1 = k2) :
    False := by
  have hkout_val : k_out.val = prev0.val + 1 := hprev0_succ.symm
  have hk1_val : k1.val = k_out.val + 1 := by
    have hEq := congrArg Fin.val hnext01
    have hk1_lt_len : k_out.val + 1 < gc.configs.length := by
      exact lt_of_eq_of_lt hkout_val.symm k_out.isLt
    simp [nextIndex, Nat.mod_eq_of_lt hk1_lt_len] at hEq
    exact hEq.symm
  have hk2_val : k2.val = k1.val + 1 := by
    have hEq := congrArg Fin.val hnext12
    have hk2_lt_len : k1.val + 1 < gc.configs.length := by
      exact lt_of_eq_of_lt hk1_val.symm k1.isLt
    simp [nextIndex, Nat.mod_eq_of_lt hk2_lt_len] at hEq
    exact hEq.symm
  have hL1_prev_kout : (gc.configs.get prev0) (left t) = (gc.configs.get k_out) (left t) := by
    symm
    exact gc.state_eq_of_ne_moverAt prev0 (left t) (by
      intro hEq
      exact left2_ne_left_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_left2.symm))
  have hL1_kout_k1 : (gc.configs.get k_out) (left t) = (gc.configs.get k1) (left t) := by
    symm
    exact gc.state_eq_of_ne_moverAt k_out (left t) (by
      intro hEq
      exact left3_ne_left_of_n_eq_six hn6 t (by simpa [hEq] using hkout_left3.symm))
  have hL1_k1_k2 : (gc.configs.get k1) (left t) = (gc.configs.get k2) (left t) := by
    symm
    exact gc.state_eq_of_ne_moverAt k1 (left t) (by
      intro hEq
      exact left2_ne_left_of_n_eq_six hn6 t (by simpa [hEq] using hk1_left2.symm))
  have hL1_eq : (gc.configs.get k2) (left t) = (gc.configs.get prev0) (left t) := by
    exact Eq.trans hL1_k1_k2.symm (Eq.trans hL1_kout_k1.symm hL1_prev_kout.symm)
  have hT_prev_kout : (gc.configs.get prev0) t = (gc.configs.get k_out) t := by
    symm
    exact gc.state_eq_of_ne_moverAt prev0 t (by
      intro hEq
      have : left (left t) = t := by simpa [hEq] using hprev0_left2
      exact left2_ne_self_of_n_eq_six hn6 t this)
  have hT_kout_k1 : (gc.configs.get k_out) t = (gc.configs.get k1) t := by
    symm
    exact gc.state_eq_of_ne_moverAt k_out t (by
      intro hEq
      have : left (left (left t)) = t := by simpa [hEq] using hkout_left3
      exact left3_ne_self_of_n_eq_six hn6 t this)
  have hT_k1_k2 : (gc.configs.get k1) t = (gc.configs.get k2) t := by
    symm
    exact gc.state_eq_of_ne_moverAt k1 t (by
      intro hEq
      have : left (left t) = t := by simpa [hEq] using hk1_left2
      exact left2_ne_self_of_n_eq_six hn6 t this)
  have hT_eq : (gc.configs.get k2) t = (gc.configs.get prev0) t := by
    exact Eq.trans hT_k1_k2.symm (Eq.trans hT_kout_k1.symm hT_prev_kout.symm)
  have hleft2_ifc_prev_kout : gc.intervalFireCount (left (left t)) prev0.val k_out.val = 1 := by
    rw [hkout_val, intervalFireCount_single gc (left (left t)) prev0.isLt]
    simp [hprev0_left2]
  have hleft2_ifc_kout_k1 : gc.intervalFireCount (left (left t)) k_out.val k1.val = 0 := by
    rw [hk1_val, intervalFireCount_single gc (left (left t)) k_out.isLt]
    simp [hkout_left3, left3_ne_left2_of_n_eq_six hn6 t]
  have hleft2_ifc_k1_k2 : gc.intervalFireCount (left (left t)) k1.val k2.val = 1 := by
    rw [hk2_val, intervalFireCount_single gc (left (left t)) k1.isLt]
    simp [hk1_left2]
  have hsplit1 := intervalFireCount_split gc (left (left t))
    (a := prev0.val) (c := k_out.val) (b := k2.val)
    (Nat.le_of_eq hprev0_succ) (by
      rw [hk2_val]
      omega)
  have hsplit2 := intervalFireCount_split gc (left (left t))
    (a := k_out.val) (c := k1.val) (b := k2.val)
    (Nat.le_of_eq hk1_val) (by
      rw [hk2_val]
      omega)
  have hleft2_ifc_even : Even (gc.intervalFireCount (left (left t)) prev0.val k2.val) := by
    rw [hsplit1, hsplit2, hleft2_ifc_prev_kout, hleft2_ifc_kout_k1, hleft2_ifc_k1_k2]
    decide
  have hleft2_eq : (gc.configs.get k2) (left (left t)) = (gc.configs.get prev0) (left (left t)) := by
    symm
    exact binary_config_eq_of_even_intervalFireCount gc (left (left t)) hbin_left2
      prev0.val k2.val (by omega) k2.isLt hleft2_ifc_even
  have hnonmover_prev0 : gc.moverAt prev0 ≠ left t := by
    intro hEq
    exact left2_ne_left_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_left2)
  have hec : hasEntryConflict gc := by
    refine ⟨k2, prev0, left t, hk2_left1, hnonmover_prev0, ?_, ?_, ?_⟩
    · simpa using hleft2_eq
    · simpa using hL1_eq
    · simpa using hT_eq
  exact entryConflict_impossible gc hec

theorem right_same_side_five_step_word_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (prev0 k_out k1 k2 : Fin gc.configs.length)
    (hprev0_right2 : gc.moverAt prev0 = right (right t))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hk1_right2 : gc.moverAt k1 = right (right t))
    (hk2_right1 : gc.moverAt k2 = right t)
    (hprev0_succ : prev0.val + 1 = k_out.val)
    (hk1_val : k1.val = k_out.val + 1)
    (hk2_val : k2.val = k_out.val + 2) :
    False := by
  have hnext_prev0 : nextIndex gc.configs prev0 = k_out := by
    apply Fin.ext
    simp [nextIndex, hprev0_succ, Nat.mod_eq_of_lt k_out.isLt]
  have hnext01 : nextIndex gc.configs k_out = k1 := by
    apply Fin.ext
    have hk1_lt_len : k_out.val + 1 < gc.configs.length := by
      exact lt_of_eq_of_lt hk1_val.symm k1.isLt
    simp [nextIndex, Nat.mod_eq_of_lt hk1_lt_len, hk1_val]
  have hnext12 : nextIndex gc.configs k1 = k2 := by
    apply Fin.ext
    have hk2_eq : k2.val = k1.val + 1 := by omega
    have hk2_lt_len : k1.val + 1 < gc.configs.length := by
      exact lt_of_eq_of_lt hk2_eq.symm k2.isLt
    simp [nextIndex, Nat.mod_eq_of_lt hk2_lt_len, hk2_eq]

  have hR1_prev_kout : (gc.configs.get prev0) (right t) = (gc.configs.get k_out) (right t) := by
    have h := gc.state_eq_of_ne_moverAt prev0 (right t) (by
      intro hEq
      exact right2_ne_right_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_right2.symm))
    rw [hnext_prev0] at h
    exact h.symm
  have hR1_kout_k1 : (gc.configs.get k_out) (right t) = (gc.configs.get k1) (right t) := by
    have h := gc.state_eq_of_ne_moverAt k_out (right t) (by
      intro hEq
      exact right3_ne_right_of_n_eq_six hn6 t (by simpa [hEq] using hkout_right3.symm))
    rw [hnext01] at h
    exact h.symm
  have hR1_k1_k2 : (gc.configs.get k1) (right t) = (gc.configs.get k2) (right t) := by
    have h := gc.state_eq_of_ne_moverAt k1 (right t) (by
      intro hEq
      exact right2_ne_right_of_n_eq_six hn6 t (by simpa [hEq] using hk1_right2.symm))
    rw [hnext12] at h
    exact h.symm
  have hR1_eq : (gc.configs.get k2) (right t) = (gc.configs.get prev0) (right t) := by
    exact Eq.trans hR1_k1_k2.symm (Eq.trans hR1_kout_k1.symm hR1_prev_kout.symm)

  have hT_prev_kout : (gc.configs.get prev0) t = (gc.configs.get k_out) t := by
    have h := gc.state_eq_of_ne_moverAt prev0 t (by
      intro hEq
      exact right2_ne_self_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_right2.symm))
    rw [hnext_prev0] at h
    exact h.symm
  have hT_kout_k1 : (gc.configs.get k_out) t = (gc.configs.get k1) t := by
    have h := gc.state_eq_of_ne_moverAt k_out t (by
      intro hEq
      exact right3_ne_self_of_n_eq_six hn6 t (by simpa [hEq] using hkout_right3.symm))
    rw [hnext01] at h
    exact h.symm
  have hT_k1_k2 : (gc.configs.get k1) t = (gc.configs.get k2) t := by
    have h := gc.state_eq_of_ne_moverAt k1 t (by
      intro hEq
      exact right2_ne_self_of_n_eq_six hn6 t (by simpa [hEq] using hk1_right2.symm))
    rw [hnext12] at h
    exact h.symm
  have hT_eq : (gc.configs.get k2) t = (gc.configs.get prev0) t := by
    exact Eq.trans hT_k1_k2.symm (Eq.trans hT_kout_k1.symm hT_prev_kout.symm)

  have hright2_ifc_prev_kout : gc.intervalFireCount (right (right t)) prev0.val k_out.val = 1 := by
    have hone := intervalFireCount_single gc (right (right t)) prev0.isLt
    simpa [hprev0_succ, hprev0_right2] using hone
  have hright2_ifc_kout_k1 : gc.intervalFireCount (right (right t)) k_out.val k1.val = 0 := by
    have hzero := intervalFireCount_single gc (right (right t)) k_out.isLt
    simpa [hk1_val, hkout_right3, right3_ne_right2_of_n_eq_six hn6 t] using hzero
  have hright2_ifc_k1_k2 : gc.intervalFireCount (right (right t)) k1.val k2.val = 1 := by
    have hk2_eq : k2.val = k1.val + 1 := by omega
    rw [hk2_eq]
    rw [intervalFireCount_single gc (right (right t)) k1.isLt]
    simp [hk1_right2]
  have hsplit1 := intervalFireCount_split gc (right (right t))
    (a := prev0.val) (c := k_out.val) (b := k2.val)
    (by omega) (by omega)
  have hsplit2 := intervalFireCount_split gc (right (right t))
    (a := k_out.val) (c := k1.val) (b := k2.val)
    (by omega) (by omega)
  have hright2_ifc_even : Even (gc.intervalFireCount (right (right t)) prev0.val k2.val) := by
    rw [hsplit1, hsplit2, hright2_ifc_prev_kout, hright2_ifc_kout_k1, hright2_ifc_k1_k2]
    decide
  have hright2_eq : (gc.configs.get k2) (right (right t)) = (gc.configs.get prev0) (right (right t)) := by
    symm
    exact binary_config_eq_of_even_intervalFireCount gc (right (right t)) hbin_right2
      prev0.val k2.val (by omega) k2.isLt hright2_ifc_even

  have hnonmover_prev0 : gc.moverAt prev0 ≠ right t := by
    intro hEq
    exact right2_ne_right_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_right2.symm)
  have hec : hasEntryConflict gc := by
    refine ⟨k2, prev0, right t, hk2_right1, hnonmover_prev0, ?_, ?_, ?_⟩
    · have hTeq' : (gc.configs.get k2) (left (right t)) = (gc.configs.get prev0) (left (right t)) := by
        convert hT_eq using 1 <;> rw [left_right_eq_self]
      exact hTeq'
    · simpa using hR1_eq
    · simpa using hright2_eq
  exact entryConflict_impossible gc hec

theorem left_first_later_shared_end_cross_only_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (hbin_left3 : isBinary sys.rs (left (left (left t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_left3 : gc.moverAt j1 = left (left (left t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ left (left (left t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
    ∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      gc.moverAt prev0 = right (right t) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = left (left t) ∧
      gc.moverAt k2 = left t ∧
      k2.val + 1 = phase1.s.val := by
  rcases left_first_later_shared_end_same_or_cross_n6
      gc t hall hn6 hbin_left2 hbin_left3 j1 k_out hj1_left3 hj1_lt_kout
      hkout_left3 hfirst hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with hsame | hcross
  · rcases hsame with ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ,
      hprev0_left2, hnext01, hnext12, hk1_left2, hk2_left1, hk2_succ⟩
    have hk1_val : k1.val = k_out.val + 1 := by
      have hEq := congrArg Fin.val hnext01
      have hk1_lt_len : k_out.val + 1 < gc.configs.length := by
        exact lt_of_le_of_lt (Nat.succ_le_of_lt (by simpa [hphase0a] using phase0.ha_lt_s)) phase0.s.isLt
      simp [nextIndex, Nat.mod_eq_of_lt hk1_lt_len] at hEq
      exact hEq.symm
    have hk2_val : k2.val = k_out.val + 2 := by
      have hEq := congrArg Fin.val hnext12
      have hk2_lt_len : k1.val + 1 < gc.configs.length := by
        rw [hk1_val]
        exact lt_of_le_of_lt (show k_out.val + 2 ≤ phase0.s.val by omega) phase0.s.isLt
      simp [nextIndex, Nat.mod_eq_of_lt hk2_lt_len] at hEq
      rw [hk1_val] at hEq
      omega
    exact False.elim <| left_same_side_five_step_word_false_n6
      gc t hn6 hbin_left2 prev0 k_out k1 k2 hprev0_left2 hkout_left3 hk1_left2 hk2_left1
      hprev0_succ hk1_val hk2_val
  · exact hcross

theorem right_first_later_shared_end_cross_only_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hall : ∀ phase : TernaryPhase gc t, isNormalFormGap gc t phase)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (hbin_right3 : isBinary sys.rs (right (right (right t))))
    (j1 k_out : Fin gc.configs.length)
    (hj1_right3 : gc.moverAt j1 = right (right (right t)))
    (hj1_lt_kout : j1.val < k_out.val)
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hfirst :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val → k.val < k_out.val → gc.moverAt k ≠ right (right (right t)))
    (hj_tail :
      ∀ k : Fin gc.configs.length,
        j1.val < k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t)))
    (hno_t_to_kout : ∀ k : Fin gc.configs.length,
      j1.val < k.val → k.val ≤ k_out.val → gc.moverAt k ≠ t)
    (phase0 : TernaryPhase gc t)
    (hphase0a : phase0.a = k_out)
    (hlong : k_out.val + 2 < phase0.s.val)
    (hphase_branch :
      ∀ k : Fin gc.configs.length,
        k_out.val < k.val → k.val < phase0.s.val →
        gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
    ∃ phase1 : TernaryPhase gc t, ∃ prev0 k1 k2 : Fin gc.configs.length,
      phase1.a = j1 ∧
      phase1.s = phase0.s ∧
      prev0.val + 1 = k_out.val ∧
      gc.moverAt prev0 = left (left t) ∧
      nextIndex gc.configs k_out = k1 ∧
      nextIndex gc.configs k1 = k2 ∧
      gc.moverAt k1 = right (right t) ∧
      gc.moverAt k2 = right t ∧
      k2.val + 1 = phase1.s.val := by
  rcases right_first_later_shared_end_same_or_cross_n6
      gc t hall hn6 hbin_right2 hbin_right3 j1 k_out hj1_right3 hj1_lt_kout
      hkout_right3 hfirst hj_tail hno_t_to_kout phase0 hphase0a hlong hphase_branch with hcross | hsame
  · exact hcross
  · rcases hsame with ⟨phase1, prev0, k1, k2, hphase1a, hphase1s, hprev0_succ,
      hprev0_right2, hnext01, hnext12, hk1_right2, hk2_right1, hk2_succ⟩
    have hk1_val : k1.val = k_out.val + 1 := by
      have hEq := congrArg Fin.val hnext01
      have hk1_lt_len : k_out.val + 1 < gc.configs.length := by
        exact lt_of_le_of_lt (Nat.succ_le_of_lt (by simpa [hphase0a] using phase0.ha_lt_s)) phase0.s.isLt
      simp [nextIndex, Nat.mod_eq_of_lt hk1_lt_len] at hEq
      exact hEq.symm
    have hk2_val : k2.val = k_out.val + 2 := by
      have hEq := congrArg Fin.val hnext12
      have hk2_lt_len : k1.val + 1 < gc.configs.length := by
        rw [hk1_val]
        exact lt_of_le_of_lt (show k_out.val + 2 ≤ phase0.s.val by omega) phase0.s.isLt
      simp [nextIndex, Nat.mod_eq_of_lt hk2_lt_len] at hEq
      rw [hk1_val] at hEq
      omega
    exact False.elim <| right_same_side_five_step_word_false_n6
      gc t hn6 hbin_right2 prev0 k_out k1 k2 hprev0_right2 hkout_right3 hk1_right2 hk2_right1
      hprev0_succ hk1_val hk2_val

private theorem left_cross_opposite_predecessor_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_left2 : isBinary sys.rs (left (left t)))
    (hbin_left3 : isBinary sys.rs (left (left (left t))))
    (q prev0 k_out k1 : Fin gc.configs.length)
    (hq_left3 : gc.moverAt q = left (left (left t)))
    (hprev0_right2 : gc.moverAt prev0 = right (right t))
    (hkout_left3 : gc.moverAt k_out = left (left (left t)))
    (hk1_left2 : gc.moverAt k1 = left (left t))
    (hnext_q : nextIndex gc.configs q = prev0)
    (hnext_prev0 : nextIndex gc.configs prev0 = k_out)
    (hnext_kout : nextIndex gc.configs k_out = k1) :
    False := by
  have hO_q_prev_val :
      ((gc.configs.get prev0) (left (left (left t)))).val =
        (((gc.configs.get q) (left (left (left t)))).val + 1) % 2 := by
    have hflip := binary_step_flip_val gc (left (left (left t))) hbin_left3 q hq_left3
    rw [hnext_q] at hflip
    exact hflip
  have hO_prev_kout :
      (gc.configs.get k_out) (left (left (left t))) =
        (gc.configs.get prev0) (left (left (left t))) := by
    have h := gc.state_eq_of_ne_moverAt prev0 (left (left (left t))) (by
      intro hEq
      exact left3_ne_right2_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_right2))
    rw [hnext_prev0] at h
    exact h
  have hO_kout_k1_val :
      ((gc.configs.get k1) (left (left (left t)))).val =
        (((gc.configs.get k_out) (left (left (left t)))).val + 1) % 2 := by
    have hflip := binary_step_flip_val gc (left (left (left t))) hbin_left3 k_out hkout_left3
    rw [hnext_kout] at hflip
    exact hflip
  have hO_prev_kout_val :
      ((gc.configs.get k_out) (left (left (left t)))).val =
        ((gc.configs.get prev0) (left (left (left t)))).val := by
    exact congrArg Fin.val hO_prev_kout
  have hO_eq_val :
      ((gc.configs.get k1) (left (left (left t)))).val =
        ((gc.configs.get q) (left (left (left t)))).val := by
    rw [hO_kout_k1_val, hO_prev_kout_val, hO_q_prev_val]
    omega
  have hO_eq :
      (gc.configs.get k1) (left (left (left t))) =
        (gc.configs.get q) (left (left (left t))) := by
    exact Fin.ext hO_eq_val

  have hL2_q_prev :
      (gc.configs.get prev0) (left (left t)) =
        (gc.configs.get q) (left (left t)) := by
    have h := gc.state_eq_of_ne_moverAt q (left (left t)) (by
      intro hEq
      exact left3_ne_left2_of_n_eq_six hn6 t (by simpa [hEq] using hq_left3.symm))
    rw [hnext_q] at h
    exact h
  have hL2_prev_kout :
      (gc.configs.get k_out) (left (left t)) =
        (gc.configs.get prev0) (left (left t)) := by
    have h := gc.state_eq_of_ne_moverAt prev0 (left (left t)) (by
      intro hEq
      exact left2_ne_right2_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_right2))
    rw [hnext_prev0] at h
    exact h
  have hL2_kout_k1 :
      (gc.configs.get k1) (left (left t)) =
        (gc.configs.get k_out) (left (left t)) := by
    have h := gc.state_eq_of_ne_moverAt k_out (left (left t)) (by
      intro hEq
      exact left3_ne_left2_of_n_eq_six hn6 t (by simpa [hEq] using hkout_left3.symm))
    rw [hnext_kout] at h
    exact h
  have hL2_eq :
      (gc.configs.get k1) (left (left t)) =
        (gc.configs.get q) (left (left t)) := by
    exact Eq.trans hL2_kout_k1 (Eq.trans hL2_prev_kout hL2_q_prev)

  have hL1_q_prev :
      (gc.configs.get prev0) (left t) =
        (gc.configs.get q) (left t) := by
    have h := gc.state_eq_of_ne_moverAt q (left t) (by
      intro hEq
      exact left3_ne_left_of_n_eq_six hn6 t (by simpa [hEq] using hq_left3.symm))
    rw [hnext_q] at h
    exact h
  have hL1_prev_kout :
      (gc.configs.get k_out) (left t) =
        (gc.configs.get prev0) (left t) := by
    have h := gc.state_eq_of_ne_moverAt prev0 (left t) (by
      intro hEq
      exact right2_ne_left_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_right2.symm))
    rw [hnext_prev0] at h
    exact h
  have hL1_kout_k1 :
      (gc.configs.get k1) (left t) =
        (gc.configs.get k_out) (left t) := by
    have h := gc.state_eq_of_ne_moverAt k_out (left t) (by
      intro hEq
      exact left3_ne_left_of_n_eq_six hn6 t (by simpa [hEq] using hkout_left3.symm))
    rw [hnext_kout] at h
    exact h
  have hL1_eq :
      (gc.configs.get k1) (left t) =
        (gc.configs.get q) (left t) := by
    exact Eq.trans hL1_kout_k1 (Eq.trans hL1_prev_kout hL1_q_prev)

  have hnonmover_q : gc.moverAt q ≠ left (left t) := by
    intro hEq
    exact left3_ne_left2_of_n_eq_six hn6 t (by simpa [hEq] using hq_left3.symm)
  have hec : hasEntryConflict gc := by
    refine ⟨k1, q, left (left t), hk1_left2, hnonmover_q, ?_, ?_, ?_⟩
    · simpa using hO_eq
    · simpa using hL2_eq
    · have hL1eq' : (gc.configs.get k1) (right (left (left t))) = (gc.configs.get q) (right (left (left t))) := by
        convert hL1_eq using 1 <;> rw [right_left_eq_self]
      exact hL1eq'
  exact entryConflict_impossible gc hec

private theorem right_cross_opposite_predecessor_false_n6
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hn6 : sys.rs.n = 6)
    (hbin_right2 : isBinary sys.rs (right (right t)))
    (hbin_right3 : isBinary sys.rs (right (right (right t))))
    (q prev0 k_out k1 : Fin gc.configs.length)
    (hq_right3 : gc.moverAt q = right (right (right t)))
    (hprev0_left2 : gc.moverAt prev0 = left (left t))
    (hkout_right3 : gc.moverAt k_out = right (right (right t)))
    (hk1_right2 : gc.moverAt k1 = right (right t))
    (hnext_q : nextIndex gc.configs q = prev0)
    (hnext_prev0 : nextIndex gc.configs prev0 = k_out)
    (hnext_kout : nextIndex gc.configs k_out = k1) :
    False := by
  have hO_q_prev_val :
      ((gc.configs.get prev0) (right (right (right t)))).val =
        (((gc.configs.get q) (right (right (right t)))).val + 1) % 2 := by
    have hflip := binary_step_flip_val gc (right (right (right t))) hbin_right3 q hq_right3
    rw [hnext_q] at hflip
    exact hflip
  have hO_prev_kout :
      (gc.configs.get k_out) (right (right (right t))) =
        (gc.configs.get prev0) (right (right (right t))) := by
    have h := gc.state_eq_of_ne_moverAt prev0 (right (right (right t))) (by
      intro hEq
      exact left2_ne_right3_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_left2.symm))
    rw [hnext_prev0] at h
    exact h
  have hO_kout_k1_val :
      ((gc.configs.get k1) (right (right (right t)))).val =
        (((gc.configs.get k_out) (right (right (right t)))).val + 1) % 2 := by
    have hflip := binary_step_flip_val gc (right (right (right t))) hbin_right3 k_out hkout_right3
    rw [hnext_kout] at hflip
    exact hflip
  have hO_prev_kout_val :
      ((gc.configs.get k_out) (right (right (right t)))).val =
        ((gc.configs.get prev0) (right (right (right t)))).val := by
    exact congrArg Fin.val hO_prev_kout
  have hO_eq_val :
      ((gc.configs.get k1) (right (right (right t)))).val =
        ((gc.configs.get q) (right (right (right t)))).val := by
    rw [hO_kout_k1_val, hO_prev_kout_val, hO_q_prev_val]
    omega
  have hO_eq :
      (gc.configs.get k1) (right (right (right t))) =
        (gc.configs.get q) (right (right (right t))) := by
    exact Fin.ext hO_eq_val

  have hR2_q_prev :
      (gc.configs.get prev0) (right (right t)) =
        (gc.configs.get q) (right (right t)) := by
    have h := gc.state_eq_of_ne_moverAt q (right (right t)) (by
      intro hEq
      exact right3_ne_right2_of_n_eq_six hn6 t (by simpa [hEq] using hq_right3.symm))
    rw [hnext_q] at h
    exact h
  have hR2_prev_kout :
      (gc.configs.get k_out) (right (right t)) =
        (gc.configs.get prev0) (right (right t)) := by
    have h := gc.state_eq_of_ne_moverAt prev0 (right (right t)) (by
      intro hEq
      exact left2_ne_right2_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_left2.symm))
    rw [hnext_prev0] at h
    exact h
  have hR2_kout_k1 :
      (gc.configs.get k1) (right (right t)) =
        (gc.configs.get k_out) (right (right t)) := by
    have h := gc.state_eq_of_ne_moverAt k_out (right (right t)) (by
      intro hEq
      exact right3_ne_right2_of_n_eq_six hn6 t (by simpa [hEq] using hkout_right3.symm))
    rw [hnext_kout] at h
    exact h
  have hR2_eq :
      (gc.configs.get k1) (right (right t)) =
        (gc.configs.get q) (right (right t)) := by
    exact Eq.trans hR2_kout_k1 (Eq.trans hR2_prev_kout hR2_q_prev)

  have hR1_q_prev :
      (gc.configs.get prev0) (right t) =
        (gc.configs.get q) (right t) := by
    have h := gc.state_eq_of_ne_moverAt q (right t) (by
      intro hEq
      exact right3_ne_right_of_n_eq_six hn6 t (by simpa [hEq] using hq_right3.symm))
    rw [hnext_q] at h
    exact h
  have hR1_prev_kout :
      (gc.configs.get k_out) (right t) =
        (gc.configs.get prev0) (right t) := by
    have h := gc.state_eq_of_ne_moverAt prev0 (right t) (by
      intro hEq
      exact left2_ne_right_of_n_eq_six hn6 t (by simpa [hEq] using hprev0_left2.symm))
    rw [hnext_prev0] at h
    exact h
  have hR1_kout_k1 :
      (gc.configs.get k1) (right t) =
        (gc.configs.get k_out) (right t) := by
    have h := gc.state_eq_of_ne_moverAt k_out (right t) (by
      intro hEq
      exact right3_ne_right_of_n_eq_six hn6 t (by simpa [hEq] using hkout_right3.symm))
    rw [hnext_kout] at h
    exact h
  have hR1_eq :
      (gc.configs.get k1) (right t) =
        (gc.configs.get q) (right t) := by
    exact Eq.trans hR1_kout_k1 (Eq.trans hR1_prev_kout hR1_q_prev)

  have hnonmover_q : gc.moverAt q ≠ right (right t) := by
    intro hEq
    exact right3_ne_right2_of_n_eq_six hn6 t (by simpa [hEq] using hq_right3.symm)
  have hec : hasEntryConflict gc := by
    refine ⟨k1, q, right (right t), hk1_right2, hnonmover_q, ?_, ?_, ?_⟩
    · simpa using hR1_eq
    · simpa using hR2_eq
    · simpa using hO_eq
  exact entryConflict_impossible gc hec

-/
-/
-/

theorem m6_residue_phase_shape_with_second_neighbor_after_opposite
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        ∃ phase : TernaryPhase gc t,
          (∀ k : Fin gc.configs.length,
            phase.a.val ≤ k.val → k.val < phase.s.val →
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)) ∨
          (∃ a0 a1 : Fin gc.configs.length,
            phase.a.val ≤ a0.val ∧
            a0.val < phase.s.val ∧
            gc.moverAt a0 = left (left (left t)) ∧
            nextIndex gc.configs a0 = a1 ∧
            a1.val < phase.s.val ∧
            (gc.moverAt a1 = left (left t) ∨ gc.moverAt a1 = right (right t))) := by
  rcases m6_binary_sandwich_residue_with_phase sys hvalid hn hcount with
    ⟨gc, hconv, t, hmt, hbL, hbR, _hfc2, _hfc_lt, hall, phase, _⟩
  rcases phase_all_local5_or_last_opposite_of_n_eq_six gc t phase hn with hall_local | hlast
  · exact ⟨gc, hconv, t, hmt, hbL, hbR, phase, Or.inl hall_local⟩
  · rcases hlast with ⟨a0, ha0_ge_a, ha0_lt_s, ha0_opp, htail⟩
    rcases allNormal_last_opposite_next_is_second_neighbor gc t hall phase hn a0
        ha0_lt_s ha0_opp htail with ⟨a1, hnext, ha1_lt_s, ha1_side⟩
    exact ⟨gc, hconv, t, hmt, hbL, hbR, phase,
      Or.inr ⟨a0, a1, ha0_ge_a, ha0_lt_s, ha0_opp, hnext, ha1_lt_s, ha1_side⟩⟩

theorem m6_residue_phase_shape_with_tight_tail_after_opposite
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        ∃ phase : TernaryPhase gc t,
          (∀ k : Fin gc.configs.length,
            phase.a.val ≤ k.val → k.val < phase.s.val →
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)) ∨
          (∃ a0 a1 : Fin gc.configs.length,
            phase.a.val ≤ a0.val ∧
            a0.val < phase.s.val ∧
            gc.moverAt a0 = left (left (left t)) ∧
            nextIndex gc.configs a0 = a1 ∧
            a1.val < phase.s.val ∧
            ((gc.moverAt a1 = left (left t) ∧
              (∀ k : Fin gc.configs.length,
                a1.val ≤ k.val → k.val < phase.s.val →
                gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) ∧
              gc.intervalFireCount (left t) a1.val phase.s.val = 1 ∧
              gc.intervalFireCount (right t) a1.val phase.s.val = 0) ∨
             (gc.moverAt a1 = right (right t) ∧
              (∀ k : Fin gc.configs.length,
                a1.val ≤ k.val → k.val < phase.s.val →
                gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) ∧
              gc.intervalFireCount (left t) a1.val phase.s.val = 0 ∧
              gc.intervalFireCount (right t) a1.val phase.s.val = 1))) := by
  rcases m6_binary_sandwich_residue_with_phase sys hvalid hn hcount with
    ⟨gc, hconv, t, hmt, hbL, hbR, _hfc2, _hfc_lt, hall, phase, _⟩
  rcases phase_all_local5_or_last_opposite_of_n_eq_six gc t phase hn with hall_local | hlast
  · exact ⟨gc, hconv, t, hmt, hbL, hbR, phase, Or.inl hall_local⟩
  · rcases hlast with ⟨a0, ha0_ge_a, ha0_lt_s, ha0_opp, htail⟩
    rcases allNormal_last_opposite_tail_tight gc t hall phase hn a0
        ha0_ge_a ha0_lt_s ha0_opp htail with hleft | hright
    · rcases hleft with ⟨a1, hnext, ha1_lt_s, ha1_ll, htail1, hJ1, hK0⟩
      exact ⟨gc, hconv, t, hmt, hbL, hbR, phase,
        Or.inr ⟨a0, a1, ha0_ge_a, ha0_lt_s, ha0_opp, hnext, ha1_lt_s,
          Or.inl ⟨ha1_ll, htail1, hJ1, hK0⟩⟩⟩
    · rcases hright with ⟨a1, hnext, ha1_lt_s, ha1_rr, htail1, hJ0, hK1⟩
      exact ⟨gc, hconv, t, hmt, hbL, hbR, phase,
        Or.inr ⟨a0, a1, ha0_ge_a, ha0_lt_s, ha0_opp, hnext, ha1_lt_s,
          Or.inr ⟨ha1_rr, htail1, hJ0, hK1⟩⟩⟩

theorem m6_residue_phase_shape_with_tail_word_after_opposite
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        ∃ phase : TernaryPhase gc t,
          (∀ k : Fin gc.configs.length,
            phase.a.val ≤ k.val → k.val < phase.s.val →
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)) ∨
          (∃ a0 a1 prev : Fin gc.configs.length,
            phase.a.val ≤ a0.val ∧
            a0.val < phase.s.val ∧
            gc.moverAt a0 = left (left (left t)) ∧
            nextIndex gc.configs a0 = a1 ∧
            prev.val + 1 = phase.s.val ∧
            ((gc.moverAt a1 = left (left t) ∧
              gc.moverAt prev = left t ∧
              ∀ k : Fin gc.configs.length,
                a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = left (left t)) ∨
             (gc.moverAt a1 = right (right t) ∧
              gc.moverAt prev = right t ∧
              ∀ k : Fin gc.configs.length,
                a1.val ≤ k.val → k.val < prev.val → gc.moverAt k = right (right t)))) := by
  rcases m6_binary_sandwich_residue_with_phase sys hvalid hn hcount with
    ⟨gc, hconv, t, hmt, hbL, hbR, _hfc2, _hfc_lt, hall, phase, _⟩
  rcases phase_all_local5_or_last_opposite_of_n_eq_six gc t phase hn with hall_local | hlast
  · exact ⟨gc, hconv, t, hmt, hbL, hbR, phase, Or.inl hall_local⟩
  · rcases hlast with ⟨a0, ha0_ge_a, ha0_lt_s, ha0_opp, htail⟩
    rcases allNormal_last_opposite_tail_word gc t hall phase hn a0
        ha0_ge_a ha0_lt_s ha0_opp htail with hleft | hright
    · rcases hleft with ⟨a1, prev, hnext, hprev_succ, ha1_ll, hprev_l, hword⟩
      exact ⟨gc, hconv, t, hmt, hbL, hbR, phase,
        Or.inr ⟨a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hnext, hprev_succ,
          Or.inl ⟨ha1_ll, hprev_l, hword⟩⟩⟩
    · rcases hright with ⟨a1, prev, hnext, hprev_succ, ha1_rr, hprev_r, hword⟩
      exact ⟨gc, hconv, t, hmt, hbL, hbR, phase,
        Or.inr ⟨a0, a1, prev, ha0_ge_a, ha0_lt_s, ha0_opp, hnext, hprev_succ,
          Or.inr ⟨ha1_rr, hprev_r, hword⟩⟩⟩

theorem m6_residue_phase_shape
    (sys : System) (hvalid : valid sys)
    (hn : sys.rs.n = 6) (hcount : binaryCount sys.rs = 5) :
    ∃ gc : GoodCycle sys,
      converges sys gc ∧
      ∃ t : Fin sys.rs.n,
        sys.rs.m t ≥ 3 ∧
        sys.rs.m (left t) = 2 ∧
        sys.rs.m (right t) = 2 ∧
        ∃ phase : TernaryPhase gc t,
          (∀ k : Fin gc.configs.length,
            phase.a.val ≤ k.val → k.val < phase.s.val →
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)) ∨
          (∃ a0 : Fin gc.configs.length,
            phase.a.val ≤ a0.val ∧
            a0.val < phase.s.val ∧
            gc.moverAt a0 = left (left (left t)) ∧
            ∀ k : Fin gc.configs.length,
              a0.val < k.val → k.val < phase.s.val →
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) := by
  rcases m6_binary_sandwich_residue_with_phase sys hvalid hn hcount with
    ⟨gc, hconv, t, hmt, hbL, hbR, _hfc2, _hfc_lt, _hall, phase, _⟩
  exact ⟨gc, hconv, t, hmt, hbL, hbR, phase,
    phase_all_local5_or_last_opposite_of_n_eq_six gc t phase hn⟩

end LeanMn
