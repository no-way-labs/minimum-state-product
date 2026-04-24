/-
  FCBound.lean — Fire count bound and entry conflict for 3 consecutive binary
  in zero-winding good cycles.

  For 3 consecutive binary {i, p = right i, rri = right(right i)} in a
  zero-winding good cycle: proves edge flow constraints, frozen-neighbor
  entry conflicts, and the binary fire count dispatch (fc = 0 or fc >= 2).

  All results sorry-free, no axioms.
-/
import LeanMn.LowerBound.Archive.EntryConflict.OppositeStart
import LeanMn.LowerBound.EntryConflict.IsolatedFirings
import LeanMn.LowerBound.EntryConflict.BinaryRightCrossing

namespace LeanMn

variable {sys : System}

/-! ### Ring topology helpers -/

private theorem right_ne_self_fcb (p : Fin sys.rs.n) : right p ≠ p := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hp := p.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega

private theorem i_ne_p_fcb (i : Fin sys.rs.n) : i ≠ right i :=
  fun h => right_ne_self_fcb i h.symm

private theorem rri_ne_p_fcb (i : Fin sys.rs.n) : right (right i) ≠ right i := by
  intro h; have hval := congrArg Fin.val h; simp only [right_val] at hval
  have hi := i.isLt; have hn := sys.rs.n_ge_4
  by_cases hp1 : i.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hp1] at hval
    by_cases hp2 : i.val + 1 + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp2] at hval; omega
    · rw [show i.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
  · rw [show i.val + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval; omega

/-! ### fireCount helpers -/

private theorem fireCount_pos_of_moverAt (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) (hmov : gc.moverAt k = p) :
    0 < gc.fireCount p := by
  have h2 := Finset.single_le_sum
    (f := fun j : Fin gc.configs.length => if gc.moverAt j = p then (1 : Nat) else 0)
    (fun j _ => by simp only []; split_ifs <;> omega) (Finset.mem_univ k)
  simp only [hmov, ite_true] at h2
  rw [gc.fireCount_eq_sum_moverAt]; omega

private theorem neverMover_of_fc_zero (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p = 0) (k : Fin gc.configs.length) :
    gc.moverAt k ≠ p := by
  intro hmov; exact absurd (fireCount_pos_of_moverAt gc p k hmov) (by omega)

/-! ### Zero winding edge flow balance -/

/-- Zero winding forces cwMoveCountAt(p) = ccwMoveCountAt(right p). -/
theorem zeroWinding_cw_eq_ccw_right (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n) :
    gc.cwMoveCountAt p = gc.ccwMoveCountAt (right p) := by
  have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero p
  unfold GoodCycle.edgeNetFlow at hflow; omega

/-- Zero winding: cwMoveCountAt(i) = ccwMoveCountAt(right i). -/
theorem zeroWinding_left_cw_eq_ccw (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (i : Fin sys.rs.n) :
    gc.cwMoveCountAt i = gc.ccwMoveCountAt (right i) :=
  zeroWinding_cw_eq_ccw_right gc hzero i

/-! ### Three never-fire safe processor contradiction -/

/-- If all 3 consecutive binary processors have fc = 0, the middle one is safe. -/
theorem three_neverFire_safe (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (hfc_i : gc.fireCount i = 0)
    (hfc_p : gc.fireCount (right i) = 0)
    (hfc_rri : gc.fireCount (right (right i)) = 0)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False := by
  apply hno_safe
  refine ⟨right i, fun k => ⟨?_, ?_, ?_⟩⟩
  · exact neverMover_of_fc_zero gc (right i) hfc_p k
  · rw [left_right_eq_self]; exact neverMover_of_fc_zero gc i hfc_i k
  · exact neverMover_of_fc_zero gc (right (right i)) hfc_rri k

/-! ### Frozen-neighbor parity lemmas -/

/-- rri frozen in gap → R-parity even. -/
private theorem rri_frozen_gap_even
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (mg : MinFiringGap gc (right i))
    (hR_frozen : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right (right i)) :
    gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
    gc.prefixFireCount (right (right i)) mg.b.val % 2 :=
  frozen_in_gap_even_parity mg (right (right i)) (rri_ne_p_fcb i) hR_frozen

/-- i frozen in gap → L-parity even. -/
private theorem i_frozen_gap_even
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (mg : MinFiringGap gc (right i))
    (hL_frozen : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ i) :
    gc.prefixFireCount i (mg.a.val + 1) % 2 =
    gc.prefixFireCount i mg.b.val % 2 :=
  frozen_in_gap_even_parity mg i (i_ne_p_fcb i) hL_frozen

/-- i frozen outside gap → L-parity even (all firings in gap = fc(i) = even). -/
private theorem i_frozen_complement_even
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hL_before : ∀ k : Fin gc.configs.length, k.val ≤ mg.a.val → gc.moverAt k ≠ i)
    (hL_after : ∀ k : Fin gc.configs.length, mg.b.val ≤ k.val → gc.moverAt k ≠ i) :
    gc.prefixFireCount i (mg.a.val + 1) % 2 =
    gc.prefixFireCount i mg.b.val % 2 :=
  all_firings_in_gap_even_parity mg i h3bin.1 (i_ne_p_fcb i) hL_before hL_after

/-- rri frozen outside gap → R-parity even. -/
private theorem rri_frozen_complement_even
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hR_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ right (right i))
    (hR_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ right (right i)) :
    gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
    gc.prefixFireCount (right (right i)) mg.b.val % 2 :=
  all_firings_in_gap_even_parity mg (right (right i)) h3bin.2.2
    (rri_ne_p_fcb i) hR_before hR_after

/-! ### Entry conflict from frozen patterns -/

/-- Both even parities → entry conflict. -/
theorem fc_both_even_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL_even : gc.prefixFireCount i (mg.a.val + 1) % 2 =
               gc.prefixFireCount i mg.b.val % 2)
    (hR_even : gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
               gc.prefixFireCount (right (right i)) mg.b.val % 2) :
    hasEntryConflict gc :=
  minGap_parity_ec h3bin mg hgap2 hL_even hR_even

/-- rri frozen in gap + i frozen outside → entry conflict. -/
theorem fc_frozen_cross_ec
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hR_gap : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val →
      gc.moverAt k ≠ right (right i))
    (hL_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ i)
    (hL_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ i) :
    hasEntryConflict gc :=
  opposite_start_entry_conflict h3bin mg hgap2 hR_gap hL_before hL_after

/-- i frozen in gap + rri frozen outside → entry conflict. -/
theorem fc_frozen_cross_ec_sym
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL_gap : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val →
      gc.moverAt k ≠ i)
    (hR_before : ∀ k : Fin gc.configs.length,
      k.val ≤ mg.a.val → gc.moverAt k ≠ right (right i))
    (hR_after : ∀ k : Fin gc.configs.length,
      mg.b.val ≤ k.val → gc.moverAt k ≠ right (right i)) :
    hasEntryConflict gc :=
  opposite_start_entry_conflict_sym h3bin mg hgap2 hL_gap hR_before hR_after

/-! ### Binary fire count dispatch -/

/-- A binary processor's fire count is 0 or >= 2. -/
theorem binary_fc_zero_or_ge2 (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p) :
    gc.fireCount p = 0 ∨ gc.fireCount p ≥ 2 := by
  by_cases h0 : gc.fireCount p = 0
  · exact Or.inl h0
  · right
    have heven := gc.binary_fireCount_even p hbin
    have hne1 := gc.fireCount_ne_one p
    obtain ⟨k, hk⟩ := heven
    omega

/-! ### Zero-winding edge flow with fc = 0 -/

private theorem moveCountAt_zero_of_fc_zero (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p = 0) :
    gc.cwMoveCountAt p = 0 ∧ gc.stayMoveCountAt p = 0 ∧ gc.ccwMoveCountAt p = 0 := by
  have hpart := gc.fireCount_eq_moveCount_partition p
  rw [hfc] at hpart
  constructor
  · -- cwMoveCountAt is a sum of nonneg terms, and the total is 0
    unfold GoodCycle.cwMoveCountAt
    apply Finset.sum_eq_zero; intro k _
    have : gc.moverAt k ≠ p := neverMover_of_fc_zero gc p hfc k
    simp [this]
  constructor
  · unfold GoodCycle.stayMoveCountAt
    apply Finset.sum_eq_zero; intro k _
    have : gc.moverAt k ≠ p := neverMover_of_fc_zero gc p hfc k
    simp [this]
  · unfold GoodCycle.ccwMoveCountAt
    apply Finset.sum_eq_zero; intro k _
    have : gc.moverAt k ≠ p := neverMover_of_fc_zero gc p hfc k
    simp [this]

/-- Zero winding + fc(p) = 0 → cwMoveCountAt(left p) = 0. -/
theorem zeroWinding_fc_zero_left_cw_zero (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n) (hfc : gc.fireCount p = 0) :
    gc.cwMoveCountAt (left p) = 0 := by
  have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero (left p)
  unfold GoodCycle.edgeNetFlow at hflow
  simp [right_left_eq_self] at hflow
  have ⟨_, _, hccw⟩ := moveCountAt_zero_of_fc_zero gc p hfc
  omega

/-- Zero winding + fc(p) = 0 → ccwMoveCountAt(right p) = 0. -/
theorem zeroWinding_fc_zero_right_ccw_zero (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n) (hfc : gc.fireCount p = 0) :
    gc.ccwMoveCountAt (right p) = 0 := by
  have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero p
  unfold GoodCycle.edgeNetFlow at hflow
  have ⟨hcw, _, _⟩ := moveCountAt_zero_of_fc_zero gc p hfc
  omega

/-- Zero winding + fc(p) = 0: left(p) never fires CW (toward p). -/
theorem zeroWinding_fc_zero_left_never_cw (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n) (hfc : gc.fireCount p = 0)
    (k : Fin gc.configs.length) (hmov : gc.moverAt k = left p) :
    gc.stepDir k ≠ .cw := by
  intro hcw
  have hcw_count := zeroWinding_fc_zero_left_cw_zero gc hzero p hfc
  -- cwMoveCountAt(left p) = 0, but step k contributes 1
  unfold GoodCycle.cwMoveCountAt at hcw_count
  have h1 : 1 ≤ ∑ j : Fin gc.configs.length,
      if gc.moverAt j = left p ∧ gc.stepDir j = .cw then 1 else 0 := by
    have hsingle := Finset.single_le_sum
      (f := fun j : Fin gc.configs.length =>
        if gc.moverAt j = left p ∧ gc.stepDir j = .cw then (1 : Nat) else 0)
      (fun j _ => by simp only []; split_ifs <;> omega) (Finset.mem_univ k)
    simp only [hmov, hcw, and_self, ite_true] at hsingle
    omega
  omega

/-- Zero winding + fc(p) = 0: right(p) never fires CCW (toward p). -/
theorem zeroWinding_fc_zero_right_never_ccw (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n) (hfc : gc.fireCount p = 0)
    (k : Fin gc.configs.length) (hmov : gc.moverAt k = right p) :
    gc.stepDir k ≠ .ccw := by
  intro hccw
  have hccw_count := zeroWinding_fc_zero_right_ccw_zero gc hzero p hfc
  unfold GoodCycle.ccwMoveCountAt at hccw_count
  have h1 : 1 ≤ ∑ j : Fin gc.configs.length,
      if gc.moverAt j = right p ∧ gc.stepDir j = .ccw then 1 else 0 := by
    have hsingle := Finset.single_le_sum
      (f := fun j : Fin gc.configs.length =>
        if gc.moverAt j = right p ∧ gc.stepDir j = .ccw then (1 : Nat) else 0)
      (fun j _ => by simp only []; split_ifs <;> omega) (Finset.mem_univ k)
    simp only [hmov, hccw, and_self, ite_true] at hsingle
    omega
  omega

/-- Zero winding + fc(p) = 0: left(p) never sends the mover to p. -/
theorem zeroWinding_fc_zero_left_never_sends_to_p (gc : GoodCycle sys)
    (_hzero : gc.zeroWinding) (p : Fin sys.rs.n) (hfc : gc.fireCount p = 0)
    (k : Fin gc.configs.length) (_hmov : gc.moverAt k = left p) :
    gc.moverAt (nextIndex gc.configs k) ≠ p :=
  neverMover_of_fc_zero gc p hfc (nextIndex gc.configs k)

/-- Zero winding + fc(p) = 0: right(p) never sends the mover to p. -/
theorem zeroWinding_fc_zero_right_never_sends_to_p (gc : GoodCycle sys)
    (_hzero : gc.zeroWinding) (p : Fin sys.rs.n) (hfc : gc.fireCount p = 0)
    (k : Fin gc.configs.length) (_hmov : gc.moverAt k = right p) :
    gc.moverAt (nextIndex gc.configs k) ≠ p :=
  neverMover_of_fc_zero gc p hfc (nextIndex gc.configs k)

/-- The mover never visits p when fc(p) = 0. -/
theorem mover_never_at_p_of_fc_zero (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hfc : gc.fireCount p = 0) (k : Fin gc.configs.length) :
    gc.moverAt k ≠ p :=
  neverMover_of_fc_zero gc p hfc k

/-! ### Assembly: fc >= 2 isolated + frozen conditions → False -/

/-- fc(p) >= 2 + isolated + cross-frozen conditions → False via entry conflict. -/
theorem fc_ge2_frozen_false
    (_gc : GoodCycle sys) (_hconv : converges sys _gc)
    (i : Fin sys.rs.n)
    (h3bin : threeConsecutiveBinary sys.rs i)
    (hfc : _gc.fireCount (right i) ≥ 2)
    (hiso : ∀ (a : Fin _gc.configs.length),
      _gc.moverAt a = right i → _gc.moverAt (nextIndex _gc.configs a) ≠ right i)
    (hfrozen :
      (-- Pattern A: rri frozen in gap, i frozen in complement
       (∀ k : Fin _gc.configs.length,
         let mg := exists_minFiringGap _gc (right i) hfc
         mg.a.val < k.val → k.val < mg.b.val →
         _gc.moverAt k ≠ right (right i)) ∧
       (∀ k : Fin _gc.configs.length,
         let mg := exists_minFiringGap _gc (right i) hfc
         k.val ≤ mg.a.val → _gc.moverAt k ≠ i) ∧
       (∀ k : Fin _gc.configs.length,
         let mg := exists_minFiringGap _gc (right i) hfc
         mg.b.val ≤ k.val → _gc.moverAt k ≠ i))
      ∨
      (-- Pattern B: i frozen in gap, rri frozen in complement
       (∀ k : Fin _gc.configs.length,
         let mg := exists_minFiringGap _gc (right i) hfc
         mg.a.val < k.val → k.val < mg.b.val →
         _gc.moverAt k ≠ i) ∧
       (∀ k : Fin _gc.configs.length,
         let mg := exists_minFiringGap _gc (right i) hfc
         k.val ≤ mg.a.val → _gc.moverAt k ≠ right (right i)) ∧
       (∀ k : Fin _gc.configs.length,
         let mg := exists_minFiringGap _gc (right i) hfc
         mg.b.val ≤ k.val → _gc.moverAt k ≠ right (right i)))) :
    False := by
  set mg := exists_minFiringGap _gc (right i) hfc
  have hgap2 := allIsolated_gap_ge2 mg hiso
  have hec : hasEntryConflict _gc := by
    rcases hfrozen with ⟨hR, hLb, hLa⟩ | ⟨hL, hRb, hRa⟩
    · exact opposite_start_entry_conflict h3bin mg hgap2 hR hLb hLa
    · exact opposite_start_entry_conflict_sym h3bin mg hgap2 hL hRb hRa
  exact entryConflict_impossible _gc hec

end LeanMn
