/-
  PairedCrossing.lean — Paired Edge Crossing Lemma for Zero-Winding Cycles

  For a zero-winding good cycle where some edge has both CW and CCW
  crossings, there exist steps a, b crossing that edge in opposite
  directions with no intervening crossings of the same edge.

  This is the core combinatorial step for the zero-winding entry
  conflict argument: between adjacent opposite-direction crossings,
  the local state at the shared endpoint is preserved.
-/
import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

/-! ### Edge crossing definitions -/

/-- The mover walk crosses edge `{p, right p}` at step `k`. -/
noncomputable def edgeCrossAt' (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) : Prop :=
  (gc.moverAt k = p ∧ gc.moverAt (nextIndex gc.configs k) = right p) ∨
    (gc.moverAt k = right p ∧ gc.moverAt (nextIndex gc.configs k) = p)

noncomputable instance (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) : Decidable (edgeCrossAt' gc p k) := by
  unfold edgeCrossAt'; infer_instance

/-- Edge crossing reformulated in terms of stepDir. -/
theorem edgeCrossAt'_iff_stepDir (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) :
    edgeCrossAt' gc p k ↔
      (gc.moverAt k = p ∧ gc.stepDir k = .cw) ∨
        (gc.moverAt k = right p ∧ gc.stepDir k = .ccw) := by
  constructor
  · intro hcross
    rcases hcross with hcw | hccw
    · left
      refine ⟨hcw.1, ?_⟩
      have hright : gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k) := by
        simpa [hcw.1] using hcw.2
      exact gc.stepDir_eq_cw_of_eq_right hright
    · right
      refine ⟨hccw.1, ?_⟩
      have hleft : gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) := by
        rw [hccw.1]
        calc
          gc.moverAt (nextIndex gc.configs k) = p := hccw.2
          _ = left (right p) := by simpa using (left_right_eq_self p).symm
      exact gc.stepDir_eq_ccw_of_eq_left hleft
  · intro hstep
    rcases hstep with hcw | hccw
    · left
      refine ⟨hcw.1, ?_⟩
      simpa [hcw.1] using gc.eq_right_of_stepDir_eq_cw hcw.2
    · right
      refine ⟨hccw.1, ?_⟩
      calc
        gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) :=
          gc.eq_left_of_stepDir_eq_ccw hccw.2
        _ = left (right p) := by rw [hccw.1]
        _ = p := by simpa using left_right_eq_self p

/-! ### CW and CCW crossing subsets -/

/-- Step k is a CW crossing of edge (p, right p). -/
noncomputable def edgeCWCrossAt (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) : Prop :=
  gc.moverAt k = p ∧ gc.stepDir k = .cw

noncomputable instance decidableEdgeCWCrossAt (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (k : Fin gc.configs.length) :
    Decidable (edgeCWCrossAt gc p k) := by
  unfold edgeCWCrossAt; infer_instance

/-- Step k is a CCW crossing of edge (p, right p). -/
noncomputable def edgeCCWCrossAt (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) : Prop :=
  gc.moverAt k = right p ∧ gc.stepDir k = .ccw

noncomputable instance decidableEdgeCCWCrossAt (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (k : Fin gc.configs.length) :
    Decidable (edgeCCWCrossAt gc p k) := by
  unfold edgeCCWCrossAt; infer_instance

theorem edgeCrossAt'_iff_cwOrCcw (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) :
    edgeCrossAt' gc p k ↔ edgeCWCrossAt gc p k ∨ edgeCCWCrossAt gc p k := by
  rw [edgeCrossAt'_iff_stepDir]; rfl

theorem edgeCWCrossAt_imp (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) (h : edgeCWCrossAt gc p k) :
    edgeCrossAt' gc p k :=
  (edgeCrossAt'_iff_cwOrCcw gc p k).mpr (Or.inl h)

theorem edgeCCWCrossAt_imp (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) (h : edgeCCWCrossAt gc p k) :
    edgeCrossAt' gc p k :=
  (edgeCrossAt'_iff_cwOrCcw gc p k).mpr (Or.inr h)

theorem not_cwAndCcw (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (k : Fin gc.configs.length) :
    ¬(edgeCWCrossAt gc p k ∧ edgeCCWCrossAt gc p k) := by
  intro ⟨hcw, hccw⟩
  have : (StepDir.cw : StepDir) = .ccw := hcw.2.symm.trans hccw.2
  cases this

/-! ### Both CW and CCW crossings exist at zero-winding edges -/

theorem ccwMoveCountAt_pos_of_cwMoveCountAt_pos_zeroWinding
    (gc : GoodCycle sys) (hzero : gc.zeroWinding) (p : Fin sys.rs.n)
    (hpos : 0 < gc.cwMoveCountAt p) :
    0 < gc.ccwMoveCountAt (right p) := by
  have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero p
  unfold GoodCycle.edgeNetFlow at hflow
  omega

/-- The set of CW crossings of edge (p, right p). -/
noncomputable def GoodCycle.edgeCWSteps (gc : GoodCycle sys)
    (p : Fin sys.rs.n) : Finset (Fin gc.configs.length) :=
  Finset.univ.filter (fun k => edgeCWCrossAt gc p k)

/-- The set of CCW crossings of edge (p, right p). -/
noncomputable def GoodCycle.edgeCCWSteps (gc : GoodCycle sys)
    (p : Fin sys.rs.n) : Finset (Fin gc.configs.length) :=
  Finset.univ.filter (fun k => edgeCCWCrossAt gc p k)

theorem cwSteps_card_eq (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    (gc.edgeCWSteps p).card = gc.cwMoveCountAt p := by
  unfold GoodCycle.edgeCWSteps GoodCycle.cwMoveCountAt edgeCWCrossAt
  simp only [Finset.card_filter]

theorem ccwSteps_card_eq (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    (gc.edgeCCWSteps p).card = gc.ccwMoveCountAt (right p) := by
  unfold GoodCycle.edgeCCWSteps GoodCycle.ccwMoveCountAt edgeCCWCrossAt
  simp only [Finset.card_filter]

theorem cwSteps_nonempty (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hpos : 0 < gc.cwMoveCountAt p) :
    (gc.edgeCWSteps p).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have := cwSteps_card_eq gc p
  rw [hempty, Finset.card_empty] at this
  omega

theorem ccwSteps_nonempty (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hpos : 0 < gc.ccwMoveCountAt (right p)) :
    (gc.edgeCCWSteps p).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have := ccwSteps_card_eq gc p
  rw [hempty, Finset.card_empty] at this
  omega

/-! ### The set of opposite-type crossing pairs -/

/-- The set of pairs (a, b) of crossings of edge (p, right p) with
    a.val < b.val and opposite types (one CW, one CCW). -/
noncomputable def GoodCycle.oppPairs (gc : GoodCycle sys)
    (p : Fin sys.rs.n) :
    Finset (Fin gc.configs.length × Fin gc.configs.length) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ⟨a, b⟩ =>
    a.val < b.val ∧ edgeCrossAt' gc p a ∧ edgeCrossAt' gc p b ∧
      ((edgeCWCrossAt gc p a ∧ edgeCCWCrossAt gc p b) ∨
       (edgeCCWCrossAt gc p a ∧ edgeCWCrossAt gc p b))

/-- The gap of a pair. -/
def pairGap {L : Nat} (pair : Fin L × Fin L) : Nat :=
  pair.2.val - pair.1.val

/-! ### Nonemptiness of opposite crossing pairs -/

private theorem ne_val_of_cw_ccw (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (ha : edgeCWCrossAt gc p a) (hb : edgeCCWCrossAt gc p b) :
    a.val ≠ b.val := by
  intro heq
  have haeq : a = b := Fin.ext heq
  subst haeq
  exact not_cwAndCcw gc p a ⟨ha, hb⟩

theorem oppPairs_nonempty (gc : GoodCycle sys)
    (hzero : gc.zeroWinding) (p : Fin sys.rs.n)
    (hpos : 0 < gc.cwMoveCountAt p) :
    (gc.oppPairs p).Nonempty := by
  have hccw_pos := ccwMoveCountAt_pos_of_cwMoveCountAt_pos_zeroWinding gc hzero p hpos
  obtain ⟨a, ha⟩ := cwSteps_nonempty gc p hpos
  obtain ⟨b, hb⟩ := ccwSteps_nonempty gc p hccw_pos
  have ha_mem : edgeCWCrossAt gc p a := by
    simpa [GoodCycle.edgeCWSteps] using ha
  have hb_mem : edgeCCWCrossAt gc p b := by
    simpa [GoodCycle.edgeCCWSteps] using hb
  have hne := ne_val_of_cw_ccw gc p a b ha_mem hb_mem
  by_cases hlt : a.val < b.val
  · refine ⟨(a, b), ?_⟩
    simp only [GoodCycle.oppPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ⟨hlt,
      edgeCWCrossAt_imp gc p a ha_mem,
      edgeCCWCrossAt_imp gc p b hb_mem,
      Or.inl ⟨ha_mem, hb_mem⟩⟩
  · have hlt' : b.val < a.val := by omega
    refine ⟨(b, a), ?_⟩
    simp only [GoodCycle.oppPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ⟨hlt',
      edgeCCWCrossAt_imp gc p b hb_mem,
      edgeCWCrossAt_imp gc p a ha_mem,
      Or.inr ⟨hb_mem, ha_mem⟩⟩

/-! ### The paired crossing lemma -/

/-- **Paired Edge Crossing Lemma.** For a zero-winding good cycle where
    edge (p, right p) has at least one CW crossing, there exist steps a and b
    crossing that edge in opposite directions (one CW, one CCW) with
    a.val < b.val and no crossings of the same edge strictly between them.

    This is the core combinatorial fact for the zero-winding entry conflict:
    between adjacent opposite-direction crossings, the states of the shared
    endpoint processors are constrained by the no-intervening-crossing gap. -/
theorem exists_paired_edge_crossing (gc : GoodCycle sys)
    (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n)
    (hpos : 0 < gc.cwMoveCountAt p) :
    ∃ (a b : Fin gc.configs.length),
      edgeCrossAt' gc p a ∧
      edgeCrossAt' gc p b ∧
      a.val < b.val ∧
      (∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k) ∧
      ((edgeCWCrossAt gc p a ∧ edgeCCWCrossAt gc p b) ∨
       (edgeCCWCrossAt gc p a ∧ edgeCWCrossAt gc p b)) := by
  -- The set of opposite-type crossing pairs is nonempty
  have hne := oppPairs_nonempty gc hzero p hpos
  -- Map to gaps and find the minimum
  let gapSet := (gc.oppPairs p).image pairGap
  have hgapNe : gapSet.Nonempty := Finset.Nonempty.image hne pairGap
  set minGap := gapSet.min' hgapNe with hMinGapDef
  -- There exists a pair achieving the minimum gap
  have hMinMem : minGap ∈ gapSet := Finset.min'_mem gapSet hgapNe
  rw [Finset.mem_image] at hMinMem
  obtain ⟨⟨a, b⟩, habMem, habGap⟩ := hMinMem
  simp only [GoodCycle.oppPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and] at habMem
  obtain ⟨hlt, haCross, hbCross, hTypes⟩ := habMem
  -- The gap of (a, b) equals minGap
  have hGapEq : b.val - a.val = minGap := habGap
  -- For any pair in oppPairs, its gap is ≥ minGap
  have hMinLE : ∀ pair ∈ gc.oppPairs p, minGap ≤ pairGap pair := by
    intro pair hpair
    exact Finset.min'_le gapSet (pairGap pair)
      (Finset.mem_image_of_mem pairGap hpair)
  -- Show no crossing strictly between a and b
  have hNoBetween : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k := by
    intro k hak hkb hkCross
    rw [edgeCrossAt'_iff_cwOrCcw] at hkCross
    -- In all cases, we find a pair with strictly smaller gap
    rcases hkCross with hkCW | hkCCW
    · -- k is a CW crossing
      rcases hTypes with ⟨haCW, hbCCW⟩ | ⟨haCCW, hbCW⟩
      · -- a CW, b CCW, k CW → (k, b) is CW-CCW, gap < (a, b)
        have hPairMem : (k, b) ∈ gc.oppPairs p := by
          simp only [GoodCycle.oppPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and]
          exact ⟨hkb, edgeCWCrossAt_imp gc p k hkCW, hbCross, Or.inl ⟨hkCW, hbCCW⟩⟩
        have hLE := hMinLE (k, b) hPairMem
        simp [pairGap] at hLE habGap
        omega
      · -- a CCW, b CW, k CW → (a, k) is CCW-CW, gap < (a, b)
        have hPairMem : (a, k) ∈ gc.oppPairs p := by
          simp only [GoodCycle.oppPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and]
          exact ⟨hak, haCross, edgeCWCrossAt_imp gc p k hkCW, Or.inr ⟨haCCW, hkCW⟩⟩
        have hLE := hMinLE (a, k) hPairMem
        simp [pairGap] at hLE habGap
        omega
    · -- k is a CCW crossing
      rcases hTypes with ⟨haCW, hbCCW⟩ | ⟨haCCW, hbCW⟩
      · -- a CW, b CCW, k CCW → (a, k) is CW-CCW, gap < (a, b)
        have hPairMem : (a, k) ∈ gc.oppPairs p := by
          simp only [GoodCycle.oppPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and]
          exact ⟨hak, haCross, edgeCCWCrossAt_imp gc p k hkCCW, Or.inl ⟨haCW, hkCCW⟩⟩
        have hLE := hMinLE (a, k) hPairMem
        simp [pairGap] at hLE habGap
        omega
      · -- a CCW, b CW, k CCW → (k, b) is CCW-CW, gap < (a, b)
        have hPairMem : (k, b) ∈ gc.oppPairs p := by
          simp only [GoodCycle.oppPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and]
          exact ⟨hkb, edgeCCWCrossAt_imp gc p k hkCCW, hbCross, Or.inr ⟨hkCCW, hbCW⟩⟩
        have hLE := hMinLE (k, b) hPairMem
        simp [pairGap] at hLE habGap
        omega
  exact ⟨a, b, haCross, hbCross, hlt, hNoBetween, hTypes⟩

/-! ### CW step count positivity for non-trivial zero-winding cycles -/

/-- In a zero-winding good cycle where the mover changes position at some
    step, the CW step count is positive. -/
theorem cwStepCount_pos_of_zeroWinding_of_exists_nonStay (gc : GoodCycle sys)
    (hzero : gc.zeroWinding)
    (hstep : ∃ k : Fin gc.configs.length, gc.stepDir k ≠ .stay) :
    0 < gc.cwStepCount := by
  by_contra hle
  push_neg at hle
  have hcw0 : gc.cwStepCount = 0 := by omega
  have hccw0 : gc.ccwStepCount = 0 := by
    have := gc.cwStepCount_eq_ccwStepCount_of_zeroWinding hzero
    omega
  -- All steps are stay-steps
  have hallStay : ∀ k : Fin gc.configs.length, gc.stepDir k = .stay := by
    intro k
    rcases gc.stepDir_cases k with hcw | hstay | hccw
    · exfalso
      have : 0 < gc.cwStepCount := by
        unfold GoodCycle.cwStepCount
        have : (∑ j : Fin gc.configs.length, if gc.stepDir j = .cw then 1 else 0) ≥ 1 := by
          calc (∑ j : Fin gc.configs.length, if gc.stepDir j = .cw then 1 else 0)
              ≥ (if gc.stepDir k = .cw then 1 else 0) :=
                Finset.single_le_sum (f := fun j => if gc.stepDir j = .cw then 1 else 0)
                  (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
            _ = 1 := by simp [hcw]
        omega
      omega
    · exact hstay
    · exfalso
      have : 0 < gc.ccwStepCount := by
        unfold GoodCycle.ccwStepCount
        have : (∑ j : Fin gc.configs.length, if gc.stepDir j = .ccw then 1 else 0) ≥ 1 := by
          calc (∑ j : Fin gc.configs.length, if gc.stepDir j = .ccw then 1 else 0)
              ≥ (if gc.stepDir k = .ccw then 1 else 0) :=
                Finset.single_le_sum (f := fun j => if gc.stepDir j = .ccw then 1 else 0)
                  (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
            _ = 1 := by simp [hccw]
        omega
      omega
  obtain ⟨k, hk⟩ := hstep
  exact hk (hallStay k)

/-- In a zero-winding good cycle with CW step count > 0, there exists an
    edge with a CW crossing (cwMoveCountAt > 0). -/
theorem exists_edge_with_cw_crossing (gc : GoodCycle sys)
    (hpos : 0 < gc.cwStepCount) :
    ∃ p : Fin sys.rs.n, 0 < gc.cwMoveCountAt p := by
  by_contra hall
  push_neg at hall
  have : gc.cwStepCount = 0 := by
    rw [gc.cwStepCount_eq_sum_cwMoveCountAt]
    apply Finset.sum_eq_zero
    intro p _
    have := hall p
    omega
  omega

end LeanMn
