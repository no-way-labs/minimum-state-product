import LeanMn.LowerBound.GoodCycleBasics

namespace LeanMn

variable {sys : System}

/-! ### Uniform direction mover words -/

/-- Every mover step advances clockwise. -/
def GoodCycle.uniformCW (gc : GoodCycle sys) : Prop :=
  ∀ k : Fin gc.configs.length,
    gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k)

/-- Every mover step advances counterclockwise. -/
def GoodCycle.uniformCCW (gc : GoodCycle sys) : Prop :=
  ∀ k : Fin gc.configs.length,
    gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k)

/-- The mover word has one global direction. -/
def GoodCycle.uniformDirection (gc : GoodCycle sys) : Prop :=
  gc.uniformCW ∨ gc.uniformCCW

/-- Step direction in the mover word. -/
inductive StepDir
  | cw
  | stay
  | ccw
  deriving DecidableEq, Repr

/-- The local direction of one mover-word step. -/
noncomputable def GoodCycle.stepDir (gc : GoodCycle sys) (k : Fin gc.configs.length) : StepDir :=
  let curr := gc.moverAt k
  let nxt := gc.moverAt (nextIndex gc.configs k)
  if hcw : nxt = right curr then .cw
  else if hstay : nxt = curr then .stay
  else .ccw

/-- A mover word is same-direction clockwise if it never takes a CCW step. -/
noncomputable def GoodCycle.sameDirectionCW (gc : GoodCycle sys) : Prop :=
  ∀ k : Fin gc.configs.length, gc.stepDir k ≠ .ccw

/-- A mover word is same-direction counterclockwise if it never takes a CW step. -/
noncomputable def GoodCycle.sameDirectionCCW (gc : GoodCycle sys) : Prop :=
  ∀ k : Fin gc.configs.length, gc.stepDir k ≠ .cw

/-- No-reversal mover words keep one global sign, but may allow stay-steps. -/
noncomputable def GoodCycle.noReversal (gc : GoodCycle sys) : Prop :=
  gc.sameDirectionCW ∨ gc.sameDirectionCCW

/-- Two local step directions form a reversal when they are opposite non-stay moves. -/
def StepDir.reverses (d₁ d₂ : StepDir) : Prop :=
  (d₁ = .cw ∧ d₂ = .ccw) ∨ (d₁ = .ccw ∧ d₂ = .cw)

/-- A reversal occurs at step `k` when consecutive local directions flip sign. -/
noncomputable def GoodCycle.reversalAt (gc : GoodCycle sys) (k : Fin gc.configs.length) : Prop :=
  StepDir.reverses (gc.stepDir k) (gc.stepDir (nextIndex gc.configs k))

noncomputable instance (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    Decidable (gc.reversalAt k) := by
  unfold GoodCycle.reversalAt StepDir.reverses
  infer_instance

/-- The set of reversal positions in the mover word. -/
noncomputable def GoodCycle.reversalSteps (gc : GoodCycle sys) :
    Finset (Fin gc.configs.length) :=
  Finset.univ.filter (fun k => gc.reversalAt k)

/-- Count how many reversals occur in the mover word. -/
noncomputable def GoodCycle.reversalCount (gc : GoodCycle sys) : Nat :=
  (gc.reversalSteps).card

/-- Zero-winding BAF branch: exactly one reversal in the mover word. -/
noncomputable def GoodCycle.hasOneReversal (gc : GoodCycle sys) : Prop :=
  gc.reversalCount = 1

/-- Zero-winding wiggle branch: at least two reversals in the mover word. -/
noncomputable def GoodCycle.hasMultiReversal (gc : GoodCycle sys) : Prop :=
  2 ≤ gc.reversalCount

theorem mem_reversalSteps_iff (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    k ∈ gc.reversalSteps ↔ gc.reversalAt k := by
  unfold GoodCycle.reversalSteps
  simp

/-- Count the clockwise steps in a mover word. -/
noncomputable def GoodCycle.cwStepCount (gc : GoodCycle sys) : Nat :=
  ∑ k : Fin gc.configs.length, if gc.stepDir k = .cw then 1 else 0

/-- Count the stay-steps in a mover word. -/
noncomputable def GoodCycle.stayStepCount (gc : GoodCycle sys) : Nat :=
  ∑ k : Fin gc.configs.length, if gc.stepDir k = .stay then 1 else 0

/-- Count the counterclockwise steps in a mover word. -/
noncomputable def GoodCycle.ccwStepCount (gc : GoodCycle sys) : Nat :=
  ∑ k : Fin gc.configs.length, if gc.stepDir k = .ccw then 1 else 0

private lemma left_ne_self_cycletypes {n : Nat} (hn : 4 ≤ n) (i : Fin n) :
    left i ≠ i := by
  intro h
  have := congrArg Fin.val h
  simp only [left_val] at this
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at this
    omega

private lemma right_ne_self_cycletypes {n : Nat} (hn : 4 ≤ n) (i : Fin n) :
    right i ≠ i := by
  intro h
  have := congrArg Fin.val h
  simp only [right_val] at this
  have hi := i.isLt
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at this
    omega
  · rw [show i.val + 1 = n by omega, Nat.mod_self] at this
    omega

private lemma right_ne_left_cycletypes {n : Nat} (hn : 4 ≤ n) (i : Fin n) :
    right i ≠ left i := by
  intro h
  have := congrArg Fin.val h
  simp only [right_val, left_val] at this
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · by_cases hlt : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hlt] at this
      rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at this
      omega
    · rw [show i.val + 1 = n by omega, Nat.mod_self] at this
      rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at this
      omega

theorem GoodCycle.stepDir_eq_cw_of_eq_right (gc : GoodCycle sys)
    {k : Fin gc.configs.length}
    (h : gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k)) :
    gc.stepDir k = .cw := by
  unfold GoodCycle.stepDir
  simp [h]

theorem GoodCycle.stepDir_eq_stay_of_eq_self (gc : GoodCycle sys)
    {k : Fin gc.configs.length}
    (h : gc.moverAt (nextIndex gc.configs k) = gc.moverAt k) :
    gc.stepDir k = .stay := by
  unfold GoodCycle.stepDir
  have hcw : gc.moverAt k ≠ right (gc.moverAt k) := by
    intro hright
    exact right_ne_self_cycletypes sys.rs.n_ge_4 (gc.moverAt k) hright.symm
  simp [h, hcw]

theorem GoodCycle.stepDir_eq_ccw_of_eq_left (gc : GoodCycle sys)
    {k : Fin gc.configs.length}
    (h : gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k)) :
    gc.stepDir k = .ccw := by
  unfold GoodCycle.stepDir
  have hcw : left (gc.moverAt k) ≠ right (gc.moverAt k) := by
    intro hright
    exact right_ne_left_cycletypes sys.rs.n_ge_4 (gc.moverAt k) hright.symm
  have hstay : left (gc.moverAt k) ≠ gc.moverAt k := by
    intro hself
    exact left_ne_self_cycletypes sys.rs.n_ge_4 (gc.moverAt k) hself
  simp [h, hcw, hstay]

theorem GoodCycle.stepDir_cases (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    gc.stepDir k = .cw ∨ gc.stepDir k = .stay ∨ gc.stepDir k = .ccw := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · right
    right
    exact gc.stepDir_eq_ccw_of_eq_left hleft
  · right
    left
    exact gc.stepDir_eq_stay_of_eq_self hself
  · left
    exact gc.stepDir_eq_cw_of_eq_right hright

theorem GoodCycle.eq_right_of_stepDir_eq_cw (gc : GoodCycle sys)
    {k : Fin gc.configs.length}
    (h : gc.stepDir k = .cw) :
    gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k) := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · have hccw : gc.stepDir k = .ccw := gc.stepDir_eq_ccw_of_eq_left hleft
    rw [hccw] at h
    cases h
  · have hstay : gc.stepDir k = .stay := gc.stepDir_eq_stay_of_eq_self hself
    rw [hstay] at h
    cases h
  · exact hright

theorem GoodCycle.eq_self_of_stepDir_eq_stay (gc : GoodCycle sys)
    {k : Fin gc.configs.length}
    (h : gc.stepDir k = .stay) :
    gc.moverAt (nextIndex gc.configs k) = gc.moverAt k := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · have hccw : gc.stepDir k = .ccw := gc.stepDir_eq_ccw_of_eq_left hleft
    rw [hccw] at h
    cases h
  · exact hself
  · have hcw : gc.stepDir k = .cw := gc.stepDir_eq_cw_of_eq_right hright
    rw [hcw] at h
    cases h

theorem GoodCycle.eq_left_of_stepDir_eq_ccw (gc : GoodCycle sys)
    {k : Fin gc.configs.length}
    (h : gc.stepDir k = .ccw) :
    gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · exact hleft
  · have hstay : gc.stepDir k = .stay := gc.stepDir_eq_stay_of_eq_self hself
    rw [hstay] at h
    cases h
  · have hcw : gc.stepDir k = .cw := gc.stepDir_eq_cw_of_eq_right hright
    rw [hcw] at h
    cases h

theorem GoodCycle.uniformCW_implies_sameDirectionCW (gc : GoodCycle sys)
    (hCW : gc.uniformCW) :
    gc.sameDirectionCW := by
  intro k
  rw [gc.stepDir_eq_cw_of_eq_right (hCW k)]
  decide

theorem GoodCycle.uniformCCW_implies_sameDirectionCCW (gc : GoodCycle sys)
    (hCCW : gc.uniformCCW) :
    gc.sameDirectionCCW := by
  intro k
  rw [gc.stepDir_eq_ccw_of_eq_left (hCCW k)]
  decide

theorem GoodCycle.uniformDirection_implies_noReversal (gc : GoodCycle sys)
    (hdir : gc.uniformDirection) :
    gc.noReversal := by
  rcases hdir with hCW | hCCW
  · exact Or.inl (gc.uniformCW_implies_sameDirectionCW hCW)
  · exact Or.inr (gc.uniformCCW_implies_sameDirectionCCW hCCW)

theorem GoodCycle.stepCount_partition (gc : GoodCycle sys) :
    gc.cwStepCount + gc.stayStepCount + gc.ccwStepCount = gc.configs.length := by
  unfold GoodCycle.cwStepCount GoodCycle.stayStepCount GoodCycle.ccwStepCount
  calc
    (∑ k : Fin gc.configs.length, if gc.stepDir k = .cw then 1 else 0) +
        (∑ k : Fin gc.configs.length, if gc.stepDir k = .stay then 1 else 0) +
        (∑ k : Fin gc.configs.length, if gc.stepDir k = .ccw then 1 else 0)
      = ∑ k : Fin gc.configs.length,
          ((if gc.stepDir k = .cw then 1 else 0) +
            (if gc.stepDir k = .stay then 1 else 0) +
            (if gc.stepDir k = .ccw then 1 else 0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ∑ _k : Fin gc.configs.length, 1 := by
          apply Finset.sum_congr rfl
          intro k _
          rcases gc.stepDir_cases k with hcw | hstay | hccw
          · simp [hcw]
          · simp [hstay]
          · simp [hccw]
    _ = gc.configs.length := by simp

theorem GoodCycle.signedStep_eq_stepDir (gc : GoodCycle sys)
    (k : Fin gc.configs.length) :
    signedStep sys.rs.n (gc.moverAt k) (gc.moverAt (nextIndex gc.configs k)) =
      match gc.stepDir k with
      | .cw => 1
      | .stay => 0
      | .ccw => -1 := by
  rcases gc.stepDir_cases k with hcw | hstay | hccw
  · rw [hcw]
    simpa [gc.eq_right_of_stepDir_eq_cw hcw] using signedStep_right (gc.moverAt k)
  · rw [hstay]
    simpa [gc.eq_self_of_stepDir_eq_stay hstay] using
      signedStep_self sys.rs.n_ge_4 (gc.moverAt k)
  · rw [hccw]
    simpa [gc.eq_left_of_stepDir_eq_ccw hccw] using
      signedStep_left sys.rs.n_ge_4 (gc.moverAt k)

theorem GoodCycle.totalDisplacement_eq_cwStepCount_sub_ccwStepCount (gc : GoodCycle sys) :
    totalDisplacement gc = gc.cwStepCount - gc.ccwStepCount := by
  rw [LeanMn.totalDisplacement_eq_moverAt_sum]
  calc
    ∑ k : Fin gc.configs.length,
        signedStep sys.rs.n (gc.moverAt k) (gc.moverAt (nextIndex gc.configs k))
      = ∑ k : Fin gc.configs.length,
          match gc.stepDir k with
          | .cw => (1 : Int)
          | .stay => 0
          | .ccw => -1 := by
            apply Finset.sum_congr rfl
            intro k _
            exact gc.signedStep_eq_stepDir k
    _ = ∑ k : Fin gc.configs.length,
          ((if gc.stepDir k = .cw then (1 : Int) else 0) -
            (if gc.stepDir k = .ccw then (1 : Int) else 0)) := by
            apply Finset.sum_congr rfl
            intro k _
            rcases gc.stepDir_cases k with hcw | hstay | hccw
            · simp [hcw]
            · simp [hstay]
            · simp [hccw]
    _ = (∑ k : Fin gc.configs.length, if gc.stepDir k = .cw then (1 : Int) else 0) -
          ∑ k : Fin gc.configs.length, if gc.stepDir k = .ccw then (1 : Int) else 0 := by
            rw [Finset.sum_sub_distrib]
    _ = gc.cwStepCount - gc.ccwStepCount := by
          simp [GoodCycle.cwStepCount, GoodCycle.ccwStepCount]

theorem GoodCycle.cwStepCount_eq_ccwStepCount_of_zeroWinding (gc : GoodCycle sys)
    (hzero : gc.zeroWinding) :
    gc.cwStepCount = gc.ccwStepCount := by
  unfold GoodCycle.zeroWinding at hzero
  rw [gc.totalDisplacement_eq_cwStepCount_sub_ccwStepCount] at hzero
  omega

theorem GoodCycle.ccwStepCount_eq_zero_of_sameDirectionCW (gc : GoodCycle sys)
    (hdir : gc.sameDirectionCW) :
    gc.ccwStepCount = 0 := by
  unfold GoodCycle.ccwStepCount
  refine Finset.sum_eq_zero ?_
  intro k _
  have hk : gc.stepDir k ≠ .ccw := hdir k
  by_cases hstep : gc.stepDir k = .ccw
  · exact False.elim (hk hstep)
  · simp [hstep]

theorem GoodCycle.cwStepCount_eq_zero_of_sameDirectionCCW (gc : GoodCycle sys)
    (hdir : gc.sameDirectionCCW) :
    gc.cwStepCount = 0 := by
  unfold GoodCycle.cwStepCount
  refine Finset.sum_eq_zero ?_
  intro k _
  have hk : gc.stepDir k ≠ .cw := hdir k
  by_cases hstep : gc.stepDir k = .cw
  · exact False.elim (hk hstep)
  · simp [hstep]

theorem GoodCycle.stepCounts_eq_zero_of_noReversal_and_zeroWinding (gc : GoodCycle sys)
    (hnr : gc.noReversal) (hzero : gc.zeroWinding) :
    gc.cwStepCount = 0 ∧ gc.ccwStepCount = 0 := by
  have heq : gc.cwStepCount = gc.ccwStepCount := gc.cwStepCount_eq_ccwStepCount_of_zeroWinding hzero
  rcases hnr with hcw | hccw
  · have hccw0 : gc.ccwStepCount = 0 := gc.ccwStepCount_eq_zero_of_sameDirectionCW hcw
    exact ⟨by simpa [hccw0] using heq, hccw0⟩
  · have hcw0 : gc.cwStepCount = 0 := gc.cwStepCount_eq_zero_of_sameDirectionCCW hccw
    exact ⟨hcw0, by simpa [hcw0] using heq.symm⟩

theorem GoodCycle.stayStepCount_eq_length_of_noReversal_and_zeroWinding (gc : GoodCycle sys)
    (hnr : gc.noReversal) (hzero : gc.zeroWinding) :
    gc.stayStepCount = gc.configs.length := by
  rcases gc.stepCounts_eq_zero_of_noReversal_and_zeroWinding hnr hzero with ⟨hcw, hccw⟩
  rw [← gc.stepCount_partition, hcw, hccw]
  omega

theorem GoodCycle.not_reversalAt_of_sameDirectionCW (gc : GoodCycle sys)
    (hdir : gc.sameDirectionCW) (k : Fin gc.configs.length) :
    ¬gc.reversalAt k := by
  unfold GoodCycle.reversalAt StepDir.reverses
  intro hrev
  cases hstep : gc.stepDir k <;> cases hnext : gc.stepDir (nextIndex gc.configs k) <;> simp [hstep, hnext] at hrev
  · exact hdir (nextIndex gc.configs k) hnext
  · exact hdir k hstep

theorem GoodCycle.not_reversalAt_of_sameDirectionCCW (gc : GoodCycle sys)
    (hdir : gc.sameDirectionCCW) (k : Fin gc.configs.length) :
    ¬gc.reversalAt k := by
  unfold GoodCycle.reversalAt StepDir.reverses
  intro hrev
  cases hstep : gc.stepDir k <;> cases hnext : gc.stepDir (nextIndex gc.configs k) <;> simp [hstep, hnext] at hrev
  · exact hdir k hstep
  · exact hdir (nextIndex gc.configs k) hnext

theorem GoodCycle.reversalCount_eq_zero_of_noReversal (gc : GoodCycle sys)
    (hnr : gc.noReversal) :
    gc.reversalCount = 0 := by
  unfold GoodCycle.reversalCount
  apply Finset.card_eq_zero.mpr
  ext k
  simp [mem_reversalSteps_iff]
  rcases hnr with hcw | hccw
  · exact gc.not_reversalAt_of_sameDirectionCW hcw k
  · exact gc.not_reversalAt_of_sameDirectionCCW hccw k

private theorem hasBinary_of_hasGe3Binary (h3bin : hasGe3Binary sys.rs) :
    ∃ p : Fin sys.rs.n, isBinary sys.rs p := by
  unfold hasGe3Binary binaryCount at h3bin
  have hpos :
      0 < (Finset.univ.filter (fun i : Fin sys.rs.n => sys.rs.m i = 2)).card := by
    omega
  rcases Finset.card_pos.mp hpos with ⟨p, hp⟩
  exact ⟨p, by simpa using Finset.mem_filter.mp hp |>.2⟩

theorem GoodCycle.fireCount_eq_sum_moverAt (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.fireCount p = ∑ k : Fin gc.configs.length, if gc.moverAt k = p then (1 : Nat) else 0 := by
  rw [GoodCycle.fireCount, GoodCycle.prefixFireCount, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [gc.fireIndicator_of_lt p k.isLt]

/-- Count how often processor `p` fires and the next mover is clockwise. -/
noncomputable def GoodCycle.cwMoveCountAt (gc : GoodCycle sys) (p : Fin sys.rs.n) : Nat :=
  ∑ k : Fin gc.configs.length, if gc.moverAt k = p ∧ gc.stepDir k = .cw then 1 else 0

/-- Count how often processor `p` fires and remains the next mover. -/
noncomputable def GoodCycle.stayMoveCountAt (gc : GoodCycle sys) (p : Fin sys.rs.n) : Nat :=
  ∑ k : Fin gc.configs.length, if gc.moverAt k = p ∧ gc.stepDir k = .stay then 1 else 0

/-- Count how often processor `p` fires and the next mover is counterclockwise. -/
noncomputable def GoodCycle.ccwMoveCountAt (gc : GoodCycle sys) (p : Fin sys.rs.n) : Nat :=
  ∑ k : Fin gc.configs.length, if gc.moverAt k = p ∧ gc.stepDir k = .ccw then 1 else 0

theorem GoodCycle.fireCount_eq_moveCount_partition (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.cwMoveCountAt p + gc.stayMoveCountAt p + gc.ccwMoveCountAt p = gc.fireCount p := by
  rw [gc.fireCount_eq_sum_moverAt p]
  unfold GoodCycle.cwMoveCountAt GoodCycle.stayMoveCountAt GoodCycle.ccwMoveCountAt
  calc
    (∑ k : Fin gc.configs.length, if gc.moverAt k = p ∧ gc.stepDir k = .cw then 1 else 0) +
        (∑ k : Fin gc.configs.length, if gc.moverAt k = p ∧ gc.stepDir k = .stay then 1 else 0) +
        (∑ k : Fin gc.configs.length, if gc.moverAt k = p ∧ gc.stepDir k = .ccw then 1 else 0)
      = ∑ k : Fin gc.configs.length,
          ((if gc.moverAt k = p ∧ gc.stepDir k = .cw then 1 else 0) +
            (if gc.moverAt k = p ∧ gc.stepDir k = .stay then 1 else 0) +
            (if gc.moverAt k = p ∧ gc.stepDir k = .ccw then 1 else 0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ∑ k : Fin gc.configs.length, if gc.moverAt k = p then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hm : gc.moverAt k = p
          · rcases gc.stepDir_cases k with hcw | hstay | hccw
            · simp [hm, hcw]
            · simp [hm, hstay]
            · simp [hm, hccw]
          · simp [hm]

theorem GoodCycle.nextMover_eq_iff (gc : GoodCycle sys)
    (k : Fin gc.configs.length) (p : Fin sys.rs.n) :
    gc.moverAt (nextIndex gc.configs k) = p ↔
      (gc.moverAt k = left p ∧ gc.stepDir k = .cw) ∨
        (gc.moverAt k = p ∧ gc.stepDir k = .stay) ∨
          (gc.moverAt k = right p ∧ gc.stepDir k = .ccw) := by
  constructor
  · intro hnext
    rcases gc.stepDir_cases k with hcw | hstay | hccw
    · left
      refine ⟨?_, hcw⟩
      have hright : right (gc.moverAt k) = p := by
        calc
          right (gc.moverAt k) = gc.moverAt (nextIndex gc.configs k) := by
            symm
            exact gc.eq_right_of_stepDir_eq_cw hcw
          _ = p := hnext
      calc
        gc.moverAt k = left (right (gc.moverAt k)) := by
          symm
          simpa using (left_right_eq_self (gc.moverAt k))
        _ = left p := by rw [hright]
    · right
      left
      refine ⟨?_, hstay⟩
      calc
        gc.moverAt k = gc.moverAt (nextIndex gc.configs k) := by
          symm
          exact gc.eq_self_of_stepDir_eq_stay hstay
        _ = p := hnext
    · right
      right
      refine ⟨?_, hccw⟩
      have hleft : left (gc.moverAt k) = p := by
        calc
          left (gc.moverAt k) = gc.moverAt (nextIndex gc.configs k) := by
            symm
            exact gc.eq_left_of_stepDir_eq_ccw hccw
          _ = p := hnext
      calc
        gc.moverAt k = right (left (gc.moverAt k)) := by
          symm
          simpa using (right_left_eq_self (gc.moverAt k))
        _ = right p := by rw [hleft]
  · intro h
    rcases h with hcw | hstay | hccw
    · calc
        gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k) := gc.eq_right_of_stepDir_eq_cw hcw.2
        _ = right (left p) := by rw [hcw.1]
        _ = p := by simpa using (right_left_eq_self p)
    · simpa [hstay.1] using gc.eq_self_of_stepDir_eq_stay hstay.2
    · calc
        gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) := gc.eq_left_of_stepDir_eq_ccw hccw.2
        _ = left (right p) := by rw [hccw.1]
        _ = p := by simpa using (left_right_eq_self p)

theorem GoodCycle.fireCount_eq_entryMoveCount_partition (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.cwMoveCountAt (left p) + gc.stayMoveCountAt p + gc.ccwMoveCountAt (right p) =
      gc.fireCount p := by
  rw [gc.fireCount_eq_sum_moverAt p]
  unfold GoodCycle.cwMoveCountAt GoodCycle.stayMoveCountAt GoodCycle.ccwMoveCountAt
  calc
    (∑ k : Fin gc.configs.length, if gc.moverAt k = left p ∧ gc.stepDir k = .cw then 1 else 0) +
        (∑ k : Fin gc.configs.length, if gc.moverAt k = p ∧ gc.stepDir k = .stay then 1 else 0) +
        (∑ k : Fin gc.configs.length, if gc.moverAt k = right p ∧ gc.stepDir k = .ccw then 1 else 0)
      = ∑ k : Fin gc.configs.length,
          ((if gc.moverAt k = left p ∧ gc.stepDir k = .cw then 1 else 0) +
            (if gc.moverAt k = p ∧ gc.stepDir k = .stay then 1 else 0) +
            (if gc.moverAt k = right p ∧ gc.stepDir k = .ccw then 1 else 0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ∑ k : Fin gc.configs.length, if gc.moverAt (nextIndex gc.configs k) = p then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hnext : gc.moverAt (nextIndex gc.configs k) = p
          · rcases (gc.nextMover_eq_iff k p).mp hnext with hcw | hstay | hccw
            · simp [hnext, hcw]
            · simp [hnext, hstay]
            · simp [hnext, hccw]
          · rcases gc.stepDir_cases k with hcw | hstay | hccw
            · have hm : gc.moverAt k ≠ left p := by
                intro hm
                exact hnext ((gc.nextMover_eq_iff k p).mpr (Or.inl ⟨hm, hcw⟩))
              simp [hnext, hcw, hm]
            · have hm : gc.moverAt k ≠ p := by
                intro hm
                exact hnext ((gc.nextMover_eq_iff k p).mpr (Or.inr (Or.inl ⟨hm, hstay⟩)))
              simp [hnext, hstay, hm]
            · have hm : gc.moverAt k ≠ right p := by
                intro hm
                exact hnext ((gc.nextMover_eq_iff k p).mpr (Or.inr (Or.inr ⟨hm, hccw⟩)))
              simp [hnext, hccw, hm]
    _ = ∑ k : Fin gc.configs.length, if gc.moverAt k = p then 1 else 0 := by
          simpa using
            (Fintype.sum_bijective (nextIndex gc.configs) (nextIndex_bijective gc.configs)
              (fun k => if gc.moverAt (nextIndex gc.configs k) = p then (1 : Nat) else 0)
              (fun k => if gc.moverAt k = p then (1 : Nat) else 0)
              (fun k => rfl))

theorem GoodCycle.outgoingMoveCount_eq_incomingMoveCount (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.cwMoveCountAt p + gc.ccwMoveCountAt p =
      gc.cwMoveCountAt (left p) + gc.ccwMoveCountAt (right p) := by
  have hcurr := gc.fireCount_eq_moveCount_partition p
  have hprev := gc.fireCount_eq_entryMoveCount_partition p
  omega

noncomputable def GoodCycle.edgeNetFlow (gc : GoodCycle sys) (p : Fin sys.rs.n) : Int :=
  (gc.cwMoveCountAt p : Int) - gc.ccwMoveCountAt (right p)

theorem GoodCycle.edgeNetFlow_eq_left (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.edgeNetFlow p = gc.edgeNetFlow (left p) := by
  have hrl : gc.ccwMoveCountAt (right (left p)) = gc.ccwMoveCountAt p := by
    simpa using congrArg gc.ccwMoveCountAt (right_left_eq_self p)
  unfold GoodCycle.edgeNetFlow
  rw [hrl]
  have hbal := gc.outgoingMoveCount_eq_incomingMoveCount p
  omega

private theorem sum_cwMoveIndicator (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    (∑ p : Fin sys.rs.n, if gc.moverAt k = p ∧ gc.stepDir k = .cw then 1 else 0) =
      if gc.stepDir k = .cw then 1 else 0 := by
  by_cases hcw : gc.stepDir k = .cw
  · rw [if_pos hcw]
    rw [Finset.sum_eq_single (gc.moverAt k)]
    · simp [hcw]
    · intro p _ hp
      have hne : gc.moverAt k ≠ p := by
        intro h
        exact hp h.symm
      simp [hne, hcw]
    · intro hmem
      simp at hmem
  · rw [if_neg hcw]
    refine Finset.sum_eq_zero ?_
    intro p _
    simp [hcw]

private theorem sum_ccwMoveIndicator (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    (∑ p : Fin sys.rs.n, if gc.moverAt k = p ∧ gc.stepDir k = .ccw then 1 else 0) =
      if gc.stepDir k = .ccw then 1 else 0 := by
  by_cases hccw : gc.stepDir k = .ccw
  · rw [if_pos hccw]
    rw [Finset.sum_eq_single (gc.moverAt k)]
    · simp [hccw]
    · intro p _ hp
      have hne : gc.moverAt k ≠ p := by
        intro h
        exact hp h.symm
      simp [hne, hccw]
    · intro hmem
      simp at hmem
  · rw [if_neg hccw]
    refine Finset.sum_eq_zero ?_
    intro p _
    simp [hccw]

theorem GoodCycle.cwStepCount_eq_sum_cwMoveCountAt (gc : GoodCycle sys) :
    gc.cwStepCount = ∑ p : Fin sys.rs.n, gc.cwMoveCountAt p := by
  unfold GoodCycle.cwStepCount GoodCycle.cwMoveCountAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  symm
  exact sum_cwMoveIndicator gc k

theorem GoodCycle.ccwStepCount_eq_sum_ccwMoveCountAt (gc : GoodCycle sys) :
    gc.ccwStepCount = ∑ p : Fin sys.rs.n, gc.ccwMoveCountAt p := by
  unfold GoodCycle.ccwStepCount GoodCycle.ccwMoveCountAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  symm
  exact sum_ccwMoveIndicator gc k

theorem GoodCycle.totalDisplacement_eq_sum_edgeNetFlow (gc : GoodCycle sys) :
    totalDisplacement gc = ∑ p : Fin sys.rs.n, gc.edgeNetFlow p := by
  have hright_bij : Function.Bijective (@right sys.rs.n) := by
    constructor
    · intro a b hab
      simpa using congrArg left hab
    · intro b
      exact ⟨left b, by simpa using (right_left_eq_self b)⟩
  calc
    totalDisplacement gc
      = ((∑ p : Fin sys.rs.n, gc.cwMoveCountAt p : Nat) : Int) -
          ∑ p : Fin sys.rs.n, gc.ccwMoveCountAt p := by
            rw [gc.totalDisplacement_eq_cwStepCount_sub_ccwStepCount,
              gc.cwStepCount_eq_sum_cwMoveCountAt,
              gc.ccwStepCount_eq_sum_ccwMoveCountAt]
    _ = (∑ p : Fin sys.rs.n, (gc.cwMoveCountAt p : Int)) -
          ∑ p : Fin sys.rs.n, (gc.ccwMoveCountAt p : Int) := by
            simp
    _ = (∑ p : Fin sys.rs.n, (gc.cwMoveCountAt p : Int)) -
          ∑ p : Fin sys.rs.n, (gc.ccwMoveCountAt (right p) : Int) := by
            congr 1
            symm
            simpa using
              (Fintype.sum_bijective right hright_bij
                (fun p => (gc.ccwMoveCountAt (right p) : Int))
                (fun p => (gc.ccwMoveCountAt p : Int))
                (fun p => rfl))
    _ = ∑ p : Fin sys.rs.n, gc.edgeNetFlow p := by
          unfold GoodCycle.edgeNetFlow
          rw [Finset.sum_sub_distrib]

private theorem fireCount_eq_left_of_uniformCW (gc : GoodCycle sys)
    (hCW : gc.uniformCW) (p : Fin sys.rs.n) :
    gc.fireCount p = gc.fireCount (left p) := by
  rw [gc.fireCount_eq_sum_moverAt p, gc.fireCount_eq_sum_moverAt (left p)]
  calc
    (∑ k : Fin gc.configs.length, if gc.moverAt k = p then (1 : Nat) else 0)
        = ∑ k : Fin gc.configs.length,
            if gc.moverAt (nextIndex gc.configs k) = p then (1 : Nat) else 0 := by
            symm
            simpa using
              (Fintype.sum_bijective (nextIndex gc.configs) (nextIndex_bijective gc.configs)
                (fun k => if gc.moverAt (nextIndex gc.configs k) = p then (1 : Nat) else 0)
                (fun k => if gc.moverAt k = p then (1 : Nat) else 0)
                (fun k => rfl))
    _ = (∑ k : Fin gc.configs.length, if gc.moverAt k = left p then (1 : Nat) else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          have hiff : gc.moverAt (nextIndex gc.configs k) = p ↔ gc.moverAt k = left p := by
            rw [hCW k]
            constructor
            · intro h
              calc
                gc.moverAt k = left (right (gc.moverAt k)) := by
                  symm
                  simpa using (left_right_eq_self (gc.moverAt k))
                _ = left p := by rw [h]
            · intro h
              calc
                right (gc.moverAt k) = right (left p) := by rw [h]
                _ = p := by simpa using (right_left_eq_self p)
          by_cases hk : gc.moverAt k = left p
          · simp [hk, hiff.mpr hk]
          · have hk' : ¬gc.moverAt (nextIndex gc.configs k) = p := by
              intro hnext
              exact hk (hiff.mp hnext)
            simp [hk, hk']

private theorem fireCount_eq_right_of_uniformCCW (gc : GoodCycle sys)
    (hCCW : gc.uniformCCW) (p : Fin sys.rs.n) :
    gc.fireCount p = gc.fireCount (right p) := by
  rw [gc.fireCount_eq_sum_moverAt p, gc.fireCount_eq_sum_moverAt (right p)]
  calc
    (∑ k : Fin gc.configs.length, if gc.moverAt k = p then (1 : Nat) else 0)
        = ∑ k : Fin gc.configs.length,
            if gc.moverAt (nextIndex gc.configs k) = p then (1 : Nat) else 0 := by
            symm
            simpa using
              (Fintype.sum_bijective (nextIndex gc.configs) (nextIndex_bijective gc.configs)
                (fun k => if gc.moverAt (nextIndex gc.configs k) = p then (1 : Nat) else 0)
                (fun k => if gc.moverAt k = p then (1 : Nat) else 0)
                (fun k => rfl))
    _ = (∑ k : Fin gc.configs.length, if gc.moverAt k = right p then (1 : Nat) else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          have hiff : gc.moverAt (nextIndex gc.configs k) = p ↔ gc.moverAt k = right p := by
            rw [hCCW k]
            constructor
            · intro h
              calc
                gc.moverAt k = right (left (gc.moverAt k)) := by
                  symm
                  simpa using (right_left_eq_self (gc.moverAt k))
                _ = right p := by rw [h]
            · intro h
              calc
                left (gc.moverAt k) = left (right p) := by rw [h]
                _ = p := by simpa using (left_right_eq_self p)
          by_cases hk : gc.moverAt k = right p
          · simp [hk, hiff.mpr hk]
          · have hk' : ¬gc.moverAt (nextIndex gc.configs k) = p := by
              intro hnext
              exact hk (hiff.mp hnext)
            simp [hk, hk']

private def advance (p : Fin sys.rs.n) (d : Nat) : Fin sys.rs.n :=
  ⟨(p.val + d) % sys.rs.n, Nat.mod_lt _ (by
    have hn := sys.rs.n_ge_4
    omega)⟩

@[simp] private theorem advance_zero (p : Fin sys.rs.n) :
    advance p 0 = p := by
  ext
  simp [advance, Nat.mod_eq_of_lt p.isLt]

@[simp] private theorem advance_succ (p : Fin sys.rs.n) (d : Nat) :
    advance p (d + 1) = right (advance p d) := by
  ext
  simp [advance, right_val]
  rw [show p.val + (d + 1) = (p.val + d) + 1 by omega]

private theorem exists_advance_eq (p q : Fin sys.rs.n) :
    ∃ d, advance p d = q := by
  by_cases hpq : p.val ≤ q.val
  · refine ⟨q.val - p.val, ?_⟩
    ext
    have hs : p.val + (q.val - p.val) = q.val := by omega
    simp [advance]
    rw [hs, Nat.mod_eq_of_lt q.isLt]
  · refine ⟨q.val + sys.rs.n - p.val, ?_⟩
    ext
    have hs : p.val + (q.val + sys.rs.n - p.val) = q.val + sys.rs.n := by omega
    simp [advance]
    rw [hs, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]

theorem GoodCycle.edgeNetFlow_constant (gc : GoodCycle sys)
    (p q : Fin sys.rs.n) :
    gc.edgeNetFlow q = gc.edgeNetFlow p := by
  rcases exists_advance_eq p q with ⟨d, hq⟩
  subst hq
  induction d with
  | zero =>
      simp [advance_zero]
  | succ d ih =>
      rw [advance_succ]
      have hstep :
          gc.edgeNetFlow (right (advance p d)) = gc.edgeNetFlow (advance p d) := by
        simpa using gc.edgeNetFlow_eq_left (right (advance p d))
      exact hstep.trans ih

theorem GoodCycle.totalDisplacement_eq_n_mul_edgeNetFlow (gc : GoodCycle sys)
    (p : Fin sys.rs.n) :
    totalDisplacement gc = (sys.rs.n : Int) * gc.edgeNetFlow p := by
  calc
    totalDisplacement gc = ∑ q : Fin sys.rs.n, gc.edgeNetFlow q :=
      gc.totalDisplacement_eq_sum_edgeNetFlow
    _ = ∑ _q : Fin sys.rs.n, gc.edgeNetFlow p := by
          apply Finset.sum_congr rfl
          intro q _
          exact gc.edgeNetFlow_constant p q
    _ = (sys.rs.n : Int) * gc.edgeNetFlow p := by
          simp

theorem GoodCycle.edgeNetFlow_natAbs_eq_one_of_isOddWinding (gc : GoodCycle sys)
    (hodd : gc.isOddWinding) (p : Fin sys.rs.n) :
    Int.natAbs (gc.edgeNetFlow p) = 1 := by
  unfold GoodCycle.isOddWinding at hodd
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow p, Int.natAbs_mul] at hodd
  have hnpos : 0 < sys.rs.n := by
    have hn := sys.rs.n_ge_4
    omega
  have hodd' : sys.rs.n * Int.natAbs (gc.edgeNetFlow p) = sys.rs.n * 1 := by
    simpa using hodd
  exact Nat.eq_of_mul_eq_mul_left hnpos hodd'

theorem GoodCycle.edgeNetFlow_eq_zero_of_zeroWinding (gc : GoodCycle sys)
    (hzero : gc.zeroWinding) (p : Fin sys.rs.n) :
    gc.edgeNetFlow p = 0 := by
  unfold GoodCycle.zeroWinding at hzero
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow p] at hzero
  obtain hlen | hflow := Int.mul_eq_zero.mp hzero
  · norm_num at hlen
    have hn := sys.rs.n_ge_4
    omega
  · exact hflow

theorem GoodCycle.edgeNetFlow_eq_one_or_neg_one_of_isOddWinding (gc : GoodCycle sys)
    (hodd : gc.isOddWinding) (p : Fin sys.rs.n) :
    gc.edgeNetFlow p = 1 ∨ gc.edgeNetFlow p = -1 := by
  have hflow : Int.natAbs (gc.edgeNetFlow p) = 1 :=
    gc.edgeNetFlow_natAbs_eq_one_of_isOddWinding hodd p
  rw [Int.natAbs_eq_iff] at hflow
  simpa [Nat.cast_one] using hflow

theorem fireCount_constant_of_uniformCW (gc : GoodCycle sys)
    (hCW : gc.uniformCW) (p q : Fin sys.rs.n) :
    gc.fireCount q = gc.fireCount p := by
  rcases exists_advance_eq p q with ⟨d, hq⟩
  subst hq
  induction d with
  | zero =>
      simp [advance_zero]
  | succ d ih =>
      rw [advance_succ, fireCount_eq_left_of_uniformCW gc hCW]
      simpa using ih

theorem fireCount_constant_of_uniformCCW (gc : GoodCycle sys)
    (hCCW : gc.uniformCCW) (p q : Fin sys.rs.n) :
    gc.fireCount q = gc.fireCount p := by
  rcases exists_advance_eq p q with ⟨d, hq⟩
  subst hq
  induction d with
  | zero =>
      simp [advance_zero]
  | succ d ih =>
      rw [advance_succ]
      calc
        gc.fireCount (right (advance p d)) = gc.fireCount (advance p d) := by
          symm
          exact fireCount_eq_right_of_uniformCCW gc hCCW (advance p d)
        _ = gc.fireCount p := ih

/-- A uniform clockwise mover word contributes `+1` at every step. -/
theorem GoodCycle.totalDisplacement_eq_length_of_uniformCW (gc : GoodCycle sys)
    (hCW : gc.uniformCW) :
    totalDisplacement gc = gc.configs.length := by
  rw [LeanMn.totalDisplacement_eq_moverAt_sum]
  have hs :
      ∀ k : Fin gc.configs.length,
        signedStep sys.rs.n (gc.moverAt k) (gc.moverAt (nextIndex gc.configs k)) = 1 := by
    intro k
    simpa [hCW k] using signedStep_right (gc.moverAt k)
  simp [hs]

/-- A uniform counterclockwise mover word contributes `-1` at every step. -/
theorem GoodCycle.totalDisplacement_eq_neg_length_of_uniformCCW (gc : GoodCycle sys)
    (hCCW : gc.uniformCCW) :
    totalDisplacement gc = -((gc.configs.length : Nat) : Int) := by
  rw [LeanMn.totalDisplacement_eq_moverAt_sum]
  have hs :
      ∀ k : Fin gc.configs.length,
        signedStep sys.rs.n (gc.moverAt k) (gc.moverAt (nextIndex gc.configs k)) = -1 := by
    intro k
    simpa [hCCW k] using signedStep_left sys.rs.n_ge_4 (gc.moverAt k)
  simp [hs]

private theorem length_eq_n_of_uniformCW_isOddWinding (gc : GoodCycle sys)
    (hCW : gc.uniformCW) (hodd : gc.isOddWinding) :
    gc.configs.length = sys.rs.n := by
  unfold GoodCycle.isOddWinding at hodd
  rw [gc.totalDisplacement_eq_length_of_uniformCW hCW] at hodd
  simpa using hodd

private theorem length_eq_n_of_uniformCCW_isOddWinding (gc : GoodCycle sys)
    (hCCW : gc.uniformCCW) (hodd : gc.isOddWinding) :
    gc.configs.length = sys.rs.n := by
  unfold GoodCycle.isOddWinding at hodd
  rw [gc.totalDisplacement_eq_neg_length_of_uniformCCW hCCW, Int.natAbs_neg] at hodd
  simpa using hodd

private theorem fireCount_eq_one_of_uniformCW_isOddWinding (gc : GoodCycle sys)
    (hCW : gc.uniformCW) (hodd : gc.isOddWinding) (p : Fin sys.rs.n) :
    gc.fireCount p = 1 := by
  have hlen : gc.configs.length = sys.rs.n := length_eq_n_of_uniformCW_isOddWinding gc hCW hodd
  have hconst : ∀ q : Fin sys.rs.n, gc.fireCount q = gc.fireCount p :=
    fun q => fireCount_constant_of_uniformCW gc hCW p q
  have hsum := gc.sum_fireCount
  rw [hlen] at hsum
  have hsum' :
      (∑ q : Fin sys.rs.n, gc.fireCount q) = ∑ q : Fin sys.rs.n, gc.fireCount p := by
    apply Finset.sum_congr rfl
    intro q _
    exact hconst q
  rw [hsum'] at hsum
  have hconstsum : (∑ q : Fin sys.rs.n, gc.fireCount p) = sys.rs.n * gc.fireCount p := by
    simp
  have hsum'' : sys.rs.n * gc.fireCount p = sys.rs.n := by
    simpa [hconstsum] using hsum
  have hnpos : 0 < sys.rs.n := by
    have hn := sys.rs.n_ge_4
    omega
  have hone : gc.fireCount p = 1 := by
    exact Nat.eq_of_mul_eq_mul_left hnpos (by simpa using hsum'')
  exact hone

private theorem fireCount_eq_one_of_uniformCCW_isOddWinding (gc : GoodCycle sys)
    (hCCW : gc.uniformCCW) (hodd : gc.isOddWinding) (p : Fin sys.rs.n) :
    gc.fireCount p = 1 := by
  have hlen : gc.configs.length = sys.rs.n := length_eq_n_of_uniformCCW_isOddWinding gc hCCW hodd
  have hconst : ∀ q : Fin sys.rs.n, gc.fireCount q = gc.fireCount p :=
    fun q => fireCount_constant_of_uniformCCW gc hCCW p q
  have hsum := gc.sum_fireCount
  rw [hlen] at hsum
  have hsum' :
      (∑ q : Fin sys.rs.n, gc.fireCount q) = ∑ q : Fin sys.rs.n, gc.fireCount p := by
    apply Finset.sum_congr rfl
    intro q _
    exact hconst q
  rw [hsum'] at hsum
  have hconstsum : (∑ q : Fin sys.rs.n, gc.fireCount p) = sys.rs.n * gc.fireCount p := by
    simp
  have hsum'' : sys.rs.n * gc.fireCount p = sys.rs.n := by
    simpa [hconstsum] using hsum
  have hnpos : 0 < sys.rs.n := by
    have hn := sys.rs.n_ge_4
    omega
  have hone : gc.fireCount p = 1 := by
    exact Nat.eq_of_mul_eq_mul_left hnpos (by simpa using hsum'')
  exact hone

/-- A same-direction mover word cannot have odd winding once the ring has a
    binary processor: uniform direction would force every processor to fire
    exactly once, contradicting binary parity. -/
theorem GoodCycle.not_uniformDirection_and_isOddWinding_of_hasGe3Binary
    (gc : GoodCycle sys) (h3bin : hasGe3Binary sys.rs) :
    ¬(gc.uniformDirection ∧ gc.isOddWinding) := by
  rcases hasBinary_of_hasGe3Binary (sys := sys) h3bin with ⟨p, hbin⟩
  intro h
  rcases h with ⟨hdir, hodd⟩
  rcases hdir with hCW | hCCW
  · have hfire : gc.fireCount p = 1 := fireCount_eq_one_of_uniformCW_isOddWinding gc hCW hodd p
    have heven : Even (gc.fireCount p) := gc.binary_fireCount_even p hbin
    have : ¬Even 1 := by decide
    exact this (hfire ▸ heven)
  · have hfire : gc.fireCount p = 1 := fireCount_eq_one_of_uniformCCW_isOddWinding gc hCCW hodd p
    have heven : Even (gc.fireCount p) := gc.binary_fireCount_even p hbin
    have : ¬Even 1 := by decide
    exact this (hfire ▸ heven)

/-! ### Edge traversal counting -/

/-- The mover walk crosses edge `{i, i+1}` at step `k`. -/
noncomputable def edgeCrossAt (gc : GoodCycle sys) (i : Fin sys.rs.n) (k : Fin gc.configs.length) : Prop :=
  (gc.moverAt k = i ∧ gc.moverAt (nextIndex gc.configs k) = right i) ∨
    (gc.moverAt k = right i ∧ gc.moverAt (nextIndex gc.configs k) = i)

noncomputable instance (gc : GoodCycle sys) (i : Fin sys.rs.n) (k : Fin gc.configs.length) :
    Decidable (edgeCrossAt gc i k) := by
  unfold edgeCrossAt
  infer_instance

/-- The set of mover-word steps that cross edge `{i, i+1}`. -/
noncomputable def GoodCycle.edgeCrossSteps (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    Finset (Fin gc.configs.length) :=
  Finset.univ.filter (fun k => edgeCrossAt gc i k)

/-- Count how many times the mover walk crosses edge `{i, i+1}`. -/
noncomputable def GoodCycle.edgeTraversalCount (gc : GoodCycle sys) (i : Fin sys.rs.n) : Nat :=
  (gc.edgeCrossSteps i).card

theorem mem_edgeCrossSteps_iff (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (k : Fin gc.configs.length) :
    k ∈ gc.edgeCrossSteps i ↔ edgeCrossAt gc i k := by
  unfold GoodCycle.edgeCrossSteps
  simp

theorem edgeCrossAt_iff_stepDir (gc : GoodCycle sys) (i : Fin sys.rs.n)
    (k : Fin gc.configs.length) :
    edgeCrossAt gc i k ↔
      (gc.moverAt k = i ∧ gc.stepDir k = .cw) ∨
        (gc.moverAt k = right i ∧ gc.stepDir k = .ccw) := by
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
          gc.moverAt (nextIndex gc.configs k) = i := hccw.2
          _ = left (right i) := by simpa using (left_right_eq_self i).symm
      exact gc.stepDir_eq_ccw_of_eq_left hleft
  · intro hstep
    rcases hstep with hcw | hccw
    · left
      refine ⟨hcw.1, ?_⟩
      simpa [hcw.1] using gc.eq_right_of_stepDir_eq_cw hcw.2
    · right
      refine ⟨hccw.1, ?_⟩
      calc
        gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) := gc.eq_left_of_stepDir_eq_ccw hccw.2
        _ = left (right i) := by rw [hccw.1]
        _ = i := by simpa using left_right_eq_self i

theorem GoodCycle.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right
    (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    gc.edgeTraversalCount i = gc.cwMoveCountAt i + gc.ccwMoveCountAt (right i) := by
  unfold GoodCycle.edgeTraversalCount GoodCycle.edgeCrossSteps
    GoodCycle.cwMoveCountAt GoodCycle.ccwMoveCountAt
  calc
    (Finset.univ.filter (fun k => edgeCrossAt gc i k)).card
      = Finset.sum (Finset.univ.filter (fun k => edgeCrossAt gc i k)) (fun _ => (1 : Nat)) := by
          simp
    _ = ∑ k : Fin gc.configs.length, if edgeCrossAt gc i k then 1 else 0 := by simp
    _ = ∑ k : Fin gc.configs.length,
          ((if gc.moverAt k = i ∧ gc.stepDir k = .cw then 1 else 0) +
            (if gc.moverAt k = right i ∧ gc.stepDir k = .ccw then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro k _
            have hdisj :
                ¬((gc.moverAt k = i ∧ gc.stepDir k = .cw) ∧
                  (gc.moverAt k = right i ∧ gc.stepDir k = .ccw)) := by
              intro hboth
              have hneq : (StepDir.cw : StepDir) ≠ .ccw := by decide
              exact hneq (hboth.1.2.symm.trans hboth.2.2)
            by_cases hp : gc.moverAt k = i ∧ gc.stepDir k = .cw
            · have hq : ¬(gc.moverAt k = right i ∧ gc.stepDir k = .ccw) := by
                intro hq
                exact hdisj ⟨hp, hq⟩
              simp [edgeCrossAt_iff_stepDir, hp, hq]
            · by_cases hq : gc.moverAt k = right i ∧ gc.stepDir k = .ccw
              · simp [edgeCrossAt_iff_stepDir, hp, hq]
              · simp [edgeCrossAt_iff_stepDir, hp, hq]
    _ = (∑ k : Fin gc.configs.length, if gc.moverAt k = i ∧ gc.stepDir k = .cw then 1 else 0) +
          ∑ k : Fin gc.configs.length, if gc.moverAt k = right i ∧ gc.stepDir k = .ccw then 1 else 0 := by
            rw [Finset.sum_add_distrib]

/-! ### Signed edge flux: exact CW/CCW move count relations -/

/-- Zero winding implies CW moves at p equal CCW moves at right p, for every edge. -/
theorem GoodCycle.cwMoveCountAt_eq_ccwMoveCountAt_right_of_zeroWinding
    (gc : GoodCycle sys) (hzero : gc.zeroWinding) (p : Fin sys.rs.n) :
    gc.cwMoveCountAt p = gc.ccwMoveCountAt (right p) := by
  have hflow : gc.edgeNetFlow p = 0 := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero p
  unfold GoodCycle.edgeNetFlow at hflow
  omega

/-- Zero winding implies the edge traversal count is exactly twice the CW move count. -/
theorem GoodCycle.edgeTraversalCount_eq_twice_cwMoveCountAt_of_zeroWinding
    (gc : GoodCycle sys) (hzero : gc.zeroWinding) (p : Fin sys.rs.n) :
    gc.edgeTraversalCount p = 2 * gc.cwMoveCountAt p := by
  rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right]
  rw [gc.cwMoveCountAt_eq_ccwMoveCountAt_right_of_zeroWinding hzero]
  omega

/-- Zero winding implies the edge traversal count is exactly twice the CCW move count
    from the right endpoint. -/
theorem GoodCycle.edgeTraversalCount_eq_twice_ccwMoveCountAt_right_of_zeroWinding
    (gc : GoodCycle sys) (hzero : gc.zeroWinding) (p : Fin sys.rs.n) :
    gc.edgeTraversalCount p = 2 * gc.ccwMoveCountAt (right p) := by
  rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right]
  rw [gc.cwMoveCountAt_eq_ccwMoveCountAt_right_of_zeroWinding hzero]
  omega

/-- Odd winding with positive net flow: CW moves = CCW moves from right + 1. -/
theorem GoodCycle.cwMoveCountAt_eq_ccwMoveCountAt_right_succ_of_pos_flow
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hflow : gc.edgeNetFlow p = 1) :
    gc.cwMoveCountAt p = gc.ccwMoveCountAt (right p) + 1 := by
  unfold GoodCycle.edgeNetFlow at hflow
  omega

/-- Odd winding with negative net flow: CCW moves from right = CW moves + 1. -/
theorem GoodCycle.ccwMoveCountAt_right_eq_cwMoveCountAt_succ_of_neg_flow
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hflow : gc.edgeNetFlow p = -1) :
    gc.ccwMoveCountAt (right p) = gc.cwMoveCountAt p + 1 := by
  unfold GoodCycle.edgeNetFlow at hflow
  omega

/-- The edge net flow equals `totalDisplacement / n` (exact integer division). -/
theorem GoodCycle.edgeNetFlow_eq_totalDisplacement_div_n
    (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.edgeNetFlow p * (sys.rs.n : Int) = totalDisplacement gc := by
  rw [gc.totalDisplacement_eq_n_mul_edgeNetFlow p]
  ring

/-- The total cycle length partitions evenly across edges:
    summing traversal counts over all edges gives cwStepCount + ccwStepCount.
    Each CW step crosses exactly one edge in the CW direction, and each CCW step
    crosses exactly one edge in the CCW direction. -/
theorem GoodCycle.sum_edgeTraversalCount
    (gc : GoodCycle sys) :
    (∑ p : Fin sys.rs.n, gc.edgeTraversalCount p) =
      gc.cwStepCount + gc.ccwStepCount := by
  have hrewrite : (∑ p : Fin sys.rs.n, gc.edgeTraversalCount p) =
      ∑ p : Fin sys.rs.n, (gc.cwMoveCountAt p + gc.ccwMoveCountAt (right p)) := by
    apply Finset.sum_congr rfl
    intro p _
    exact gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right p
  rw [hrewrite,
      Finset.sum_add_distrib,
      gc.cwStepCount_eq_sum_cwMoveCountAt,
      gc.ccwStepCount_eq_sum_ccwMoveCountAt]
  congr 1
  have hleft_bij : Function.Bijective (@left sys.rs.n) := by
    constructor
    · intro a b hab
      simpa using congrArg right hab
    · intro b
      exact ⟨right b, by simpa using (left_right_eq_self b)⟩
  have := Fintype.sum_bijective left hleft_bij
      (fun p => gc.ccwMoveCountAt (right (left p)))
      (fun p => gc.ccwMoveCountAt (right p))
      (fun p => rfl)
  simp [show ∀ p : Fin sys.rs.n, right (left p) = p from
    fun p => by simpa using right_left_eq_self p] at this
  exact this.symm

-- NOTE: edgeTraversalCount is NOT generally constant across edges.
-- It is constant for uniform-direction cycles (sweep/uniform CW/CCW),
-- but for general mover words with reversals, different edges can have
-- different traversal counts. The previously-stated edgeTraversalCount_constant
-- theorem was incorrect and has been removed.

end LeanMn
