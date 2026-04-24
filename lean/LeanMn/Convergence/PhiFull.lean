/-
  Convergence/PhiFull.lean — FutureFc (Φ_full) definition + monotonicity

  Defines the maximum frontier count reachable from a configuration via any
  sequence of bad steps. This is non-increasing: every bad step c→c' has
  FutureFc(c') ≤ FutureFc(c), because the set of configs reachable from c'
  is a subset of those reachable from c.
-/
import LeanMn.Convergence.CopyDAG

namespace LeanMn

/-! ### Forward bad step and bad-reachability -/

/-- Forward bad step: `cup2BadStepFwd c c'` means there is a bad step from `c` to `c'`. -/
def cup2BadStepFwd (n : Nat) (hn : 4 ≤ n)
    (c c' : Config (cup2Spec n hn)) : Prop :=
  badStep (cup2System n hn) (cup2GoodCycle n hn) c' c

/-- Bad-reachable via reflexive transitive closure of forward bad steps. -/
def cup2BadReachable (n : Nat) (hn : 4 ≤ n)
    (c d : Config (cup2Spec n hn)) : Prop :=
  Relation.ReflTransGen (cup2BadStepFwd n hn) c d

instance (n : Nat) (hn : 4 ≤ n) (c c' : Config (cup2Spec n hn)) :
    Decidable (cup2BadStepFwd n hn c c') := by
  unfold cup2BadStepFwd
  infer_instance

lemma cup2BadReachable_refl (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2BadReachable n hn c c :=
  Relation.ReflTransGen.refl

lemma cup2BadReachable_step (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hstep : cup2BadStepFwd n hn c c') :
    cup2BadReachable n hn c c' :=
  Relation.ReflTransGen.single hstep

lemma cup2BadReachable_trans (n : Nat) (hn : 4 ≤ n)
    {a b c : Config (cup2Spec n hn)}
    (hab : cup2BadReachable n hn a b)
    (hbc : cup2BadReachable n hn b c) :
    cup2BadReachable n hn a c :=
  Relation.ReflTransGen.trans hab hbc

/-- If c reaches d and there is a bad step from d to e, then c reaches e. -/
lemma cup2BadReachable_of_step (n : Nat) (hn : 4 ≤ n)
    {c d : Config (cup2Spec n hn)}
    (hcd : cup2BadReachable n hn c d)
    {e : Config (cup2Spec n hn)}
    (hde : cup2BadStepFwd n hn d e) :
    cup2BadReachable n hn c e :=
  cup2BadReachable_trans n hn hcd (cup2BadReachable_step n hn hde)

/-- If there is a bad step from c to c', then anything reachable from c'
    is also reachable from c. -/
lemma cup2BadReachable_of_badStep (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hstep : cup2BadStepFwd n hn c c')
    {d : Config (cup2Spec n hn)}
    (hreach : cup2BadReachable n hn c' d) :
    cup2BadReachable n hn c d :=
  cup2BadReachable_trans n hn (cup2BadReachable_step n hn hstep) hreach

/-! ### FutureFc definition -/

/-- The set of configs bad-reachable from `c`, as a `Finset`. -/
noncomputable def cup2ReachableSet (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) : Finset (Config (cup2Spec n hn)) := by
  classical
  exact Finset.univ.filter fun d => cup2BadReachable n hn c d

/-- FutureFc: the maximum fc over all bad-reachable configs (including self). -/
noncomputable def cup2FutureFc (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) : Nat :=
  (cup2ReachableSet n hn c).sup (fun d => cup2Fc n hn d)

/-! ### Basic properties -/

lemma mem_cup2ReachableSet_iff (n : Nat) (hn : 4 ≤ n)
    (c d : Config (cup2Spec n hn)) :
    d ∈ cup2ReachableSet n hn c ↔ cup2BadReachable n hn c d := by
  classical
  unfold cup2ReachableSet
  simp [Finset.mem_filter]

lemma self_mem_cup2ReachableSet (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    c ∈ cup2ReachableSet n hn c := by
  rw [mem_cup2ReachableSet_iff]
  exact cup2BadReachable_refl n hn c

lemma cup2FutureFc_attained (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    ∃ d : Config (cup2Spec n hn),
      cup2BadReachable n hn c d ∧
        cup2Fc n hn d = cup2FutureFc n hn c := by
  rcases Finset.exists_mem_eq_sup (cup2ReachableSet n hn c)
      ⟨c, self_mem_cup2ReachableSet n hn c⟩ (fun d => cup2Fc n hn d) with
    ⟨d, hd, hsup⟩
  exact ⟨d, (mem_cup2ReachableSet_iff n hn c d).mp hd, hsup.symm⟩

lemma cup2FutureFc_eq_fc_of_reachable_fc_le (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn))
    (hfc_le : ∀ d : Config (cup2Spec n hn),
      cup2BadReachable n hn c d → cup2Fc n hn d ≤ cup2Fc n hn c) :
    cup2FutureFc n hn c = cup2Fc n hn c := by
  apply le_antisymm
  · unfold cup2FutureFc
    apply Finset.sup_le
    intro d hd
    exact hfc_le d ((mem_cup2ReachableSet_iff n hn c d).mp hd)
  · unfold cup2FutureFc
    exact Finset.le_sup (f := fun d => cup2Fc n hn d) (self_mem_cup2ReachableSet n hn c)

/-- fc(c) ≤ FutureFc(c), since c is bad-reachable from itself. -/
lemma cup2Fc_le_cup2FutureFc (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Fc n hn c ≤ cup2FutureFc n hn c := by
  unfold cup2FutureFc
  exact Finset.le_sup (f := fun d => cup2Fc n hn d) (self_mem_cup2ReachableSet n hn c)

/-! ### Monotonicity -/

/-- Reachable set inclusion: if c reaches d, then Reachable(d) ⊆ Reachable(c). -/
lemma cup2ReachableSet_subset_of_reachable (n : Nat) (hn : 4 ≤ n)
    {c d : Config (cup2Spec n hn)}
    (hcd : cup2BadReachable n hn c d) :
    cup2ReachableSet n hn d ⊆ cup2ReachableSet n hn c := by
  intro e he
  rw [mem_cup2ReachableSet_iff] at he ⊢
  exact cup2BadReachable_trans n hn hcd he

/-- FutureFc is monotone: if c reaches d, then FutureFc(d) ≤ FutureFc(c). -/
theorem cup2FutureFc_mono (n : Nat) (hn : 4 ≤ n)
    {c d : Config (cup2Spec n hn)}
    (hcd : cup2BadReachable n hn c d) :
    cup2FutureFc n hn d ≤ cup2FutureFc n hn c := by
  unfold cup2FutureFc
  apply Finset.sup_le
  intro e he
  exact Finset.le_sup (f := fun d => cup2Fc n hn d)
    (cup2ReachableSet_subset_of_reachable n hn hcd he)

/-- FutureFc does not increase on a single bad step. -/
theorem cup2FutureFc_step_mono (n : Nat) (hn : 4 ≤ n)
    {c' c : Config (cup2Spec n hn)}
    (hbad : badStep (cup2System n hn) (cup2GoodCycle n hn) c' c) :
    cup2FutureFc n hn c' ≤ cup2FutureFc n hn c := by
  apply cup2FutureFc_mono
  exact cup2BadReachable_step n hn hbad

/-! ### Bad step splitting: constant vs dropping FutureFc -/

/-- A bad step that preserves FutureFc. -/
def cup2BadConstFutureStep (n : Nat) (hn : 4 ≤ n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  badStep (cup2System n hn) (cup2GoodCycle n hn) c' c ∧
    cup2FutureFc n hn c' = cup2FutureFc n hn c

/-- A bad step that strictly decreases FutureFc. -/
def cup2BadDropFutureStep (n : Nat) (hn : 4 ≤ n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  badStep (cup2System n hn) (cup2GoodCycle n hn) c' c ∧
    cup2FutureFc n hn c' < cup2FutureFc n hn c

/-- Every bad step either preserves or strictly decreases FutureFc. -/
theorem badStep_futureFc_split (n : Nat) (hn : 4 ≤ n)
    {c' c : Config (cup2Spec n hn)}
    (hbad : badStep (cup2System n hn) (cup2GoodCycle n hn) c' c) :
    cup2BadConstFutureStep n hn c' c ∨ cup2BadDropFutureStep n hn c' c := by
  have hle := cup2FutureFc_step_mono n hn hbad
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · left
    exact ⟨hbad, heq⟩
  · right
    exact ⟨hbad, hlt⟩

/-- Dropping steps are well-founded via InvImage on FutureFc. -/
theorem cup2BadDropFutureStep_wf (n : Nat) (hn : 4 ≤ n) :
    WellFounded (cup2BadDropFutureStep n hn) := by
  apply WellFounded.mono (InvImage.wf (cup2FutureFc n hn) Nat.lt_wfRel.wf)
  intro c' c ⟨_, hlt⟩
  exact hlt

end LeanMn
