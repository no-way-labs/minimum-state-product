/-
  IntervalDisplacement.lean

  Prefix / interval displacement infrastructure for mover-word reasoning.
-/
import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

/-- Signed displacement contributed by step `k` of the mover word. -/
noncomputable def GoodCycle.displacementStep (gc : GoodCycle sys) (k : Nat) : Int :=
  if hk : k < gc.configs.length then
    match gc.stepDir ⟨k, hk⟩ with
    | .cw => 1
    | .stay => 0
    | .ccw => -1
  else
    0

/-- Displacement accumulated over the prefix `[0, k)` of the mover word. -/
noncomputable def GoodCycle.prefixDisplacement (gc : GoodCycle sys) (k : Nat) : Int :=
  Finset.sum (Finset.range k) fun i => gc.displacementStep i

/-- Displacement accumulated on the half-open interval `[a, b)`. -/
noncomputable def GoodCycle.intervalDisplacement (gc : GoodCycle sys) (a b : Nat) : Int :=
  gc.prefixDisplacement b - gc.prefixDisplacement a

@[simp] theorem GoodCycle.displacementStep_of_lt (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length) :
    gc.displacementStep k =
      match gc.stepDir ⟨k, hk⟩ with
      | .cw => 1
      | .stay => 0
      | .ccw => -1 := by
  simp [GoodCycle.displacementStep, hk]

@[simp] theorem GoodCycle.displacementStep_of_ge (gc : GoodCycle sys)
    {k : Nat} (hk : gc.configs.length ≤ k) :
    gc.displacementStep k = 0 := by
  simp [GoodCycle.displacementStep, Nat.not_lt.mpr hk]

theorem GoodCycle.displacementStep_eq_signedStep (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length) :
    gc.displacementStep k =
      signedStep sys.rs.n (gc.moverAt ⟨k, hk⟩)
        (gc.moverAt (nextIndex gc.configs ⟨k, hk⟩)) := by
  rw [gc.displacementStep_of_lt hk, gc.signedStep_eq_stepDir ⟨k, hk⟩]
  rfl

@[simp] theorem GoodCycle.prefixDisplacement_zero (gc : GoodCycle sys) :
    gc.prefixDisplacement 0 = 0 := by
  simp [GoodCycle.prefixDisplacement]

@[simp] theorem GoodCycle.prefixDisplacement_succ (gc : GoodCycle sys) (k : Nat) :
    gc.prefixDisplacement (k + 1) =
      gc.prefixDisplacement k + gc.displacementStep k := by
  rw [GoodCycle.prefixDisplacement, GoodCycle.prefixDisplacement, Finset.sum_range_succ]

@[simp] theorem GoodCycle.intervalDisplacement_self (gc : GoodCycle sys) (a : Nat) :
    gc.intervalDisplacement a a = 0 := by
  simp [GoodCycle.intervalDisplacement]

/-- Full-cycle displacement is the prefix displacement at the cycle length. -/
theorem totalDisplacement_eq_prefixDisplacement_full (gc : GoodCycle sys) :
    totalDisplacement gc = gc.prefixDisplacement gc.configs.length := by
  rw [totalDisplacement_eq_moverAt_sum, GoodCycle.prefixDisplacement,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simpa using (gc.displacementStep_eq_signedStep k.isLt).symm

/-- Prefix decomposition across a cut point. -/
theorem GoodCycle.intervalDisplacement_split (gc : GoodCycle sys)
    {a c b : Nat} (_hac : a ≤ c) (_hcb : c ≤ b) :
    gc.intervalDisplacement a b =
      gc.intervalDisplacement a c + gc.intervalDisplacement c b := by
  unfold GoodCycle.intervalDisplacement
  omega

/-- If every step in `[a, b)` is a stay-step, the prefix displacement is unchanged. -/
theorem GoodCycle.prefixDisplacement_eq_of_allStay
    (gc : GoodCycle sys) {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hstay : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.stepDir k = .stay) :
    gc.prefixDisplacement b = gc.prefixDisplacement a := by
  induction b, hab using Nat.le_induction with
  | base =>
      rfl
  | succ b hab ih =>
      have hb_lt : b < gc.configs.length := by omega
      have hstep : gc.stepDir ⟨b, hb_lt⟩ = .stay := by
        exact hstay ⟨b, hb_lt⟩ hab (Nat.lt_succ_self _)
      rw [gc.prefixDisplacement_succ,
        ih (by omega) (fun k hk1 hk2 => hstay k hk1 (by omega))]
      rw [gc.displacementStep_of_lt hb_lt, hstep]
      simp

/-- If every step in `[a, b)` is a stay-step, the interval displacement is zero. -/
theorem intervalDisplacement_eq_zero_of_allStay
    (gc : GoodCycle sys) {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length)
    (hstay : ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.stepDir k = .stay) :
    gc.intervalDisplacement a b = 0 := by
  unfold GoodCycle.intervalDisplacement
  rw [gc.prefixDisplacement_eq_of_allStay hab hb hstay]
  simp

/-- Single-step interval displacement equals the local signed step value. -/
theorem GoodCycle.intervalDisplacement_single_step (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length) :
    gc.intervalDisplacement k (k + 1) =
      match gc.stepDir ⟨k, hk⟩ with
      | .cw => 1
      | .stay => 0
      | .ccw => -1 := by
  unfold GoodCycle.intervalDisplacement
  rw [gc.prefixDisplacement_succ]
  simp [gc.displacementStep_of_lt hk]

theorem GoodCycle.intervalDisplacement_single_step_eq_cw (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length)
    (hdir : gc.stepDir ⟨k, hk⟩ = .cw) :
    gc.intervalDisplacement k (k + 1) = 1 := by
  rw [gc.intervalDisplacement_single_step hk, hdir]

theorem GoodCycle.intervalDisplacement_single_step_eq_stay (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length)
    (hdir : gc.stepDir ⟨k, hk⟩ = .stay) :
    gc.intervalDisplacement k (k + 1) = 0 := by
  rw [gc.intervalDisplacement_single_step hk, hdir]

theorem GoodCycle.intervalDisplacement_single_step_eq_ccw (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length)
    (hdir : gc.stepDir ⟨k, hk⟩ = .ccw) :
    gc.intervalDisplacement k (k + 1) = -1 := by
  rw [gc.intervalDisplacement_single_step hk, hdir]

end LeanMn
