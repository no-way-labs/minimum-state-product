import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Function.Iterate

namespace LeanMn

/-!
Scratch definitions for the controller-reuse recurrence side of the program.

This file is intentionally not imported elsewhere yet.
-/

universe u v w x

structure ControllerEntry (Shadow : Type u) (Ctrl : Type v) (Mover : Type w) where
  shadow : Shadow
  ctrl : Ctrl
  mover : Mover

def Realizes
    {State : Type x} {Shadow : Type u} {Ctrl : Type v} {Mover : Type w}
    (shadowOf : State → Shadow)
    (ctrlOf : State → Ctrl)
    (enabled : State → Mover → Prop)
    (x : State)
    (e : ControllerEntry Shadow Ctrl Mover) : Prop :=
  shadowOf x = e.shadow ∧ ctrlOf x = e.ctrl ∧ enabled x e.mover

structure BadReuseRegion
    (State : Type x) (Shadow : Type u) (Ctrl : Type v) (Mover : Type w)
    [DecidableEq State] where
  carrier : Finset State
  nonempty : carrier.Nonempty
  disjoint_good : State → Prop
  shadowOf : State → Shadow
  ctrlOf : State → Ctrl
  enabled : State → Mover → Prop
  step : State → Mover → State
  entries : Finset (ControllerEntry Shadow Ctrl Mover)
  sound : ∀ x ∈ carrier, ∃ e ∈ entries, Realizes shadowOf ctrlOf enabled x e
  closed :
    ∀ x ∈ carrier,
      ∀ e ∈ entries, Realizes shadowOf ctrlOf enabled x e →
        step x e.mover ∈ carrier

noncomputable def BadReuseRegion.reusedSucc
    {State : Type x} {Shadow : Type u} {Ctrl : Type v} {Mover : Type w}
    [DecidableEq State] (B : BadReuseRegion State Shadow Ctrl Mover) :
    {x // x ∈ B.carrier} → {x // x ∈ B.carrier} := by
  classical
  intro x
  let hs := B.sound x.1 x.2
  let e : ControllerEntry Shadow Ctrl Mover := Classical.choose hs
  have hspec : e ∈ B.entries ∧ Realizes B.shadowOf B.ctrlOf B.enabled x.1 e :=
    Classical.choose_spec hs
  exact ⟨B.step x.1 e.mover, B.closed x.1 x.2 e hspec.left hspec.right⟩

theorem BadReuseRegion.exists_recurrence_pair
    {State : Type x} {Shadow : Type u} {Ctrl : Type v} {Mover : Type w}
    [DecidableEq State] (B : BadReuseRegion State Shadow Ctrl Mover) :
    ∃ x : {x // x ∈ B.carrier}, ∃ m n : ℕ, m < n ∧
      (B.reusedSucc)^[m] x = (B.reusedSucc)^[n] x := by
  classical
  let α : Type x := {x // x ∈ B.carrier}
  haveI : Fintype α := Finset.Subtype.fintype B.carrier
  rcases B.nonempty with ⟨x0, hx0⟩
  let x : α := ⟨x0, hx0⟩
  let f : Fin (Fintype.card α + 1) → α := fun i => (B.reusedSucc)^[i.1] x
  have hcard : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    simp
  rcases Fintype.exists_ne_map_eq_of_card_lt (f := f) hcard with
    ⟨i, j, hij, hijf⟩
  have hij_nat : i.1 ≠ j.1 := by
    intro h
    apply hij
    exact Fin.ext h
  rcases lt_or_gt_of_ne hij_nat with hlt | hgt
  · refine ⟨x, i.1, j.1, hlt, ?_⟩
    simpa [f] using hijf
  · refine ⟨x, j.1, i.1, hgt, ?_⟩
    simpa [f] using hijf.symm

theorem BadReuseRegion.exists_nontrivial_cycle
    {State : Type x} {Shadow : Type u} {Ctrl : Type v} {Mover : Type w}
    [DecidableEq State] (B : BadReuseRegion State Shadow Ctrl Mover) :
    ∃ x : {x // x ∈ B.carrier}, ∃ n : ℕ, 0 < n ∧ (B.reusedSucc)^[n] x = x := by
  classical
  rcases B.exists_recurrence_pair with ⟨x, m, n, hmn, hEq⟩
  rcases Nat.exists_eq_add_of_lt hmn with ⟨k, rfl⟩
  refine ⟨(B.reusedSucc)^[m] x, k + 1, Nat.succ_pos _, ?_⟩
  calc
    (B.reusedSucc)^[k + 1] ((B.reusedSucc)^[m] x) = (B.reusedSucc)^[k + 1 + m] x := by
      rw [← Function.iterate_add_apply]
    _ = (B.reusedSucc)^[m + k + 1] x := by
      rw [Nat.add_comm, Nat.add_assoc]
    _ = (B.reusedSucc)^[m] x := by simpa using hEq.symm

end LeanMn
