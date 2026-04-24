/-
  Convergence/Reachable.lean — Computable reachable set for Fintype

  Provides Decidable (Relation.ReflTransGen r a b) for decidable r on Fintype,
  making FutureFc and Φ_full computable. Enables native_decide on cphi_bridge.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace LeanMn

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One step: expand set by adding all one-step successors. -/
def reachExpand (r : α → α → Prop) [DecidableRel r] (s : Finset α) : Finset α :=
  s ∪ Finset.univ.filter fun b => ∃ a ∈ s, r a b

/-- Iterate expansion k times. -/
def reachIter (r : α → α → Prop) [DecidableRel r] (s : Finset α) : Nat → Finset α
  | 0 => s
  | k + 1 => reachExpand r (reachIter r s k)

/-- Computable reachable set from a single start element. -/
def reachableFinset (r : α → α → Prop) [DecidableRel r] (start : α) : Finset α :=
  reachIter r {start} (Fintype.card α)

/-! ### Basic properties of reachExpand -/

variable {r : α → α → Prop} [DecidableRel r]

lemma subset_reachExpand (s : Finset α) : s ⊆ reachExpand r s :=
  Finset.subset_union_left

lemma mem_reachExpand_iff {s : Finset α} {b : α} :
    b ∈ reachExpand r s ↔ b ∈ s ∨ ∃ a ∈ s, r a b := by
  simp [reachExpand, Finset.mem_union, Finset.mem_filter]

/-- If expand doesn't change the set, the set is closed under r. -/
lemma closed_of_reachExpand_eq {s : Finset α} (heq : reachExpand r s = s)
    {a b : α} (ha : a ∈ s) (hr : r a b) : b ∈ s := by
  have : b ∈ reachExpand r s := mem_reachExpand_iff.mpr (Or.inr ⟨a, ha, hr⟩)
  rwa [heq] at this

/-! ### Monotonicity of reachIter -/

lemma reachIter_mono_subset (s : Finset α) (k : Nat) :
    s ⊆ reachIter r s k := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact ih.trans (subset_reachExpand _)

lemma reachIter_step_subset (s : Finset α) (k : Nat) :
    reachIter r s k ⊆ reachIter r s (k + 1) :=
  subset_reachExpand _

lemma reachIter_mono_fuel (s : Finset α) {j k : Nat} (h : j ≤ k) :
    reachIter r s j ⊆ reachIter r s k := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact ih.trans (reachIter_step_subset s _)

/-! ### Forward direction: reachIter only contains reachable states -/

lemma reachIter_reachable {start : α} (k : Nat) :
    ∀ x ∈ reachIter r {start} k, Relation.ReflTransGen r start x := by
  induction k with
  | zero =>
    intro x hx; simp only [reachIter] at hx
    rw [Finset.mem_singleton] at hx; subst hx
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro x hx
    simp only [reachIter] at hx
    rw [mem_reachExpand_iff] at hx
    rcases hx with hx | ⟨a, ha, hr⟩
    · exact ih x hx
    · exact (ih a ha).tail hr

/-! ### Stability: after enough iterations, the set is a fixed point -/

/-- Once stable, stays stable one more step. -/
lemma reachIter_stable_succ {s : Finset α} {k : Nat}
    (heq : reachIter r s (k + 1) = reachIter r s k) :
    reachIter r s (k + 2) = reachIter r s (k + 1) := by
  -- reachIter r s (k + 2) = reachExpand r (reachIter r s (k + 1)) [def]
  -- reachIter r s (k + 1) = reachExpand r (reachIter r s k) [def]
  -- So need: reachExpand r (reachIter r s (k + 1)) = reachExpand r (reachIter r s k)
  -- Which follows from heq
  show reachExpand r (reachIter r s (k + 1)) = reachIter r s (k + 1)
  rw [heq]; exact heq

/-- Once stable, stays stable for all larger fuel. -/
lemma reachIter_stable_ge {s : Finset α} {k : Nat}
    (heq : reachIter r s (k + 1) = reachIter r s k) {m : Nat} (hm : k ≤ m) :
    reachIter r s (m + 1) = reachIter r s m := by
  induction hm with
  | refl => exact heq
  | step hm ih => exact reachIter_stable_succ ih

/-- Strict growth implies card growth. -/
lemma card_grow_of_strict {s : Finset α} {k : Nat}
    (hstrict : ∀ j, j < k → reachIter r s (j + 1) ≠ reachIter r s j) :
    s.card + k ≤ (reachIter r s k).card := by
  induction k with
  | zero => simp [reachIter]
  | succ n ih =>
    have ih' := ih (fun j hj => hstrict j (Nat.lt_succ_of_lt hj))
    have hne := hstrict n (Nat.lt_succ_iff.mpr le_rfl)
    have hsub : reachIter r s n ⊆ reachIter r s (n + 1) := reachIter_step_subset s n
    have hlt : (reachIter r s n).card < (reachIter r s (n + 1)).card :=
      Finset.card_lt_card (hsub.ssubset_of_ne (Ne.symm hne))
    omega

/-- After Fintype.card α iterations from a singleton, the set is stable. -/
theorem reachIter_stable_at_card (start : α) :
    reachIter r {start} (Fintype.card α + 1) = reachIter r {start} (Fintype.card α) := by
  by_contra hne
  have hstrict : ∀ j, j ≤ Fintype.card α →
      reachIter r {start} (j + 1) ≠ reachIter r {start} j := by
    intro j hj heq_j
    exact hne (reachIter_stable_ge heq_j hj)
  have hgrow := card_grow_of_strict (k := Fintype.card α + 1)
    (fun j hj => hstrict j (by omega))
  have hcard_bound : (reachIter r {start} (Fintype.card α + 1)).card ≤ Fintype.card α :=
    Finset.card_le_univ _
  have hcard_start : ({start} : Finset α).card = 1 := Finset.card_singleton start
  omega

/-- After Fintype.card α iterations, reachExpand is identity (fixed point). -/
theorem reachIter_is_fixpoint (start : α) :
    reachExpand r (reachIter r {start} (Fintype.card α)) =
      reachIter r {start} (Fintype.card α) :=
  reachIter_stable_at_card start

/-! ### Backward direction: reachable states are in the fixed point -/

lemma reachableFinset_closed {start : α} {a b : α}
    (ha : a ∈ reachableFinset r start) (hr : r a b) :
    b ∈ reachableFinset r start :=
  closed_of_reachExpand_eq (reachIter_is_fixpoint start) ha hr

lemma mem_reachableFinset_of_reachable {start : α} {b : α}
    (h : Relation.ReflTransGen r start b) :
    b ∈ reachableFinset r start := by
  induction h with
  | refl => exact reachIter_mono_subset {start} _ (Finset.mem_singleton.mpr rfl)
  | tail _hab hbc ih => exact reachableFinset_closed ih hbc

/-! ### Main theorem -/

theorem mem_reachableFinset_iff {start : α} {b : α} :
    b ∈ reachableFinset r start ↔ Relation.ReflTransGen r start b :=
  ⟨reachIter_reachable (Fintype.card α) b, mem_reachableFinset_of_reachable⟩

/-! ### Decidable instance for ReflTransGen -/

instance instDecidableReflTransGen (r : α → α → Prop) [DecidableRel r] (a b : α) :
    Decidable (Relation.ReflTransGen r a b) :=
  decidable_of_iff (b ∈ reachableFinset r a) mem_reachableFinset_iff

end LeanMn
