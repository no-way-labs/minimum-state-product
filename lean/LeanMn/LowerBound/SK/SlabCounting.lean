/-
  LowerBound/SK/SlabCounting.lean — Slab counting theorem: SK ≥ 1 for n ≥ 6

  The mathematical argument is self-contained and sorry-free.
  Connection to the token ring infrastructure is at the bottom.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace SlabCounting

/-! ## §1. The slab inequality -/

theorem slab_gt_budget (n : ℕ) (hn : 6 ≤ n) : n + 1 < 2 ^ (n - 3) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h1 : m + 1 - 3 = (m - 3) + 1 := by omega
    rw [h1, pow_succ]
    linarith

/-! ## §2. Abstract pigeonhole on blocking

The core math: L items each needing coverage S. Total budget ≤ (n+1)·L.
When S > n+1, some item is uncovered. -/

/-- If L items each need cost ≥ S, and the total budget is ≤ B·L,
    and S > B, then at least one item is underfunded. -/
theorem exists_underfunded {L : ℕ} (hL : 0 < L)
    (cost : Fin L → ℕ) (budget : Fin L → ℕ)
    (S B : ℕ) (hS : S > B)
    (hcost : ∀ k, S ≤ cost k)
    (hbudget : ∑ k : Fin L, budget k ≤ B * L) :
    ∃ k : Fin L, budget k < cost k := by
  by_contra h
  push_neg at h
  -- Every item has budget ≥ cost ≥ S. So total budget ≥ L * S.
  have : L * S ≤ ∑ k : Fin L, budget k := by
    calc L * S = ∑ _k : Fin L, S := by simp [Finset.sum_const]
      _ ≤ ∑ k : Fin L, budget k := by
          apply Finset.sum_le_sum
          intro k _
          exact le_trans (hcost k) (h k)
  -- But total budget ≤ B * L < S * L. Contradiction.
  have : L * S ≤ B * L := le_trans this hbudget
  have : S * L ≤ B * L := by linarith
  have : S ≤ B := Nat.le_of_mul_le_mul_right this hL
  omega

/-! ## §3. Chain lemma for finite directed graphs

In any finite directed graph, if at least one vertex has an outgoing
edge, then the graph contains a directed cycle. -/

/-- Pigeonhole on function iteration: if `f : α → α` on a finite type,
    then iterating f from any start must revisit a value within
    `Fintype.card α + 1` steps. -/
theorem Function.Iterate.exists_eq [Fintype α] [DecidableEq α]
    (f : α → α) (a : α) :
    ∃ i j, i < j ∧ j ≤ Fintype.card α ∧ f^[i] a = f^[j] a := by
  -- The sequence a, f a, f^2 a, ..., f^n a has n+1 terms in a type of size n.
  -- By pigeonhole, two must be equal.
  have h := Fintype.exists_ne_map_eq_of_card_lt (α := Fin (Fintype.card α + 1))
    (β := α) (fun i => f^[i.val] a) (by simp)
  obtain ⟨i, j, hne, heq⟩ := h
  by_cases hij : i < j
  · exact ⟨i.val, j.val, by omega, by omega, heq⟩
  · push_neg at hij
    have : j < i := lt_of_le_of_ne hij (fun h => hne (Fin.ext (by omega)))
    exact ⟨j.val, i.val, by omega, by omega, heq.symm⟩

/-- A total function on a finite type, restricted to a subset that it
    maps into itself, has a periodic orbit. Therefore the subset
    contains a nonempty "closed" sub-subset (every element maps to
    another element in the sub-subset).

    This is the chain-to-cycle argument: follow f from any start
    in S. Since f maps S → S and S is finite, the chain revisits,
    forming a cycle. The cycle is the closed subset. -/
theorem exists_closed_nonempty_subset [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → α)
    (hS : S.Nonempty) (hf : ∀ x ∈ S, f x ∈ S) :
    ∃ T : Finset α, T ⊆ S ∧ T.Nonempty ∧ ∀ x ∈ T, f x ∈ T := by
  -- Pick any start ∈ S. Iterate f. Get i < j with f^i = f^j.
  -- The set {f^i, f^(i+1), ..., f^(j-1)} is closed under f.
  obtain ⟨start, hstart⟩ := hS
  obtain ⟨i, j, hij, _, heq⟩ := Function.Iterate.exists_eq f start
  -- All iterates of start stay in S (by induction using hf)
  have hmem : ∀ k, f^[k] start ∈ S := by
    intro k; induction k with
    | zero => simpa
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hf _ ih
  -- The cycle orbit {f^i(start), ..., f^(j-1)(start)} is closed
  let T := (Finset.Ico i j).image (fun k => f^[k] start)
  refine ⟨T, ?_, ?_, ?_⟩
  · -- T ⊆ S
    intro x hx
    simp only [T, Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact hmem k
  · -- T.Nonempty
    refine ⟨f^[i] start, ?_⟩
    simp only [T, Finset.mem_image, Finset.mem_Ico]
    exact ⟨i, ⟨le_refl _, hij⟩, rfl⟩
  · -- ∀ x ∈ T, f x ∈ T
    intro x hx
    simp only [T, Finset.mem_image, Finset.mem_Ico] at hx ⊢
    obtain ⟨k, ⟨hki, hkj⟩, rfl⟩ := hx
    by_cases hk : k + 1 < j
    · refine ⟨k + 1, ⟨by omega, hk⟩, ?_⟩
      rw [Function.iterate_succ_apply']
    · -- k + 1 = j, so f^(k+1) = f^j = f^i (by heq)
      have : k + 1 = j := by omega
      refine ⟨i, ⟨le_refl _, hij⟩, ?_⟩
      have heq2 : f^[j] start = f (f^[k] start) := by
        conv_lhs => rw [← this]
        rw [Function.iterate_succ_apply']
      rw [heq, heq2]

/-! ## §4. The slab counting argument (abstract form)

State the argument abstractly over any "cycle system" with:
- n positions on a ring
- L fires (det move entries), one per step
- Each entry at position p covers a slab of size ≥ S
- Each fire step contributes 1 to source count (α total = L)
- Each cycle config contributes to ≤ n target slabs (β total ≤ nL)
-/

/-- The slab counting theorem in pure arithmetic form.

    Given n ≥ 6 and L ≥ 1 det entries, each covering a slab of
    size ≥ 2^(n-3), and a blocking budget of at most (n+1)·L:
    at least one entry is unblocked. -/
theorem slab_unblocked (n L : ℕ) (hn : 6 ≤ n) (hL : 0 < L)
    (slabSize : Fin L → ℕ) (blocked : Fin L → ℕ)
    (h_slab : ∀ k, 2 ^ (n - 3) ≤ slabSize k)
    (h_block : ∑ k : Fin L, blocked k ≤ (n + 1) * L) :
    ∃ k : Fin L, blocked k < slabSize k := by
  exact exists_underfunded hL slabSize blocked
    (2 ^ (n - 3)) (n + 1) (slab_gt_budget n hn) h_slab h_block

/-! ## §5. Assembly: slab counting + chain = SK ≥ 1

The full argument:
1. slab_unblocked → ∃ unblocked entry
2. Unblocked entry → ∃ VC-NG edge (source and target both in NG)
3. Edge in finite graph → directed cycle exists
4. Directed cycle → SK nonempty

Steps 1 and 3 are proved above. Steps 2 and 4 connect to the token
ring infrastructure.
-/

-- The mathematical core is complete:
-- slab_gt_budget + exists_underfunded + chain lemma.
-- What remains is connecting to token ring types (see §6 below).

end SlabCounting

/-! ## §6. Token ring connection

The abstract math above (§1–§5) is sorry-free except for the two
graph-theory chain lemmas. The connection to the token ring LB proof
requires implementing:

(a) Each det move entry has slab_size ≥ 2^(n-3)
    → definitional: slab = ∏_{i ∉ nbrs(p)} |V_i|, each |V_i| ≥ 2
(b) Σ blocked ≤ (n+1)·L
    → counting: α = L exactly, β ≤ nL by one-per-position
(c) Unblocked entry → VC-NG edge
    → definitional: unblocked = ∃ source in NG with target in NG
(d) VC-NG edge → SK nonempty
    → graph theory: chain lemma above + SK contains all cycles

(a)-(c) are definitional unfoldings once detOf/forcedNeighbors exist.
(d) uses exists_closed_subset above.

Additionally needed:
- Det consistency (all-binary → L=2n): finite argument on {0,1}^3
- n=5 computation: native_decide on 25 multisets
-/
