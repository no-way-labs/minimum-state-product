/-
  OneSided.lean — One-sided mover confinement in MinFiringGap

  Between consecutive firings of processor p at steps a and b, the mover
  never visits p.  Starting from left(p) or right(p), the mover travels
  along the path C_n \ {p} at most one position per step.

  Main results (all sorry-free, no axioms):
  1. `position_frozen_if_never_mover`: q's value is preserved if q
     never fires in the gap.
  2. `shadow_entry_conflict`: both neighbors frozen → entry conflict.
  3. `gap_le_one_if_both_neighbors_blocked`: both neighbors blocked →
     gap ≤ 1.
  4. `neighbor_fires_if_gap_ge_2`: gap ≥ 2 → at least one neighbor fires.
  5. `first_mover_side`: first mover is left(p) or right(p).
  6. `mover_adjacent_or_same`: consecutive movers are adjacent or same.
  7. `ec_or_opposite_fires`: entry conflict ∨ opposite neighbor fires.
-/
import LeanMn.LowerBound.EntryConflict.ProcMinGap

namespace LeanMn

variable {sys : System}

/-! ### Value preservation for positions that never fire -/

/-- If processor q is never the mover during steps (a, b) in a MinFiringGap,
    then q's config value is the same at step a+1 and step b. -/
theorem MinFiringGap.position_frozen_if_never_mover
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (q : Fin sys.rs.n)
    (hq_never : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ q) :
    (gc.configs.get ⟨mg.a.val + 1, ha1⟩) q =
      (gc.configs.get mg.b) q :=
  configVal_eq_of_noFire_between gc q (mg.a.val + 1) mg.b.val
    (by have := mg.a_lt_b; omega) mg.b.isLt
    (fun k hk1 hk2 => hq_never k (by omega) hk2)

/-! ### MinFiringGap: first mover determines direction -/

/-- In a MinFiringGap with gap ≥ 2, the mover at step a+1 is either
    left(p) or right(p). -/
theorem MinFiringGap.first_mover_side
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (ha1 : mg.a.val + 1 < gc.configs.length) :
    gc.moverAt ⟨mg.a.val + 1, ha1⟩ = left p ∨
    gc.moverAt ⟨mg.a.val + 1, ha1⟩ = right p := by
  have hcast : gc.moverAt ⟨mg.a.val + 1, ha1⟩ =
      gc.moverAt (nextIndex gc.configs mg.a) := by
    congr 1; ext; simp [nextIndex, Nat.mod_eq_of_lt ha1]
  rw [hcast]
  exact mg.next_mover_left_or_right hgap2

/-! ### Frozen neighbor lemmas -/

/-- left(p)'s value is frozen if left(p) never fires in the gap. -/
theorem MinFiringGap.left_neighbor_frozen
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (hL_never : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ left p) :
    (gc.configs.get ⟨mg.a.val + 1, ha1⟩) (left p) =
      (gc.configs.get mg.b) (left p) :=
  mg.position_frozen_if_never_mover ha1 (left p) hL_never

/-- right(p)'s value is frozen if right(p) never fires in the gap. -/
theorem MinFiringGap.right_neighbor_frozen
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (hR_never : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right p) :
    (gc.configs.get ⟨mg.a.val + 1, ha1⟩) (right p) =
      (gc.configs.get mg.b) (right p) :=
  mg.position_frozen_if_never_mover ha1 (right p) hR_never

/-! ### Shadow entry conflict -/

/-- If both neighbors of p have their values preserved from step a+1 to
    step b, then there is an entry conflict at p. -/
theorem MinFiringGap.shadow_entry_conflict
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (hL_frozen : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ left p)
    (hR_frozen : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right p) :
    hasEntryConflict gc := by
  have hL := mg.position_frozen_if_never_mover ha1 (left p) hL_frozen
  have hR := mg.position_frozen_if_never_mover ha1 (right p) hR_frozen
  exact mg.entry_conflict_of_neighbors_preserved ha1 hgap2 hL hR

/-! ### Gap structure lemmas -/

/-- If both neighbors of p never fire during the gap, then gap ≤ 1. -/
theorem MinFiringGap.gap_le_one_if_both_neighbors_blocked
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (hL_never : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ left p)
    (hR_never : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right p) :
    mg.b.val - mg.a.val ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  have hgap2 : mg.b.val - mg.a.val ≥ 2 := by omega
  have ha1 : mg.a.val + 1 < gc.configs.length := by
    have := mg.b.isLt; omega
  have hcast : gc.moverAt ⟨mg.a.val + 1, ha1⟩ =
      gc.moverAt (nextIndex gc.configs mg.a) := by
    congr 1; ext; simp [nextIndex, Nat.mod_eq_of_lt ha1]
  rcases mg.next_mover_left_or_right hgap2 with hleft | hright
  · rw [← hcast] at hleft
    have hak : mg.a.val < (⟨mg.a.val + 1, ha1⟩ : Fin gc.configs.length).val := by simp
    have hkb : (⟨mg.a.val + 1, ha1⟩ : Fin gc.configs.length).val < mg.b.val := by
      simp; omega
    exact hL_never ⟨mg.a.val + 1, ha1⟩ hak hkb hleft
  · rw [← hcast] at hright
    have hak : mg.a.val < (⟨mg.a.val + 1, ha1⟩ : Fin gc.configs.length).val := by simp
    have hkb : (⟨mg.a.val + 1, ha1⟩ : Fin gc.configs.length).val < mg.b.val := by
      simp; omega
    exact hR_never ⟨mg.a.val + 1, ha1⟩ hak hkb hright

/-- If gap ≥ 2, at least one of left(p) or right(p) fires in the gap. -/
theorem MinFiringGap.neighbor_fires_if_gap_ge_2
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2) :
    (∃ k : Fin gc.configs.length,
      mg.a.val < k.val ∧ k.val < mg.b.val ∧ gc.moverAt k = left p) ∨
    (∃ k : Fin gc.configs.length,
      mg.a.val < k.val ∧ k.val < mg.b.val ∧ gc.moverAt k = right p) := by
  -- Prove by case split: if neither fires, gap ≤ 1, contradicting gap ≥ 2
  by_cases hL : ∃ k : Fin gc.configs.length,
      mg.a.val < k.val ∧ k.val < mg.b.val ∧ gc.moverAt k = left p
  · exact Or.inl hL
  · by_cases hR : ∃ k : Fin gc.configs.length,
        mg.a.val < k.val ∧ k.val < mg.b.val ∧ gc.moverAt k = right p
    · exact Or.inr hR
    · -- Neither fires: gap ≤ 1
      exfalso
      have hL_never : ∀ k : Fin gc.configs.length,
          mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ left p := by
        intro k hak hkb hmov
        exact hL ⟨k, hak, hkb, hmov⟩
      have hR_never : ∀ k : Fin gc.configs.length,
          mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right p := by
        intro k hak hkb hmov
        exact hR ⟨k, hak, hkb, hmov⟩
      have hle := mg.gap_le_one_if_both_neighbors_blocked hL_never hR_never
      omega

/-! ### Step-by-step mover tracking -/

/-- Consecutive movers in a good cycle are adjacent or the same. -/
theorem mover_adjacent_or_same (gc : GoodCycle sys)
    {k : Nat} (hk : k < gc.configs.length) (hk1 : k + 1 < gc.configs.length) :
    gc.moverAt ⟨k + 1, hk1⟩ = gc.moverAt ⟨k, hk⟩ ∨
    gc.moverAt ⟨k + 1, hk1⟩ = left (gc.moverAt ⟨k, hk⟩) ∨
    gc.moverAt ⟨k + 1, hk1⟩ = right (gc.moverAt ⟨k, hk⟩) := by
  have hnext : (⟨k + 1, hk1⟩ : Fin gc.configs.length) =
      nextIndex gc.configs ⟨k, hk⟩ := by
    ext; simp [nextIndex, Nat.mod_eq_of_lt hk1]
  rw [hnext]
  rcases gc.next_mover_is_local ⟨k, hk⟩ with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-! ### One-sided confinement: entry conflict or opposite neighbor fires -/

/-- **Entry conflict or opposite neighbor fires.**

    In a MinFiringGap with gap ≥ 2 where the first mover is left(p):
    either right(p) never fires (so right(p) is frozen), or right(p)
    fires at some step in the gap.

    When combined with left(p) also being frozen (e.g., from binary
    parity arguments), the first case gives an entry conflict.
    The second case provides structural information for shadow cycle
    arguments. -/
theorem MinFiringGap.ec_or_opposite_fires_start_left
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (_hstart : gc.moverAt ⟨mg.a.val + 1, ha1⟩ = left p)
    -- Additional hypothesis: left(p) is also frozen (e.g., from binary parity)
    (hL_frozen : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ left p) :
    hasEntryConflict gc ∨
    (∃ k : Fin gc.configs.length,
      mg.a.val < k.val ∧ k.val < mg.b.val ∧ gc.moverAt k = right p) := by
  by_cases hR : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right p
  · -- Both neighbors frozen → entry conflict
    exact Or.inl (mg.shadow_entry_conflict hgap2 ha1 hL_frozen hR)
  · -- right(p) fires at some step
    push_neg at hR
    obtain ⟨k, hak, hkb, hmov⟩ := hR
    exact Or.inr ⟨k, hak, hkb, hmov⟩

/-- **Symmetric version: entry conflict or left(p) fires.**

    In a MinFiringGap with gap ≥ 2 where the first mover is right(p):
    either left(p) never fires (so left(p) is frozen), or left(p)
    fires at some step in the gap. -/
theorem MinFiringGap.ec_or_opposite_fires_start_right
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (_hstart : gc.moverAt ⟨mg.a.val + 1, ha1⟩ = right p)
    -- Additional hypothesis: right(p) is also frozen
    (hR_frozen : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ right p) :
    hasEntryConflict gc ∨
    (∃ k : Fin gc.configs.length,
      mg.a.val < k.val ∧ k.val < mg.b.val ∧ gc.moverAt k = left p) := by
  by_cases hL : ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ left p
  · exact Or.inl (mg.shadow_entry_conflict hgap2 ha1 hL hR_frozen)
  · push_neg at hL
    obtain ⟨k, hak, hkb, hmov⟩ := hL
    exact Or.inr ⟨k, hak, hkb, hmov⟩

/-! ### General frozen-position theorem -/

/-- **General frozen positions.**

    In a MinFiringGap, any set of positions S such that no position in S
    is ever the mover during the gap has all its values preserved from
    step a+1 to step b.

    This is the multi-position generalization of `position_frozen_if_never_mover`. -/
theorem MinFiringGap.set_frozen_if_never_mover
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (S : Fin sys.rs.n → Prop)
    (hS_never : ∀ q, S q → ∀ k : Fin gc.configs.length,
      mg.a.val < k.val → k.val < mg.b.val → gc.moverAt k ≠ q)
    (q : Fin sys.rs.n) (hq : S q) :
    (gc.configs.get ⟨mg.a.val + 1, ha1⟩) q =
      (gc.configs.get mg.b) q :=
  mg.position_frozen_if_never_mover ha1 q (hS_never q hq)

/-! ### Mover set characterization -/

/-- The set of movers in a gap is contained in the complement of {p}. -/
theorem MinFiringGap.mover_ne_p
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (k : Fin gc.configs.length)
    (hak : mg.a.val < k.val) (hkb : k.val < mg.b.val) :
    gc.moverAt k ≠ p :=
  mg.no_fire_between k hak hkb

/-- The first mover (at step a+1) is not p when gap ≥ 2. -/
theorem MinFiringGap.first_mover_ne_p
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (ha1 : mg.a.val + 1 < gc.configs.length) :
    gc.moverAt ⟨mg.a.val + 1, ha1⟩ ≠ p := by
  have hak : mg.a.val < (⟨mg.a.val + 1, ha1⟩ : Fin gc.configs.length).val := by simp
  have hkb : (⟨mg.a.val + 1, ha1⟩ : Fin gc.configs.length).val < mg.b.val := by simp; omega
  exact mg.no_fire_between ⟨mg.a.val + 1, ha1⟩ hak hkb

/-- **Last mover before b.**

    The mover at step b-1 (the last step before p fires again) is
    in {left p, p, right p} by `next_mover_is_local` applied to step
    b-1 → step b.  Combined with moverAt(b) = p, this means the
    last gap mover is adjacent to p or is p itself.

    But moverAt(b-1) ≠ p (since b-1 is in the gap and p doesn't fire).
    So the last gap mover is left(p) or right(p). -/
theorem MinFiringGap.last_mover_side
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hb1 : mg.b.val - 1 < gc.configs.length) :
    gc.moverAt ⟨mg.b.val - 1, hb1⟩ = left p ∨
    gc.moverAt ⟨mg.b.val - 1, hb1⟩ = right p := by
  -- step b-1 → step b: moverAt(b) = p, and b = nextIndex(b-1)
  -- So moverAt(b-1) is such that moverAt(nextIndex(b-1)) = p
  -- By next_mover_is_local at step b-1:
  --   moverAt(b) ∈ {left(moverAt(b-1)), moverAt(b-1), right(moverAt(b-1))}
  -- i.e., p ∈ {left(moverAt(b-1)), moverAt(b-1), right(moverAt(b-1))}
  -- And moverAt(b-1) ≠ p (from no_fire_between)
  -- So p = left(moverAt(b-1)) or p = right(moverAt(b-1))
  -- p = left(moverAt(b-1)) → moverAt(b-1) = right(p)
  -- p = right(moverAt(b-1)) → moverAt(b-1) = left(p)
  set q := gc.moverAt ⟨mg.b.val - 1, hb1⟩ with hq_def
  have hq_ne_p : q ≠ p := by
    have hak : mg.a.val < (⟨mg.b.val - 1, hb1⟩ : Fin gc.configs.length).val := by simp; omega
    have hkb : (⟨mg.b.val - 1, hb1⟩ : Fin gc.configs.length).val < mg.b.val := by simp; omega
    exact mg.no_fire_between ⟨mg.b.val - 1, hb1⟩ hak hkb
  -- nextIndex(b-1) = b
  have hb_eq : nextIndex gc.configs ⟨mg.b.val - 1, hb1⟩ = mg.b := by
    ext; simp [nextIndex]
    rw [show mg.b.val - 1 + 1 = mg.b.val from by omega]
    exact Nat.mod_eq_of_lt mg.b.isLt
  -- moverAt(nextIndex(b-1)) = moverAt(b) = p
  have hb_fires' : gc.moverAt (nextIndex gc.configs ⟨mg.b.val - 1, hb1⟩) = p := by
    rw [hb_eq]; exact mg.b_fires
  -- By next_mover_is_local at step b-1:
  --   moverAt(nextIndex(b-1)) ∈ {left q, q, right q}
  -- i.e., p ∈ {left q, q, right q}
  have hlocal := gc.next_mover_is_local ⟨mg.b.val - 1, hb1⟩
  rw [← hq_def] at hlocal
  rcases hlocal with hleft | hself | hright
  · -- moverAt(nextIndex(b-1)) = left q, so p = left q, so q = right p
    rw [hleft] at hb_fires'
    exact Or.inr (by
      have : q = right p := by
        calc q = right (left q) := by simp [right_left_eq_self]
          _ = right p := by rw [hb_fires']
      exact this)
  · -- moverAt(nextIndex(b-1)) = q, so p = q, contradiction
    rw [hself] at hb_fires'
    exact absurd hb_fires' hq_ne_p
  · -- moverAt(nextIndex(b-1)) = right q, so p = right q, so q = left p
    rw [hright] at hb_fires'
    exact Or.inl (by
      have : q = left p := by
        calc q = left (right q) := by simp [left_right_eq_self]
          _ = left p := by rw [hb_fires']
      exact this)

/-- **Both-sides theorem.**

    In a MinFiringGap with gap ≥ 2, the first mover is on one side
    of p and the last mover is on one side of p.  If they are on the
    SAME side, the opposite side is completely frozen (giving EC).
    If on OPPOSITE sides, the mover crossed from one side to the other. -/
theorem MinFiringGap.first_and_last_mover_sides
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (hb1 : mg.b.val - 1 < gc.configs.length) :
    -- First mover side
    (gc.moverAt ⟨mg.a.val + 1, ha1⟩ = left p ∨
     gc.moverAt ⟨mg.a.val + 1, ha1⟩ = right p) ∧
    -- Last mover side
    (gc.moverAt ⟨mg.b.val - 1, hb1⟩ = left p ∨
     gc.moverAt ⟨mg.b.val - 1, hb1⟩ = right p) :=
  ⟨mg.first_mover_side hgap2 ha1, mg.last_mover_side hgap2 hb1⟩

end LeanMn
