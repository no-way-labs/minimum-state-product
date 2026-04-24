/-
  EdgeConstraint.lean — Direction constraints from no-edge-crossing gaps

  Between paired opposite-direction crossings of edge (p, right p),
  the absence of intervening crossings constrains which processors fire
  and in what direction:

  • p can only fire CCW or stay (never CW)
  • right p can only fire CW or stay (never CCW)

  These are the strongest constraints derivable from the no-crossing
  condition alone. Combined with contiguity of the mover walk and
  short gap bounds, they let us rule out firings of specific processors
  far from the edge.
-/
import LeanMn.LowerBound.EntryConflict.PairedCrossing

namespace LeanMn

variable {sys : System}

/-! ### Direction constraints from no-crossing gaps -/

/-- Between paired crossings of edge (p, right p), processor `p` never
    fires clockwise. This is immediate from the definition of
    `edgeCWCrossAt`: a CW crossing at step k is precisely
    `moverAt k = p ∧ stepDir k = .cw`. -/
theorem not_cw_at_p_between_crossings
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (_hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (k : Fin gc.configs.length)
    (hak : a.val < k.val) (hkb : k.val < b.val) :
    ¬(gc.moverAt k = p ∧ gc.stepDir k = .cw) := by
  intro ⟨hmov, hdir⟩
  exact hno k hak hkb ((edgeCrossAt'_iff_cwOrCcw gc p k).mpr
    (Or.inl ⟨hmov, hdir⟩))

/-- Between paired crossings of edge (p, right p), processor `right p`
    never fires counterclockwise. -/
theorem not_ccw_at_right_between_crossings
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (_hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (k : Fin gc.configs.length)
    (hak : a.val < k.val) (hkb : k.val < b.val) :
    ¬(gc.moverAt k = right p ∧ gc.stepDir k = .ccw) := by
  intro ⟨hmov, hdir⟩
  exact hno k hak hkb ((edgeCrossAt'_iff_cwOrCcw gc p k).mpr
    (Or.inr ⟨hmov, hdir⟩))

/-! ### Mover walk confinement -/

/-- Between paired crossings at edge (p, right p) with gap ≤ 2 (i.e.,
    b = a + 1 or b = a + 2), the only processor that can fire in the
    open interval (a, b) is `right p` — and only CW or staying.
    Equivalently, no processor other than `right p` fires in (a, b).

    When b = a + 1: the interval (a, b) is empty, so the conclusion
    is vacuous.

    When b = a + 2: there is exactly one step k = a + 1 between the
    crossings. At step a, CW crossing means moverAt(a) = p and
    moverAt(a+1) ∈ {left p, p, right p}. Since moverAt(a+1) is the
    next mover after p fired CW, moverAt(a+1) = right p (by the CW
    direction). So moverAt(a+1) = right p.
    The no-crossing condition ensures this is not a CCW crossing,
    so stepDir(a+1) ∈ {.cw, .stay}. -/
theorem gap_le_2_mover_eq_right
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (hcw_a : edgeCWCrossAt gc p a)
    (_hccw_b : edgeCCWCrossAt gc p b)
    (_hlt : a.val < b.val)
    (hgap : b.val = a.val + 2)
    (_hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k) :
    ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → gc.moverAt k = right p := by
  intro k hak hkb
  -- k.val must be a.val + 1 (only value in the open interval)
  have hk_eq : k.val = a.val + 1 := by omega
  -- At step a: CW crossing, so moverAt(a) = p, stepDir(a) = .cw
  have ha_mover : gc.moverAt a = p := hcw_a.1
  have ha_dir : gc.stepDir a = .cw := hcw_a.2
  -- stepDir(a) = .cw means moverAt(nextIndex a) = right(moverAt a) = right p
  have ha_next : gc.moverAt (nextIndex gc.configs a) = right (gc.moverAt a) :=
    gc.eq_right_of_stepDir_eq_cw ha_dir
  rw [ha_mover] at ha_next
  -- nextIndex a has value (a.val + 1) % length
  -- Since a.val + 2 = b.val < length, we have a.val + 1 < length
  have ha1_lt : a.val + 1 < gc.configs.length := by omega
  have h_next_val : (nextIndex gc.configs a).val = a.val + 1 := by
    simp [nextIndex, Nat.mod_eq_of_lt ha1_lt]
  -- So moverAt at index (a.val + 1) = right p
  have hk_fin : k = ⟨a.val + 1, ha1_lt⟩ := Fin.ext hk_eq
  rw [hk_fin]
  -- nextIndex a and ⟨a.val + 1, _⟩ are the same Fin
  have h_idx_eq : nextIndex gc.configs a = ⟨a.val + 1, ha1_lt⟩ :=
    Fin.ext h_next_val
  rw [← h_idx_eq]
  exact ha_next

/-- In the gap-2 case with CW-then-CCW crossings, the single intermediate
    step fires `right p` in a non-CCW direction. Combined with
    `configVal_eq_of_noFire_between`, this means `right p`'s neighbors
    `p` and `right (right p)` do not fire in the gap, so their values
    are preserved between steps a and b. -/
theorem gap_2_neighbors_preserved
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (hcw_a : edgeCWCrossAt gc p a)
    (hccw_b : edgeCCWCrossAt gc p b)
    (hlt : a.val < b.val)
    (hgap : b.val = a.val + 2)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (q : Fin sys.rs.n) (hq : q ≠ right p) :
    ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → gc.moverAt k ≠ q := by
  intro k hak hkb heq
  have := gap_le_2_mover_eq_right gc p a b hcw_a hccw_b hlt hgap hno k hak hkb
  exact hq (heq ▸ this)

end LeanMn
