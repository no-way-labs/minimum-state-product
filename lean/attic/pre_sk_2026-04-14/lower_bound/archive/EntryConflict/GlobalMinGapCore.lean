/-
  GlobalMinGapCore.lean — Pure geometry lemmas for global minimum-gap arc argument

  Contains definitions and theorems about global opposite pairs, global minimum
  triples, and wrapping entry conflict elimination that do NOT depend on
  callback parameters (hConsecResidual, hNonConsecCore).

  The assembly-level theorems that wire these into the full contradiction
  (via callbacks) live in GlobalMinGap.lean.
-/
import LeanMn.LowerBound.Archive.EntryConflict.BounceArc
import LeanMn.LowerBound.EntryConflict.BinaryRightCrossing

namespace LeanMn

/-! ### Global opposite pairs across all edges -/

noncomputable def globalOppPairs {sys : System} (gc : GoodCycle sys) :
    Finset (Fin sys.rs.n × Fin gc.configs.length × Fin gc.configs.length) :=
  (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)).filter fun ⟨p, a, b⟩ =>
    a.val < b.val ∧
    edgeCrossAt' gc p a ∧
    edgeCrossAt' gc p b ∧
    (∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k) ∧
    ((edgeCWCrossAt gc p a ∧ edgeCCWCrossAt gc p b) ∨
     (edgeCCWCrossAt gc p a ∧ edgeCWCrossAt gc p b))

theorem globalOppPairs_nonempty {sys : System} (gc : GoodCycle sys)
    (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount) :
    (globalOppPairs gc).Nonempty := by
  obtain ⟨p, hp⟩ := exists_edge_with_cw_crossing gc hcw_pos
  obtain ⟨a, b, ha, hb, hlt, hno, htypes⟩ :=
    exists_paired_edge_crossing gc hzero p hp
  exact ⟨(p, a, b), by
    simp only [globalOppPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ⟨hlt, ha, hb, hno, htypes⟩⟩

noncomputable def globalTripleGap {n L : Nat}
    (t : Fin n × Fin L × Fin L) : Nat :=
  t.2.2.val - t.2.1.val

theorem exists_globalMinTriple {sys : System} (gc : GoodCycle sys)
    (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount) :
    ∃ (p : Fin sys.rs.n) (a b : Fin gc.configs.length),
      (p, a, b) ∈ globalOppPairs gc ∧
      ∀ triple ∈ globalOppPairs gc,
        b.val - a.val ≤ globalTripleGap triple := by
  have hne := globalOppPairs_nonempty gc hzero hcw_pos
  let gapSet := (globalOppPairs gc).image
    (globalTripleGap (n := sys.rs.n) (L := gc.configs.length))
  have hgapNe : gapSet.Nonempty := Finset.Nonempty.image hne _
  set minGap := gapSet.min' hgapNe
  have hMinMem : minGap ∈ gapSet := Finset.min'_mem gapSet hgapNe
  rw [Finset.mem_image] at hMinMem
  obtain ⟨⟨p, a, b⟩, hmem, hgap⟩ := hMinMem
  refine ⟨p, a, b, hmem, ?_⟩
  intro triple ht
  have : minGap ≤ globalTripleGap triple :=
    Finset.min'_le gapSet _ (Finset.mem_image_of_mem _ ht)
  simp [globalTripleGap] at hgap
  omega

theorem globalOppPairs_props {sys : System} (gc : GoodCycle sys)
    {p : Fin sys.rs.n} {a b : Fin gc.configs.length}
    (h : (p, a, b) ∈ globalOppPairs gc) :
    a.val < b.val ∧
    edgeCrossAt' gc p a ∧
    edgeCrossAt' gc p b ∧
    (∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k) ∧
    ((edgeCWCrossAt gc p a ∧ edgeCCWCrossAt gc p b) ∨
     (edgeCCWCrossAt gc p a ∧ edgeCWCrossAt gc p b)) := by
  simp only [globalOppPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and] at h
  exact h

theorem exists_subpair_in_globalOppPairs {sys : System} (gc : GoodCycle sys)
    (q : Fin sys.rs.n) (c d : Fin gc.configs.length)
    (hc : edgeCrossAt' gc q c) (hd : edgeCrossAt' gc q d)
    (hlt : c.val < d.val)
    (htypes : (edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
              (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) :
    ∃ (c' d' : Fin gc.configs.length),
      (q, c', d') ∈ globalOppPairs gc ∧
      d'.val - c'.val ≤ d.val - c.val := by
  have hmain : ∀ g : Nat, ∀ (c d : Fin gc.configs.length),
      d.val - c.val ≤ g →
      edgeCrossAt' gc q c → edgeCrossAt' gc q d →
      c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      ∃ (c' d' : Fin gc.configs.length),
        (q, c', d') ∈ globalOppPairs gc ∧ d'.val - c'.val ≤ g := by
    intro g
    induction g with
    | zero => intro c d hgap _ _ hlt _; omega
    | succ g ih =>
      intro c d hgap hc hd hlt htypes
      by_cases hnocross : ∀ k : Fin gc.configs.length,
          c.val < k.val → k.val < d.val → ¬edgeCrossAt' gc q k
      · exact ⟨c, d, by
          simp only [globalOppPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and]
          exact ⟨hlt, hc, hd, hnocross, htypes⟩, hgap⟩
      · push_neg at hnocross
        obtain ⟨k, hck, hkd, hkcross⟩ := hnocross
        rw [edgeCrossAt'_iff_cwOrCcw] at hkcross
        rcases hkcross with hkCW | hkCCW
        · rcases htypes with ⟨haCW, hbCCW⟩ | ⟨haCCW, hbCW⟩
          · obtain ⟨c', d', hmem, hle⟩ := ih k d (by omega)
              (edgeCWCrossAt_imp gc q k hkCW) (edgeCCWCrossAt_imp gc q d hbCCW)
              hkd (Or.inl ⟨hkCW, hbCCW⟩)
            exact ⟨c', d', hmem, by omega⟩
          · obtain ⟨c', d', hmem, hle⟩ := ih c k (by omega)
              hc (edgeCWCrossAt_imp gc q k hkCW) hck (Or.inr ⟨haCCW, hkCW⟩)
            exact ⟨c', d', hmem, by omega⟩
        · rcases htypes with ⟨haCW, hbCCW⟩ | ⟨haCCW, hbCW⟩
          · obtain ⟨c', d', hmem, hle⟩ := ih c k (by omega)
              hc (edgeCCWCrossAt_imp gc q k hkCCW) hck (Or.inl ⟨haCW, hkCCW⟩)
            exact ⟨c', d', hmem, by omega⟩
          · obtain ⟨c', d', hmem, hle⟩ := ih k d (by omega)
              (edgeCCWCrossAt_imp gc q k hkCCW) (edgeCWCrossAt_imp gc q d hbCW)
              hkd (Or.inr ⟨hkCCW, hbCW⟩)
            exact ⟨c', d', hmem, by omega⟩
  exact hmain (d.val - c.val) c d le_rfl hc hd hlt htypes

theorem globalMin_satisfies_hglobal {sys : System} (gc : GoodCycle sys)
    (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n) (a b : Fin gc.configs.length)
    (hmem : (p, a, b) ∈ globalOppPairs gc)
    (hmin : ∀ triple ∈ globalOppPairs gc,
      b.val - a.val ≤ globalTripleGap triple) :
    ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d →
      c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b.val - a.val ≤ d.val - c.val := by
  intro q c d hc hd hlt htypes
  obtain ⟨c', d', hmem', hle⟩ :=
    exists_subpair_in_globalOppPairs gc q c d hc hd hlt htypes
  have hmin' := hmin (q, c', d') hmem'
  simp [globalTripleGap] at hmin'
  omega

/-! ### Wrapping entry conflict helpers -/

/-- CW-CCW wrapping case: when b₀ is the last index, the entry conflict wraps
    through index 0.  The stay chain gives mover = right(p₀) on [a₀+1, b₀],
    and the CCW crossing at b₀ wraps to moverAt(0) = p₀.
    Binary double-fire-returns preserves right(p₀) value across the wrap. -/
theorem minGapArc_elim_wrap_cwccw
    {sys : System} {gc : GoodCycle sys}
    (p₀ : Fin sys.rs.n) (a₀ b₀ : Fin gc.configs.length)
    (hcw_a₀ : edgeCWCrossAt gc p₀ a₀)
    (hccw_b₀ : edgeCCWCrossAt gc p₀ b₀)
    (hlt₀ : a₀.val < b₀.val)
    (hno₀ : ∀ k : Fin gc.configs.length,
      a₀.val < k.val → k.val < b₀.val → ¬edgeCrossAt' gc p₀ k)
    (hglobal₀ : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d →
      c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b₀.val - a₀.val ≤ d.val - c.val)
    (hgap2 : b₀.val - a₀.val ≥ 2)
    (hwrap : ¬(b₀.val + 1 < gc.configs.length))
    (hbin_rp₀ : isBinary sys.rs (right p₀)) :
    False := by
  have hbval : b₀.val + 1 = gc.configs.length := by have := b₀.isLt; omega
  have hbm1_lt : b₀.val - 1 < gc.configs.length := by have := b₀.isLt; omega
  -- Stay chain: interior movers = right(p₀)
  have hbm1_mover : gc.moverAt ⟨b₀.val - 1, hbm1_lt⟩ = right p₀ :=
    (MinGapArc.mk p₀ a₀ b₀ hcw_a₀ hccw_b₀ hlt₀ hno₀ hglobal₀).all_interior_mover_eq_right_p
      hgap2 ⟨b₀.val - 1, hbm1_lt⟩
      (show a₀.val < b₀.val - 1 by omega)
      (show b₀.val - 1 ≤ b₀.val by omega)
  have hb_mover : gc.moverAt b₀ = right p₀ := hccw_b₀.1
  -- nextIndex wraps to 0
  have hnext_zero : nextIndex gc.configs b₀ = ⟨0, gc.configs_length_pos⟩ :=
    Fin.ext (by simp [nextIndex, hbval, Nat.mod_self])
  -- moverAt(0) = p₀
  have h0_mover : gc.moverAt ⟨0, gc.configs_length_pos⟩ = p₀ := by
    have hnext := gc.eq_left_of_stepDir_eq_ccw hccw_b₀.2
    rw [hccw_b₀.1, left_right_eq_self] at hnext
    rw [hnext_zero] at hnext; exact hnext
  -- nextIndex(b₀-1) = b₀
  have hnext_bm1 : nextIndex gc.configs ⟨b₀.val - 1, hbm1_lt⟩ = b₀ :=
    Fin.ext (by simp [nextIndex]; rw [show b₀.val - 1 + 1 = b₀.val from by omega]; exact Nat.mod_eq_of_lt b₀.isLt)
  -- L preservation: left(p₀) unchanged from b₀-1 to 0
  have hne_lp₀ : left p₀ ≠ right p₀ := fun h => by
    have := congrArg Fin.val h; simp only [left_val, right_val] at this
    have hp := p₀.isLt; have hn' := sys.rs.n_ge_4
    by_cases h0 : p₀.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n),
        Nat.mod_eq_of_lt (by omega : sys.rs.n - 1 < sys.rs.n)] at this; omega
    · by_cases hlt : p₀.val + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt hlt] at this
        rw [show p₀.val + sys.rs.n - 1 = (p₀.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this; omega
      · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this
        rw [show p₀.val + sys.rs.n - 1 = (p₀.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this; omega
  have hne_p₀ : p₀ ≠ right p₀ := fun h => by
    have := congrArg Fin.val h; simp only [right_val] at this
    have hp := p₀.isLt
    by_cases hp1 : p₀.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp1] at this; omega
    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega
  -- configs[0](left p₀) = configs[b₀](left p₀) = configs[b₀-1](left p₀)
  have hL_b0_0 : (gc.configs.get ⟨0, gc.configs_length_pos⟩) (left p₀) =
      (gc.configs.get b₀) (left p₀) := by
    rw [← hnext_zero]; exact gc.state_eq_of_ne_moverAt b₀ (left p₀) (by rw [hb_mover]; exact hne_lp₀)
  have hL_b0_bm1 : (gc.configs.get b₀) (left p₀) =
      (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) (left p₀) := by
    have h := gc.state_eq_of_ne_moverAt ⟨b₀.val - 1, hbm1_lt⟩ (left p₀) (by rw [hbm1_mover]; exact hne_lp₀)
    rw [hnext_bm1] at h; exact h
  -- configs[0](p₀) = configs[b₀](p₀) = configs[b₀-1](p₀)
  have hS_b0_0 : (gc.configs.get ⟨0, gc.configs_length_pos⟩) p₀ =
      (gc.configs.get b₀) p₀ := by
    rw [← hnext_zero]; exact gc.state_eq_of_ne_moverAt b₀ p₀ (by rw [hb_mover]; exact hne_p₀)
  have hS_b0_bm1 : (gc.configs.get b₀) p₀ =
      (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) p₀ := by
    have h := gc.state_eq_of_ne_moverAt ⟨b₀.val - 1, hbm1_lt⟩ p₀ (by rw [hbm1_mover]; exact hne_p₀)
    rw [hnext_bm1] at h; exact h
  -- R preservation: right(p₀) is binary, fires at b₀-1 and b₀
  -- binary_double_fire_returns: stateAfter (right p₀) (b₀-1) = stateAfter (right p₀) (b₀+1)
  -- stateAfter (right p₀) (b₀-1) = configs[b₀-1](right p₀)  (since b₀-1 < L)
  -- stateAfter (right p₀) (b₀+1) = configs[0](right p₀)  (since b₀+1 = L, wraps)
  -- stateAfter wrapping: stateAfter q (b₀+1) = configs[0](q) when b₀+1 = L
  have stateAfter_wrap_eq : ∀ (q : Fin sys.rs.n),
      gc.stateAfter q (b₀.val + 1) = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q := by
    intro q
    rw [hbval, gc.stateAfter_of_ge q le_rfl]
    rfl  -- firstIndex = ⟨0, ...⟩ definitionally
  have hR : (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) (right p₀) =
      (gc.configs.get ⟨0, gc.configs_length_pos⟩) (right p₀) := by
    have hdfire := binary_double_fire_returns gc (right p₀) hbin_rp₀
      (b₀.val - 1) b₀.val hbm1_lt (by omega) (by omega) hbm1_mover
      (by rw [show (⟨b₀.val, by omega⟩ : Fin gc.configs.length) = b₀ from Fin.ext rfl]; exact hb_mover)
      (fun k hk1 hk2 => by omega)
    rw [gc.stateAfter_of_lt (right p₀) hbm1_lt] at hdfire
    rw [stateAfter_wrap_eq] at hdfire
    exact hdfire
  -- Entry conflict at p₀: mover at 0, non-mover at b₀-1
  have hne_mover : gc.moverAt ⟨b₀.val - 1, hbm1_lt⟩ ≠ p₀ := by
    rw [hbm1_mover]; intro h
    have hval := congrArg Fin.val h; simp only [right_val] at hval
    have hp := p₀.isLt; have hn' := sys.rs.n_ge_4
    by_cases hp1 : p₀.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp1] at hval; omega
    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
  exact entryConflict_impossible gc
    ⟨⟨0, gc.configs_length_pos⟩, ⟨b₀.val - 1, hbm1_lt⟩, p₀,
     h0_mover, hne_mover,
     hL_b0_0.trans hL_b0_bm1,
     hS_b0_0.trans hS_b0_bm1,
     hR.symm⟩

/-- CCW-CW wrapping case: symmetric to cwccw but with p₀ binary and stay chain
    on p₀.  The CW crossing at b₀ wraps to moverAt(0) = right(p₀). -/
theorem minGapArcRev_elim_wrap_ccwcw
    {sys : System} {gc : GoodCycle sys}
    (p₀ : Fin sys.rs.n) (a₀ b₀ : Fin gc.configs.length)
    (hccw_a₀ : edgeCCWCrossAt gc p₀ a₀)
    (hcw_b₀ : edgeCWCrossAt gc p₀ b₀)
    (hlt₀ : a₀.val < b₀.val)
    (hno₀ : ∀ k : Fin gc.configs.length,
      a₀.val < k.val → k.val < b₀.val → ¬edgeCrossAt' gc p₀ k)
    (hglobal₀ : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d →
      c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b₀.val - a₀.val ≤ d.val - c.val)
    (hgap2 : b₀.val - a₀.val ≥ 2)
    (hwrap : ¬(b₀.val + 1 < gc.configs.length))
    (hbin_p₀ : isBinary sys.rs p₀) :
    False := by
  have hbval : b₀.val + 1 = gc.configs.length := by have := b₀.isLt; omega
  have hbm1_lt : b₀.val - 1 < gc.configs.length := by have := b₀.isLt; omega
  -- Stay chain: interior movers = p₀ (reverse case)
  have hbm1_mover : gc.moverAt ⟨b₀.val - 1, hbm1_lt⟩ = p₀ :=
    (MinGapArcReverse.mk p₀ a₀ b₀ hccw_a₀ hcw_b₀ hlt₀ hno₀ hglobal₀).all_interior_mover_eq_p
      hgap2 ⟨b₀.val - 1, hbm1_lt⟩
      (show a₀.val < b₀.val - 1 by omega)
      (show b₀.val - 1 ≤ b₀.val by omega)
  have hb_mover : gc.moverAt b₀ = p₀ := hcw_b₀.1
  -- nextIndex wraps to 0
  have hnext_zero : nextIndex gc.configs b₀ = ⟨0, gc.configs_length_pos⟩ :=
    Fin.ext (by simp [nextIndex, hbval, Nat.mod_self])
  -- moverAt(0) = right(p₀) (CW at b₀ → next is right(moverAt b₀) = right(p₀))
  have h0_mover : gc.moverAt ⟨0, gc.configs_length_pos⟩ = right p₀ := by
    have hnext := gc.eq_right_of_stepDir_eq_cw hcw_b₀.2
    rw [hcw_b₀.1] at hnext
    rw [hnext_zero] at hnext; exact hnext
  -- nextIndex(b₀-1) = b₀
  have hnext_bm1 : nextIndex gc.configs ⟨b₀.val - 1, hbm1_lt⟩ = b₀ :=
    Fin.ext (by simp [nextIndex]; rw [show b₀.val - 1 + 1 = b₀.val from by omega]; exact Nat.mod_eq_of_lt b₀.isLt)
  -- Entry conflict at right(p₀): mover at 0, non-mover at b₀-1
  -- Need: configs[0](L,S,R) at right(p₀) = configs[b₀-1](L,S,R) at right(p₀)
  -- L at right(p₀) = left(right(p₀)) = p₀
  -- S at right(p₀) = right(p₀)
  -- R at right(p₀) = right(right(p₀))
  -- stateAfter wrapping: stateAfter q (b₀+1) = configs[0](q) when b₀+1 = L
  have stateAfter_wrap_eq : ∀ (q : Fin sys.rs.n),
      gc.stateAfter q (b₀.val + 1) = (gc.configs.get ⟨0, gc.configs_length_pos⟩) q := by
    intro q
    rw [hbval, gc.stateAfter_of_ge q le_rfl]
    -- Goal: configs[firstIndex](q) = configs[0](q)
    -- firstIndex = ⟨0, ...⟩ definitionally
    rfl
  -- p₀ fires at b₀-1 and b₀, binary → L value (p₀) returns
  have hL : (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) p₀ =
      (gc.configs.get ⟨0, gc.configs_length_pos⟩) p₀ := by
    have hdfire := binary_double_fire_returns gc p₀ hbin_p₀
      (b₀.val - 1) b₀.val hbm1_lt (by omega) (by omega) hbm1_mover
      (by rw [show (⟨b₀.val, by omega⟩ : Fin gc.configs.length) = b₀ from Fin.ext rfl]; exact hb_mover)
      (fun k hk1 hk2 => by omega)
    rw [gc.stateAfter_of_lt p₀ hbm1_lt] at hdfire
    rw [stateAfter_wrap_eq] at hdfire
    exact hdfire
  -- S and R: right(p₀) and right(right(p₀)) don't fire at b₀-1 or b₀
  have hne_rp₀ : right p₀ ≠ p₀ := fun h => by
    have := congrArg Fin.val h; simp only [right_val] at this
    have hp := p₀.isLt; have hn' := sys.rs.n_ge_4
    by_cases hp1 : p₀.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp1] at this; omega
    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega
  have hne_rrp₀ : right (right p₀) ≠ p₀ := fun h => by
    have := congrArg Fin.val h; simp only [right_val] at this
    have hp := p₀.isLt; have hn' := sys.rs.n_ge_4
    by_cases hp1 : p₀.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hp1] at this
      by_cases hp2 : p₀.val + 1 + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt hp2] at this; omega
      · rw [show p₀.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega
    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self,
        Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at this; omega
  -- configs[0](right p₀) = configs[b₀](right p₀) = configs[b₀-1](right p₀)
  have hS_b0_0 : (gc.configs.get ⟨0, gc.configs_length_pos⟩) (right p₀) =
      (gc.configs.get b₀) (right p₀) := by
    rw [← hnext_zero]; exact gc.state_eq_of_ne_moverAt b₀ (right p₀) (by rw [hb_mover]; exact hne_rp₀)
  have hS_b0_bm1 : (gc.configs.get b₀) (right p₀) =
      (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) (right p₀) := by
    have h := gc.state_eq_of_ne_moverAt ⟨b₀.val - 1, hbm1_lt⟩ (right p₀) (by rw [hbm1_mover]; exact hne_rp₀)
    rw [hnext_bm1] at h; exact h
  -- configs[0](right(right p₀)) = configs[b₀-1](right(right p₀))
  have hR_b0_0 : (gc.configs.get ⟨0, gc.configs_length_pos⟩) (right (right p₀)) =
      (gc.configs.get b₀) (right (right p₀)) := by
    rw [← hnext_zero]; exact gc.state_eq_of_ne_moverAt b₀ (right (right p₀)) (by rw [hb_mover]; exact hne_rrp₀)
  have hR_b0_bm1 : (gc.configs.get b₀) (right (right p₀)) =
      (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) (right (right p₀)) := by
    have h := gc.state_eq_of_ne_moverAt ⟨b₀.val - 1, hbm1_lt⟩ (right (right p₀)) (by rw [hbm1_mover]; exact hne_rrp₀)
    rw [hnext_bm1] at h; exact h
  -- Non-mover: right(p₀) ≠ moverAt(b₀-1) = p₀
  have hne : gc.moverAt ⟨b₀.val - 1, hbm1_lt⟩ ≠ right p₀ := by
    rw [hbm1_mover]; exact hne_rp₀.symm
  exact entryConflict_impossible gc
    ⟨⟨0, gc.configs_length_pos⟩, ⟨b₀.val - 1, hbm1_lt⟩, right p₀,
     h0_mover, hne,
     by rw [left_right_eq_self]; exact (hL).symm,
     (hS_b0_0.trans hS_b0_bm1),
     (hR_b0_0.trans hR_b0_bm1)⟩

end LeanMn
