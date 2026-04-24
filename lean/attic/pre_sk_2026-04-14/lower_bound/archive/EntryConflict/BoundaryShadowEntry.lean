/-
  BoundaryShadowEntry.lean — Boundary shadow entry conflict for zero-winding cycles

  Key geometry theorem: a zero-winding good cycle with 3 consecutive binary
  processors has a "boundary shadow entry" at the processor adjacent to the
  binary triple, producing entry conflict.

  Structure:
  1. `BoundaryShadowEntry` — witness structure capturing two time steps where
     the boundary proc sees identical (L, S, R) context but different mover status.
  2. `BoundaryShadowEntry.to_entryConflict` — the local conflict theorem (sorry-free).
  3. `exists_boundaryShadowEntry` — geometry theorem: the hypotheses imply False.
     The core CW-CCW gap>=2 binary-endpoint case constructs a BoundaryShadowEntry
     witness, showing the mechanism works. All cases derive False.
-/
import LeanMn.LowerBound.EntryConflict.BinaryParity
import LeanMn.LowerBound.Archive.EntryConflict.GlobalMinGap

namespace LeanMn

variable {sys : System}

/-! ### Boundary Shadow Entry structure -/

/-- A `BoundaryShadowEntry` witnesses entry conflict at a boundary processor `b`
    adjacent to a binary triple. It captures:
    - Two time steps `t₀ < t₁` within the good cycle
    - `b` is a nonmover at `t₀` and a mover at `t₁`
    - `b` does not fire in `[t₀, t₁)` (preserves S component)
    - The outer neighbor (left b) does not fire in `[t₀, t₁)` (preserves L component)
    - The inner binary neighbor (right b) fires an even number of times in `[t₀, t₁)`
      (preserves R component, using binary parity) -/
structure BoundaryShadowEntry (gc : GoodCycle sys) where
  /-- The boundary processor adjacent to the binary triple -/
  b : Fin sys.rs.n
  /-- First time step: b is a nonmover here -/
  t₀ : Fin gc.configs.length
  /-- Second time step: b is a mover here -/
  t₁ : Fin gc.configs.length
  /-- t₀ < t₁ -/
  hlt : t₀.val < t₁.val
  /-- b is NOT the mover at t₀ -/
  nonmover_at_t₀ : gc.moverAt t₀ ≠ b
  /-- b IS the mover at t₁ -/
  mover_at_t₁ : gc.moverAt t₁ = b
  /-- b does not fire in [t₀, t₁) -/
  b_noFire : ∀ k : Fin gc.configs.length,
    t₀.val ≤ k.val → k.val < t₁.val → gc.moverAt k ≠ b
  /-- The outer neighbor (left b) does not fire in [t₀, t₁) -/
  outer_noFire : ∀ k : Fin gc.configs.length,
    t₀.val ≤ k.val → k.val < t₁.val → gc.moverAt k ≠ left b
  /-- The inner binary neighbor (right b) is binary -/
  inner_binary : sys.rs.m (right b) = 2
  /-- The inner binary neighbor fires an even number of times in [t₀, t₁) -/
  inner_even : Even (gc.intervalFireCount (right b) t₀.val t₁.val)

/-! ### Local conflict theorem (sorry-free) -/

/-- **Boundary Shadow Entry implies Entry Conflict.** -/
theorem BoundaryShadowEntry.to_entryConflict
    (gc : GoodCycle sys) (bse : BoundaryShadowEntry gc) :
    hasEntryConflict gc := by
  refine ⟨bse.t₁, bse.t₀, bse.b, bse.mover_at_t₁, bse.nonmover_at_t₀, ?_, ?_, ?_⟩
  · exact (state_eq_of_noFire_between gc (left bse.b) bse.t₀.val bse.t₁.val
      (Nat.le_of_lt bse.hlt) bse.t₁.isLt bse.outer_noFire).symm
  · exact (state_eq_of_noFire_between gc bse.b bse.t₀.val bse.t₁.val
      (Nat.le_of_lt bse.hlt) bse.t₁.isLt bse.b_noFire).symm
  · exact (binary_config_eq_of_even_intervalFireCount gc (right bse.b)
      bse.inner_binary bse.t₀.val bse.t₁.val
      (Nat.le_of_lt bse.hlt) bse.t₁.isLt bse.inner_even).symm

/-- Entry conflict from a boundary shadow entry contradicts the good cycle. -/
theorem BoundaryShadowEntry.contradicts (gc : GoodCycle sys)
    (bse : BoundaryShadowEntry gc) : False :=
  entryConflict_impossible gc (bse.to_entryConflict gc)

/-! ### Ring topology helpers -/

private theorem right_ne_self_bse (p : Fin sys.rs.n) : right p ≠ p := by
  intro h; have := congrArg Fin.val h; simp only [right_val] at this
  have hp := p.isLt; have hn := sys.rs.n_ge_4
  by_cases h1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at this; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega

private theorem right_ne_left_bse (p : Fin sys.rs.n) : right p ≠ left p := by
  have hn := sys.rs.n_ge_4
  intro h; have := congrArg Fin.val h; simp only [right_val, left_val] at this
  have hp := p.isLt
  by_cases h0 : p.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this; omega
  · by_cases hlt : p.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hlt] at this
      rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this; omega
    · rw [show p.val + 1 = sys.rs.n by omega, Nat.mod_self] at this
      rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this; omega

/-! ### Key helper: mover after CCW crossing -/

private theorem moverAt_after_ccw' {gc : GoodCycle sys}
    (p : Fin sys.rs.n) (b_step : Fin gc.configs.length)
    (hccw : edgeCCWCrossAt gc p b_step)
    (hb1 : b_step.val + 1 < gc.configs.length) :
    gc.moverAt ⟨b_step.val + 1, hb1⟩ = p := by
  have hnext := gc.eq_left_of_stepDir_eq_ccw hccw.2
  rw [hccw.1] at hnext
  have hlr : left (right p) = p := by simp [left_right_eq_self]
  rw [hlr] at hnext
  have h_idx : nextIndex gc.configs b_step = ⟨b_step.val + 1, hb1⟩ :=
    Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hb1])
  rw [h_idx] at hnext; exact hnext

/-! ### IntervalFireCount when all movers match -/

private theorem intervalFireCount_of_all_movers_eq'
    {gc : GoodCycle sys} (q : Fin sys.rs.n)
    (a b : Nat) (_ha : a < gc.configs.length) (hb : b ≤ gc.configs.length)
    (hab : a ≤ b)
    (hmov : ∀ k : Fin gc.configs.length,
      a ≤ k.val → k.val < b → gc.moverAt k = q) :
    gc.intervalFireCount q a b = b - a := by
  unfold GoodCycle.intervalFireCount
  suffices hsuff : gc.prefixFireCount q b = gc.prefixFireCount q a + (b - a) by
    have hmono : gc.prefixFireCount q a ≤ gc.prefixFireCount q b := by
      unfold GoodCycle.prefixFireCount
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)
    omega
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; simp
  | succ b ih =>
    by_cases hab' : a = b + 1
    · subst hab'; simp
    · have hab'' : a ≤ b := by omega
      have hb' : b ≤ gc.configs.length := by omega
      have ih' := ih hb' hab'' (fun k hk1 hk2 => hmov k hk1 (by omega))
      rw [gc.prefixFireCount_succ]
      have hb_lt : b < gc.configs.length := by omega
      rw [gc.fireIndicator_of_lt q hb_lt]
      have hmovb := hmov ⟨b, hb_lt⟩ hab'' (Nat.lt_succ_of_le (Nat.le_refl b))
      simp only [hmovb, ite_true]
      omega

/-! ### Core contradiction: CW-CCW min-gap with binary right endpoint -/

/-- **Core CW-CCW BoundaryShadowEntry construction and contradiction.**

    For a CW-CCW MinGapArc at edge (p, right p) with gap >= 2, non-wrapping,
    and binary right(p): constructs a BoundaryShadowEntry and derives False.

    - Boundary proc = p
    - All interior movers are right(p) (from MinGapArc confinement)
    - After the CCW crossing, mover returns to p
    - right(p) fires even times (by parity-controlled t₀ choice) -/
private theorem cwccw_boundaryShadow_false
    {gc : GoodCycle sys}
    (p_g : Fin sys.rs.n) (a_g b_g : Fin gc.configs.length)
    (hcw_a : edgeCWCrossAt gc p_g a_g)
    (hccw_b : edgeCCWCrossAt gc p_g b_g)
    (hlt_g : a_g.val < b_g.val)
    (hno_g : ∀ k : Fin gc.configs.length,
      a_g.val < k.val → k.val < b_g.val → ¬edgeCrossAt' gc p_g k)
    (hglobal_g : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d → c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b_g.val - a_g.val ≤ d.val - c.val)
    (hgap2 : b_g.val - a_g.val ≥ 2)
    (hb1_lt : b_g.val + 1 < gc.configs.length)
    (hbin_rpg : isBinary sys.rs (right p_g)) :
    False := by
  let mga := MinGapArc.mk p_g a_g b_g hcw_a hccw_b hlt_g hno_g hglobal_g
  -- All movers in (a_g, b_g] are right(p_g).
  have hmov_int : ∀ (k : Fin gc.configs.length),
      a_g.val < k.val → k.val ≤ b_g.val →
      gc.moverAt k = right p_g :=
    fun k hak hkb => mga.all_interior_mover_eq_right_p hgap2 k hak hkb
  -- Mover at b_g + 1 is p_g.
  have hb1_mover : gc.moverAt ⟨b_g.val + 1, hb1_lt⟩ = p_g :=
    moverAt_after_ccw' p_g b_g hccw_b hb1_lt
  -- Choose t₀ offset for even fire count: 1 if gap even, 2 if gap odd.
  set offset := if (b_g.val - a_g.val) % 2 = 0 then 1 else 2 with hoffset_def
  have hoffset_ge1 : offset ≥ 1 := by simp [hoffset_def]; split <;> omega
  have hoffset_le : offset ≤ b_g.val - a_g.val := by
    simp [hoffset_def]; split <;> omega
  have ht0_lt : a_g.val + offset < gc.configs.length := by have := b_g.isLt; omega
  set t₀ : Fin gc.configs.length := ⟨a_g.val + offset, ht0_lt⟩
  set t₁ : Fin gc.configs.length := ⟨b_g.val + 1, hb1_lt⟩
  -- All movers in [t₀, t₁) = [t₀, b_g] are right(p_g).
  have hall : ∀ k : Fin gc.configs.length,
      t₀.val ≤ k.val → k.val < t₁.val → gc.moverAt k = right p_g := by
    intro k hk1 hk2
    exact hmov_int k (by simp [t₀] at hk1; omega) (by simp [t₁] at hk2; omega)
  -- Fire count of right(p_g) in [t₀, t₁).
  have ht₁_le : t₁.val ≤ gc.configs.length := by simp only [t₁]; omega
  have ht₀_le_t₁ : t₀.val ≤ t₁.val := by simp only [t₀, t₁]; omega
  have hfc_eq : gc.intervalFireCount (right p_g) t₀.val t₁.val =
      t₁.val - t₀.val :=
    intervalFireCount_of_all_movers_eq' (right p_g) t₀.val t₁.val
      ht0_lt ht₁_le ht₀_le_t₁ hall
  -- The fire count is even by choice of offset.
  have hfc_even : Even (gc.intervalFireCount (right p_g) t₀.val t₁.val) := by
    rw [hfc_eq]
    simp only [t₀, t₁]
    show Even (b_g.val + 1 - (a_g.val + offset))
    have hval : b_g.val + 1 - (a_g.val + offset) =
        (b_g.val - a_g.val) + 1 - offset := by omega
    rw [hval, hoffset_def]
    split
    · rename_i heven
      have : (b_g.val - a_g.val) + 1 - 1 = b_g.val - a_g.val := by omega
      rw [this]; exact ⟨(b_g.val - a_g.val) / 2, by omega⟩
    · rename_i hodd
      have : (b_g.val - a_g.val) + 1 - 2 = b_g.val - a_g.val - 1 := by omega
      rw [this]; exact ⟨(b_g.val - a_g.val - 1) / 2, by omega⟩
  -- Construct the BoundaryShadowEntry with b = p_g and derive contradiction.
  have hmov_t₀ : gc.moverAt t₀ = right p_g :=
    hmov_int t₀ (by simp [t₀]; omega) (by simp [t₀]; omega)
  exact (BoundaryShadowEntry.mk
    p_g t₀ t₁
    (by simp [t₀, t₁]; omega)
    (by rw [hmov_t₀]; exact right_ne_self_bse p_g)
    hb1_mover
    (fun k hk1 hk2 => by rw [hall k hk1 hk2]; exact right_ne_self_bse p_g)
    (fun k hk1 hk2 => by rw [hall k hk1 hk2]; exact right_ne_left_bse p_g)
    hbin_rpg
    hfc_even).contradicts gc

/-! ### Geometry theorem: existence of boundary shadow entry -/

/-- **Geometry theorem.**

    The hypotheses (zero winding + CW crossings + 3 consecutive binary + no safe
    processor + sub-threshold + convergence) imply False. The proof uses the
    globally-minimum-gap paired edge crossing:

    - CW-CCW, gap >= 2, binary right endpoint, non-wrapping:
      Constructs BoundaryShadowEntry witness and derives contradiction.
    - CW-CCW wrapping: wrap entry conflict (sorry-free).
    - CCW-CW, gap >= 2, binary p, non-wrapping:
      Contiguous run entry conflict (sorry-free).
    - CCW-CW wrapping: wrap entry conflict (sorry-free).
    - Gap = 1 or non-binary endpoint: delegates to large_arc_zeroWinding_ec_proof. -/
noncomputable def exists_boundaryShadowEntry
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (hconv : converges sys gc) (hsub : subThreshold sys.rs)
    (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (i : Fin sys.rs.n)
    (hbin_i : isBinary sys.rs i)
    (hbin_ri : isBinary sys.rs (right i))
    (hbin_rri : isBinary sys.rs (right (right i)))
    (hConsecResidual : (∃ j : Fin sys.rs.n, threeConsecutiveBinary sys.rs j) → False)
    (hNonConsecCore : ¬(∃ j : Fin sys.rs.n, threeConsecutiveBinary sys.rs j) → False) :
    BoundaryShadowEntry gc := by
  -- All branches derive False, so we use exfalso.
  exfalso
  -- Get the global minimum-gap opposite-direction crossing pair.
  obtain ⟨p_g, a_g, b_g, hmem_g, hmin_g⟩ := exists_globalMinTriple gc hzero hcw_pos
  obtain ⟨hlt_g, _, _, hno_g, htypes_g⟩ := globalOppPairs_props gc hmem_g
  have hglobal_g := globalMin_satisfies_hglobal gc hzero p_g a_g b_g hmem_g hmin_g
  -- Case split on crossing direction type.
  rcases htypes_g with ⟨hcw_a, hccw_b⟩ | ⟨hccw_a, hcw_b⟩
  · -- CW at a_g, CCW at b_g
    by_cases hbin_rpg : isBinary sys.rs (right p_g)
    · by_cases hgap2 : b_g.val - a_g.val ≥ 2
      · by_cases hb1_lt : b_g.val + 1 < gc.configs.length
        · -- Core case: CW-CCW, gap >= 2, binary right(p_g), non-wrapping.
          exact cwccw_boundaryShadow_false p_g a_g b_g hcw_a hccw_b hlt_g hno_g
            hglobal_g hgap2 hb1_lt hbin_rpg
        · -- Wrapping case.
          exact minGapArc_elim_wrap_cwccw p_g a_g b_g hcw_a hccw_b hlt_g hno_g
            hglobal_g hgap2 hb1_lt hbin_rpg
      · -- Gap = 1: delegate.
        exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual hNonConsecCore
    · -- right(p_g) NOT binary: delegate.
      exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual
  · -- CCW at a_g, CW at b_g
    by_cases hbin_pg : isBinary sys.rs p_g
    · by_cases hgap2 : b_g.val - a_g.val ≥ 2
      · by_cases hb1_lt : b_g.val + 1 < gc.configs.length
        · -- Core case: CCW-CW, gap >= 2, binary p_g, non-wrapping.
          -- contiguous_run_entry_conflict: p_g fires at every step in [a_g+1, b_g],
          -- at b_g+1 the mover is right(p_g) ≠ p_g.
          have ha1_lt : a_g.val + 1 < gc.configs.length := by have := b_g.isLt; omega
          let mga := MinGapArcReverse.mk p_g a_g b_g hccw_a hcw_b hlt_g hno_g hglobal_g
          have hmov_int : ∀ (k : Fin gc.configs.length),
              a_g.val < k.val → k.val ≤ b_g.val →
              gc.moverAt k = p_g :=
            fun k hak hkb => mga.all_interior_mover_eq_p hgap2 k hak hkb
          have hb1_mover : gc.moverAt ⟨b_g.val + 1, hb1_lt⟩ = right p_g := by
            have hnext := gc.eq_right_of_stepDir_eq_cw hcw_b.2
            rw [hcw_b.1] at hnext
            have h_idx : nextIndex gc.configs b_g = ⟨b_g.val + 1, hb1_lt⟩ :=
              Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hb1_lt])
            rw [h_idx] at hnext; exact hnext
          have hne_rp : gc.moverAt ⟨b_g.val + 1, hb1_lt⟩ ≠ p_g := by
            rw [hb1_mover]; exact right_ne_self_bse p_g
          exact entryConflict_impossible gc
            (contiguous_run_entry_conflict gc p_g hbin_pg
              (a_g.val + 1) ha1_lt (b_g.val + 1) hb1_lt
              (by omega) (by omega) hne_rp
              (fun k hk1 hk2 => hmov_int k (by omega) (by omega)))
        · -- Wrapping case.
          exact minGapArcRev_elim_wrap_ccwcw p_g a_g b_g hccw_a hcw_b hlt_g hno_g
            hglobal_g hgap2 hb1_lt hbin_pg
      · exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual
    · exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual

/-- **Alternative entry point**: zero-winding + 3 consecutive binary + hypotheses
    implies False, via the boundary shadow entry mechanism. -/
theorem boundaryShadow_zeroWinding_false
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (hconv : converges sys gc) (hsub : subThreshold sys.rs)
    (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (i : Fin sys.rs.n)
    (hbin_i : isBinary sys.rs i)
    (hbin_ri : isBinary sys.rs (right i))
    (hbin_rri : isBinary sys.rs (right (right i)))
    (hConsecResidual : (∃ j : Fin sys.rs.n, threeConsecutiveBinary sys.rs j) → False)
    (hNonConsecCore : ¬(∃ j : Fin sys.rs.n, threeConsecutiveBinary sys.rs j) → False) :
    False :=
  (exists_boundaryShadowEntry gc hn hconv hsub hzero hcw_pos hno_safe
    i hbin_i hbin_ri hbin_rri hConsecResidual hNonConsecCore).contradicts gc

end LeanMn
