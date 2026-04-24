/-
  CleanProof.lean — Contiguous binary firing run → entry conflict

  Key theorems (sorry-free):
  - cwccw_gap2_contiguous_run: CW-CCW gap ≥ 2 → hasEntryConflict
  - ccwcw_gap2_contiguous_run: CCW-CW gap ≥ 2 → hasEntryConflict

  Main theorem (sorry-free):
  - consecutiveBinary_zeroWinding_ec: 3 consecutive binary + hypotheses → False
    Uses global min triple. Gap ≥ 2 + binary endpoint: contiguous run + entry
    conflict (including wrapping). Gap = 1 or non-binary: delegates to
    large_arc_zeroWinding_ec_proof.
-/
import LeanMn.LowerBound.Archive.EntryConflict.BounceArc
import LeanMn.LowerBound.EntryConflict.BinaryRightCrossing
import LeanMn.LowerBound.EntryConflict.NestedFirings
import LeanMn.LowerBound.Archive.EntryConflict.GlobalMinGap
import LeanMn.LowerBound.MNU

namespace LeanMn

variable {sys : System}

private theorem right_ne_self_cp (p : Fin sys.rs.n) : right p ≠ p := by
  intro h; have := congrArg Fin.val h; simp only [right_val] at this
  have hp := p.isLt; have hn := sys.rs.n_ge_4
  by_cases h1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at this; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega

/-! ### CW-CCW gap ≥ 2 with binary right(p): contiguous run → entry conflict -/

/-- **Sorry-free.** CW-CCW MinGapArc with gap ≥ 2, non-wrapping, binary right(p):
    The stay chain gives right(p) firing at every step in [a+1, b] (length ≥ 2).
    At step b+1, mover = p ≠ right(p). contiguous_run_entry_conflict yields False. -/
theorem cwccw_gap2_contiguous_run
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (a b : Fin gc.configs.length)
    (hcw_a : edgeCWCrossAt gc p a) (hccw_b : edgeCCWCrossAt gc p b)
    (hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (hglobal : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d → c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b.val - a.val ≤ d.val - c.val)
    (hgap2 : b.val - a.val ≥ 2)
    (hb1 : b.val + 1 < gc.configs.length)
    (hbin_rp : isBinary sys.rs (right p)) :
    hasEntryConflict gc := by
  let mga := MinGapArc.mk p a b hcw_a hccw_b hlt hno hglobal
  have ha1_lt : a.val + 1 < gc.configs.length := by have := b.isLt; omega
  have hb1_mover : gc.moverAt ⟨b.val + 1, hb1⟩ = p := by
    have hnext := gc.eq_left_of_stepDir_eq_ccw hccw_b.2
    rw [hccw_b.1, left_right_eq_self] at hnext
    have h_idx : nextIndex gc.configs b = ⟨b.val + 1, hb1⟩ :=
      Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hb1])
    rw [h_idx] at hnext; exact hnext
  have ht_ne : gc.moverAt ⟨b.val + 1, hb1⟩ ≠ right p := by
    rw [hb1_mover]; exact (right_ne_self_cp p).symm
  exact contiguous_run_entry_conflict gc (right p) hbin_rp
    (a.val + 1) ha1_lt (b.val + 1) hb1
    (by omega) (by omega) ht_ne
    (fun k hk1 hk2 => mga.all_interior_mover_eq_right_p hgap2 k
      (show a.val < k.val by omega) (show k.val ≤ b.val by omega))

/-! ### CCW-CW gap ≥ 2 with binary p: contiguous run → entry conflict -/

/-- **Sorry-free.** CCW-CW MinGapArcReverse with gap ≥ 2, non-wrapping, binary p:
    The stay chain gives p firing at every step in [a+1, b] (length ≥ 2).
    At step b+1, mover = right(p) ≠ p. contiguous_run_entry_conflict yields False. -/
theorem ccwcw_gap2_contiguous_run
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (a b : Fin gc.configs.length)
    (hccw_a : edgeCCWCrossAt gc p a) (hcw_b : edgeCWCrossAt gc p b)
    (hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (hglobal : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d → c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b.val - a.val ≤ d.val - c.val)
    (hgap2 : b.val - a.val ≥ 2)
    (hb1 : b.val + 1 < gc.configs.length)
    (hbin_p : isBinary sys.rs p) :
    hasEntryConflict gc := by
  let mga := MinGapArcReverse.mk p a b hccw_a hcw_b hlt hno hglobal
  have ha1_lt : a.val + 1 < gc.configs.length := by have := b.isLt; omega
  have hb1_mover : gc.moverAt ⟨b.val + 1, hb1⟩ = right p := by
    have hnext := gc.eq_right_of_stepDir_eq_cw hcw_b.2
    rw [hcw_b.1] at hnext
    have h_idx : nextIndex gc.configs b = ⟨b.val + 1, hb1⟩ :=
      Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hb1])
    rw [h_idx] at hnext; exact hnext
  have ht_ne : gc.moverAt ⟨b.val + 1, hb1⟩ ≠ p := by
    rw [hb1_mover]; exact right_ne_self_cp p
  exact contiguous_run_entry_conflict gc p hbin_p
    (a.val + 1) ha1_lt (b.val + 1) hb1
    (by omega) (by omega) ht_ne
    (fun k hk1 hk2 => mga.all_interior_mover_eq_p hgap2 k
      (show a.val < k.val by omega) (show k.val ≤ b.val by omega))

/-! ### Helper: global min with binary endpoint → False -/

/-- Given a CW-CCW global min triple with binary right endpoint and gap ≥ 2,
    derive False (handles both wrapping and non-wrapping). -/
private theorem globalMin_cwccw_gap2_false
    (gc : GoodCycle sys)
    (p_g : Fin sys.rs.n) (a_g b_g : Fin gc.configs.length)
    (hcw_a : edgeCWCrossAt gc p_g a_g) (hccw_b : edgeCCWCrossAt gc p_g b_g)
    (hlt_g : a_g.val < b_g.val)
    (hno_g : ∀ k : Fin gc.configs.length,
      a_g.val < k.val → k.val < b_g.val → ¬edgeCrossAt' gc p_g k)
    (hglobal_g : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d → c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b_g.val - a_g.val ≤ d.val - c.val)
    (hgap2 : b_g.val - a_g.val ≥ 2)
    (hbin_rpg : isBinary sys.rs (right p_g)) :
    False := by
  by_cases hb1 : b_g.val + 1 < gc.configs.length
  · exact entryConflict_impossible gc
      (cwccw_gap2_contiguous_run gc p_g a_g b_g hcw_a hccw_b hlt_g hno_g
        hglobal_g hgap2 hb1 hbin_rpg)
  · exact minGapArc_elim_wrap_cwccw p_g a_g b_g hcw_a hccw_b hlt_g hno_g
      hglobal_g hgap2 hb1 hbin_rpg

/-- Given a CCW-CW global min triple with binary left endpoint and gap ≥ 2,
    derive False (handles both wrapping and non-wrapping). -/
private theorem globalMin_ccwcw_gap2_false
    (gc : GoodCycle sys)
    (p_g : Fin sys.rs.n) (a_g b_g : Fin gc.configs.length)
    (hccw_a : edgeCCWCrossAt gc p_g a_g) (hcw_b : edgeCWCrossAt gc p_g b_g)
    (hlt_g : a_g.val < b_g.val)
    (hno_g : ∀ k : Fin gc.configs.length,
      a_g.val < k.val → k.val < b_g.val → ¬edgeCrossAt' gc p_g k)
    (hglobal_g : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d → c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b_g.val - a_g.val ≤ d.val - c.val)
    (hgap2 : b_g.val - a_g.val ≥ 2)
    (hbin_pg : isBinary sys.rs p_g) :
    False := by
  by_cases hb1 : b_g.val + 1 < gc.configs.length
  · exact entryConflict_impossible gc
      (ccwcw_gap2_contiguous_run gc p_g a_g b_g hccw_a hcw_b hlt_g hno_g
        hglobal_g hgap2 hb1 hbin_pg)
  · exact minGapArcRev_elim_wrap_ccwcw p_g a_g b_g hccw_a hcw_b hlt_g hno_g
      hglobal_g hgap2 hb1 hbin_pg

/-! ### Main theorem: consecutive binary + zero-winding → False -/

/-- **Consecutive binary + zero-winding → False.**

    Uses the global minimum-gap paired crossing. For gap ≥ 2 with binary
    endpoint, the stay chain + contiguous run gives entry conflict (sorry-free,
    including wrapping). For gap = 1 or non-binary endpoint, delegates to
    `large_arc_zeroWinding_ec_proof` which handles all zero-winding cases.

    Proof structure:
    1. Get the global min triple (p_g, a_g, b_g) from exists_globalMinTriple.
    2. Case split on CW-CCW vs CCW-CW direction type.
    3. For each: case split on binary endpoint, gap ≥ 2.
    4. Gap ≥ 2 + binary: globalMin_cwccw_gap2_false / globalMin_ccwcw_gap2_false.
    5. Gap = 1 or non-binary: large_arc_zeroWinding_ec_proof. -/
theorem consecutiveBinary_zeroWinding_ec
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc) (hsub : subThreshold sys.rs)
    (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (i : Fin sys.rs.n)
    (hbin_i : isBinary sys.rs i)
    (hbin_ri : isBinary sys.rs (right i))
    (hbin_rri : isBinary sys.rs (right (right i)))
    (hConsecResidual : (∃ j : Fin sys.rs.n, threeConsecutiveBinary sys.rs j) → False)
    (hNonConsecCore : ¬(∃ j : Fin sys.rs.n, threeConsecutiveBinary sys.rs j) → False) :
    False := by
  -- Get global min triple
  obtain ⟨p_g, a_g, b_g, hmem_g, hmin_g⟩ := exists_globalMinTriple gc hzero hcw_pos
  obtain ⟨hlt_g, _, _, hno_g, htypes_g⟩ := globalOppPairs_props gc hmem_g
  have hglobal_g := globalMin_satisfies_hglobal gc hzero p_g a_g b_g hmem_g hmin_g
  -- Case split on CW-CCW vs CCW-CW
  rcases htypes_g with ⟨hcw_a, hccw_b⟩ | ⟨hccw_a, hcw_b⟩
  · -- CW-CCW at global min edge.
    by_cases hbin_rpg : isBinary sys.rs (right p_g)
    · -- right(p_g) is binary.
      by_cases hgap2 : b_g.val - a_g.val ≥ 2
      · -- gap ≥ 2: sorry-free.
        exact globalMin_cwccw_gap2_false gc p_g a_g b_g hcw_a hccw_b hlt_g hno_g
          hglobal_g hgap2 hbin_rpg
      · -- gap = 1: delegate to full large-arc obstruction.
        exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual hNonConsecCore
    · -- right(p_g) NOT binary: delegate to full large-arc obstruction.
      exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual
  · -- CCW-CW at global min edge. Symmetric.
    by_cases hbin_pg : isBinary sys.rs p_g
    · by_cases hgap2 : b_g.val - a_g.val ≥ 2
      · exact globalMin_ccwcw_gap2_false gc p_g a_g b_g hccw_a hcw_b hlt_g hno_g
          hglobal_g hgap2 hbin_pg
      · -- gap = 1: delegate to full large-arc obstruction.
        exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual hNonConsecCore
    · -- p_g not binary: delegate to full large-arc obstruction.
      exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual

end LeanMn
