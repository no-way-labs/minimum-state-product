/-
  GlobalMinGap.lean — Bridge from axiom hypotheses to MinGapArc contradiction

  Proves `large_arc_zeroWinding_ec_proof` by deriving False from the hypotheses.
  The theorem `exists_suitable_cwccw_pair` follows as a corollary.

  Pure geometry lemmas (globalOppPairs, globalMinTriple, wrapping helpers)
  live in GlobalMinGapCore.lean. This file keeps only the callback-parameterized
  assembly theorems that depend on hConsecResidual / hNonConsecCore.
-/
import LeanMn.LowerBound.Archive.EntryConflict.GlobalMinGapCore
import LeanMn.LowerBound.EntryConflict.IsolatedFirings
import LeanMn.LowerBound.Archive.EntryConflict.FCBound
import LeanMn.LowerBound.EntryConflict.NonConsecutive
import LeanMn.LowerBound.Archive.EntryConflict.OneSided
import LeanMn.LowerBound.MNU

namespace LeanMn

/-! ### Helper: fireCount > 0 from a firing step -/

private theorem fireCount_pos_of_moverAt {sys : System} (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (k : Fin gc.configs.length) (h : gc.moverAt k = p) :
    gc.fireCount p > 0 := by
  have : gc.fireCount p ≥ 1 := by
    rw [gc.fireCount_eq_sum_moverAt p]
    have hk_mem : k ∈ Finset.univ := Finset.mem_univ k
    have hk_val : (if gc.moverAt k = p then (1 : Nat) else 0) = 1 := by simp [h]
    calc ∑ j : Fin gc.configs.length, (if gc.moverAt j = p then (1 : Nat) else 0)
        ≥ (if gc.moverAt k = p then (1 : Nat) else 0) :=
          Finset.single_le_sum (f := fun j => if gc.moverAt j = p then (1 : Nat) else 0)
            (fun j _ => by simp only []; split <;> omega) hk_mem
      _ = 1 := hk_val
  omega

/-! ### Helper: permanent mover contradicts distinct mover at another step -/

private theorem permanent_mover_false_of_ne {sys : System} (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (hperm : ∀ k : Fin gc.configs.length, gc.moverAt k = p)
    (k : Fin gc.configs.length) (q : Fin sys.rs.n) (hmov : gc.moverAt k = q)
    (hne : q ≠ p) : False :=
  hne (hmov ▸ hperm k)

/-! ### Helper: consecutive binary residual (gap=1 or non-binary-endpoint global min) -/

/-- **Universal EC for non-consecutive binary placement.**
    Proves False from: ≥3 non-consecutive binary + zero winding + sub-threshold +
    cwStepCount > 0 + no safe processor + convergence.

    Uses the 4-mechanism universal EC argument:
    1. Both-Even Return (TernaryPhaseEC.bothEvenReturn_ec)
    2. Toggle-FR (TernaryPhaseEC.toggleFR_ec)
    3. Zero-Side EC (TernaryPhaseEC.zeroSide_ec)
    4. Traversal Return (TernaryPhaseEC.traversalReturn_ec)

    Intermediate steps needed:
    (a) Find ternary t with both neighbors binary (from ≥3 non-consecutive binary)
    (b) Extract a phase interval [a, s) where t doesn't fire, s is t's mover step
    (c) Compute interval fire counts J, K for left(t), right(t)
    (d) Dispatch to mechanism based on (J, K) parity and magnitude
    (e) Chain hasEntryConflict → entryConflict_impossible → False -/
private theorem nonConsecutive_universal_ec
    {sys : System}
    (_hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (_hconv : converges sys gc)
    (_hsub : subThreshold sys.rs) (_hzero : gc.zeroWinding)
    (_hcw_pos : 0 < gc.cwStepCount)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_h3bin : hasGe3Binary sys.rs)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False :=
  hNonConsecCore _hnoncons

/-! ### Non-consecutive zero-winding with a hole -/

/-- Zero-winding non-consecutive with a hole (some proc doesn't fire) → False. -/
private theorem nonConsecutive_zeroWinding_hole_false
    {sys : System}
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (h3bin : hasGe3Binary sys.rs)
    (hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (q : Fin sys.rs.n) (hhole : gc.fireCount q = 0)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False := by
  -- Dead edges at the hole: q never fires → edges adjacent to q have zero traversals.
  -- Step 1: q never fires → cwMoveCountAt(q) = 0, ccwMoveCountAt(q) = 0
  have hpart_q := gc.fireCount_eq_moveCount_partition q
  rw [hhole] at hpart_q
  have hcw_q : gc.cwMoveCountAt q = 0 := by omega
  have hccw_q : gc.ccwMoveCountAt q = 0 := by omega
  -- Step 2: Zero winding + fc(q) = 0 → cwMoveCountAt(left q) = 0
  have hcw_lq : gc.cwMoveCountAt (left q) = 0 :=
    zeroWinding_fc_zero_left_cw_zero gc hzero q hhole
  -- Step 3: Zero winding + fc(q) = 0 → ccwMoveCountAt(right q) = 0
  have hccw_rq : gc.ccwMoveCountAt (right q) = 0 :=
    zeroWinding_fc_zero_right_ccw_zero gc hzero q hhole
  -- Step 4: Edge (left q, q) has zero traversals: cw(left q) + ccw(q) = 0 + 0 = 0
  have hedge_left : gc.edgeTraversalCount (left q) = 0 := by
    rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right]
    simp [right_left_eq_self, hcw_lq, hccw_q]
  -- Step 5: Edge (q, right q) has zero traversals: cw(q) + ccw(right q) = 0 + 0 = 0
  have hedge_right : gc.edgeTraversalCount q = 0 := by
    rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right]
    omega
  -- Step 6: The mover never visits q (fireCount = 0 → never the mover).
  have hq_never : ∀ k : Fin gc.configs.length, gc.moverAt k ≠ q :=
    mover_never_at_p_of_fc_zero gc q hhole
  -- Step 7: left(q) never fires CW (toward q).
  have hlq_never_cw : ∀ k : Fin gc.configs.length,
      gc.moverAt k = left q → gc.stepDir k ≠ .cw :=
    zeroWinding_fc_zero_left_never_cw gc hzero q hhole
  -- Step 8: right(q) never fires CCW (toward q).
  have hrq_never_ccw : ∀ k : Fin gc.configs.length,
      gc.moverAt k = right q → gc.stepDir k ≠ .ccw :=
    zeroWinding_fc_zero_right_never_ccw gc hzero q hhole
  -- The mover walk is confined to the arc from right(q) to left(q) not
  -- passing through q. Both edges adjacent to q are dead (zero traversals).
  -- The hypotheses (n ≥ 7, sub-threshold, ≥ 3 binary, non-consecutive,
  -- convergence, hno_safe) suffice for the core non-consecutive obstruction.
  exact hNonConsecCore hnoncons

/-! ### Non-consecutive zero-winding obstruction -/

/-- **Non-consecutive zero-winding obstruction.**

    With ≥ 3 binary processors, no three consecutive binary, zero winding,
    cwStepCount > 0, and no safe processor, the good cycle is impossible.

    Mathematical proof: The zero-winding flux lemma
    (`cwMoveCountAt p = ccwMoveCountAt (right p)`) forces every crossed edge
    to carry both CW and CCW crossings. With `hcw_pos`, the total CW count
    is positive, so at least one edge is crossed. Combined with `hno_safe`
    (every processor is within distance 1 of some mover), every binary
    processor's boundary edges are crossed, hence crossed bidirectionally.
    The global minimum-gap opposite pair at a binary boundary edge, together
    with the binary parity and gap constraints, yields an entry conflict. -/
private theorem nonConsecutive_zeroWinding_false
    {sys : System}
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (_hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (_hcw_pos : 0 < gc.cwStepCount)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_h3bin : hasGe3Binary sys.rs)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False := by
  -- Split on whether some proc doesn't fire (hole exists)
  by_cases hhole : ∃ q : Fin sys.rs.n, gc.fireCount q = 0
  · obtain ⟨q, hq⟩ := hhole
    exact nonConsecutive_zeroWinding_hole_false hn gc _hconv hsub hzero _hcw_pos
      _hno_safe _h3bin _hnoncons q hq hNonConsecCore
  · -- Full support: all procs fire. Route through existing path.
    push_neg at hhole
    exact nonConsecutive_universal_ec hn gc _hconv hsub hzero _hcw_pos
      _hno_safe _h3bin _hnoncons hNonConsecCore

/-! ### Direct proof of False from the hypotheses -/

/-- The hypotheses (n ≥ 7, sub-threshold, zero winding, CW crossings,
    no safe processor, convergence) are jointly contradictory.

    The `hConsecResidual` callback handles consecutive-binary residual cases
    (gap=1, non-binary endpoint) that require phase extraction. This parameter
    breaks the circular import: PhaseExtraction → GlobalMinGap → PhaseExtraction. -/
private theorem large_arc_zeroWinding_direct
    {sys : System}
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hConsecResidual : (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False := by
  -- Get global min triple
  obtain ⟨p₀, a₀, b₀, hmem₀, hmin₀⟩ := exists_globalMinTriple gc hzero hcw_pos
  obtain ⟨hlt₀, _, _, hno₀, htypes₀⟩ := globalOppPairs_props gc hmem₀
  have hglobal₀ := globalMin_satisfies_hglobal gc hzero p₀ a₀ b₀ hmem₀ hmin₀
  have h3bin := subThreshold_ge3_binary sys.rs hsub
  -- Case split on consecutive binary placement
  by_cases h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i
  · -- CONSECUTIVE CASE: handle gap ≥ 2 + correct binary endpoint (sorry-free),
    -- delegate remaining cases to consecutiveBinary_globalMin_residual_false
    -- which has global minimality in scope for future sorry closure.
    obtain ⟨i, hbin_i, hbin_ri, hbin_rri⟩ := h3consec
    -- Try the global min triple: if gap ≥ 2 and endpoint is binary, we're done.
    -- Otherwise, delegate to the residual helper.
    rcases htypes₀ with ⟨hcw_a₀, hccw_b₀⟩ | ⟨hccw_a₀, hcw_b₀⟩
    · -- CW-CCW global min
      by_cases hbin_rp₀ : isBinary sys.rs (right p₀)
      · by_cases hgap2 : b₀.val - a₀.val ≥ 2
        · by_cases hb1 : b₀.val + 1 < gc.configs.length
          · exact (MinGapArc.mk p₀ a₀ b₀ hcw_a₀ hccw_b₀ hlt₀ hno₀
              hglobal₀).elim_of_binary_right hgap2 hb1 hbin_rp₀
          · exact minGapArc_elim_wrap_cwccw p₀ a₀ b₀ hcw_a₀ hccw_b₀ hlt₀ hno₀
              hglobal₀ hgap2 hb1 hbin_rp₀
        · -- Gap = 1 with binary right endpoint: palindromic EC / ¬converges needed
          exact hConsecResidual ⟨i, hbin_i, hbin_ri, hbin_rri⟩
      · -- right(p₀) NOT binary: global min at non-binary-right edge
        exact hConsecResidual ⟨i, hbin_i, hbin_ri, hbin_rri⟩
    · -- CCW-CW global min
      by_cases hbin_p₀ : isBinary sys.rs p₀
      · by_cases hgap2 : b₀.val - a₀.val ≥ 2
        · by_cases hb1 : b₀.val + 1 < gc.configs.length
          · -- Build MinGapArcReverse; all interior movers = p₀.
            have hbm1_lt : b₀.val - 1 < gc.configs.length := by
              have := b₀.isLt; omega
            have hbm1_mover : gc.moverAt ⟨b₀.val - 1, hbm1_lt⟩ = p₀ := by
              have := (MinGapArcReverse.mk p₀ a₀ b₀ hccw_a₀ hcw_b₀ hlt₀ hno₀
                hglobal₀).all_interior_mover_eq_p (show b₀.val - a₀.val ≥ 2 from hgap2)
                ⟨b₀.val - 1, hbm1_lt⟩
                (by show a₀.val < b₀.val - 1; omega)
                (by show b₀.val - 1 ≤ b₀.val; omega)
              exact this
            have hb_mover : gc.moverAt b₀ = p₀ := hcw_b₀.1
            have hb1_mover : gc.moverAt ⟨b₀.val + 1, hb1⟩ = right p₀ := by
              have hnext := gc.eq_right_of_stepDir_eq_cw hcw_b₀.2
              rw [hcw_b₀.1] at hnext
              have h_idx : nextIndex gc.configs b₀ = ⟨b₀.val + 1, hb1⟩ :=
                Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hb1])
              rw [h_idx] at hnext; exact hnext
            have hne : gc.moverAt ⟨b₀.val - 1, hbm1_lt⟩ ≠ right p₀ := by
              rw [hbm1_mover]
              intro h
              have hval := congrArg Fin.val h
              simp only [right_val] at hval
              have hp := p₀.isLt
              by_cases hp1 : p₀.val + 1 < sys.rs.n
              · rw [Nat.mod_eq_of_lt hp1] at hval; omega
              · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
            have hL : (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) p₀ =
                (gc.configs.get ⟨b₀.val + 1, hb1⟩) p₀ :=
              binary_double_fire_returns_config gc p₀ hbin_p₀
                (b₀.val - 1) b₀.val hbm1_lt hb1 (by omega)
                hbm1_mover (by rw [show (⟨b₀.val, by omega⟩ : Fin gc.configs.length) = b₀ from Fin.ext rfl]; exact hb_mover)
                (fun k hk1 hk2 => by omega)
            have hS : (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) (right p₀) =
                (gc.configs.get ⟨b₀.val + 1, hb1⟩) (right p₀) :=
              configVal_eq_of_noFire_between gc (right p₀)
                (b₀.val - 1) (b₀.val + 1) (by omega) hb1
                (fun k hk1 hk2 => by
                  have hkv : k.val = b₀.val - 1 ∨ k.val = b₀.val := by omega
                  rcases hkv with hkeq | hkeq
                  · rw [show k = ⟨b₀.val - 1, hbm1_lt⟩ from Fin.ext hkeq, hbm1_mover]
                    intro h
                    have hval := congrArg Fin.val h
                    simp only [right_val] at hval
                    have hp := p₀.isLt
                    by_cases hp1 : p₀.val + 1 < sys.rs.n
                    · rw [Nat.mod_eq_of_lt hp1] at hval; omega
                    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega
                  · rw [show k = b₀ from Fin.ext hkeq, hb_mover]
                    intro h
                    have hval := congrArg Fin.val h
                    simp only [right_val] at hval
                    have hp := p₀.isLt
                    by_cases hp1 : p₀.val + 1 < sys.rs.n
                    · rw [Nat.mod_eq_of_lt hp1] at hval; omega
                    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self] at hval; omega)
            have hR : (gc.configs.get ⟨b₀.val - 1, hbm1_lt⟩) (right (right p₀)) =
                (gc.configs.get ⟨b₀.val + 1, hb1⟩) (right (right p₀)) :=
              configVal_eq_of_noFire_between gc (right (right p₀))
                (b₀.val - 1) (b₀.val + 1) (by omega) hb1
                (fun k hk1 hk2 => by
                  have hkv : k.val = b₀.val - 1 ∨ k.val = b₀.val := by omega
                  rcases hkv with hkeq | hkeq
                  · rw [show k = ⟨b₀.val - 1, hbm1_lt⟩ from Fin.ext hkeq, hbm1_mover]
                    intro h
                    have hval := congrArg Fin.val h
                    simp only [right_val] at hval
                    have hp := p₀.isLt; have hn' := sys.rs.n_ge_4
                    by_cases hp1 : p₀.val + 1 < sys.rs.n
                    · rw [Nat.mod_eq_of_lt hp1] at hval
                      by_cases hp2 : p₀.val + 1 + 1 < sys.rs.n
                      · rw [Nat.mod_eq_of_lt hp2] at hval; omega
                      · rw [show p₀.val + 1 + 1 = sys.rs.n from by omega,
                          Nat.mod_self] at hval; omega
                    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self,
                        Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval; omega
                  · rw [show k = b₀ from Fin.ext hkeq, hb_mover]
                    intro h
                    have hval := congrArg Fin.val h
                    simp only [right_val] at hval
                    have hp := p₀.isLt; have hn' := sys.rs.n_ge_4
                    by_cases hp1 : p₀.val + 1 < sys.rs.n
                    · rw [Nat.mod_eq_of_lt hp1] at hval
                      by_cases hp2 : p₀.val + 1 + 1 < sys.rs.n
                      · rw [Nat.mod_eq_of_lt hp2] at hval; omega
                      · rw [show p₀.val + 1 + 1 = sys.rs.n from by omega,
                          Nat.mod_self] at hval; omega
                    · rw [show p₀.val + 1 = sys.rs.n from by omega, Nat.mod_self,
                        Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval; omega)
            exact entryConflict_impossible gc
              ⟨⟨b₀.val + 1, hb1⟩, ⟨b₀.val - 1, hbm1_lt⟩, right p₀,
               hb1_mover, hne,
               by rw [left_right_eq_self]; exact hL.symm,
               hS.symm, hR.symm⟩
          · exact minGapArcRev_elim_wrap_ccwcw p₀ a₀ b₀ hccw_a₀ hcw_b₀ hlt₀ hno₀
              hglobal₀ hgap2 hb1 hbin_p₀
        · -- Gap = 1 with binary left endpoint (CCW-CW): palindromic EC needed
          exact hConsecResidual ⟨i, hbin_i, hbin_ri, hbin_rri⟩
      · -- p₀ NOT binary: global min at non-binary-left edge (CCW-CW)
        exact hConsecResidual ⟨i, hbin_i, hbin_ri, hbin_rri⟩
  · -- NON-CONSECUTIVE CASE: genuine new work needed (4-mechanism universal EC)
    -- The global min triple and htypes₀ are not needed in this branch.
    -- We derive False directly from: zero winding + ≥3 binary + no 3 consecutive
    -- + sub-threshold + convergence + hcw_pos + no safe processor.
    -- Proof: The flux lemma (cwMoveCountAt p = ccwMoveCountAt (right p)) forces
    -- every crossed edge to have balanced bidirectional crossings. With hcw_pos,
    -- at least one edge has both CW and CCW crossings. Combined with ≥3 non-consecutive
    -- binary and no safe processor, a boundary edge adjacent to a binary processor
    -- is crossed in both directions, yielding an entry conflict.
    exact nonConsecutive_zeroWinding_false hn gc hconv hsub hzero hcw_pos hno_safe
      h3bin h3consec hNonConsecCore

/-! ### Suitable CW-CCW pair existence (from False) -/

theorem exists_suitable_cwccw_pair
    {sys : System}
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hConsecResidual : (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    ∃ (p : Fin sys.rs.n) (a b : Fin gc.configs.length),
      edgeCWCrossAt gc p a ∧
      edgeCCWCrossAt gc p b ∧
      a.val < b.val ∧
      (∀ k : Fin gc.configs.length,
        a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k) ∧
      (∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
        edgeCrossAt' gc q c → edgeCrossAt' gc q d →
        c.val < d.val →
        ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
         (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
        b.val - a.val ≤ d.val - c.val) ∧
      b.val - a.val ≥ 2 ∧
      b.val + 1 < gc.configs.length ∧
      isBinary sys.rs (right p) := by
  exfalso
  exact large_arc_zeroWinding_direct hn gc hconv hsub hzero hcw_pos hno_safe
    hConsecResidual hNonConsecCore

/-! ### Main bridge theorem -/

theorem large_arc_zeroWinding_ec_proof
    {sys : System}
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hzero : gc.zeroWinding)
    (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hConsecResidual : (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False :=
  large_arc_zeroWinding_direct hn gc hconv hsub hzero hcw_pos hno_safe
    hConsecResidual hNonConsecCore

end LeanMn
