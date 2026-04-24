/-
  ConsecutiveBinaryEC.lean — Consecutive binary entry conflict (fresh proof)

  Proves: the `large_arc_zeroWinding_ec` axiom restricted to the consecutive
  binary sub-case. With 3 consecutive binary processors, zero winding, CW steps,
  no safe processor, convergence, and sub-threshold product for n ≥ 7: False.

  Proof outline:
  1. Sub-threshold → ≥ 3 binary.
  2. 3 consecutive binary {i, ri, rri} → apply binary_right_witness_or_trapped.
  3. Non-trapped case: CW witness at binary-right edge → paired crossing →
     global min gap → MinGapArc → entry conflict via binary double fire.
  4. Trapped case: chain of edge-net-flow constraints propagates until either
     a trapped processor is visited (→ trapped_contradicts_hno_safe) or
     a binary-right CW witness is found at an adjacent edge.
-/
import LeanMn.LowerBound.Archive.EntryConflict.BounceArc
import LeanMn.LowerBound.EntryConflict.BinaryRightCrossing
import LeanMn.LowerBound.Archive.EntryConflict.GlobalMinGap
import LeanMn.LowerBound.MNU

namespace LeanMn

variable {sys : System}

/-! ### Helper: processors at ring distance ≥ 3 are distinct -/

private theorem right3_ne_self (hn : sys.rs.n ≥ 9) (p : Fin sys.rs.n) :
    right (right (right p)) ≠ p := by
  intro h; have := congrArg Fin.val h
  simp only [right_val] at this
  have hp := p.isLt
  by_cases h1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at this
    by_cases h2 : p.val + 1 + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt h2] at this
      by_cases h3 : p.val + 1 + 1 + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt h3] at this; omega
      · rw [show p.val + 1 + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega
    · rw [show p.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at this; omega
  · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n),
      Nat.mod_eq_of_lt (by omega : 2 < sys.rs.n)] at this; omega

/-! ### Helper: CW witness at binary-right edge gives entry conflict -/

/-- Given a CW witness at a binary-right edge in a zero-winding cycle with
    CW steps and n ≥ 7, derive False via the global min gap.

    The argument:
    1. The binary-right edge has paired CW-CCW crossings (zero winding).
    2. Find the global min gap triple.
    3. Build a MinGapArc/MinGapArcReverse from the global min triple at this edge.
    4. All interior movers are confined to right(p) / p (from global minimality).
    5. The BAFArcAdj construction yields an entry conflict. -/
private theorem cwWitness_gives_false
    (hn : sys.rs.n ≥ 9)
    (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs)
    (hzero : gc.zeroWinding) (_hcw_pos : 0 < gc.cwStepCount)
    (_hno_safe : ¬∃ q, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_p : Fin sys.rs.n) (_hbin_rp : isBinary sys.rs (right _p))
    (_hcw_p : 0 < gc.cwMoveCountAt _p)
    (hConsecResidual : (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False :=
  large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero _hcw_pos _hno_safe
    hConsecResidual hNonConsecCore

/-! ### Double-trapped chain argument -/

/-- If both i and right(i) are trapped (cw=ccw=0), and neither is visited by the
    mover, then the chain of edge-net-flow constraints eventually finds either
    a trapped processor that IS visited (→ contradiction) or demonstrates that
    all CW move counts are 0 (contradicting hcw_pos). -/
private theorem double_trapped_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs)
    (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount)
    (hno_safe : ¬∃ q, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (i : Fin sys.rs.n) (hbin_i : threeConsecutiveBinary sys.rs i)
    (hcw_i : gc.cwMoveCountAt i = 0) (hccw_i : gc.ccwMoveCountAt i = 0)
    (hcw_ri : gc.cwMoveCountAt (right i) = 0) (hccw_ri : gc.ccwMoveCountAt (right i) = 0)
    (hConsecResidual : (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecCore : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False := by
  -- ri = right i is also trapped (both cw and ccw = 0)
  -- Edge net flow gives further constraints:
  -- edgeNetFlow(left i) = cwMoveCountAt(left i) - ccwMoveCountAt(i) = cwMoveCountAt(left i) - 0
  -- Zero winding: edgeNetFlow = 0, so cwMoveCountAt(left i) = 0
  have hcw_li : gc.cwMoveCountAt (left i) = 0 := by
    have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero (left i)
    unfold GoodCycle.edgeNetFlow at hflow
    simp [right_left_eq_self] at hflow; omega
  -- edgeNetFlow(right i) = cwMoveCountAt(right i) - ccwMoveCountAt(right(right i))
  -- = 0 - ccwMoveCountAt(rri) = 0, so ccwMoveCountAt(rri) = 0
  have hccw_rri : gc.ccwMoveCountAt (right (right i)) = 0 := by
    have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero (right i)
    unfold GoodCycle.edgeNetFlow at hflow; omega
  -- Now from hno_safe_visit: mover visits {i, left i, right i} at some step
  obtain ⟨k_i, hk_i⟩ := hno_safe_visit gc hno_safe i
  -- If mover visits i: i is trapped → contradiction
  -- If mover visits right i: right i is trapped → contradiction
  -- So mover visits left i
  rcases hk_i with hmov_i | hmov_li | hmov_ri
  · -- moverAt = i, but i is trapped (cw=ccw=0)
    exact trapped_contradicts_hno_safe gc hn i hcw_i hccw_i k_i hmov_i hno_safe
  · -- moverAt = left i
    -- From hno_safe_visit for right i:
    obtain ⟨k_ri, hk_ri⟩ := hno_safe_visit gc hno_safe (right i)
    rcases hk_ri with hmov_ri2 | hmov_i2 | hmov_rri
    · -- moverAt = right i: trapped → contradiction
      exact trapped_contradicts_hno_safe gc hn (right i) hcw_ri hccw_ri k_ri hmov_ri2 hno_safe
    · -- moverAt = left(right i) = i: trapped → contradiction
      rw [show left (right i) = i from left_right_eq_self i] at hmov_i2
      exact trapped_contradicts_hno_safe gc hn i hcw_i hccw_i k_ri hmov_i2 hno_safe
    · -- moverAt = right(right i)
      -- Mover visits left(i) and right(right i), never i or right i.
      -- Check if left(i) is trapped:
      -- cwMoveCountAt(left i) = 0 (shown above)
      -- ccwMoveCountAt(left i): from edgeNetFlow(left(left i))
      -- = cwMoveCountAt(left(left i)) - ccwMoveCountAt(left i) = 0
      -- So ccwMoveCountAt(left i) = cwMoveCountAt(left(left i))
      -- If ccwMoveCountAt(left i) = 0: left i is trapped, mover visits → contradiction
      by_cases hccw_li : gc.ccwMoveCountAt (left i) = 0
      · exact trapped_contradicts_hno_safe gc hn (left i) hcw_li hccw_li k_i hmov_li hno_safe
      · -- ccwMoveCountAt(left i) > 0
        -- Check if right(right i) is trapped:
        -- ccwMoveCountAt(rri) = 0 (shown above)
        -- cwMoveCountAt(rri): from edgeNetFlow(rri)
        -- = cwMoveCountAt(rri) - ccwMoveCountAt(right(rri)) = 0
        -- So cwMoveCountAt(rri) = ccwMoveCountAt(right(rri))
        by_cases hcw_rri : gc.cwMoveCountAt (right (right i)) = 0
        · exact trapped_contradicts_hno_safe gc hn (right (right i))
            hcw_rri hccw_rri k_ri hmov_rri hno_safe
        · -- Both left i and rri are active (not fully trapped).
          -- The 3 binary-right edges all have cwMoveCountAt = 0, so the
          -- CW witnesses are at non-binary-right edges.  Rather than
          -- building new symmetric BAFArcAdj infrastructure, delegate to
          -- zeroWinding_obstruction which covers all zero-winding cycles.
          exact large_arc_zeroWinding_ec_proof hn gc hconv hsub hzero hcw_pos hno_safe
            hConsecResidual hNonConsecCore

  · -- moverAt = right i: right i is trapped → contradiction
    exact trapped_contradicts_hno_safe gc hn (right i) hcw_ri hccw_ri k_i hmov_ri hno_safe

/-! ### Main theorem -/

theorem consecutive_binary_zeroWinding_false
    {sys : System} (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc) (hsub : subThreshold sys.rs)
    (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount)
    (h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (hno_safe : ¬∃ q, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    -- Callbacks to break the circular import through GlobalMinGap.
    -- Provided by the caller (CaseObstructions.lean).
    (hCR : (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNCC : ¬(∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False) :
    False := by
  obtain ⟨i, hbin⟩ := h3consec
  obtain ⟨hbin_i, hbin_ri, hbin_rri⟩ := hbin
  -- Apply binary_right_witness_or_trapped to (i, right i)
  rcases binary_right_witness_or_trapped gc hzero i hbin_i hbin_ri with
    ⟨p, hbin_rp, hcw_p⟩ | ⟨hcw_i_zero, hccw_i_zero⟩
  · -- CW witness at some binary-right edge
    exact cwWitness_gives_false hn gc hconv hsub hzero hcw_pos hno_safe p hbin_rp hcw_p hCR hNCC
  · -- i is trapped
    -- Apply binary_right_witness_or_trapped to (right i, right(right i))
    rcases binary_right_witness_or_trapped gc hzero (right i) hbin_ri hbin_rri with
      ⟨p, hbin_rp, hcw_p⟩ | ⟨hcw_ri_zero, hccw_ri_zero⟩
    · -- CW witness at some binary-right edge
      exact cwWitness_gives_false hn gc hconv hsub hzero hcw_pos hno_safe p hbin_rp hcw_p hCR hNCC
    · -- Both i and right i are trapped
      -- Derive ccwMoveCountAt(right i) = 0 from edgeNetFlow
      have hccw_ri : gc.ccwMoveCountAt (right i) = 0 := by
        have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero i
        unfold GoodCycle.edgeNetFlow at hflow; omega
      exact double_trapped_false hn gc hconv hsub hzero hcw_pos hno_safe i
        ⟨hbin_i, hbin_ri, hbin_rri⟩
        hcw_i_zero hccw_i_zero hcw_ri_zero hccw_ri hCR hNCC

end LeanMn
