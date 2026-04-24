/-
  BounceArc.lean — MinGapArc-based entry conflict for zero-winding cycles

  Given a globally-minimum-gap CW-CCW paired crossing at edge (p, right p)
  with gap >= 2:

  1. The mover at step a+1 is right(p) (CW crossing pushes right).
  2. right(p) cannot fire CW in (a,b) (MinGap: would create smaller pair).
  3. right(p) cannot fire CCW in (a,b) (EdgeConstraint: would cross edge).
  4. So every step k in [a+1, b] has moverAt(k) = right(p) (stay chain).

  Setting cwNeighborStep = b-1 and ccwNeighborStep = b:
  - right(p) fires at exactly b-1 and b, no firings between (empty interval).
  - binary_double_fire_returns gives R preservation.
  - p does not fire in [b-1, b] (moverAt = right(p) everywhere).
  - left(p) does not fire in [b-1, b] (moverAt = right(p) everywhere).

  Hence BAFArcAdj.elim_of_binary_right applies and yields False.

  Uses: BAFWord.lean, MinGap.lean, RingDisplacement.lean.
-/
import LeanMn.LowerBound.EntryConflict.BAFWord
import LeanMn.LowerBound.Archive.EntryConflict.MinGap
import LeanMn.LowerBound.Archive.EntryConflict.RingDisplacement

namespace LeanMn

/-! ### Ring topology helpers -/

private theorem right_ne_self_ba {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    right a ≠ a := by
  intro h
  have hval := congrArg Fin.val h
  simp only [right_val] at hval
  have ha := a.isLt
  by_cases hp1 : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt hp1] at hval; omega
  · rw [show a.val + 1 = n from by omega, Nat.mod_self] at hval; omega

private theorem right_ne_left_ba {sys : System} (p : Fin sys.rs.n) :
    right p ≠ left p := by
  have hn := sys.rs.n_ge_4
  intro h
  have := congrArg Fin.val h
  simp only [right_val, left_val] at this
  have hp := p.isLt
  by_cases h0 : p.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  · by_cases hlt : p.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hlt] at this
      rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this
      omega
    · rw [show p.val + 1 = sys.rs.n by omega, Nat.mod_self] at this
      rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this
      omega

/-! ### MinGapArc: the paired edge crossing with global min gap -/

/-- A MinGapArc captures a CW-then-CCW paired crossing at edge (p, right p)
    with globally minimal gap across ALL edges. -/
structure MinGapArc {sys : System} (gc : GoodCycle sys) where
  p : Fin sys.rs.n
  a : Fin gc.configs.length
  b : Fin gc.configs.length
  hcw_a : edgeCWCrossAt gc p a
  hccw_b : edgeCCWCrossAt gc p b
  hlt : a.val < b.val
  hno : ∀ k : Fin gc.configs.length,
    a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k
  hglobal : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
    edgeCrossAt' gc q c → edgeCrossAt' gc q d →
    c.val < d.val →
    ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
     (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
    b.val - a.val ≤ d.val - c.val

/-! ### Mover confinement in a MinGapArc -/

theorem MinGapArc.mover_ne_p {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArc gc)
    (hgap_lt_n : mga.b.val - mga.a.val < sys.rs.n)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val ≤ mga.b.val) :
    gc.moverAt k ≠ mga.p := by
  intro hmov
  by_cases hk_eq_b : k.val = mga.b.val
  · have hb_mov : gc.moverAt mga.b = right mga.p := mga.hccw_b.1
    have hk_eq : k = mga.b := Fin.ext hk_eq_b
    rw [hk_eq] at hmov; rw [hmov] at hb_mov
    exact absurd hb_mov.symm (right_ne_self_ba sys.rs.n_ge_4 mga.p)
  · exact mover_no_return_within_short_gap gc mga.p mga.a k
      mga.hcw_a hak (by omega)
      (fun j haj hjk => mga.hno j haj (by omega)) hmov

theorem MinGapArc.right_p_no_cw {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArc gc)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val < mga.b.val) :
    ¬(gc.moverAt k = right mga.p ∧ gc.stepDir k = .cw) :=
  no_cw_fire_at_right_in_minGap gc mga.p mga.a mga.b
    mga.hcw_a mga.hccw_b mga.hlt mga.hno mga.hglobal k hak hkb

theorem MinGapArc.right_p_no_ccw {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArc gc)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val < mga.b.val) :
    ¬(gc.moverAt k = right mga.p ∧ gc.stepDir k = .ccw) :=
  not_ccw_at_right_between_crossings gc mga.p mga.a mga.b
    mga.hlt mga.hno k hak hkb

/-! ### All interior steps have mover at right(p) -/

private theorem moverAt_succ_of_cw_cross {sys : System}
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (a : Fin gc.configs.length)
    (hcw : edgeCWCrossAt gc p a)
    (ha1 : a.val + 1 < gc.configs.length) :
    gc.moverAt ⟨a.val + 1, ha1⟩ = right p := by
  have hnext := gc.eq_right_of_stepDir_eq_cw hcw.2
  rw [hcw.1] at hnext
  have h_idx : nextIndex gc.configs a = ⟨a.val + 1, ha1⟩ :=
    Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt ha1])
  rw [h_idx] at hnext
  exact hnext

private theorem mover_stay_chain_step {sys : System}
    (gc : GoodCycle sys) (mga : MinGapArc gc)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val < mga.b.val)
    (hmov : gc.moverAt k = right mga.p)
    (hk1 : k.val + 1 < gc.configs.length) :
    gc.moverAt ⟨k.val + 1, hk1⟩ = right mga.p := by
  have hncw := mga.right_p_no_cw k hak hkb
  have hnccw := mga.right_p_no_ccw k hak hkb
  have hstay : gc.stepDir k = .stay := by
    rcases gc.stepDir_cases k with hcw | hstay | hccw
    · exact absurd ⟨hmov, hcw⟩ hncw
    · exact hstay
    · exact absurd ⟨hmov, hccw⟩ hnccw
  have heq := gc.eq_self_of_stepDir_eq_stay hstay
  have h_idx : nextIndex gc.configs k = ⟨k.val + 1, hk1⟩ :=
    Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hk1])
  rw [h_idx] at heq
  rw [heq, hmov]

theorem MinGapArc.all_interior_mover_eq_right_p
    {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArc gc)
    (hgap2 : mga.b.val - mga.a.val ≥ 2)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val ≤ mga.b.val) :
    gc.moverAt k = right mga.p := by
  have ha1 : mga.a.val + 1 < gc.configs.length := by
    have := mga.b.isLt; omega
  -- Prove by induction on offset d that for all indices a+1+d in [a+1, b],
  -- the mover is right(p).
  suffices hsuff : ∀ d : Nat, ∀ (j : Fin gc.configs.length),
      j.val = mga.a.val + 1 + d → j.val ≤ mga.b.val →
      gc.moverAt j = right mga.p by
    exact hsuff (k.val - (mga.a.val + 1)) k (by omega) hkb
  intro d
  induction d with
  | zero =>
    intro j hj _hjb
    have hj_eq : j = ⟨mga.a.val + 1, ha1⟩ := Fin.ext (by omega)
    rw [hj_eq]
    exact moverAt_succ_of_cw_cross gc mga.p mga.a mga.hcw_a ha1
  | succ d ih =>
    intro j hj hjb
    have hd_lt_b : mga.a.val + 1 + d < mga.b.val := by omega
    have hd_lt_len : mga.a.val + 1 + d < gc.configs.length := by
      have := mga.b.isLt; omega
    -- The predecessor has mover = right(p) by IH
    set hprev_idx : Fin gc.configs.length := ⟨mga.a.val + 1 + d, hd_lt_len⟩ with hprev_idx_def
    have hprev_val : hprev_idx.val = mga.a.val + 1 + d := by simp [hprev_idx]
    have hprev_le : hprev_idx.val ≤ mga.b.val := by rw [hprev_val]; omega
    have hprev : gc.moverAt hprev_idx = right mga.p :=
      ih hprev_idx (by simp [hprev_idx]) hprev_le
    -- j = a+1+d+1, so j = predecessor + 1
    have hj_val : j.val = mga.a.val + 1 + d + 1 := hj
    have hj_lt : mga.a.val + 1 + d + 1 < gc.configs.length := by
      rw [← hj_val]; exact j.isLt
    have hj_eq : j = ⟨mga.a.val + 1 + d + 1, hj_lt⟩ := Fin.ext hj_val
    rw [hj_eq]
    have hprev_ak : mga.a.val < hprev_idx.val := by rw [hprev_val]; omega
    have hsucc_lt : hprev_idx.val + 1 < gc.configs.length := by
      rw [hprev_val]; exact hj_lt
    exact mover_stay_chain_step gc mga hprev_idx hprev_ak hd_lt_b hprev hsucc_lt

/-! ### The step after b has mover at p -/

private theorem moverAt_succ_of_ccw_cross {sys : System}
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (b : Fin gc.configs.length)
    (hccw : edgeCCWCrossAt gc p b)
    (hb1 : b.val + 1 < gc.configs.length) :
    gc.moverAt ⟨b.val + 1, hb1⟩ = p := by
  have hnext := gc.eq_left_of_stepDir_eq_ccw hccw.2
  rw [hccw.1] at hnext
  have hlr : left (right p) = p := by simp [left_right_eq_self]
  rw [hlr] at hnext
  have h_idx : nextIndex gc.configs b = ⟨b.val + 1, hb1⟩ :=
    Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hb1])
  rw [h_idx] at hnext
  exact hnext

/-! ### The BAFArcAdj construction from MinGapArc with gap >= 2 -/

noncomputable def MinGapArc.toBAFArcAdj
    {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArc gc)
    (hgap2 : mga.b.val - mga.a.val ≥ 2)
    (hb1 : mga.b.val + 1 < gc.configs.length) :
    BAFArcAdj gc :=
  have hbm1_lt : mga.b.val - 1 < gc.configs.length := by
    have := mga.b.isLt; omega
  have hbm1_mover : gc.moverAt ⟨mga.b.val - 1, hbm1_lt⟩ = right mga.p :=
    mga.all_interior_mover_eq_right_p hgap2 ⟨mga.b.val - 1, hbm1_lt⟩
      (by show mga.a.val < mga.b.val - 1; omega)
      (by show mga.b.val - 1 ≤ mga.b.val; omega)
  have hb_mover : gc.moverAt mga.b = right mga.p := mga.hccw_b.1
  have hb1_mover : gc.moverAt ⟨mga.b.val + 1, hb1⟩ = mga.p :=
    moverAt_succ_of_ccw_cross gc mga.p mga.b mga.hccw_b hb1
  {
    proc := mga.p
    cwProcStep := mga.a
    cwNeighborStep := ⟨mga.b.val - 1, hbm1_lt⟩
    ccwNeighborStep := mga.b
    ccwProcStep := ⟨mga.b.val + 1, hb1⟩
    cw_order := by show mga.a.val < mga.b.val - 1; omega
    mid_order := by show mga.b.val - 1 < mga.b.val; omega
    ccw_order := by show mga.b.val < mga.b.val + 1; omega
    cw_proc_mover := mga.hcw_a.1
    cw_neighbor_mover := hbm1_mover
    ccw_neighbor_mover := hb_mover
    ccw_proc_mover := hb1_mover
    proc_noFire := fun k hk1 hk2 => by
      have hk_val : k.val = mga.b.val - 1 ∨ k.val = mga.b.val := by
        have : mga.b.val - 1 ≤ k.val := hk1
        have : k.val < mga.b.val + 1 := hk2
        omega
      rcases hk_val with hk_eq | hk_eq
      · rw [show k = ⟨mga.b.val - 1, hbm1_lt⟩ from Fin.ext hk_eq, hbm1_mover]
        exact right_ne_self_ba sys.rs.n_ge_4 mga.p
      · rw [show k = mga.b from Fin.ext hk_eq, hb_mover]
        exact right_ne_self_ba sys.rs.n_ge_4 mga.p
    leftProc_noFire := fun k hk1 hk2 => by
      have hk_val : k.val = mga.b.val - 1 ∨ k.val = mga.b.val := by
        have : mga.b.val - 1 ≤ k.val := hk1
        have : k.val < mga.b.val + 1 := hk2
        omega
      rcases hk_val with hk_eq | hk_eq
      · rw [show k = ⟨mga.b.val - 1, hbm1_lt⟩ from Fin.ext hk_eq, hbm1_mover]
        exact right_ne_left_ba mga.p
      · rw [show k = mga.b from Fin.ext hk_eq, hb_mover]
        exact right_ne_left_ba mga.p
    rightProc_noFire_mid := fun k hk1 hk2 => by
      -- The interval (b-1, b) is empty
      have : mga.b.val - 1 < k.val := hk1
      have : k.val < mga.b.val := hk2
      omega
    ccw_adjacent := by show mga.b.val + 1 = mga.b.val + 1; rfl
  }

theorem MinGapArc.elim_of_binary_right
    {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArc gc)
    (hgap2 : mga.b.val - mga.a.val ≥ 2)
    (hb1 : mga.b.val + 1 < gc.configs.length)
    (hbin : isBinary sys.rs (right mga.p)) :
    False :=
  (mga.toBAFArcAdj hgap2 hb1).elim_of_binary_right hbin

/-! ### MinGapArcReverse: the CCW-then-CW symmetric dual -/

/-- A MinGapArcReverse captures a CCW-then-CW paired crossing at edge (p, right p)
    with globally minimal gap across ALL edges.

    Symmetric dual of `MinGapArc`:
    - MinGapArc:        CW at a (mover=p), CCW at b (mover=right(p)). Stay at right(p).
    - MinGapArcReverse: CCW at a (mover=right(p)), CW at b (mover=p). Stay at p. -/
structure MinGapArcReverse {sys : System} (gc : GoodCycle sys) where
  p : Fin sys.rs.n
  a : Fin gc.configs.length
  b : Fin gc.configs.length
  hccw_a : edgeCCWCrossAt gc p a
  hcw_b : edgeCWCrossAt gc p b
  hlt : a.val < b.val
  hno : ∀ k : Fin gc.configs.length,
    a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k
  hglobal : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
    edgeCrossAt' gc q c → edgeCrossAt' gc q d →
    c.val < d.val →
    ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
     (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
    b.val - a.val ≤ d.val - c.val

/-! ### Mover confinement in a MinGapArcReverse -/

theorem MinGapArcReverse.p_no_ccw {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArcReverse gc)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val < mga.b.val) :
    ¬(gc.moverAt k = mga.p ∧ gc.stepDir k = .ccw) :=
  no_ccw_fire_at_p_in_minGap gc mga.p mga.a mga.b
    mga.hccw_a mga.hcw_b mga.hlt mga.hno mga.hglobal k hak hkb

theorem MinGapArcReverse.p_no_cw {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArcReverse gc)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val < mga.b.val) :
    ¬(gc.moverAt k = mga.p ∧ gc.stepDir k = .cw) :=
  not_cw_at_p_between_crossings gc mga.p mga.a mga.b
    mga.hlt mga.hno k hak hkb

/-! ### All interior steps have mover at p (reverse) -/

private theorem moverAt_succ_of_ccw_cross_rev {sys : System}
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (a : Fin gc.configs.length)
    (hccw : edgeCCWCrossAt gc p a)
    (ha1 : a.val + 1 < gc.configs.length) :
    gc.moverAt ⟨a.val + 1, ha1⟩ = p := by
  have hnext := gc.eq_left_of_stepDir_eq_ccw hccw.2
  rw [hccw.1] at hnext
  have hlr : left (right p) = p := by simp [left_right_eq_self]
  rw [hlr] at hnext
  have h_idx : nextIndex gc.configs a = ⟨a.val + 1, ha1⟩ :=
    Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt ha1])
  rw [h_idx] at hnext
  exact hnext

private theorem mover_stay_chain_step_rev {sys : System}
    (gc : GoodCycle sys) (mga : MinGapArcReverse gc)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val < mga.b.val)
    (hmov : gc.moverAt k = mga.p)
    (hk1 : k.val + 1 < gc.configs.length) :
    gc.moverAt ⟨k.val + 1, hk1⟩ = mga.p := by
  have hncw := mga.p_no_cw k hak hkb
  have hnccw := mga.p_no_ccw k hak hkb
  have hstay : gc.stepDir k = .stay := by
    rcases gc.stepDir_cases k with hcw | hstay | hccw
    · exact absurd ⟨hmov, hcw⟩ hncw
    · exact hstay
    · exact absurd ⟨hmov, hccw⟩ hnccw
  have heq := gc.eq_self_of_stepDir_eq_stay hstay
  have h_idx : nextIndex gc.configs k = ⟨k.val + 1, hk1⟩ :=
    Fin.ext (by simp [nextIndex, Nat.mod_eq_of_lt hk1])
  rw [h_idx] at heq
  rw [heq, hmov]

theorem MinGapArcReverse.all_interior_mover_eq_p
    {sys : System} {gc : GoodCycle sys}
    (mga : MinGapArcReverse gc)
    (hgap2 : mga.b.val - mga.a.val ≥ 2)
    (k : Fin gc.configs.length)
    (hak : mga.a.val < k.val) (hkb : k.val ≤ mga.b.val) :
    gc.moverAt k = mga.p := by
  have ha1 : mga.a.val + 1 < gc.configs.length := by
    have := mga.b.isLt; omega
  suffices hsuff : ∀ d : Nat, ∀ (j : Fin gc.configs.length),
      j.val = mga.a.val + 1 + d → j.val ≤ mga.b.val →
      gc.moverAt j = mga.p by
    exact hsuff (k.val - (mga.a.val + 1)) k (by omega) hkb
  intro d
  induction d with
  | zero =>
    intro j hj _hjb
    have hj_eq : j = ⟨mga.a.val + 1, ha1⟩ := Fin.ext (by omega)
    rw [hj_eq]
    exact moverAt_succ_of_ccw_cross_rev gc mga.p mga.a mga.hccw_a ha1
  | succ d ih =>
    intro j hj hjb
    have hd_lt_b : mga.a.val + 1 + d < mga.b.val := by omega
    have hd_lt_len : mga.a.val + 1 + d < gc.configs.length := by
      have := mga.b.isLt; omega
    set hprev_idx : Fin gc.configs.length := ⟨mga.a.val + 1 + d, hd_lt_len⟩ with hprev_idx_def
    have hprev_val : hprev_idx.val = mga.a.val + 1 + d := by simp [hprev_idx]
    have hprev_le : hprev_idx.val ≤ mga.b.val := by rw [hprev_val]; omega
    have hprev : gc.moverAt hprev_idx = mga.p :=
      ih hprev_idx (by simp [hprev_idx]) hprev_le
    have hj_val : j.val = mga.a.val + 1 + d + 1 := hj
    have hj_lt : mga.a.val + 1 + d + 1 < gc.configs.length := by
      rw [← hj_val]; exact j.isLt
    have hj_eq : j = ⟨mga.a.val + 1 + d + 1, hj_lt⟩ := Fin.ext hj_val
    rw [hj_eq]
    have hprev_ak : mga.a.val < hprev_idx.val := by rw [hprev_val]; omega
    have hsucc_lt : hprev_idx.val + 1 < gc.configs.length := by
      rw [hprev_val]; exact hj_lt
    exact mover_stay_chain_step_rev gc mga hprev_idx hprev_ak hd_lt_b hprev hsucc_lt

end LeanMn
