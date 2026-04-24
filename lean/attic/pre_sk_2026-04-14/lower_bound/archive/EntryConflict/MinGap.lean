/-
  MinGap.lean — Global minimum-gap descent for paired edge crossings

  At the globally-minimum-gap opposite-direction edge crossing pair,
  `right p` does not fire clockwise in the interior.  This is the key
  well-founded descent step: a CW fire at `right p` would create a
  CW crossing of the adjacent edge with a strictly smaller gap pair,
  contradicting the global minimality of the gap.
-/
import LeanMn.LowerBound.EntryConflict.PairedCrossing
import LeanMn.LowerBound.Archive.EntryConflict.EdgeConstraint

namespace LeanMn

variable {sys : System}

/-! ### Auxiliary ring topology -/

private theorem right_right_ne_right (p : Fin sys.rs.n) :
    right (right p) ≠ right p := by
  have hn := sys.rs.n_ge_4
  intro h
  -- right(right p) = right p means right p = left(right p) = p after applying left
  have : left (right (right p)) = left (right p) := congrArg left h
  simp at this
  -- this says right p = p, but right p ≠ p for n ≥ 4
  have : right p = p := this
  have hval := congrArg Fin.val this
  simp only [right_val] at hval
  have hp := p.isLt
  by_cases h1 : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt h1] at hval; omega
  · rw [show p.val + 1 = sys.rs.n by omega, Nat.mod_self] at hval; omega

/-! ### The CW crossing at adjacent edge produces a smaller-gap pair -/

/-- Between paired crossings of edge (p, right p), if right p fires CW at step k
    (creating a CW crossing of the adjacent edge), the mover must return through
    that adjacent edge going CCW at some step in (k, b]. -/
private theorem exists_ccw_crossing_adjacent
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (_hcw_a : edgeCWCrossAt gc p a)
    (hccw_b : edgeCCWCrossAt gc p b)
    (_hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (k : Fin gc.configs.length)
    (hak : a.val < k.val) (hkb : k.val < b.val)
    (hcw_k : edgeCWCrossAt gc (right p) k) :
    ∃ j : Fin gc.configs.length,
      k.val < j.val ∧ j.val ≤ b.val ∧
      edgeCCWCrossAt gc (right p) j := by
  -- The mover at step k+1 is right(right p)
  have hk1_lt : k.val + 1 < gc.configs.length := by omega
  have hk_next : gc.moverAt (nextIndex gc.configs k) = right (right p) := by
    rw [gc.eq_right_of_stepDir_eq_cw hcw_k.2, hcw_k.1]
  have hk_next_val : (nextIndex gc.configs k).val = k.val + 1 := by
    simp [nextIndex, Nat.mod_eq_of_lt hk1_lt]
  -- Prove: for any m with k < m ≤ b and moverAt m = right p,
  -- there exists a CCW crossing of edge (right p, right(right p)) in (k, b].
  -- We use strong induction on (m - k).
  -- The trick: scan backward from m. At step m-1:
  --   moverAt(prev) = p going CW → contradicts hno
  --   moverAt(prev) = right p staying → recurse with prev
  --   moverAt(prev) = right(right p) going CCW → found it
  suffices hmain : ∀ d : Nat, ∀ (m : Fin gc.configs.length),
      m.val - k.val = d → k.val < m.val → m.val ≤ b.val →
      gc.moverAt m = right p →
      ∃ j, k.val < j.val ∧ j.val ≤ b.val ∧ edgeCCWCrossAt gc (right p) j by
    exact hmain (b.val - k.val) b rfl (by omega) le_rfl hccw_b.1
  intro d
  induction d with
  | zero =>
    intro m hd hkm
    omega  -- d = 0 but k < m means m - k > 0
  | succ d ih =>
    intro m hd hkm hmb hm_mov
    -- Look at step m - 1
    have hm1_lt : m.val - 1 < gc.configs.length := by omega
    set prev : Fin gc.configs.length := ⟨m.val - 1, hm1_lt⟩
    have hprev_succ : prev.val + 1 = m.val := by simp [prev]; omega
    have hprev_next_lt : prev.val + 1 < gc.configs.length := by omega
    have hprev_next_eq : nextIndex gc.configs prev = m := by
      apply Fin.ext
      simp [nextIndex, prev, Nat.mod_eq_of_lt hprev_next_lt]
      omega
    -- moverAt(nextIndex prev) = right p
    have hprev_to_m : gc.moverAt (nextIndex gc.configs prev) = right p := by
      rw [hprev_next_eq]; exact hm_mov
    -- By nextMover_eq_iff, three cases for moverAt(prev)
    rcases (gc.nextMover_eq_iff prev (right p)).mp hprev_to_m with
      ⟨hprev_mov, hprev_dir⟩ | ⟨hprev_mov, hprev_dir⟩ | ⟨hprev_mov, hprev_dir⟩
    · -- moverAt(prev) = left(right p) = p, stepDir = .cw
      -- This is a CW crossing of edge (p, right p)
      have hp_eq : left (right p) = p := by simpa using left_right_eq_self p
      rw [hp_eq] at hprev_mov
      have hap : a.val < prev.val := by simp [prev]; omega
      have hpb : prev.val < b.val := by simp [prev]; omega
      exact absurd
        ((edgeCrossAt'_iff_cwOrCcw gc p prev).mpr (Or.inl ⟨hprev_mov, hprev_dir⟩))
        (hno prev hap hpb)
    · -- moverAt(prev) = right p, stepDir = .stay → recurse
      by_cases hpk : k.val < prev.val
      · have hpd : prev.val - k.val = d := by simp [prev]; omega
        have hpb : prev.val ≤ b.val := by simp [prev]; omega
        exact ih prev hpd hpk hpb hprev_mov
      · -- prev ≤ k, so m = k+1
        have hm_eq : m.val = k.val + 1 := by simp [prev] at hpk; omega
        -- But moverAt(k+1) = right(right p) ≠ right p
        have hm_eq_next : m = nextIndex gc.configs k :=
          Fin.ext (by rw [hk_next_val]; omega)
        rw [hm_eq_next] at hm_mov
        exact absurd (hm_mov ▸ hk_next) (Ne.symm (right_right_ne_right p))
    · -- moverAt(prev) = right(right p), stepDir = .ccw → found it!
      refine ⟨prev, ?_, ?_, ⟨hprev_mov, hprev_dir⟩⟩
      · -- k < prev: prev = m - 1, and m - k = d + 1, so m - 1 - k = d ≥ 1 since d ≥ 0
        -- Actually d could be 0. But m > k and prev = m - 1, so prev ≥ k.
        -- We need prev > k, i.e., m - 1 > k, i.e., m > k + 1, i.e., m ≥ k + 2.
        -- But m - k = d + 1 and d ≥ 0, so m ≥ k + 1.
        -- If m = k + 1, then prev = k, and moverAt(prev) = right(right p).
        -- But moverAt(k) = right p (from hcw_k), so right(right p) = right p → contradiction.
        by_cases hpk : k.val < prev.val
        · exact hpk
        · have hm_eq : m.val = k.val + 1 := by simp [prev] at hpk; omega
          have hm_eq_next : m = nextIndex gc.configs k :=
            Fin.ext (by rw [hk_next_val]; omega)
          -- moverAt(prev) = moverAt(k) since prev = k
          have hprev_k : prev = k := Fin.ext (by simp [prev]; omega)
          rw [hprev_k] at hprev_mov
          -- moverAt(k) = right(right p), but also moverAt(k) = right p
          rw [hcw_k.1] at hprev_mov
          exact absurd hprev_mov.symm (right_right_ne_right p)
      · simp [prev]; omega

/-- **No CW fire at right p in global min-gap interior.**
    At any minimum-gap opposite-direction crossing pair for edge (p, right p),
    if (a, b) has CW at a and CCW at b with no crossings between,
    and this gap is globally minimal across all edges, then `right p` does
    not fire clockwise at any step in (a, b). -/
theorem no_cw_fire_at_right_in_minGap
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (hcw_a : edgeCWCrossAt gc p a)
    (hccw_b : edgeCCWCrossAt gc p b)
    (hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    -- Global minimality: gap b - a is ≤ the gap of every opposite pair at every edge
    (hglobal : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d →
      c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b.val - a.val ≤ d.val - c.val) :
    ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val →
      ¬(gc.moverAt k = right p ∧ gc.stepDir k = .cw) := by
  intro k hak hkb ⟨hmov, hdir⟩
  -- Step k is a CW crossing of edge (right p, right(right p))
  have hcw_k : edgeCWCrossAt gc (right p) k := ⟨hmov, hdir⟩
  -- There is a CCW crossing of edge (right p, right(right p)) at some j with k < j ≤ b
  obtain ⟨j, hkj, hjb, hccw_j⟩ :=
    exists_ccw_crossing_adjacent gc p a b hcw_a hccw_b hlt hno k hak hkb hcw_k
  -- The pair (k, j) at edge (right p) has gap j - k < b - a
  have hgap_small : j.val - k.val < b.val - a.val := by omega
  -- Apply global minimality
  have hle := hglobal (right p) k j
    (edgeCWCrossAt_imp gc (right p) k hcw_k)
    (edgeCCWCrossAt_imp gc (right p) j hccw_j)
    hkj (Or.inl ⟨hcw_k, hccw_j⟩)
  omega

/-! ### Symmetric: left(left p) ≠ left p -/

private theorem left_ne_self (p : Fin sys.rs.n) :
    left p ≠ p := by
  intro h
  have hval := congrArg Fin.val h
  simp only [left_val] at hval
  have hp := p.isLt; have hn := sys.rs.n_ge_4
  by_cases h0 : p.val = 0
  · rw [h0, show 0 + sys.rs.n - 1 = sys.rs.n - 1 from by omega,
      Nat.mod_eq_of_lt (by omega)] at hval; omega
  · rw [show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval; omega

private theorem left_left_ne_left (p : Fin sys.rs.n) :
    left (left p) ≠ left p := by
  intro h
  have : right (left (left p)) = right (left p) := congrArg right h
  simp at this
  -- this : left p = p
  exact left_ne_self p this

private theorem left_left_ne_self (p : Fin sys.rs.n) :
    left (left p) ≠ p := by
  intro h
  -- left(left p) = p means left p = right(left(left p)) = right p
  have hlp_eq_rp : left p = right p := by
    calc left p = right (left (left p)) := by simp [right_left_eq_self]
      _ = right p := by rw [h]
  -- left p = right p contradicts n ≥ 4
  -- right p ≠ left p for n ≥ 4 (they differ by 2 mod n)
  have hn := sys.rs.n_ge_4
  have hval := congrArg Fin.val hlp_eq_rp
  simp only [left_val, right_val] at hval
  have hp := p.isLt
  by_cases h0 : p.val = 0
  · rw [h0] at hval; simp only [Nat.zero_add] at hval
    rw [Nat.mod_eq_of_lt (by omega : sys.rs.n - 1 < sys.rs.n),
        Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hval; omega
  · by_cases h1 : p.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt h1,
        show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval; omega
    · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self,
        show p.val + sys.rs.n - 1 = (p.val - 1) + sys.rs.n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval; omega

/-! ### Symmetric: CW crossing at left-adjacent edge from CCW fire at p -/

/-- Between CCW-CW crossings of edge (p, right p), if p fires CCW at step k
    (creating a CCW crossing of edge (left p, p)), the mover must return through
    that edge going CW at some step in (k, b].

    Symmetric dual of `exists_ccw_crossing_adjacent`. -/
private theorem exists_cw_crossing_left_adjacent
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (_hccw_a : edgeCCWCrossAt gc p a)
    (hcw_b : edgeCWCrossAt gc p b)
    (_hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (k : Fin gc.configs.length)
    (hak : a.val < k.val) (hkb : k.val < b.val)
    (hccw_k : edgeCCWCrossAt gc (left p) k) :
    ∃ j : Fin gc.configs.length,
      k.val < j.val ∧ j.val ≤ b.val ∧
      edgeCWCrossAt gc (left p) j := by
  -- At step k: moverAt = right(left p) = p fires CCW, so
  -- at step k+1 moverAt = left(right(left p)) = left p.
  have hk1_lt : k.val + 1 < gc.configs.length := by omega
  have hk_next : gc.moverAt (nextIndex gc.configs k) = left p := by
    rw [gc.eq_left_of_stepDir_eq_ccw hccw_k.2, hccw_k.1]
    simp
  have hk_next_val : (nextIndex gc.configs k).val = k.val + 1 := by
    simp [nextIndex, Nat.mod_eq_of_lt hk1_lt]
  -- Scan backward from m (where moverAt m = p) to find CW crossing at edge (left p, p).
  -- At step m - 1: three cases via nextMover_eq_iff:
  --   moverAt(prev) = right p going CCW → crossing edge (p, right p) → contradicts hno
  --   moverAt(prev) = p staying → recurse
  --   moverAt(prev) = left p going CW → CW crossing at edge (left p, p)!
  suffices hmain : ∀ d : Nat, ∀ (m : Fin gc.configs.length),
      m.val - k.val = d → k.val < m.val → m.val ≤ b.val →
      gc.moverAt m = p →
      ∃ j, k.val < j.val ∧ j.val ≤ b.val ∧ edgeCWCrossAt gc (left p) j by
    exact hmain (b.val - k.val) b rfl (by omega) le_rfl hcw_b.1
  intro d
  induction d with
  | zero =>
    intro m hd hkm
    omega
  | succ d ih =>
    intro m hd hkm hmb hm_mov
    have hm1_lt : m.val - 1 < gc.configs.length := by omega
    set prev : Fin gc.configs.length := ⟨m.val - 1, hm1_lt⟩
    have hprev_val : prev.val = m.val - 1 := rfl
    have hprev_next_lt : prev.val + 1 < gc.configs.length := by
      rw [hprev_val]; omega
    have hprev_next_eq : nextIndex gc.configs prev = m := by
      apply Fin.ext
      simp [nextIndex, prev, Nat.mod_eq_of_lt hprev_next_lt]
      omega
    have hprev_to_m : gc.moverAt (nextIndex gc.configs prev) = p := by
      rw [hprev_next_eq]; exact hm_mov
    rcases (gc.nextMover_eq_iff prev p).mp hprev_to_m with
      ⟨hprev_mov, hprev_dir⟩ | ⟨hprev_mov, hprev_dir⟩ | ⟨hprev_mov, hprev_dir⟩
    · -- moverAt(prev) = left p, stepDir = .cw → CW crossing at edge (left p, p)!
      refine ⟨prev, ?_, ?_, ⟨hprev_mov, hprev_dir⟩⟩
      · -- k < prev
        by_cases hpk : k.val < prev.val
        · exact hpk
        · have hm_eq : m.val = k.val + 1 := by simp [prev] at hpk; omega
          -- Then prev = k, so moverAt(k) = left p.
          have hprev_k : prev = k := Fin.ext (by simp [prev]; omega)
          rw [hprev_k] at hprev_mov
          -- hccw_k.1 : moverAt k = right(left p), and right(left p) = p
          have hk_mov_p : gc.moverAt k = p := by
            rw [hccw_k.1]; exact right_left_eq_self p
          -- hprev_mov : moverAt k = left p, hk_mov_p : moverAt k = p
          -- So left p = p, contradiction for n ≥ 4.
          exact absurd (hprev_mov.symm.trans hk_mov_p) (left_ne_self p)
      · simp [prev]; omega
    · -- moverAt(prev) = p, stepDir = .stay → recurse
      by_cases hpk : k.val < prev.val
      · have hpd : prev.val - k.val = d := by simp [prev]; omega
        have hpb : prev.val ≤ b.val := by simp [prev]; omega
        exact ih prev hpd hpk hpb hprev_mov
      · -- prev ≤ k, so m = k + 1
        have hm_eq : m.val = k.val + 1 := by simp [prev] at hpk; omega
        -- moverAt(k+1) = left p ≠ p
        have hm_eq_next : m = nextIndex gc.configs k :=
          Fin.ext (by rw [hk_next_val]; omega)
        rw [hm_eq_next] at hm_mov
        -- hk_next : moverAt(nextIndex k) = left p
        -- hm_mov : moverAt(nextIndex k) = p
        -- So left p = p, contradiction
        exact absurd (hm_mov ▸ hk_next) (Ne.symm (left_ne_self p))
    · -- moverAt(prev) = right p, stepDir = .ccw
      -- This is a CCW crossing of edge (p, right p) → contradicts hno
      have hrp_eq : right (left p) = p := by simp
      -- Actually hccw_k has moverAt k = right(left p) = p, dir = ccw.
      -- The CCW crossing at edge (p, right p) is: moverAt = right p, dir = ccw
      -- But here moverAt(prev) = right p, dir = ccw, so this IS a CCW crossing at edge (p, right p)
      have hap : a.val < prev.val := by simp [prev]; omega
      have hpb : prev.val < b.val := by simp [prev]; omega
      exact absurd
        ((edgeCrossAt'_iff_cwOrCcw gc p prev).mpr (Or.inr ⟨hprev_mov, hprev_dir⟩))
        (hno prev hap hpb)

/-- **No CCW fire at p in global min-gap interior (CCW-CW case).**
    At any minimum-gap opposite-direction crossing pair for edge (p, right p),
    if (a, b) has CCW at a and CW at b with no crossings between,
    and this gap is globally minimal across all edges, then `p` does
    not fire counterclockwise at any step in (a, b).

    Symmetric dual of `no_cw_fire_at_right_in_minGap`. -/
theorem no_ccw_fire_at_p_in_minGap
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (a b : Fin gc.configs.length)
    (hccw_a : edgeCCWCrossAt gc p a)
    (hcw_b : edgeCWCrossAt gc p b)
    (hlt : a.val < b.val)
    (hno : ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val → ¬edgeCrossAt' gc p k)
    (hglobal : ∀ (q : Fin sys.rs.n) (c d : Fin gc.configs.length),
      edgeCrossAt' gc q c → edgeCrossAt' gc q d →
      c.val < d.val →
      ((edgeCWCrossAt gc q c ∧ edgeCCWCrossAt gc q d) ∨
       (edgeCCWCrossAt gc q c ∧ edgeCWCrossAt gc q d)) →
      b.val - a.val ≤ d.val - c.val) :
    ∀ k : Fin gc.configs.length,
      a.val < k.val → k.val < b.val →
      ¬(gc.moverAt k = p ∧ gc.stepDir k = .ccw) := by
  intro k hak hkb ⟨hmov, hdir⟩
  -- Step k: p fires CCW. Since right(left p) = p, this is a CCW crossing
  -- of edge (left p, p) = edge (left p, right(left p)).
  have hccw_k : edgeCCWCrossAt gc (left p) k := by
    constructor
    · rw [hmov]; exact (right_left_eq_self p).symm
    · exact hdir
  -- There exists a CW crossing of edge (left p, p) at some j with k < j ≤ b
  obtain ⟨j, hkj, hjb, hcw_j⟩ :=
    exists_cw_crossing_left_adjacent gc p a b hccw_a hcw_b hlt hno k hak hkb hccw_k
  -- The pair (k, j) at edge (left p) is CCW-CW with gap j - k < b - a
  have hgap_small : j.val - k.val < b.val - a.val := by omega
  -- Apply global minimality
  have hle := hglobal (left p) k j
    (edgeCCWCrossAt_imp gc (left p) k hccw_k)
    (edgeCWCrossAt_imp gc (left p) j hcw_j)
    hkj (Or.inr ⟨hccw_k, hcw_j⟩)
  omega

end LeanMn
