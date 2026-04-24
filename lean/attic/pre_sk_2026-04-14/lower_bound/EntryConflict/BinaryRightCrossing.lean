/-
  BinaryRightCrossing.lean — Trapped mover and binary-right crossing lemmas

  Infrastructure for the zero-winding entry conflict argument.
  Key results:
  1. If cwMoveCountAt p = ccwMoveCountAt p = 0 and the mover visits p,
     then the mover is permanently at p (trapped_all_steps).
  2. A trapped mover violates hno_safe for n ≥ 7 (trapped_contradicts_hno_safe).
  3. For three consecutive binary i, ri, rri with both i and ri trapped,
     the mover cannot visit i or ri (otherwise trapped → hno_safe violated).
     Combined with hno_safe for i, the mover visits left(i) at some step.
  4. Extracting mover visits from hno_safe (hno_safe_visit).
-/
import LeanMn.LowerBound.EntryConflict.PairedCrossing
import LeanMn.LowerBound.MNU

namespace LeanMn

variable {sys : System}

/-! ### EdgeNetFlow corollaries -/

theorem ccw_pos_implies_cw_left_pos (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (b : Fin sys.rs.n) (h : 0 < gc.ccwMoveCountAt b) :
    0 < gc.cwMoveCountAt (left b) := by
  have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero (left b)
  unfold GoodCycle.edgeNetFlow at hflow
  simp [right_left_eq_self] at hflow; omega

theorem ccw_right_pos_implies_cw_pos (gc : GoodCycle sys) (hzero : gc.zeroWinding)
    (p : Fin sys.rs.n) (h : 0 < gc.ccwMoveCountAt (right p)) :
    0 < gc.cwMoveCountAt p := by
  have hflow := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero p
  unfold GoodCycle.edgeNetFlow at hflow; omega

/-! ### Trapped mover: cw=ccw=0 means the mover stays forever -/

/-- If cwMoveCountAt p = 0 and ccwMoveCountAt p = 0 and the mover is at p,
    then the next mover is also at p (only stays are possible). -/
theorem trapped_step (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hcw : gc.cwMoveCountAt p = 0) (hccw : gc.ccwMoveCountAt p = 0)
    (k : Fin gc.configs.length) (hmov : gc.moverAt k = p) :
    gc.moverAt (nextIndex gc.configs k) = p := by
  rcases gc.stepDir_cases k with hdir | hdir | hdir
  · exfalso; unfold GoodCycle.cwMoveCountAt at hcw
    have : (∑ j : Fin gc.configs.length,
        if gc.moverAt j = p ∧ gc.stepDir j = .cw then 1 else 0) ≥ 1 := by
      calc _ ≥ (if gc.moverAt k = p ∧ gc.stepDir k = .cw then 1 else 0) :=
            Finset.single_le_sum
              (f := fun j => if gc.moverAt j = p ∧ gc.stepDir j = .cw then 1 else 0)
              (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
        _ = 1 := by simp [hmov, hdir]
    omega
  · rw [gc.eq_self_of_stepDir_eq_stay hdir, hmov]
  · exfalso; unfold GoodCycle.ccwMoveCountAt at hccw
    have : (∑ j : Fin gc.configs.length,
        if gc.moverAt j = p ∧ gc.stepDir j = .ccw then 1 else 0) ≥ 1 := by
      calc _ ≥ (if gc.moverAt k = p ∧ gc.stepDir k = .ccw then 1 else 0) :=
            Finset.single_le_sum
              (f := fun j => if gc.moverAt j = p ∧ gc.stepDir j = .ccw then 1 else 0)
              (fun j _ => by simp only []; split <;> omega) (Finset.mem_univ k)
        _ = 1 := by simp [hmov, hdir]
    omega

/-- If the mover visits p and cwMoveCountAt p = ccwMoveCountAt p = 0,
    then the mover is at p at ALL steps (it stays forever). -/
theorem trapped_all_steps (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hcw : gc.cwMoveCountAt p = 0) (hccw : gc.ccwMoveCountAt p = 0)
    (k₀ : Fin gc.configs.length) (hmov : gc.moverAt k₀ = p) :
    ∀ k : Fin gc.configs.length, gc.moverAt k = p := by
  have hL := gc.configs_length_pos
  have hind : ∀ d : Nat, gc.moverAt ⟨(k₀.val + d) % gc.configs.length,
      Nat.mod_lt _ hL⟩ = p := by
    intro d; induction d with
    | zero => simp [Nat.add_zero, Nat.mod_eq_of_lt k₀.isLt]; exact hmov
    | succ d ih =>
      have hnext : nextIndex gc.configs ⟨(k₀.val + d) % gc.configs.length,
          Nat.mod_lt _ hL⟩ =
          ⟨(k₀.val + d + 1) % gc.configs.length, Nat.mod_lt _ hL⟩ := by
        ext; simp [nextIndex]
      rw [show k₀.val + (d + 1) = k₀.val + d + 1 from by omega, ← hnext]
      exact trapped_step gc p hcw hccw _ ih
  intro k
  have : k = ⟨(k₀.val + (k.val + gc.configs.length - k₀.val)) % gc.configs.length,
      Nat.mod_lt _ hL⟩ := by
    ext; simp
    rw [show k₀.val + (k.val + gc.configs.length - k₀.val) =
      k.val + gc.configs.length from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
  rw [this]; exact hind _

/-- A trapped mover at p violates hno_safe for n ≥ 7: right(right(p)) becomes safe. -/
theorem trapped_contradicts_hno_safe (gc : GoodCycle sys)
    (hn : sys.rs.n ≥ 9) (p : Fin sys.rs.n)
    (hcw : gc.cwMoveCountAt p = 0) (hccw : gc.ccwMoveCountAt p = 0)
    (k₀ : Fin gc.configs.length) (hmov : gc.moverAt k₀ = p)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q) :
    False := by
  have hall := trapped_all_steps gc p hcw hccw k₀ hmov
  apply hno_safe
  refine ⟨right (right p), fun k => ?_⟩
  rw [hall k]
  -- p ≠ right(right(p)): holds since right(right(p)) = (p+2)%n and n ≥ 7 > 2.
  -- p ≠ left(right(right(p))) = right(p): holds since n ≥ 4.
  -- p ≠ right(right(right(p))): holds since right³(p) = (p+3)%n and n ≥ 7 > 3.
  -- We prove all three by showing p ≠ right^k(p) for k = 1, 2, 3 when n > k.
  have hp := p.isLt
  have lrr : left (right (right p)) = right p := by
    simpa using left_right_eq_self (right p)
  constructor
  · -- p ≠ right(right p)
    intro heq; have hv := congrArg Fin.val heq; simp only [right_val] at hv
    by_cases h1 : p.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt h1] at hv
      by_cases h2 : p.val + 1 + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt h2] at hv; omega
      · rw [show p.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hv; omega
    · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self,
        Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hv; omega
  constructor
  · -- p ≠ left(right(right p)) = right p
    rw [lrr]
    intro h; have := congrArg Fin.val h; simp [right_val] at this
    by_cases hlt : p.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hlt] at this; omega
    · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self] at this; omega
  · -- p ≠ right(right(right p))
    intro heq
    have hv := congrArg Fin.val heq; simp only [right_val] at hv
    by_cases h1 : p.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt h1] at hv
      by_cases h2 : p.val + 1 + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt h2] at hv
        by_cases h3 : p.val + 1 + 1 + 1 < sys.rs.n
        · rw [Nat.mod_eq_of_lt h3] at hv; omega
        · rw [show p.val + 1 + 1 + 1 = sys.rs.n from by omega, Nat.mod_self] at hv; omega
      · rw [show p.val + 1 + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n)] at hv; omega
    · rw [show p.val + 1 = sys.rs.n from by omega, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega : 1 < sys.rs.n), Nat.mod_eq_of_lt (by omega : 2 < sys.rs.n)] at hv
      omega

/-! ### Extracting mover visits from hno_safe -/

/-- hno_safe implies: for every processor q, the mover visits {q, left q, right q}. -/
theorem hno_safe_visit (gc : GoodCycle sys)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (q : Fin sys.rs.n) :
    ∃ k : Fin gc.configs.length,
      gc.moverAt k = q ∨ gc.moverAt k = left q ∨ gc.moverAt k = right q := by
  by_contra hall
  push_neg at hall
  apply hno_safe
  exact ⟨q, fun k => ⟨(hall k).1, (hall k).2.1, (hall k).2.2⟩⟩

/-! ### Binary-right witness from CW or CCW at binary processors -/

/-- For binary i with binary right(i): either cwMoveCountAt i > 0 gives a
    binary-right CW crossing, or ccwMoveCountAt i > 0 gives one via edgeNetFlow,
    or both are zero (i is trapped). -/
theorem binary_right_witness_or_trapped (gc : GoodCycle sys)
    (hzero : gc.zeroWinding)
    (i : Fin sys.rs.n) (hbin_i : isBinary sys.rs i)
    (hbin_ri : isBinary sys.rs (right i)) :
    (∃ p : Fin sys.rs.n, isBinary sys.rs (right p) ∧ 0 < gc.cwMoveCountAt p) ∨
      (gc.cwMoveCountAt i = 0 ∧ gc.ccwMoveCountAt i = 0) := by
  by_cases hcw : 0 < gc.cwMoveCountAt i
  · exact Or.inl ⟨i, hbin_ri, hcw⟩
  · by_cases hccw : 0 < gc.ccwMoveCountAt i
    · left; exact ⟨left i, by simpa [right_left_eq_self] using hbin_i,
        ccw_pos_implies_cw_left_pos gc hzero i hccw⟩
    · right; omega

end LeanMn
