/-
  RingDisplacement.lean — Ring displacement bound for mover walks

  After a CW crossing of edge (p, right p) at step a, the mover starts
  at right p.  Without further crossings, it takes ≥ n steps for the mover
  to return to p (going the "long way" around the ring C_n).
-/
import LeanMn.LowerBound.EntryConflict.PairedCrossing

namespace LeanMn

variable {sys : System}

/-! ### CW ring distance from right p -/

private def D (p : Fin sys.rs.n) (q : Fin sys.rs.n) : Nat :=
  (q.val + sys.rs.n - (right p).val) % sys.rs.n

private theorem D_right_p (p : Fin sys.rs.n) : D p (right p) = 0 := by
  simp [D, Nat.mod_self]

private theorem D_p (p : Fin sys.rs.n) : D p p = sys.rs.n - 1 := by
  have hn := sys.rs.n_ge_4
  simp only [D, right_val]
  by_cases hwrap : p.val + 1 < sys.rs.n
  · rw [Nat.mod_eq_of_lt hwrap,
      show p.val + sys.rs.n - (p.val + 1) = sys.rs.n - 1 by omega,
      Nat.mod_eq_of_lt (by omega)]
  · rw [show p.val + 1 = sys.rs.n by omega, Nat.mod_self,
      show p.val + sys.rs.n - 0 = p.val + sys.rs.n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]; omega

private theorem raw_cases (p q : Fin sys.rs.n) :
    q.val + sys.rs.n - (right p).val = D p q ∨
    q.val + sys.rs.n - (right p).val = D p q + sys.rs.n := by
  set rp := right p; set d := D p q
  have : (q.val + sys.rs.n - rp.val) % sys.rs.n = d := rfl
  rcases Nat.lt_or_ge (q.val + sys.rs.n - rp.val) sys.rs.n with h | h
  · left; rwa [Nat.mod_eq_of_lt h] at this
  · right
    rw [show q.val + sys.rs.n - rp.val =
      (q.val + sys.rs.n - rp.val - sys.rs.n) + sys.rs.n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by
        have := q.isLt; have := rp.isLt; omega)] at this; omega

private theorem D_eq_zero_iff (p q : Fin sys.rs.n) :
    D p q = 0 ↔ q = right p := by
  have hn := sys.rs.n_ge_4
  constructor
  · intro h
    rcases raw_cases p q with hr | hr <;> {
      have := q.isLt; have := (right p).isLt
      exact Fin.ext (by omega) }
  · intro h; rw [h]; exact D_right_p p

private theorem D_right_of_lt (p q : Fin sys.rs.n)
    (hlt : D p q < sys.rs.n - 1) :
    D p (right q) = D p q + 1 := by
  have hn := sys.rs.n_ge_4
  set d := D p q; set rp := right p
  -- D p (right q) = ((q+1)%n + n - rp) % n
  -- We know q + n - rp ≡ d (mod n) and d < n-1
  -- So (q+1) + n - rp ≡ d+1 (mod n) and d+1 < n
  unfold D
  rcases raw_cases p q with hr | hr
  · -- q + n - rp = d (the "small" case, q ≥ rp - n, i.e., usually q ≥ rp)
    -- So q = d + rp - n or q = d + rp depending...
    -- q + n - rp = d, so q = d + rp - n. Since q ≥ 0, d + rp ≥ n.
    -- Actually q.val = d + rp.val - n if rp.val > d... no:
    -- q.val + n - rp.val = d, so q.val = d + rp.val - n. Need d + rp.val ≥ n.
    -- But d could be 0 and rp.val could be 0, giving q.val = -n which is impossible.
    -- Actually Nat subtraction: q.val + sys.rs.n - rp.val = d means
    -- q.val + sys.rs.n ≥ rp.val (always true since sys.rs.n ≥ 4 > rp.val... no, rp.val < n)
    -- So q.val = d + rp.val - sys.rs.n (as Nat, this requires d + rp.val ≥ n)
    -- OR q.val + n - rp.val = d with q.val + n ≥ rp.val, so d = q.val + n - rp.val
    -- which means q.val = d - n + rp.val. Since d < n: if rp.val ≤ d then q.val = d - rp.val... hmm
    -- Let's just case-split on (q.val + 1) < n
    by_cases hq1 : q.val + 1 < sys.rs.n
    · rw [right_val, Nat.mod_eq_of_lt hq1,
        show q.val + 1 + sys.rs.n - rp.val = d + 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
    · have hqn : q.val + 1 = sys.rs.n := by have := q.isLt; omega
      rw [right_val, hqn, Nat.mod_self,
        show 0 + sys.rs.n - rp.val = d + 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
  · -- q + n - rp = d + n (the "large" case)
    -- So q = d + rp. Since d < n-1 and rp < n, q could be up to 2n-2.
    -- But q < n, so d + rp < n, meaning q = d + rp and d + rp < n.
    -- Wait: q + n - rp = d + n means q = d + rp. q < n and rp < n.
    -- d + rp < n (since q = d + rp < n).
    by_cases hq1 : q.val + 1 < sys.rs.n
    · rw [right_val, Nat.mod_eq_of_lt hq1,
        show q.val + 1 + sys.rs.n - rp.val = d + 1 + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · -- q + 1 = n, so q = n-1. q = d + rp, so d + rp = n - 1.
      -- d + 1 = n - rp. Since rp < n: d + 1 ≥ 1.
      -- (0 + n - rp) % n = (n - rp) % n.
      -- If rp = 0: (n - 0) % n = 0. But d + 1 = n, d = n-1. But d < n-1. Contradiction.
      -- If rp > 0: n - rp < n, so (n - rp) % n = n - rp = d + 1. Result = d + 1. ✓
      have hqn : q.val + 1 = sys.rs.n := by have := q.isLt; omega
      have hrp_pos : 0 < rp.val := by
        by_contra h; push_neg at h
        have : rp.val = 0 := by omega
        omega -- d + rp = n - 1, rp = 0, d = n-1, contradicts d < n-1
      rw [right_val, hqn, Nat.mod_self,
        show 0 + sys.rs.n - rp.val = d + 1 by omega,
        Nat.mod_eq_of_lt (by omega)]

private theorem D_left_of_pos (p q : Fin sys.rs.n)
    (hpos : 0 < D p q) :
    D p (left q) = D p q - 1 := by
  have hn := sys.rs.n_ge_4
  set d := D p q; set rp := right p
  have hrp := rp.isLt; have hq := q.isLt
  have hd_lt : d < sys.rs.n := Nat.mod_lt _ (by omega)
  unfold D
  rcases raw_cases p q with hr | hr
  · -- q + n - rp = d, with d > 0
    have hlq : (left q).val = if q.val = 0 then sys.rs.n - 1 else q.val - 1 := by
      rw [left_val]
      split
      · next h => rw [h, show 0 + sys.rs.n - 1 = sys.rs.n - 1 by omega,
          Nat.mod_eq_of_lt (by omega)]
      · next h =>
        rw [show q.val + sys.rs.n - 1 = (q.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    show ((left q).val + sys.rs.n - rp.val) % sys.rs.n = d - 1
    split_ifs at hlq with hq0
    · -- q = 0: left q = n - 1
      rw [hlq, show sys.rs.n - 1 + sys.rs.n - rp.val = (d - 1) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · -- q > 0: left q = q - 1
      rw [hlq, show q.val - 1 + sys.rs.n - rp.val = d - 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
  · -- q + n - rp = d + n, so q = d + rp, d > 0
    by_cases hq0 : q.val = 0
    · omega -- q = 0 = d + rp with d > 0 → impossible
    · -- left q = (q-1+n) % n = q-1 (since 0 < q < n)
      have hq_pos : 0 < q.val := by omega
      have hq_lt := q.isLt
      have hleft_val : (left q).val = q.val - 1 := by
        rw [left_val, show q.val + sys.rs.n - 1 = (q.val - 1) + sys.rs.n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      -- D p (left q) = (left_q + n - rp) % n = (q-1 + n - rp) % n
      show (((left q).val + sys.rs.n - rp.val) % sys.rs.n) = d - 1
      rw [hleft_val]
      -- q - 1 + n - rp = (d + rp) - 1 + n - rp = d - 1 + n
      rw [show q.val - 1 + sys.rs.n - rp.val = (d - 1) + sys.rs.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ### The main bound by induction on gap -/

private theorem D_moverAt_le (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (a : Fin gc.configs.length)
    (hcw : edgeCWCrossAt gc p a)
    : ∀ d : Nat, 0 < d → d < sys.rs.n →
      (hjlt : a.val + d < gc.configs.length) →
      (∀ i : Fin gc.configs.length,
        a.val < i.val → i.val ≤ a.val + d → ¬edgeCrossAt' gc p i) →
      D p (gc.moverAt ⟨a.val + d, hjlt⟩) ≤ d - 1 := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ d ih =>
    intro hpos hdn hjlt hno
    by_cases hd0 : d = 0
    · subst hd0
      have hnext : (nextIndex gc.configs a).val = a.val + 1 := by
        simp [nextIndex, Nat.mod_eq_of_lt hjlt]
      conv_lhs => rw [show gc.moverAt ⟨a.val + 1, hjlt⟩ =
        gc.moverAt (nextIndex gc.configs a) from by congr 1; exact Fin.ext hnext.symm]
      rw [gc.eq_right_of_stepDir_eq_cw hcw.2, hcw.1, D_right_p]
    · have hprev_lt : a.val + d < gc.configs.length := by omega
      have ih_prev : D p (gc.moverAt ⟨a.val + d, hprev_lt⟩) ≤ d - 1 :=
        ih (by omega) (by omega) hprev_lt (fun i hi1 hi2 => hno i hi1 (by omega))
      set prev : Fin gc.configs.length := ⟨a.val + d, hprev_lt⟩
      have hnext : (nextIndex gc.configs prev).val = a.val + (d + 1) := by
        simp [nextIndex, prev, Nat.mod_eq_of_lt (by omega : a.val + d + 1 < gc.configs.length)]
        omega
      conv_lhs => rw [show gc.moverAt ⟨a.val + (d + 1), hjlt⟩ =
        gc.moverAt (nextIndex gc.configs prev) from by
          congr 1; exact Fin.ext hnext.symm]
      have hD_lt : D p (gc.moverAt prev) < sys.rs.n - 1 := by omega
      rcases gc.next_mover_is_local prev with hleft | hstay | hright
      · rw [hleft]
        by_cases hdzero : D p (gc.moverAt prev) = 0
        · -- moverAt prev = right p, CCW step → crossing
          have hmov_rp := (D_eq_zero_iff p _).mp hdzero
          have hdir_ccw := gc.stepDir_eq_ccw_of_eq_left hleft
          have hcross : edgeCrossAt' gc p prev :=
            (edgeCrossAt'_iff_cwOrCcw gc p prev).mpr (Or.inr ⟨hmov_rp, hdir_ccw⟩)
          have hprev_gt : a.val < prev.val := by simp [prev]; omega
          have hprev_le : prev.val ≤ a.val + (d + 1) := by simp [prev]
          exact absurd hcross (hno prev hprev_gt hprev_le)
        · rw [D_left_of_pos p _ (by omega)]; omega
      · rw [hstay]; omega
      · rw [hright, D_right_of_lt p _ hD_lt]; omega

/-- **Ring Displacement Bound.** After a CW crossing of edge (p, right p)
    at step a, with no further crossings in (a, k], the mover at step k
    is not at p provided the gap k − a is less than n. -/
theorem mover_no_return_within_short_gap (gc : GoodCycle sys)
    (p : Fin sys.rs.n) (a k : Fin gc.configs.length)
    (hcw : edgeCWCrossAt gc p a)
    (hak : a.val < k.val)
    (hgap : k.val - a.val < sys.rs.n)
    (hno_cross : ∀ j : Fin gc.configs.length,
      a.val < j.val → j.val ≤ k.val → ¬edgeCrossAt' gc p j) :
    gc.moverAt k ≠ p := by
  intro hmov
  have hd := k.val - a.val
  have hjlt : a.val + (k.val - a.val) < gc.configs.length := by omega
  have hfin_eq : (⟨a.val + (k.val - a.val), hjlt⟩ : Fin gc.configs.length) = k :=
    Fin.ext (show a.val + (k.val - a.val) = k.val by omega)
  have hak_le : a.val + (k.val - a.val) = k.val := by omega
  have hbound := D_moverAt_le gc p a hcw (k.val - a.val) (by omega) hgap hjlt
    (fun i hi1 hi2 => hno_cross i hi1 (by omega))
  rw [hfin_eq, hmov, D_p] at hbound
  omega

end LeanMn
