import LeanMn.Basic

open scoped BigOperators

namespace LeanMn

structure RingSpec where
  n : Nat
  n_ge_4 : 4 ≤ n
  m : Fin n → Nat
  m_pos : ∀ i, 2 ≤ m i

def Config (rs : RingSpec) := (i : Fin rs.n) → Fin (rs.m i)

instance (rs : RingSpec) : DecidableEq (Config rs) := by
  unfold Config
  infer_instance

instance (rs : RingSpec) : Fintype (Config rs) := by
  unfold Config
  infer_instance

def left {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.1 + n - 1) % n, by
    have hn : n ≠ 0 := by
      intro h
      subst h
      exact Nat.not_lt_zero _ i.2
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩

def right {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, by
    have hn : n ≠ 0 := by
      intro h
      subst h
      exact Nat.not_lt_zero _ i.2
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩

@[simp] theorem left_val {n : Nat} (i : Fin n) : (left i).1 = (i.1 + n - 1) % n := rfl
@[simp] theorem right_val {n : Nat} (i : Fin n) : (right i).1 = (i.1 + 1) % n := rfl

@[simp] theorem left_right_eq_self {n : Nat} (i : Fin n) : left (right i) = i := by
  ext
  by_cases hwrap : i.val + 1 < n
  · rw [left_val, right_val, Nat.mod_eq_of_lt hwrap]
    rw [show i.val + 1 + n - 1 = i.val + n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt i.isLt
  · have hEq : i.val + 1 = n := by omega
    rw [left_val, right_val, hEq, Nat.mod_self]
    rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    omega

@[simp] theorem right_left_eq_self {n : Nat} (i : Fin n) : right (left i) = i := by
  ext
  rw [right_val, left_val]
  by_cases hzero : i.val = 0
  · rw [hzero, Nat.zero_add]
    have hn : 0 < n := by
      have hne : n ≠ 0 := by
        intro h
        subst h
        exact Nat.not_lt_zero _ i.isLt
      exact Nat.pos_of_ne_zero hne
    have hnm1 : (n - 1) % n = n - 1 := by
      exact Nat.mod_eq_of_lt (by omega)
    have hsum : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
    rw [hnm1, hsum, Nat.mod_self]
  · rw [show (i.val + n - 1) % n = i.val - 1 by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

def TransFn (rs : RingSpec) :=
  (i : Fin rs.n) →
    Fin (rs.m (left i)) →
      Fin (rs.m i) →
        Fin (rs.m (right i)) →
          Fin (rs.m i)

structure System where
  rs : RingSpec
  f : TransFn rs

def stateProduct (rs : RingSpec) : Nat :=
  ∏ i : Fin rs.n, rs.m i

end LeanMn
