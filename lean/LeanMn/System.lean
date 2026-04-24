import LeanMn.Dijkstra
import LeanMn.Tables

namespace LeanMn

def cup2M (n : Nat) (i : Fin n) : Nat :=
  if i.1 = 0 ∨ i.1 + 1 = n then 2 else 3

lemma cup2M_eq_two_of_endpoint {n : Nat} {i : Fin n} (h : i.1 = 0 ∨ i.1 + 1 = n) :
    cup2M n i = 2 := by
  simp [cup2M, h]

lemma cup2M_eq_three_of_notEndpoint {n : Nat} {i : Fin n} (h : ¬(i.1 = 0 ∨ i.1 + 1 = n)) :
    cup2M n i = 3 := by
  simp [cup2M, h]

def cup2Spec (n : Nat) (hn : 4 ≤ n) : RingSpec where
  n := n
  n_ge_4 := hn
  m := cup2M n
  m_pos := by
    intro i
    by_cases h : i.1 = 0 ∨ i.1 + 1 = n <;> simp [cup2M, h]

lemma left_val_of_ne_zero {n : Nat} {i : Fin n} (h0 : i.1 ≠ 0) :
    (left i).1 = i.1 - 1 := by
  rw [left_val]
  have hlt : i.1 - 1 < n := by
    omega
  have hdecomp : i.1 + n - 1 = n + (i.1 - 1) := by
    omega
  rw [hdecomp, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma right_val_of_not_top {n : Nat} {i : Fin n} (htop : i.1 + 1 ≠ n) :
    (right i).1 = i.1 + 1 := by
  rw [right_val, Nat.mod_eq_of_lt]
  omega

lemma right_val_of_top {n : Nat} {i : Fin n} (htop : i.1 + 1 = n) :
    (right i).1 = 0 := by
  rw [right_val, htop, Nat.mod_self]

lemma cup2M_left_bot {n : Nat} (hn : 4 ≤ n) {i : Fin n} (h0 : i.1 = 0) :
    cup2M n (left i) = 2 := by
  apply cup2M_eq_two_of_endpoint
  right
  rw [left_val, h0]
  have hpos : 0 < n := by
    omega
  rw [Nat.zero_add, Nat.mod_eq_of_lt]
  · omega
  · omega

lemma cup2M_right_bot {n : Nat} (hn : 4 ≤ n) {i : Fin n} (h0 : i.1 = 0) :
    cup2M n (right i) = 3 := by
  have htop : i.1 + 1 ≠ n := by
    omega
  have hright : (right i).1 = 1 := by
    rw [right_val_of_not_top htop, h0]
  apply cup2M_eq_three_of_notEndpoint
  intro h
  rw [hright] at h
  omega

lemma cup2M_left_low {n : Nat} (_hn : 4 ≤ n) {i : Fin n} (h1 : i.1 = 1) :
    cup2M n (left i) = 2 := by
  have h0 : i.1 ≠ 0 := by
    omega
  have hleft : (left i).1 = 0 := by
    rw [left_val_of_ne_zero h0, h1]
  apply cup2M_eq_two_of_endpoint
  left
  exact hleft

lemma cup2M_self_low {n : Nat} (hn : 4 ≤ n) {i : Fin n} (h1 : i.1 = 1) :
    cup2M n i = 3 := by
  apply cup2M_eq_three_of_notEndpoint
  intro h
  omega

lemma cup2M_right_low {n : Nat} (hn : 4 ≤ n) {i : Fin n} (h1 : i.1 = 1) :
    cup2M n (right i) = 3 := by
  have htop : i.1 + 1 ≠ n := by
    omega
  have hright : (right i).1 = 2 := by
    rw [right_val_of_not_top htop, h1]
  apply cup2M_eq_three_of_notEndpoint
  intro h
  rw [hright] at h
  omega

lemma cup2M_left_top {n : Nat} (hn : 4 ≤ n) {i : Fin n} (htop : i.1 + 1 = n) :
    cup2M n (left i) = 3 := by
  have h0 : i.1 ≠ 0 := by
    omega
  have hleft : (left i).1 = n - 2 := by
    rw [left_val_of_ne_zero h0]
    omega
  apply cup2M_eq_three_of_notEndpoint
  intro h
  rw [hleft] at h
  omega

lemma cup2M_right_top {n : Nat} (_hn : 4 ≤ n) {i : Fin n} (htop : i.1 + 1 = n) :
    cup2M n (right i) = 2 := by
  have hright : (right i).1 = 0 := right_val_of_top htop
  apply cup2M_eq_two_of_endpoint
  left
  exact hright

lemma cup2M_self_high {n : Nat} (_hn : 4 ≤ n) {i : Fin n} (hhigh : i.1 + 2 = n) :
    cup2M n i = 3 := by
  apply cup2M_eq_three_of_notEndpoint
  intro h
  omega

lemma cup2M_left_high {n : Nat} (hn : 4 ≤ n) {i : Fin n} (hhigh : i.1 + 2 = n) :
    cup2M n (left i) = 3 := by
  have h0 : i.1 ≠ 0 := by
    omega
  have hleft : (left i).1 = n - 3 := by
    rw [left_val_of_ne_zero h0]
    omega
  apply cup2M_eq_three_of_notEndpoint
  intro h
  rw [hleft] at h
  omega

lemma cup2M_right_high {n : Nat} (hn : 4 ≤ n) {i : Fin n} (hhigh : i.1 + 2 = n) :
    cup2M n (right i) = 2 := by
  have htop : i.1 + 1 ≠ n := by
    omega
  have hright : (right i).1 = n - 1 := by
    rw [right_val_of_not_top htop]
    omega
  apply cup2M_eq_two_of_endpoint
  right
  rw [hright]
  omega

lemma cup2M_self_mid {n : Nat} (_hn : 4 ≤ n) {i : Fin n}
    (h0 : i.1 ≠ 0) (htop : i.1 + 1 ≠ n) :
    cup2M n i = 3 := by
  apply cup2M_eq_three_of_notEndpoint
  exact fun h => h.elim h0 htop

lemma cup2M_left_mid {n : Nat} (hn : 4 ≤ n) {i : Fin n}
    (h0 : i.1 ≠ 0) (h1 : i.1 ≠ 1) (htop : i.1 + 1 ≠ n) :
    cup2M n (left i) = 3 := by
  have hleft : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  apply cup2M_eq_three_of_notEndpoint
  intro h
  rw [hleft] at h
  omega

lemma cup2M_right_mid {n : Nat} (_hn : 4 ≤ n) {i : Fin n}
    (_h0 : i.1 ≠ 0) (htop : i.1 + 1 ≠ n) (hhigh : i.1 + 2 ≠ n) :
    cup2M n (right i) = 3 := by
  have hright : (right i).1 = i.1 + 1 := right_val_of_not_top htop
  apply cup2M_eq_three_of_notEndpoint
  intro h
  rw [hright] at h
  omega

lemma cup2M_middle (m : Nat) (i : Fin m) :
    cup2M (m + 2) (Fin.castSucc i.succ) = 3 := by
  apply cup2M_eq_three_of_notEndpoint
  intro h
  rcases h with hzero | hend
  · have : ((Fin.castSucc i.succ : Fin (m + 2)).1) = i.1 + 1 := by rfl
    rw [this] at hzero
    omega
  · have : ((Fin.castSucc i.succ : Fin (m + 2)).1) = i.1 + 1 := by rfl
    rw [this] at hend
    omega

def cup2OutVal (n : Nat) (i : Fin n) (L S R : Nat) : Nat :=
  if i.1 = 0 then
    TBotVal L S R
  else if i.1 = 1 then
    TLowVal L S R
  else if i.1 + 1 = n then
    TTopVal L S R
  else if i.1 + 2 = n then
    THighVal L S R
  else
    TMidVal L S R

def cup2Trans (n : Nat) (hn : 4 ≤ n) : TransFn (cup2Spec n hn) := by
  intro i L S R
  refine ⟨cup2OutVal n i L.1 S.1 R.1, ?_⟩
  change cup2OutVal n i L.1 S.1 R.1 < cup2M n i
  by_cases h0 : i.1 = 0
  · have hself : cup2M n i = 2 := cup2M_eq_two_of_endpoint (Or.inl h0)
    have hL : L.1 < 2 := by
      simpa [cup2Spec, cup2M_left_bot hn h0] using L.2
    have hS : S.1 < 2 := by
      simpa [cup2Spec, hself] using S.2
    have hR : R.1 < 3 := by
      simpa [cup2Spec, cup2M_right_bot hn h0] using R.2
    rw [hself]
    simpa [cup2OutVal, h0] using TBotVal_lt hL hS hR
  · by_cases h1 : i.1 = 1
    · have hself : cup2M n i = 3 := cup2M_self_low hn h1
      have hL : L.1 < 2 := by
        simpa [cup2Spec, cup2M_left_low hn h1] using L.2
      have hS : S.1 < 3 := by
        simpa [cup2Spec, hself] using S.2
      have hR : R.1 < 3 := by
        simpa [cup2Spec, cup2M_right_low hn h1] using R.2
      rw [hself]
      simpa [cup2OutVal, h0, h1] using TLowVal_lt hL hS hR
    ·
      by_cases htop : i.1 + 1 = n
      · have hself : cup2M n i = 2 := cup2M_eq_two_of_endpoint (Or.inr htop)
        have hL : L.1 < 3 := by
          simpa [cup2Spec, cup2M_left_top hn htop] using L.2
        have hS : S.1 < 2 := by
          simpa [cup2Spec, hself] using S.2
        have hR : R.1 < 2 := by
          simpa [cup2Spec, cup2M_right_top hn htop] using R.2
        rw [hself]
        simpa [cup2OutVal, h0, h1, htop] using TTopVal_lt hL hS hR
      ·
        by_cases hhigh : i.1 + 2 = n
        · have hself : cup2M n i = 3 := cup2M_self_high hn hhigh
          have hL : L.1 < 3 := by
            simpa [cup2Spec, cup2M_left_high hn hhigh] using L.2
          have hS : S.1 < 3 := by
            simpa [cup2Spec, hself] using S.2
          have hR : R.1 < 2 := by
            simpa [cup2Spec, cup2M_right_high hn hhigh] using R.2
          rw [hself]
          simpa [cup2OutVal, h0, h1, htop, hhigh] using THighVal_lt hL hS hR
        · have hself : cup2M n i = 3 := cup2M_self_mid hn h0 htop
          have hL : L.1 < 3 := by
            simpa [cup2Spec, cup2M_left_mid hn h0 h1 htop] using L.2
          have hS : S.1 < 3 := by
            simpa [cup2Spec, hself] using S.2
          have hR : R.1 < 3 := by
            simpa [cup2Spec, cup2M_right_mid hn h0 htop hhigh] using R.2
          rw [hself]
          simpa [cup2OutVal, h0, h1, htop, hhigh] using TMidVal_lt hL hS hR

def cup2System (n : Nat) (hn : 4 ≤ n) : System where
  rs := cup2Spec n hn
  f := cup2Trans n hn

theorem cup2_stateProduct_aux (m : Nat) :
    ∏ i : Fin (m + 2), cup2M (m + 2) i = 4 * 3 ^ m := by
  calc
    ∏ i : Fin (m + 2), cup2M (m + 2) i
      = (∏ i : Fin (m + 1), cup2M (m + 2) (Fin.castSucc i)) *
          cup2M (m + 2) (Fin.last (m + 1)) := by
          simpa using (Fin.prod_univ_castSucc (f := fun i : Fin (m + 2) => cup2M (m + 2) i))
    _ = (∏ i : Fin (m + 1), cup2M (m + 2) (Fin.castSucc i)) * 2 := by
          rw [cup2M_eq_two_of_endpoint (n := m + 2) (i := Fin.last (m + 1)) (Or.inr rfl)]
    _ = (cup2M (m + 2) (Fin.castSucc (0 : Fin (m + 1))) *
          ∏ i : Fin m, cup2M (m + 2) (Fin.castSucc i.succ)) * 2 := by
          rw [Fin.prod_univ_succ]
    _ = (2 * ∏ i : Fin m, 3) * 2 := by
          rw [cup2M_eq_two_of_endpoint (n := m + 2) (i := Fin.castSucc (0 : Fin (m + 1)))
            (Or.inl rfl)]
          have hmid :
              (∏ i : Fin m, cup2M (m + 2) (Fin.castSucc i.succ)) = ∏ i : Fin m, 3 := by
            congr
            ext i
            exact cup2M_middle m i
          rw [hmid]
    _ = (2 * 3 ^ m) * 2 := by
          rw [Fin.prod_const]
    _ = 4 * 3 ^ m := by
          calc
            (2 * 3 ^ m) * 2 = 2 * ((3 ^ m) * 2) := by rw [Nat.mul_assoc]
            _ = 2 * (2 * 3 ^ m) := by rw [Nat.mul_comm (3 ^ m) 2]
            _ = (2 * 2) * 3 ^ m := by rw [← Nat.mul_assoc]
            _ = 4 * 3 ^ m := by norm_num

theorem cup2_stateProduct (n : Nat) (hn : 4 ≤ n) :
    stateProduct (cup2Spec n hn) = 4 * 3 ^ (n - 2) := by
  change ∏ i : Fin n, cup2M n i = 4 * 3 ^ (n - 2)
  have hdecomp : n = n - 2 + 2 := by
    omega
  calc
    ∏ i : Fin n, cup2M n i = ∏ i : Fin (n - 2 + 2), cup2M (n - 2 + 2) i := by
      simpa using congrArg (fun k : Nat => ∏ i : Fin k, cup2M k i) hdecomp
    _ = 4 * 3 ^ (n - 2) := cup2_stateProduct_aux (n - 2)

end LeanMn
