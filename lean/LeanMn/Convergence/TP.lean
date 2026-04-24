import LeanMn.Convergence.CopyDAG

namespace LeanMn

open scoped BigOperators

def cup2Exp2BitVal (n j a b : Nat) : Nat :=
  if 2 ≤ j ∧ j + 2 < n ∧ a = 2 ∧ b ≠ 2 then 1 else 0

def cup2Exp2Term (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (j : Fin n) : Nat :=
  cup2Exp2BitVal n j.1 (c j).1 (c (right j)).1

def cup2Exp2Count (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat :=
  ∑ j : Fin n, cup2Exp2Term n hn c j

def cup2Int21BitVal (n j a b : Nat) : Nat :=
  if 2 ≤ j ∧ j + 2 < n ∧ a = 2 ∧ b = 1 then 1 else 0

def cup2Int21Term (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (j : Fin n) : Nat :=
  cup2Int21BitVal n j.1 (c j).1 (c (right j)).1

def cup2Int21Count (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat :=
  ∑ j : Fin n, cup2Int21Term n hn c j

def cup2Exp2WeightTerm (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (j : Fin n) : Nat :=
  j.1 * cup2Exp2Term n hn c j

def cup2Exp2Weight (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat :=
  ∑ j : Fin n, cup2Exp2WeightTerm n hn c j

def cup2TpInvariant (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat × Nat × Nat :=
  (cup2Exp2Count n hn c, cup2Int21Count n hn c, cup2Exp2Weight n hn c)

def cup2TpPreservingMove (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n) : Prop :=
  cup2TpInvariant n hn (move (cup2System n hn) c i) = cup2TpInvariant n hn c

def localExp2Before (n : Nat) (i : Fin n) (L S R : Nat) : Nat :=
  cup2Exp2BitVal n (left i).1 L S + cup2Exp2BitVal n i.1 S R

def localExp2After (n : Nat) (i : Fin n) (L _S R out : Nat) : Nat :=
  cup2Exp2BitVal n (left i).1 L out + cup2Exp2BitVal n i.1 out R

def localInt21Before (n : Nat) (i : Fin n) (L S R : Nat) : Nat :=
  cup2Int21BitVal n (left i).1 L S + cup2Int21BitVal n i.1 S R

def localInt21After (n : Nat) (i : Fin n) (L _S R out : Nat) : Nat :=
  cup2Int21BitVal n (left i).1 L out + cup2Int21BitVal n i.1 out R

def localExp2WeightBefore (n : Nat) (i : Fin n) (L S R : Nat) : Nat :=
  (left i).1 * cup2Exp2BitVal n (left i).1 L S + i.1 * cup2Exp2BitVal n i.1 S R

def localExp2WeightAfter (n : Nat) (i : Fin n) (L _S R out : Nat) : Nat :=
  (left i).1 * cup2Exp2BitVal n (left i).1 L out + i.1 * cup2Exp2BitVal n i.1 out R

lemma cup2Exp2Term_move_eq_of_mem_adjacentComplement (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i j : Fin n) (hj : j ∈ adjacentComplement i) :
    cup2Exp2Term n hn (move (cup2System n hn) c i) j = cup2Exp2Term n hn c j := by
  have hn2 : 2 ≤ n := by omega
  have hji : j ≠ i := (mem_adjacentComplement_iff i j).mp hj |>.1
  have hright : right j ≠ i := right_ne_of_mem_adjacentComplement hn2 i j hj
  unfold cup2Exp2Term cup2Exp2BitVal
  simp [move, hji, hright]

lemma cup2Int21Term_move_eq_of_mem_adjacentComplement (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i j : Fin n) (hj : j ∈ adjacentComplement i) :
    cup2Int21Term n hn (move (cup2System n hn) c i) j = cup2Int21Term n hn c j := by
  have hn2 : 2 ≤ n := by omega
  have hji : j ≠ i := (mem_adjacentComplement_iff i j).mp hj |>.1
  have hright : right j ≠ i := right_ne_of_mem_adjacentComplement hn2 i j hj
  unfold cup2Int21Term cup2Int21BitVal
  simp [move, hji, hright]

lemma cup2Exp2WeightTerm_move_eq_of_mem_adjacentComplement (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i j : Fin n) (hj : j ∈ adjacentComplement i) :
    cup2Exp2WeightTerm n hn (move (cup2System n hn) c i) j =
      cup2Exp2WeightTerm n hn c j := by
  unfold cup2Exp2WeightTerm
  rw [cup2Exp2Term_move_eq_of_mem_adjacentComplement n hn c i j hj]

lemma cup2Exp2_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Exp2Count n hn c =
      localExp2Before n i (c (left i)).1 (c i).1 (c (right i)).1 +
        Finset.sum (adjacentComplement i) (cup2Exp2Term n hn c) := by
  have hn2 : 2 ≤ n := by omega
  rw [cup2Exp2Count, sum_univ_eq_adjacentComplement hn2 (cup2Exp2Term n hn c) i]
  unfold localExp2Before cup2Exp2Term
  rw [right_left hn2 i]
  ac_rfl

lemma cup2Exp2_move_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Exp2Count n hn (move (cup2System n hn) c i) =
      localExp2After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) +
          Finset.sum (adjacentComplement i)
            (cup2Exp2Term n hn (move (cup2System n hn) c i)) := by
  have hn2 : 2 ≤ n := by omega
  have hout :
      ((cup2System n hn).f i (c (left i)) (c i) (c (right i))).1 =
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 := by
    rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
    rw [cup2Trans_val]
  rw [cup2Exp2Count,
    sum_univ_eq_adjacentComplement hn2
      (fun j => cup2Exp2Term n hn (move (cup2System n hn) c i) j) i]
  unfold localExp2After cup2Exp2Term
  simp [move, left_ne_self hn2 i, right_ne_self hn2 i, right_left hn2 i]
  rw [hout]
  ac_rfl

lemma cup2Int21_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Int21Count n hn c =
      localInt21Before n i (c (left i)).1 (c i).1 (c (right i)).1 +
        Finset.sum (adjacentComplement i) (cup2Int21Term n hn c) := by
  have hn2 : 2 ≤ n := by omega
  rw [cup2Int21Count, sum_univ_eq_adjacentComplement hn2 (cup2Int21Term n hn c) i]
  unfold localInt21Before cup2Int21Term
  rw [right_left hn2 i]
  ac_rfl

lemma cup2Int21_move_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Int21Count n hn (move (cup2System n hn) c i) =
      localInt21After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) +
          Finset.sum (adjacentComplement i)
            (cup2Int21Term n hn (move (cup2System n hn) c i)) := by
  have hn2 : 2 ≤ n := by omega
  have hout :
      ((cup2System n hn).f i (c (left i)) (c i) (c (right i))).1 =
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 := by
    rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
    rw [cup2Trans_val]
  rw [cup2Int21Count,
    sum_univ_eq_adjacentComplement hn2
      (fun j => cup2Int21Term n hn (move (cup2System n hn) c i) j) i]
  unfold localInt21After cup2Int21Term
  simp [move, left_ne_self hn2 i, right_ne_self hn2 i, right_left hn2 i]
  rw [hout]
  ac_rfl

lemma cup2Exp2Weight_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Exp2Weight n hn c =
      localExp2WeightBefore n i (c (left i)).1 (c i).1 (c (right i)).1 +
        Finset.sum (adjacentComplement i) (cup2Exp2WeightTerm n hn c) := by
  have hn2 : 2 ≤ n := by omega
  rw [cup2Exp2Weight, sum_univ_eq_adjacentComplement hn2 (cup2Exp2WeightTerm n hn c) i]
  unfold localExp2WeightBefore cup2Exp2WeightTerm cup2Exp2Term
  rw [right_left hn2 i]
  ac_rfl

lemma cup2Exp2Weight_move_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Exp2Weight n hn (move (cup2System n hn) c i) =
      localExp2WeightAfter n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) +
          Finset.sum (adjacentComplement i)
            (cup2Exp2WeightTerm n hn (move (cup2System n hn) c i)) := by
  have hn2 : 2 ≤ n := by omega
  have hout :
      ((cup2System n hn).f i (c (left i)) (c i) (c (right i))).1 =
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 := by
    rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
    rw [cup2Trans_val]
  rw [cup2Exp2Weight,
    sum_univ_eq_adjacentComplement hn2
      (fun j => cup2Exp2WeightTerm n hn (move (cup2System n hn) c i) j) i]
  unfold localExp2WeightAfter cup2Exp2WeightTerm cup2Exp2Term
  simp [move, left_ne_self hn2 i, right_ne_self hn2 i, right_left hn2 i]
  rw [hout]
  ac_rfl

lemma cup2Exp2_rest_move_eq (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    Finset.sum (adjacentComplement i) (cup2Exp2Term n hn (move (cup2System n hn) c i)) =
      Finset.sum (adjacentComplement i) (cup2Exp2Term n hn c) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact cup2Exp2Term_move_eq_of_mem_adjacentComplement n hn c i j hj

lemma cup2Int21_rest_move_eq (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    Finset.sum (adjacentComplement i) (cup2Int21Term n hn (move (cup2System n hn) c i)) =
      Finset.sum (adjacentComplement i) (cup2Int21Term n hn c) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact cup2Int21Term_move_eq_of_mem_adjacentComplement n hn c i j hj

lemma cup2Exp2Weight_rest_move_eq (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    Finset.sum (adjacentComplement i) (cup2Exp2WeightTerm n hn (move (cup2System n hn) c i)) =
      Finset.sum (adjacentComplement i) (cup2Exp2WeightTerm n hn c) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact cup2Exp2WeightTerm_move_eq_of_mem_adjacentComplement n hn c i j hj

lemma cup2TpPreserving_local_eqs (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n)
    (htp : cup2TpPreservingMove n hn c i) :
    localExp2After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) =
      localExp2Before n i (c (left i)).1 (c i).1 (c (right i)).1 ∧
    localInt21After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) =
      localInt21Before n i (c (left i)).1 (c i).1 (c (right i)).1 ∧
    localExp2WeightAfter n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) =
      localExp2WeightBefore n i (c (left i)).1 (c i).1 (c (right i)).1 := by
  have hExp2Totals : cup2Exp2Count n hn (move (cup2System n hn) c i) = cup2Exp2Count n hn c := by
    exact congrArg Prod.fst htp
  have hRest : (cup2Int21Count n hn (move (cup2System n hn) c i), cup2Exp2Weight n hn (move (cup2System n hn) c i)) =
      (cup2Int21Count n hn c, cup2Exp2Weight n hn c) := by
    exact congrArg Prod.snd htp
  have hInt21Totals : cup2Int21Count n hn (move (cup2System n hn) c i) = cup2Int21Count n hn c := by
    exact congrArg Prod.fst hRest
  have hWeightTotals : cup2Exp2Weight n hn (move (cup2System n hn) c i) = cup2Exp2Weight n hn c := by
    exact congrArg Prod.snd hRest
  constructor
  · rw [cup2Exp2_move_split n hn c i, cup2Exp2_split n hn c i, cup2Exp2_rest_move_eq n hn c i] at hExp2Totals
    omega
  constructor
  · rw [cup2Int21_move_split n hn c i, cup2Int21_split n hn c i, cup2Int21_rest_move_eq n hn c i] at hInt21Totals
    omega
  · rw [cup2Exp2Weight_move_split n hn c i, cup2Exp2Weight_split n hn c i,
      cup2Exp2Weight_rest_move_eq n hn c i] at hWeightTotals
    omega

lemma cup2Exp2BitVal_eq_zero_of_lt_two (n j a b : Nat) (hj : j < 2) :
    cup2Exp2BitVal n j a b = 0 := by
  unfold cup2Exp2BitVal
  simp [Nat.not_le_of_lt hj]

lemma cup2Exp2BitVal_eq_zero_of_ge_top (n j a b : Nat) (hj : n ≤ j + 2) :
    cup2Exp2BitVal n j a b = 0 := by
  unfold cup2Exp2BitVal
  simp [not_lt_of_ge hj]

lemma cup2Exp2BitVal_eq_inner (n j a b : Nat) (hj0 : 2 ≤ j) (hj1 : j + 2 < n) :
    cup2Exp2BitVal n j a b = if a = 2 ∧ b ≠ 2 then 1 else 0 := by
  unfold cup2Exp2BitVal
  simp [hj0, hj1]

lemma localExp2High_le (L S : Fin 3) (R : Fin 2) :
    (if L.1 = 2 ∧ THighVal L.1 S.1 R.1 ≠ 2 then 1 else 0) ≤
      (if L.1 = 2 ∧ S.1 ≠ 2 then 1 else 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;> decide

lemma localExp2Mid_inner_le (L S R : Fin 3) :
    (if L.1 = 2 ∧ TMidVal L.1 S.1 R.1 ≠ 2 then 1 else 0) +
        (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) ≤
      (if L.1 = 2 ∧ S.1 ≠ 2 then 1 else 0) +
        (if S.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;> decide

lemma localInt21High_le (L S : Fin 3) (R : Fin 2) :
    (if L.1 = 2 ∧ THighVal L.1 S.1 R.1 = 1 then 1 else 0) ≤
      (if L.1 = 2 ∧ S.1 = 1 then 1 else 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;> decide

lemma localInt21Mid_inner_le (L S R : Fin 3) :
    (if L.1 = 2 ∧ TMidVal L.1 S.1 R.1 = 1 then 1 else 0) +
        (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 = 1 then 1 else 0) ≤
      (if L.1 = 2 ∧ S.1 = 1 then 1 else 0) +
        (if S.1 = 2 ∧ R.1 = 1 then 1 else 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;> decide

lemma localExp2WeightHigh_le (w : Nat) (L S : Fin 3) (R : Fin 2) :
    w * (if L.1 = 2 ∧ THighVal L.1 S.1 R.1 ≠ 2 then 1 else 0) ≤
      w * (if L.1 = 2 ∧ S.1 ≠ 2 then 1 else 0) := by
  exact Nat.mul_le_mul_left w (localExp2High_le L S R)

-- Int21 analogues of the Exp2 position lemmas
lemma cup2Int21BitVal_eq_zero_of_lt_two (n j a b : Nat) (hj : j < 2) :
    cup2Int21BitVal n j a b = 0 := by
  unfold cup2Int21BitVal; simp [Nat.not_le_of_lt hj]

lemma cup2Int21BitVal_eq_zero_of_ge_top (n j a b : Nat) (hj : n ≤ j + 2) :
    cup2Int21BitVal n j a b = 0 := by
  unfold cup2Int21BitVal; simp [not_lt_of_ge hj]

lemma cup2Int21BitVal_eq_inner (n j a b : Nat) (hj0 : 2 ≤ j) (hj1 : j + 2 < n) :
    cup2Int21BitVal n j a b = if a = 2 ∧ b = 1 then 1 else 0 := by
  unfold cup2Int21BitVal; simp [hj0, hj1]

lemma localExp2Mid_right_only_le (L S R : Fin 3) :
    (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) ≤
      (if S.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;> native_decide

lemma localInt21Mid_right_only_le (L S R : Fin 3) :
    (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 = 1 then 1 else 0) ≤
      (if S.1 = 2 ∧ R.1 = 1 then 1 else 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;> native_decide

lemma localExp2WeightMid_inner_le_param (w : Nat) (L S R : Fin 3) :
    w * (if L.1 = 2 ∧ TMidVal L.1 S.1 R.1 ≠ 2 then 1 else 0) +
    (w + 1) * (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) ≤
    w * (if L.1 = 2 ∧ S.1 ≠ 2 then 1 else 0) +
    (w + 1) * (if S.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) := by
  set la := (if L.1 = 2 ∧ TMidVal L.1 S.1 R.1 ≠ 2 then 1 else (0 : Nat))
  set lb := (if L.1 = 2 ∧ S.1 ≠ 2 then 1 else (0 : Nat))
  set ra := (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 ≠ 2 then 1 else (0 : Nat))
  set rb := (if S.1 = 2 ∧ R.1 ≠ 2 then 1 else (0 : Nat))
  have hl : la ≤ lb ∨ (la = lb + 1 ∧ ra + 1 ≤ rb) := by
    fin_cases L <;> fin_cases S <;> fin_cases R <;> native_decide
  rcases hl with hle | ⟨hla, hra⟩
  · exact Nat.add_le_add (Nat.mul_le_mul_left w hle)
      (Nat.mul_le_mul_left (w + 1) (localExp2Mid_right_only_le L S R))
  · calc w * la + (w + 1) * ra
        = w * (lb + 1) + (w + 1) * ra := by rw [hla]
      _ = w * lb + w + (w + 1) * ra := by ring
      _ ≤ w * lb + (w + 1) + (w + 1) * ra := by omega
      _ = w * lb + (w + 1) * (ra + 1) := by ring
      _ ≤ w * lb + (w + 1) * rb := Nat.add_le_add_left (Nat.mul_le_mul_left _ hra) _

lemma localExp2WeightMid_right_only_le (w : Nat) (L S R : Fin 3) :
    w * (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) ≤
      w * (if S.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) := by
  exact Nat.mul_le_mul_left w (localExp2Mid_right_only_le L S R)

def cup2TpBase (n : Nat) : Nat :=
  n * n + 1

def cup2TpCodeOf (n exp2 i21 weight : Nat) : Nat :=
  (exp2 * cup2TpBase n + i21) * cup2TpBase n + weight

def cup2TpCode (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat :=
  cup2TpCodeOf n
    (cup2Exp2Count n hn c)
    (cup2Int21Count n hn c)
    (cup2Exp2Weight n hn c)

def localTpCodeBefore (n : Nat) (i : Fin n) (L S R : Nat) : Nat :=
  cup2TpCodeOf n
    (localExp2Before n i L S R)
    (localInt21Before n i L S R)
    (localExp2WeightBefore n i L S R)

def localTpCodeAfter (n : Nat) (i : Fin n) (L S R out : Nat) : Nat :=
  cup2TpCodeOf n
    (localExp2After n i L S R out)
    (localInt21After n i L S R out)
    (localExp2WeightAfter n i L S R out)

lemma cup2Exp2Term_le_one (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (j : Fin n) :
    cup2Exp2Term n hn c j ≤ 1 := by
  unfold cup2Exp2Term cup2Exp2BitVal
  split_ifs <;> omega

lemma cup2Int21Term_le_one (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (j : Fin n) :
    cup2Int21Term n hn c j ≤ 1 := by
  unfold cup2Int21Term cup2Int21BitVal
  split_ifs <;> omega

lemma cup2Exp2WeightTerm_le_n (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (j : Fin n) :
    cup2Exp2WeightTerm n hn c j ≤ n := by
  unfold cup2Exp2WeightTerm cup2Exp2Term cup2Exp2BitVal
  split_ifs <;> omega

lemma cup2Exp2Count_le_n (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Exp2Count n hn c ≤ n := by
  unfold cup2Exp2Count
  calc
    ∑ j : Fin n, cup2Exp2Term n hn c j ≤ ∑ j : Fin n, 1 := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact cup2Exp2Term_le_one n hn c j
    _ = n := by simp

lemma cup2Int21Count_le_n (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Int21Count n hn c ≤ n := by
  unfold cup2Int21Count
  calc
    ∑ j : Fin n, cup2Int21Term n hn c j ≤ ∑ j : Fin n, 1 := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact cup2Int21Term_le_one n hn c j
    _ = n := by simp

lemma cup2Exp2Weight_le_sq (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Exp2Weight n hn c ≤ n * n := by
  unfold cup2Exp2Weight
  calc
    ∑ j : Fin n, cup2Exp2WeightTerm n hn c j ≤ ∑ _j : Fin n, n := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact cup2Exp2WeightTerm_le_n n hn c j
    _ = n * n := by simp

lemma cup2Exp2Count_lt_base (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Exp2Count n hn c < cup2TpBase n := by
  have hle := cup2Exp2Count_le_n n hn c
  have hn1 : 1 ≤ n := by omega
  unfold cup2TpBase
  nlinarith

lemma cup2Int21Count_lt_base (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Int21Count n hn c < cup2TpBase n := by
  have hle := cup2Int21Count_le_n n hn c
  have hn1 : 1 ≤ n := by omega
  unfold cup2TpBase
  nlinarith

lemma cup2Exp2Weight_lt_base (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Exp2Weight n hn c < cup2TpBase n := by
  have hle := cup2Exp2Weight_le_sq n hn c
  unfold cup2TpBase
  omega

lemma cup2TpCode_eq_iff (n : Nat)
    {a1 b1 c1 a2 b2 c2 : Nat}
    (hb1 : b1 < cup2TpBase n) (hc1 : c1 < cup2TpBase n)
    (hb2 : b2 < cup2TpBase n) (hc2 : c2 < cup2TpBase n) :
    cup2TpCodeOf n a1 b1 c1 = cup2TpCodeOf n a2 b2 c2 ↔
      a1 = a2 ∧ b1 = b2 ∧ c1 = c2 := by
  constructor
  · intro h
    have hbase : 0 < cup2TpBase n := by
      unfold cup2TpBase
      omega
    have hc1mod : cup2TpCodeOf n a1 b1 c1 % cup2TpBase n = c1 := by
      unfold cup2TpCodeOf
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add]
      simpa [Nat.mod_eq_of_lt hc1]
    have hc2mod : cup2TpCodeOf n a2 b2 c2 % cup2TpBase n = c2 := by
      unfold cup2TpCodeOf
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add]
      simpa [Nat.mod_eq_of_lt hc2]
    have hc : c1 = c2 := by
      rw [← hc1mod, h, hc2mod]
    have hmul :
        (a1 * cup2TpBase n + b1) * cup2TpBase n =
          (a2 * cup2TpBase n + b2) * cup2TpBase n := by
      unfold cup2TpCodeOf at h
      omega
    have hab :
        a1 * cup2TpBase n + b1 = a2 * cup2TpBase n + b2 := by
      exact Nat.mul_right_cancel hbase (by simpa using hmul)
    have hb1mod : (a1 * cup2TpBase n + b1) % cup2TpBase n = b1 := by
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add]
      simpa [Nat.mod_eq_of_lt hb1]
    have hb2mod : (a2 * cup2TpBase n + b2) % cup2TpBase n = b2 := by
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add]
      simpa [Nat.mod_eq_of_lt hb2]
    have hb : b1 = b2 := by
      rw [← hb1mod, hab, hb2mod]
    have ha : a1 = a2 := by
      rw [hb] at hab
      have hmul' : a1 * cup2TpBase n = a2 * cup2TpBase n := by
        omega
      exact Nat.eq_of_mul_eq_mul_right hbase hmul'
    exact ⟨ha, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

lemma cup2TpInvariant_eq_of_code_eq (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hcode : cup2TpCode n hn c' = cup2TpCode n hn c) :
    cup2TpInvariant n hn c' = cup2TpInvariant n hn c := by
  have hiff := cup2TpCode_eq_iff n
    (a1 := cup2Exp2Count n hn c')
    (b1 := cup2Int21Count n hn c')
    (c1 := cup2Exp2Weight n hn c')
    (a2 := cup2Exp2Count n hn c)
    (b2 := cup2Int21Count n hn c)
    (c2 := cup2Exp2Weight n hn c)
    (cup2Int21Count_lt_base n hn c')
    (cup2Exp2Weight_lt_base n hn c')
    (cup2Int21Count_lt_base n hn c)
    (cup2Exp2Weight_lt_base n hn c)
  have htrip :
      cup2Exp2Count n hn c' = cup2Exp2Count n hn c ∧
        cup2Int21Count n hn c' = cup2Int21Count n hn c ∧
        cup2Exp2Weight n hn c' = cup2Exp2Weight n hn c := by
    simpa [cup2TpCode] using (hiff.mp hcode)
  rcases htrip with ⟨h1, h2, h3⟩
  simp [cup2TpInvariant, h1, h2, h3]

-- Note: The old Exp2Count counterexample (TMidVal(2,1,1)=2 at n=5) is now
-- invalid after the liveness fix (TMidVal(2,1,1)=0). With the fix,
-- Exp2Count is non-increasing on ALL bad steps for all n ≥ 5.

end LeanMn
