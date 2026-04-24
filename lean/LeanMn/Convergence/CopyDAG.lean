import LeanMn.Cycle

namespace LeanMn

open scoped BigOperators

def frontierBitVal (a b : Nat) : Nat :=
  if a = b then 0 else 1

def cup2FrontierTypeVal (a b : Nat) : Nat :=
  if a = b then 0 else (b + 3 - a) % 3

def cup2W1 (n j : Nat) : Nat :=
  if j + 1 = n then 0 else if j + 2 = n then 1 else j + 1

def cup2W2 (n j : Nat) : Nat :=
  if j + 1 = n then 0 else if j = 0 then n - 1 else n - 1 - j

def cup2PsiWeightVal (n j a b : Nat) : Nat :=
  if _h : a = b then 0
  else if cup2FrontierTypeVal a b = 1 then cup2W1 n j else cup2W2 n j

def cup2FrontierBit (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (j : Fin n) : Nat :=
  frontierBitVal (c j).1 (c (right j)).1

def cup2PsiTerm (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (j : Fin n) : Nat :=
  cup2PsiWeightVal n j.1 (c j).1 (c (right j)).1

def cup2Fc (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat :=
  ∑ j : Fin n, cup2FrontierBit n hn c j

def cup2Psi (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat :=
  ∑ j : Fin n, cup2PsiTerm n hn c j

lemma left_ne_self {n : Nat} (hn : 2 ≤ n) (i : Fin n) : left i ≠ i := by
  by_cases h0 : i.1 = 0
  · have hleft : (left i).1 = n - 1 := by
      rw [left_val, h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    intro h
    have hval := congrArg Fin.val h
    rw [hleft, h0] at hval
    omega
  · have hleft : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
    intro h
    have hval := congrArg Fin.val h
    rw [hleft] at hval
    omega

lemma left_right {n : Nat} (hn : 2 ≤ n) (i : Fin n) : left (right i) = i := by
  ext
  by_cases htop : i.1 + 1 = n
  · have hright : (right i).1 = 0 := right_val_of_top htop
    have hleft : (left (right i)).1 = n - 1 := by
      rw [left_val, hright, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hleft]
    omega
  · have hright : (right i).1 = i.1 + 1 := right_val_of_not_top htop
    have hright0 : (right i).1 ≠ 0 := by
      rw [hright]
      omega
    have hleft : (left (right i)).1 = (right i).1 - 1 := left_val_of_ne_zero hright0
    rw [hleft, hright]
    omega

lemma right_left {n : Nat} (hn : 2 ≤ n) (i : Fin n) : right (left i) = i := by
  ext
  by_cases h0 : i.1 = 0
  · have hleft : (left i).1 = n - 1 := by
      rw [left_val, h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have htop : (left i).1 + 1 = n := by
      rw [hleft]
      omega
    rw [right_val_of_top (i := left i) htop, h0]
  · have hleft : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
    have htop : (left i).1 + 1 ≠ n := by
      rw [hleft]
      omega
    rw [right_val_of_not_top (i := left i) htop, hleft]
    omega

lemma right_ne_self {n : Nat} (hn : 2 ≤ n) (i : Fin n) : right i ≠ i := by
  intro h
  have h' : i = left i := by
    simpa [left_right hn i] using congrArg left h
  exact left_ne_self hn i h'.symm

@[simp] lemma move_apply_self_val (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    (move (cup2System n hn) c i i).1 =
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 := by
  rw [move]
  simp
  rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
  rw [cup2Trans_val]

@[simp] lemma move_apply_ne (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn))
    (i j : Fin n) (h : j ≠ i) :
    move (cup2System n hn) c i j = c j := by
  simp [move, h]

def adjacentComplement {n : Nat} (i : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase i).erase (left i)

lemma mem_adjacentComplement_iff {n : Nat} (i j : Fin n) :
    j ∈ adjacentComplement i ↔ j ≠ i ∧ j ≠ left i := by
  unfold adjacentComplement
  simp [and_comm]

lemma right_ne_of_mem_adjacentComplement {n : Nat} (hn : 2 ≤ n) (i j : Fin n)
    (hj : j ∈ adjacentComplement i) : right j ≠ i := by
  intro h
  have hj' : j = left i := by
    have := congrArg left h
    simpa [left_right hn j] using this
  exact (mem_adjacentComplement_iff i j).mp hj |>.2 hj'

lemma sum_univ_eq_adjacentComplement {n : Nat} {α : Type*} [AddCommMonoid α]
    (hn : 2 ≤ n) (f : Fin n → α) (i : Fin n) :
    (∑ j : Fin n, f j) = f i + f (left i) + Finset.sum (adjacentComplement i) f := by
  unfold adjacentComplement
  rw [← Finset.add_sum_erase (Finset.univ) f (Finset.mem_univ i)]
  have hleftmem : left i ∈ Finset.univ.erase i := by
    simp [left_ne_self hn i]
  rw [← Finset.add_sum_erase (Finset.univ.erase i) f hleftmem]
  simp [add_left_comm, add_comm]

lemma cup2FrontierBit_move_eq_of_mem_adjacentComplement (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i j : Fin n) (hj : j ∈ adjacentComplement i) :
    cup2FrontierBit n hn (move (cup2System n hn) c i) j = cup2FrontierBit n hn c j := by
  have hn2 : 2 ≤ n := by omega
  have hji : j ≠ i := (mem_adjacentComplement_iff i j).mp hj |>.1
  have hright : right j ≠ i := right_ne_of_mem_adjacentComplement hn2 i j hj
  unfold cup2FrontierBit frontierBitVal
  simp [move, hji, hright]

lemma cup2PsiTerm_move_eq_of_mem_adjacentComplement (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i j : Fin n) (hj : j ∈ adjacentComplement i) :
    cup2PsiTerm n hn (move (cup2System n hn) c i) j = cup2PsiTerm n hn c j := by
  have hn2 : 2 ≤ n := by omega
  have hji : j ≠ i := (mem_adjacentComplement_iff i j).mp hj |>.1
  have hright : right j ≠ i := right_ne_of_mem_adjacentComplement hn2 i j hj
  unfold cup2PsiTerm cup2PsiWeightVal cup2FrontierTypeVal
  simp [move, hji, hright]

def localFcBefore (L S R : Nat) : Nat :=
  frontierBitVal L S + frontierBitVal S R

def localFcAfter (L _S R out : Nat) : Nat :=
  frontierBitVal L out + frontierBitVal out R

def localPsiBefore (n : Nat) (i : Fin n) (L S R : Nat) : Nat :=
  cup2PsiWeightVal n (left i).1 L S + cup2PsiWeightVal n i.1 S R

def localPsiAfter (n : Nat) (i : Fin n) (L _S R out : Nat) : Nat :=
  cup2PsiWeightVal n (left i).1 L out + cup2PsiWeightVal n i.1 out R

lemma cup2W1_last (n : Nat) (hn : 1 ≤ n) : cup2W1 n (n - 1) = 0 := by
  unfold cup2W1
  rw [Nat.sub_add_cancel hn]
  simp

lemma cup2W1_zero (n : Nat) (hn : 2 ≤ n) : cup2W1 n 0 = 1 := by
  have h1 : 1 ≠ n := by omega
  unfold cup2W1
  simp [h1]

lemma cup2W1_one (n : Nat) (hn : 4 ≤ n) : cup2W1 n 1 = 2 := by
  have h2 : 2 ≠ n := by omega
  have h3 : 3 ≠ n := by omega
  unfold cup2W1
  simp [h2, h3]

lemma cup2W1_n3 (n : Nat) (hn : 4 ≤ n) : cup2W1 n (n - 3) = n - 2 := by
  have hn1 : 1 ≤ n := by omega
  have h1 : n - 3 + 1 ≠ n := by omega
  have h2 : n - 3 + 2 ≠ n := by omega
  unfold cup2W1
  simp [h1, h2]
  omega

lemma cup2W1_n2 (n : Nat) (hn : 2 ≤ n) : cup2W1 n (n - 2) = 1 := by
  have h1 : n - 2 + 1 ≠ n := by omega
  have h2 : n - 2 + 2 = n := by omega
  unfold cup2W1
  simp [h1, h2]

lemma cup2W1_of_mid (n j : Nat) (hj : j + 2 < n) : cup2W1 n j = j + 1 := by
  have h1 : j + 1 ≠ n := by omega
  have h2 : j + 2 ≠ n := by omega
  unfold cup2W1
  simp [h1, h2]

lemma cup2W1_of_lt_last (n j : Nat) (hj : j + 1 < n) : 0 < cup2W1 n j := by
  unfold cup2W1
  have h1 : j + 1 ≠ n := by omega
  simp [h1]
  split_ifs <;> omega

lemma cup2W2_last (n : Nat) (hn : 1 ≤ n) : cup2W2 n (n - 1) = 0 := by
  unfold cup2W2
  rw [Nat.sub_add_cancel hn]
  simp

lemma cup2W2_zero (n : Nat) (hn : 2 ≤ n) : cup2W2 n 0 = n - 1 := by
  have h1 : 1 ≠ n := by omega
  unfold cup2W2
  simp [h1]

lemma cup2W2_one (n : Nat) (hn : 4 ≤ n) : cup2W2 n 1 = n - 2 := by
  have h2 : 2 ≠ n := by omega
  unfold cup2W2
  simp [h2]
  omega

lemma cup2W2_n3 (n : Nat) (hn : 4 ≤ n) : cup2W2 n (n - 3) = 2 := by
  have h1 : n - 3 + 1 ≠ n := by omega
  have h0 : n - 3 ≠ 0 := by omega
  unfold cup2W2
  simp [h1, h0]
  omega

lemma cup2W2_n2 (n : Nat) (hn : 3 ≤ n) : cup2W2 n (n - 2) = 1 := by
  have h1 : n - 2 + 1 ≠ n := by omega
  have h0 : n - 2 ≠ 0 := by omega
  unfold cup2W2
  simp [h1, h0]
  omega

lemma cup2W2_of_mid (n j : Nat) (hj0 : j ≠ 0) (hj : j + 1 < n) :
    cup2W2 n j = n - 1 - j := by
  have h1 : j + 1 ≠ n := by omega
  unfold cup2W2
  simp [h1, hj0]

lemma cup2W2_pos_of_lt_last (n j : Nat) (hj : j + 1 < n) : 0 < cup2W2 n j := by
  by_cases hj0 : j = 0
  · subst hj0
    simpa [cup2W2_zero n (by omega)] using (show 0 < n - 1 by omega)
  · rw [cup2W2_of_mid n j hj0 hj]
    omega

lemma cup2Fc_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Fc n hn c =
      localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 +
        Finset.sum (adjacentComplement i) (cup2FrontierBit n hn c) := by
  have hn2 : 2 ≤ n := by omega
  rw [cup2Fc, sum_univ_eq_adjacentComplement hn2 (cup2FrontierBit n hn c) i]
  unfold localFcBefore cup2FrontierBit frontierBitVal
  rw [right_left hn2 i]
  ac_rfl

lemma cup2Psi_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Psi n hn c =
      localPsiBefore n i (c (left i)).1 (c i).1 (c (right i)).1 +
        Finset.sum (adjacentComplement i) (cup2PsiTerm n hn c) := by
  have hn2 : 2 ≤ n := by omega
  rw [cup2Psi, sum_univ_eq_adjacentComplement hn2 (cup2PsiTerm n hn c) i]
  unfold localPsiBefore cup2PsiTerm
  rw [right_left hn2 i]
  ac_rfl

lemma cup2Fc_move_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Fc n hn (move (cup2System n hn) c i) =
      localFcAfter (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) +
          Finset.sum (adjacentComplement i)
            (cup2FrontierBit n hn (move (cup2System n hn) c i)) := by
  have hn2 : 2 ≤ n := by omega
  have hout :
      ((cup2System n hn).f i (c (left i)) (c i) (c (right i))).1 =
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 := by
    rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
    rw [cup2Trans_val]
  rw [cup2Fc,
    sum_univ_eq_adjacentComplement hn2
      (fun j => cup2FrontierBit n hn (move (cup2System n hn) c i) j) i]
  unfold localFcAfter cup2FrontierBit frontierBitVal
  simp [move,
    left_ne_self hn2 i, right_ne_self hn2 i, right_left hn2 i]
  rw [hout]
  ac_rfl

lemma cup2Psi_move_split (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Psi n hn (move (cup2System n hn) c i) =
      localPsiAfter n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) +
          Finset.sum (adjacentComplement i)
            (cup2PsiTerm n hn (move (cup2System n hn) c i)) := by
  have hn2 : 2 ≤ n := by omega
  have hout :
      ((cup2System n hn).f i (c (left i)) (c i) (c (right i))).1 =
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 := by
    rw [show (cup2System n hn).f = cup2Trans n hn by rfl]
    rw [cup2Trans_val]
  rw [cup2Psi,
    sum_univ_eq_adjacentComplement hn2
      (fun j => cup2PsiTerm n hn (move (cup2System n hn) c i) j) i]
  unfold localPsiAfter cup2PsiTerm
  simp [move,
    left_ne_self hn2 i, right_ne_self hn2 i, right_left hn2 i]
  rw [hout]
  ac_rfl

lemma cup2Fc_rest_move_eq (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    Finset.sum (adjacentComplement i) (cup2FrontierBit n hn (move (cup2System n hn) c i)) =
      Finset.sum (adjacentComplement i) (cup2FrontierBit n hn c) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact cup2FrontierBit_move_eq_of_mem_adjacentComplement n hn c i j hj

lemma cup2Psi_rest_move_eq (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n) :
    Finset.sum (adjacentComplement i) (cup2PsiTerm n hn (move (cup2System n hn) c i)) =
      Finset.sum (adjacentComplement i) (cup2PsiTerm n hn c) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact cup2PsiTerm_move_eq_of_mem_adjacentComplement n hn c i j hj

def cup2BadStepNonneg (n : Nat) (hn : 4 ≤ n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  badStep (cup2System n hn) (cup2GoodCycle n hn) c' c ∧ cup2Fc n hn c ≤ cup2Fc n hn c'

lemma localFcAfter_le_of_copyLeft (L S R : Nat) :
    localFcAfter L S R L ≤ localFcBefore L S R := by
  unfold localFcAfter localFcBefore frontierBitVal
  by_cases hLS : L = S <;> by_cases hSR : S = R <;> by_cases hLR : L = R <;>
    simp [hLS, hSR, hLR]

lemma localFcAfter_le_of_copyRight (L S R : Nat) :
    localFcAfter L S R R ≤ localFcBefore L S R := by
  unfold localFcAfter localFcBefore frontierBitVal
  by_cases hLS : L = S <;> by_cases hSR : S = R <;> by_cases hLR : L = R <;>
    simp [hLS, hSR, hLR]

lemma localFcAfter_le_of_copyNeighbor (L S R out : Nat)
    (hcopy : out = L ∨ out = R) :
    localFcAfter L S R out ≤ localFcBefore L S R := by
  rcases hcopy with h | h
  · simpa [h] using localFcAfter_le_of_copyLeft L S R
  · simpa [h] using localFcAfter_le_of_copyRight L S R

lemma localFc_delta_bounds (L S R out : Nat) :
    localFcAfter L S R out + 2 ≥ localFcBefore L S R ∧
      localFcAfter L S R out ≤ localFcBefore L S R + 2 := by
  have hbefore : localFcBefore L S R ≤ 2 := by
    unfold localFcBefore frontierBitVal
    split_ifs <;> omega
  have hafter : localFcAfter L S R out ≤ 2 := by
    unfold localFcAfter frontierBitVal
    split_ifs <;> omega
  constructor <;> omega

lemma cup2Fc_move_delta_bounds (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n) :
    cup2Fc n hn (move (cup2System n hn) c i) + 2 ≥ cup2Fc n hn c ∧
      cup2Fc n hn (move (cup2System n hn) c i) ≤ cup2Fc n hn c + 2 := by
  rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i]
  have hlocal := localFc_delta_bounds (c (left i)).1 (c i).1 (c (right i)).1
    (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1)
  omega

theorem cup2Step_fc_delta_bounds (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hstep : step (cup2System n hn) c c') :
    cup2Fc n hn c' + 2 ≥ cup2Fc n hn c ∧
      cup2Fc n hn c' ≤ cup2Fc n hn c + 2 := by
  rcases hstep with ⟨i, _hpriv, rfl⟩
  exact cup2Fc_move_delta_bounds n hn c i

lemma bot_zero_cases (L : Fin 2) (S : Fin 2) (R : Fin 3)
    (hfc : localFcAfter L.1 S.1 R.1 (TBotVal L.1 S.1 R.1) = localFcBefore L.1 S.1 R.1)
    (hpriv : TBotVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 0 ∧ R.1 = 1) ∨ (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TBotVal] at hfc hpriv ⊢

lemma low_zero_cases (L : Fin 2) (S : Fin 3) (R : Fin 3)
    (hfc : localFcAfter L.1 S.1 R.1 (TLowVal L.1 S.1 R.1) = localFcBefore L.1 S.1 R.1)
    (hpriv : TLowVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 2 ∧ R.1 = 2) ∨
      (L.1 = 1 ∧ S.1 = 0 ∧ R.1 = 0) ∨
      (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 2) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TLowVal] at hfc hpriv ⊢

lemma mid_zero_cases (L S R : Fin 3)
    (hfc : localFcAfter L.1 S.1 R.1 (TMidVal L.1 S.1 R.1) = localFcBefore L.1 S.1 R.1)
    (hpriv : TMidVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 2 ∧ R.1 = 2) ∨
      (L.1 = 1 ∧ S.1 = 0 ∧ R.1 = 0) ∨
      (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 2) ∨
      (L.1 = 2 ∧ S.1 = 1 ∧ R.1 = 1) ∨
      (L.1 = 2 ∧ S.1 = 2 ∧ R.1 = 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal] at hfc hpriv ⊢

lemma high_zero_cases (L S : Fin 3) (R : Fin 2)
    (hfc : localFcAfter L.1 S.1 R.1 (THighVal L.1 S.1 R.1) = localFcBefore L.1 S.1 R.1)
    (hpriv : THighVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 1 ∧ R.1 = 1) ∨
      (L.1 = 1 ∧ S.1 = 0 ∧ R.1 = 0) ∨
      (L.1 = 2 ∧ S.1 = 1 ∧ R.1 = 1) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, THighVal] at hfc hpriv ⊢

lemma top_zero_cases (L : Fin 3) (S R : Fin 2)
    (hfc : localFcAfter L.1 S.1 R.1 (TTopVal L.1 S.1 R.1) = localFcBefore L.1 S.1 R.1)
    (hpriv : TTopVal L.1 S.1 R.1 ≠ S.1) :
    L.1 = 0 ∧ S.1 = 1 ∧ R.1 = 1 := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TTopVal] at hfc hpriv ⊢

lemma bot_localPsi_001 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h0 : i.1 = 0) :
    localPsiAfter n i 0 0 1 (TBotVal 0 0 1) < localPsiBefore n i 0 0 1 := by
  have hleft : (left i).1 = n - 1 := by
    rw [left_val, h0, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hw1last : cup2W1 n (n - 1) = 0 := cup2W1_last n (by omega)
  have hw1zero : cup2W1 n 0 = 1 := cup2W1_zero n (by omega)
  unfold localPsiAfter localPsiBefore
  rw [hleft, h0]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TBotVal, hw1last, hw1zero]

lemma bot_localPsi_110 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h0 : i.1 = 0) :
    localPsiAfter n i 1 1 0 (TBotVal 1 1 0) < localPsiBefore n i 1 1 0 := by
  have hleft : (left i).1 = n - 1 := by
    rw [left_val, h0, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hw2last : cup2W2 n (n - 1) = 0 := cup2W2_last n (by omega)
  unfold localPsiAfter localPsiBefore
  rw [hleft, h0]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TBotVal, hw2last]
  have hw20 : cup2W2 n 0 = n - 1 := cup2W2_zero n (by omega)
  rw [hw20]
  omega

lemma zero_delta_local_psi_lt_bot (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h0 : i.1 = 0)
    {L S R : Nat} (hL : L < 2) (hS : S < 2) (hR : R < 3)
    (hfc : localFcAfter L S R (TBotVal L S R) = localFcBefore L S R)
    (hpriv : TBotVal L S R ≠ S) :
    localPsiAfter n i L S R (TBotVal L S R) < localPsiBefore n i L S R := by
  let LF : Fin 2 := ⟨L, hL⟩
  let SF : Fin 2 := ⟨S, hS⟩
  let RF : Fin 3 := ⟨R, hR⟩
  rcases bot_zero_cases LF SF RF hfc hpriv with hcase | hcase
  · rcases hcase with ⟨hL0, hS0, hR1⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    exact bot_localPsi_001 n hn i h0
  · rcases hcase with ⟨hL1, hS1, hR0⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    exact bot_localPsi_110 n hn i h0

lemma low_localPsi_022 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h1 : i.1 = 1) :
    localPsiAfter n i 0 2 2 (TLowVal 0 2 2) < localPsiBefore n i 0 2 2 := by
  have hleft : (left i).1 = 0 := by
    rw [left_val_of_ne_zero (i := i) (by omega), h1]
  have hw20 : cup2W2 n 0 = n - 1 := cup2W2_zero n (by omega)
  have hw21 : cup2W2 n 1 = n - 2 := cup2W2_one n hn
  unfold localPsiAfter localPsiBefore
  rw [hleft, h1]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TLowVal, hw20, hw21]
  omega

lemma low_localPsi_100 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h1 : i.1 = 1) :
    localPsiAfter n i 1 0 0 (TLowVal 1 0 0) < localPsiBefore n i 1 0 0 := by
  have hleft : (left i).1 = 0 := by
    rw [left_val_of_ne_zero (i := i) (by omega), h1]
  have hw20 : cup2W2 n 0 = n - 1 := cup2W2_zero n (by omega)
  have hw21 : cup2W2 n 1 = n - 2 := cup2W2_one n hn
  unfold localPsiAfter localPsiBefore
  rw [hleft, h1]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TLowVal, hw20, hw21]
  omega

lemma low_localPsi_112 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h1 : i.1 = 1) :
    localPsiAfter n i 1 1 2 (TLowVal 1 1 2) < localPsiBefore n i 1 1 2 := by
  have hleft : (left i).1 = 0 := by
    rw [left_val_of_ne_zero (i := i) (by omega), h1]
  have hw10 : cup2W1 n 0 = 1 := cup2W1_zero n (by omega)
  have hw11 : cup2W1 n 1 = 2 := cup2W1_one n hn
  unfold localPsiAfter localPsiBefore
  rw [hleft, h1]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TLowVal, hw10, hw11]

lemma zero_delta_local_psi_lt_low (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h1 : i.1 = 1)
    {L S R : Nat} (hL : L < 2) (hS : S < 3) (hR : R < 3)
    (hfc : localFcAfter L S R (TLowVal L S R) = localFcBefore L S R)
    (hpriv : TLowVal L S R ≠ S) :
    localPsiAfter n i L S R (TLowVal L S R) < localPsiBefore n i L S R := by
  let LF : Fin 2 := ⟨L, hL⟩
  let SF : Fin 3 := ⟨S, hS⟩
  let RF : Fin 3 := ⟨R, hR⟩
  rcases low_zero_cases LF SF RF hfc hpriv with hcase | hcase | hcase
  · rcases hcase with ⟨hL0, hS2, hR2⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 2 := by simpa [SF] using hS2
    have hR' : R = 2 := by simpa [RF] using hR2
    subst L S R
    exact low_localPsi_022 n hn i h1
  · rcases hcase with ⟨hL1, hS0, hR0⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    exact low_localPsi_100 n hn i h1
  · rcases hcase with ⟨hL1, hS1, hR2⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 2 := by simpa [RF] using hR2
    subst L S R
    exact low_localPsi_112 n hn i h1

lemma high_localPsi_011 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (hhigh : i.1 + 2 = n) :
    localPsiAfter n i 0 1 1 (THighVal 0 1 1) < localPsiBefore n i 0 1 1 := by
  have hleft : (left i).1 = n - 3 := by
    rw [left_val_of_ne_zero (i := i) (by omega)]
    omega
  have hself : i.1 = n - 2 := by omega
  have hw1n3 : cup2W1 n (n - 3) = n - 2 := cup2W1_n3 n hn
  have hw1n2 : cup2W1 n (n - 2) = 1 := cup2W1_n2 n (by omega)
  unfold localPsiAfter localPsiBefore
  rw [hleft, hself]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, THighVal, hw1n3, hw1n2]
  omega

lemma high_localPsi_100 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (hhigh : i.1 + 2 = n) :
    localPsiAfter n i 1 0 0 (THighVal 1 0 0) < localPsiBefore n i 1 0 0 := by
  have hleft : (left i).1 = n - 3 := by
    rw [left_val_of_ne_zero (i := i) (by omega)]
    omega
  have hself : i.1 = n - 2 := by omega
  have hw2n3 : cup2W2 n (n - 3) = 2 := cup2W2_n3 n hn
  have hw2n2 : cup2W2 n (n - 2) = 1 := cup2W2_n2 n (by omega)
  unfold localPsiAfter localPsiBefore
  rw [hleft, hself]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, THighVal, hw2n3, hw2n2]

lemma high_localPsi_211 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (hhigh : i.1 + 2 = n) :
    localPsiAfter n i 2 1 1 (THighVal 2 1 1) < localPsiBefore n i 2 1 1 := by
  have hleft : (left i).1 = n - 3 := by
    rw [left_val_of_ne_zero (i := i) (by omega)]
    omega
  have hself : i.1 = n - 2 := by omega
  have hw2n3 : cup2W2 n (n - 3) = 2 := cup2W2_n3 n hn
  have hw2n2 : cup2W2 n (n - 2) = 1 := cup2W2_n2 n (by omega)
  unfold localPsiAfter localPsiBefore
  rw [hleft, hself]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, THighVal, hw2n3, hw2n2]

lemma zero_delta_local_psi_lt_high (n : Nat) (hn : 4 ≤ n) (i : Fin n) (hhigh : i.1 + 2 = n)
    {L S R : Nat} (hL : L < 3) (hS : S < 3) (hR : R < 2)
    (hfc : localFcAfter L S R (THighVal L S R) = localFcBefore L S R)
    (hpriv : THighVal L S R ≠ S) :
    localPsiAfter n i L S R (THighVal L S R) < localPsiBefore n i L S R := by
  let LF : Fin 3 := ⟨L, hL⟩
  let SF : Fin 3 := ⟨S, hS⟩
  let RF : Fin 2 := ⟨R, hR⟩
  rcases high_zero_cases LF SF RF hfc hpriv with hcase | hcase | hcase
  · rcases hcase with ⟨hL0, hS1, hR1⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    exact high_localPsi_011 n hn i hhigh
  · rcases hcase with ⟨hL1, hS0, hR0⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    exact high_localPsi_100 n hn i hhigh
  · rcases hcase with ⟨hL2, hS1, hR1⟩
    have hL' : L = 2 := by simpa [LF] using hL2
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    exact high_localPsi_211 n hn i hhigh

lemma top_localPsi_011 (n : Nat) (hn : 4 ≤ n) (i : Fin n) (htop : i.1 + 1 = n) :
    localPsiAfter n i 0 1 1 (TTopVal 0 1 1) < localPsiBefore n i 0 1 1 := by
  have hleft : (left i).1 = n - 2 := by
    rw [left_val_of_ne_zero (i := i) (by omega)]
    omega
  have hself : i.1 = n - 1 := by omega
  have hw1n2 : cup2W1 n (n - 2) = 1 := cup2W1_n2 n (by omega)
  have hw1last : cup2W1 n (n - 1) = 0 := cup2W1_last n (by omega)
  unfold localPsiAfter localPsiBefore
  rw [hleft, hself]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TTopVal, hw1n2, hw1last]

lemma zero_delta_local_psi_lt_top (n : Nat) (hn : 4 ≤ n) (i : Fin n) (htop : i.1 + 1 = n)
    {L S R : Nat} (hL : L < 3) (hS : S < 2) (hR : R < 2)
    (hfc : localFcAfter L S R (TTopVal L S R) = localFcBefore L S R)
    (hpriv : TTopVal L S R ≠ S) :
    localPsiAfter n i L S R (TTopVal L S R) < localPsiBefore n i L S R := by
  let LF : Fin 3 := ⟨L, hL⟩
  let SF : Fin 2 := ⟨S, hS⟩
  let RF : Fin 2 := ⟨R, hR⟩
  rcases top_zero_cases LF SF RF hfc hpriv with ⟨hL0, hS1, hR1⟩
  have hL' : L = 0 := by simpa [LF] using hL0
  have hS' : S = 1 := by simpa [SF] using hS1
  have hR' : R = 1 := by simpa [RF] using hR1
  subst L S R
  exact top_localPsi_011 n hn i htop

lemma mid_localPsi_022 (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (h0 : i.1 ≠ 0) (h1 : i.1 ≠ 1) (htop : i.1 + 1 ≠ n) (hhigh : i.1 + 2 ≠ n) :
    localPsiAfter n i 0 2 2 (TMidVal 0 2 2) < localPsiBefore n i 0 2 2 := by
  have hleft : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  have hselflt : i.1 + 1 < n := by omega
  have hw2self : cup2W2 n i.1 = n - 1 - i.1 := cup2W2_of_mid n i.1 h0 hselflt
  have hleft0 : (left i).1 ≠ 0 := by rw [hleft]; omega
  have hleftlt : (left i).1 + 1 < n := by rw [hleft]; omega
  have hw2left : cup2W2 n (left i).1 = n - i.1 := by
    rw [cup2W2_of_mid n (left i).1 hleft0 hleftlt, hleft]
    omega
  have hw2left' : cup2W2 n (i.1 - 1) = n - i.1 := by
    rw [← hleft]
    exact hw2left
  unfold localPsiAfter localPsiBefore
  rw [hleft]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TMidVal]
  rw [hw2self, hw2left']
  omega

lemma mid_localPsi_100 (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (h0 : i.1 ≠ 0) (h1 : i.1 ≠ 1) (htop : i.1 + 1 ≠ n) (hhigh : i.1 + 2 ≠ n) :
    localPsiAfter n i 1 0 0 (TMidVal 1 0 0) < localPsiBefore n i 1 0 0 := by
  have hleft : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  have hselflt : i.1 + 1 < n := by omega
  have hw2self : cup2W2 n i.1 = n - 1 - i.1 := cup2W2_of_mid n i.1 h0 hselflt
  have hleft0 : (left i).1 ≠ 0 := by rw [hleft]; omega
  have hleftlt : (left i).1 + 1 < n := by rw [hleft]; omega
  have hw2left : cup2W2 n (left i).1 = n - i.1 := by
    rw [cup2W2_of_mid n (left i).1 hleft0 hleftlt, hleft]
    omega
  have hw2left' : cup2W2 n (i.1 - 1) = n - i.1 := by
    rw [← hleft]
    exact hw2left
  unfold localPsiAfter localPsiBefore
  rw [hleft]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TMidVal]
  rw [hw2self, hw2left']
  omega

lemma mid_localPsi_112 (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (h0 : i.1 ≠ 0) (h1 : i.1 ≠ 1) (htop : i.1 + 1 ≠ n) (hhigh : i.1 + 2 ≠ n) :
    localPsiAfter n i 1 1 2 (TMidVal 1 1 2) < localPsiBefore n i 1 1 2 := by
  have hleft : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  have hw1self : cup2W1 n i.1 = i.1 + 1 := by
    exact cup2W1_of_mid n i.1 (by omega)
  have hleftmid : (left i).1 + 2 < n := by rw [hleft]; omega
  have hw1left : cup2W1 n (left i).1 = i.1 := by
    rw [cup2W1_of_mid n (left i).1 hleftmid, hleft]
    omega
  have hw1left' : cup2W1 n (i.1 - 1) = i.1 := by
    rw [← hleft]
    exact hw1left
  unfold localPsiAfter localPsiBefore
  rw [hleft]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TMidVal]
  rw [hw1self, hw1left']
  omega

lemma mid_localPsi_220 (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (h0 : i.1 ≠ 0) (h1 : i.1 ≠ 1) (htop : i.1 + 1 ≠ n) (hhigh : i.1 + 2 ≠ n) :
    localPsiAfter n i 2 2 0 (TMidVal 2 2 0) < localPsiBefore n i 2 2 0 := by
  have hleft : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  have hw1self : cup2W1 n i.1 = i.1 + 1 := by
    exact cup2W1_of_mid n i.1 (by omega)
  have hleftmid : (left i).1 + 2 < n := by rw [hleft]; omega
  have hw1left : cup2W1 n (left i).1 = i.1 := by
    rw [cup2W1_of_mid n (left i).1 hleftmid, hleft]
    omega
  have hw1left' : cup2W1 n (i.1 - 1) = i.1 := by
    rw [← hleft]
    exact hw1left
  unfold localPsiAfter localPsiBefore
  rw [hleft]
  simp [cup2PsiWeightVal, cup2FrontierTypeVal, TMidVal]
  rw [hw1self, hw1left']
  omega

lemma bot_nonneg_cases (L : Fin 2) (S : Fin 2) (R : Fin 3)
    (hfc : localFcBefore L.1 S.1 R.1 ≤ localFcAfter L.1 S.1 R.1 (TBotVal L.1 S.1 R.1))
    (hpriv : TBotVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 0 ∧ R.1 = 0) ∨
      (L.1 = 0 ∧ S.1 = 0 ∧ R.1 = 1) ∨
      (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 0) ∨
      (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 2) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TBotVal] at hfc hpriv ⊢

lemma low_nonneg_cases (L : Fin 2) (S : Fin 3) (R : Fin 3)
    (hfc : localFcBefore L.1 S.1 R.1 ≤ localFcAfter L.1 S.1 R.1 (TLowVal L.1 S.1 R.1))
    (hpriv : TLowVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 2 ∧ R.1 = 2) ∨
      (L.1 = 1 ∧ S.1 = 0 ∧ R.1 = 0) ∨
      (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 2) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TLowVal] at hfc hpriv ⊢

lemma mid_nonneg_cases (L S R : Fin 3)
    (hfc : localFcBefore L.1 S.1 R.1 ≤ localFcAfter L.1 S.1 R.1 (TMidVal L.1 S.1 R.1))
    (hpriv : TMidVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 2 ∧ R.1 = 2) ∨
      (L.1 = 1 ∧ S.1 = 0 ∧ R.1 = 0) ∨
      (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 2) ∨
      (L.1 = 2 ∧ S.1 = 1 ∧ R.1 = 1) ∨
      (L.1 = 2 ∧ S.1 = 2 ∧ R.1 = 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal] at hfc hpriv ⊢

lemma high_nonneg_cases (L S : Fin 3) (R : Fin 2)
    (hfc : localFcBefore L.1 S.1 R.1 ≤ localFcAfter L.1 S.1 R.1 (THighVal L.1 S.1 R.1))
    (hpriv : THighVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 1 ∧ R.1 = 1) ∨
      (L.1 = 1 ∧ S.1 = 0 ∧ R.1 = 0) ∨
      (L.1 = 1 ∧ S.1 = 1 ∧ R.1 = 1) ∨
      (L.1 = 2 ∧ S.1 = 1 ∧ R.1 = 1) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, THighVal] at hfc hpriv ⊢

lemma top_nonneg_cases (L : Fin 3) (S R : Fin 2)
    (hfc : localFcBefore L.1 S.1 R.1 ≤ localFcAfter L.1 S.1 R.1 (TTopVal L.1 S.1 R.1))
    (hpriv : TTopVal L.1 S.1 R.1 ≠ S.1) :
    (L.1 = 0 ∧ S.1 = 1 ∧ R.1 = 1) ∨
      (L.1 = 2 ∧ S.1 = 0 ∧ R.1 = 0) := by
  fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp [localFcAfter, localFcBefore, frontierBitVal, TTopVal] at hfc hpriv ⊢

lemma bot_local_nonneg_progress (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h0 : i.1 = 0)
    {L S R : Nat} (hL : L < 2) (hS : S < 2) (hR : R < 3)
    (hfc : localFcBefore L S R ≤ localFcAfter L S R (TBotVal L S R))
    (hpriv : TBotVal L S R ≠ S) :
    localFcBefore L S R < localFcAfter L S R (TBotVal L S R) ∨
      (localFcAfter L S R (TBotVal L S R) = localFcBefore L S R ∧
        localPsiAfter n i L S R (TBotVal L S R) < localPsiBefore n i L S R) := by
  let LF : Fin 2 := ⟨L, hL⟩
  let SF : Fin 2 := ⟨S, hS⟩
  let RF : Fin 3 := ⟨R, hR⟩
  rcases bot_nonneg_cases LF SF RF hfc hpriv with hcase | hcase | hcase | hcase
  · rcases hcase with ⟨hL0, hS0, hR0⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    left
    simp [localFcAfter, localFcBefore, frontierBitVal, TBotVal]
  · rcases hcase with ⟨hL0, hS0, hR1⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TBotVal]
    · exact bot_localPsi_001 n hn i h0
  · rcases hcase with ⟨hL1, hS1, hR0⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TBotVal]
    · exact bot_localPsi_110 n hn i h0
  · rcases hcase with ⟨hL1, hS1, hR2⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 2 := by simpa [RF] using hR2
    subst L S R
    left
    simp [localFcAfter, localFcBefore, frontierBitVal, TBotVal]

lemma low_local_nonneg_progress (n : Nat) (hn : 4 ≤ n) (i : Fin n) (h1 : i.1 = 1)
    {L S R : Nat} (hL : L < 2) (hS : S < 3) (hR : R < 3)
    (hfc : localFcBefore L S R ≤ localFcAfter L S R (TLowVal L S R))
    (hpriv : TLowVal L S R ≠ S) :
    localFcAfter L S R (TLowVal L S R) = localFcBefore L S R ∧
      localPsiAfter n i L S R (TLowVal L S R) < localPsiBefore n i L S R := by
  let LF : Fin 2 := ⟨L, hL⟩
  let SF : Fin 3 := ⟨S, hS⟩
  let RF : Fin 3 := ⟨R, hR⟩
  rcases low_nonneg_cases LF SF RF hfc hpriv with hcase | hcase | hcase
  · rcases hcase with ⟨hL0, hS2, hR2⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 2 := by simpa [SF] using hS2
    have hR' : R = 2 := by simpa [RF] using hR2
    subst L S R
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · exact low_localPsi_022 n hn i h1
  · rcases hcase with ⟨hL1, hS0, hR0⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · exact low_localPsi_100 n hn i h1
  · rcases hcase with ⟨hL1, hS1, hR2⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 2 := by simpa [RF] using hR2
    subst L S R
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · exact low_localPsi_112 n hn i h1

lemma mid_local_nonneg_progress (n : Nat) (hn : 4 ≤ n) (i : Fin n)
    (h0 : i.1 ≠ 0) (h1 : i.1 ≠ 1) (htop : i.1 + 1 ≠ n) (hhigh : i.1 + 2 ≠ n)
    {L S R : Nat} (hL : L < 3) (hS : S < 3) (hR : R < 3)
    (hfc : localFcBefore L S R ≤ localFcAfter L S R (TMidVal L S R))
    (hpriv : TMidVal L S R ≠ S) :
    localFcBefore L S R < localFcAfter L S R (TMidVal L S R) ∨
      (localFcAfter L S R (TMidVal L S R) = localFcBefore L S R ∧
        localPsiAfter n i L S R (TMidVal L S R) < localPsiBefore n i L S R) := by
  let LF : Fin 3 := ⟨L, hL⟩
  let SF : Fin 3 := ⟨S, hS⟩
  let RF : Fin 3 := ⟨R, hR⟩
  rcases mid_nonneg_cases LF SF RF hfc hpriv with hcase | hcase | hcase | hcase | hcase
  · rcases hcase with ⟨hL0, hS2, hR2⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 2 := by simpa [SF] using hS2
    have hR' : R = 2 := by simpa [RF] using hR2
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · exact mid_localPsi_022 n hn i h0 h1 htop hhigh
  · rcases hcase with ⟨hL1, hS0, hR0⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · exact mid_localPsi_100 n hn i h0 h1 htop hhigh
  · rcases hcase with ⟨hL1, hS1, hR2⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 2 := by simpa [RF] using hR2
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · exact mid_localPsi_112 n hn i h0 h1 htop hhigh
  · rcases hcase with ⟨hL2, hS1, hR1⟩
    have hL' : L = 2 := by simpa [LF] using hL2
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    -- TMidVal(2,1,1) = 0 (liveness fix): fc strictly increases (1 < 2)
    left
    simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal]
  · rcases hcase with ⟨hL2, hS2, hR0⟩
    have hL' : L = 2 := by simpa [LF] using hL2
    have hS' : S = 2 := by simpa [SF] using hS2
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · exact mid_localPsi_220 n hn i h0 h1 htop hhigh

lemma high_local_nonneg_progress (n : Nat) (hn : 4 ≤ n) (i : Fin n) (hhigh : i.1 + 2 = n)
    {L S R : Nat} (hL : L < 3) (hS : S < 3) (hR : R < 2)
    (hfc : localFcBefore L S R ≤ localFcAfter L S R (THighVal L S R))
    (hpriv : THighVal L S R ≠ S) :
    localFcBefore L S R < localFcAfter L S R (THighVal L S R) ∨
      (localFcAfter L S R (THighVal L S R) = localFcBefore L S R ∧
        localPsiAfter n i L S R (THighVal L S R) < localPsiBefore n i L S R) := by
  let LF : Fin 3 := ⟨L, hL⟩
  let SF : Fin 3 := ⟨S, hS⟩
  let RF : Fin 2 := ⟨R, hR⟩
  rcases high_nonneg_cases LF SF RF hfc hpriv with hcase | hcase | hcase | hcase
  · rcases hcase with ⟨hL0, hS1, hR1⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, THighVal]
    · exact high_localPsi_011 n hn i hhigh
  · rcases hcase with ⟨hL1, hS0, hR0⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, THighVal]
    · exact high_localPsi_100 n hn i hhigh
  · rcases hcase with ⟨hL1, hS1, hR1⟩
    have hL' : L = 1 := by simpa [LF] using hL1
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    left
    simp [localFcAfter, localFcBefore, frontierBitVal, THighVal]
  · rcases hcase with ⟨hL2, hS1, hR1⟩
    have hL' : L = 2 := by simpa [LF] using hL2
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, THighVal]
    · exact high_localPsi_211 n hn i hhigh

lemma top_local_nonneg_progress (n : Nat) (hn : 4 ≤ n) (i : Fin n) (htop : i.1 + 1 = n)
    {L S R : Nat} (hL : L < 3) (hS : S < 2) (hR : R < 2)
    (hfc : localFcBefore L S R ≤ localFcAfter L S R (TTopVal L S R))
    (hpriv : TTopVal L S R ≠ S) :
    localFcBefore L S R < localFcAfter L S R (TTopVal L S R) ∨
      (localFcAfter L S R (TTopVal L S R) = localFcBefore L S R ∧
        localPsiAfter n i L S R (TTopVal L S R) < localPsiBefore n i L S R) := by
  let LF : Fin 3 := ⟨L, hL⟩
  let SF : Fin 2 := ⟨S, hS⟩
  let RF : Fin 2 := ⟨R, hR⟩
  rcases top_nonneg_cases LF SF RF hfc hpriv with hcase | hcase
  · rcases hcase with ⟨hL0, hS1, hR1⟩
    have hL' : L = 0 := by simpa [LF] using hL0
    have hS' : S = 1 := by simpa [SF] using hS1
    have hR' : R = 1 := by simpa [RF] using hR1
    subst L S R
    right
    constructor
    · simp [localFcAfter, localFcBefore, frontierBitVal, TTopVal]
    · exact top_localPsi_011 n hn i htop
  · rcases hcase with ⟨hL2, hS0, hR0⟩
    have hL' : L = 2 := by simpa [LF] using hL2
    have hS' : S = 0 := by simpa [SF] using hS0
    have hR' : R = 0 := by simpa [RF] using hR0
    subst L S R
    left
    simp [localFcAfter, localFcBefore, frontierBitVal, TTopVal]

def cup2NonnegMeasure (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) : Nat × Nat :=
  (n - cup2Fc n hn c, cup2Psi n hn c)

lemma cup2FrontierBit_le_one (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (j : Fin n) :
    cup2FrontierBit n hn c j ≤ 1 := by
  unfold cup2FrontierBit frontierBitVal
  split_ifs <;> omega

lemma cup2Fc_le_n (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) :
    cup2Fc n hn c ≤ n := by
  unfold cup2Fc
  calc
    ∑ j : Fin n, cup2FrontierBit n hn c j ≤ ∑ _j : Fin n, (1 : Nat) := by
      refine Finset.sum_le_sum ?_
      intro j _hj
      exact cup2FrontierBit_le_one n hn c j
    _ = n := by simp

lemma cup2First_lt_of_localFc_lt (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n)
    {out : Nat}
    (hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = out)
    (hfc : localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 <
      localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 out) :
    n - cup2Fc n hn (move (cup2System n hn) c i) < n - cup2Fc n hn c := by
  have hbefore_le_n :
      localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 +
          Finset.sum (adjacentComplement i) (cup2FrontierBit n hn c) ≤ n := by
    have h := cup2Fc_le_n n hn c
    rw [cup2Fc_split n hn c i] at h
    exact h
  have hafter_le_n :
      localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 out +
          Finset.sum (adjacentComplement i) (cup2FrontierBit n hn c) ≤ n := by
    have h := cup2Fc_le_n n hn (move (cup2System n hn) c i)
    rw [cup2Fc_move_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout] at h
    exact h
  rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout]
  omega

lemma cup2Fc_eq_of_localFc_eq (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n)
    {out : Nat}
    (hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = out)
    (hfc : localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 out =
      localFcBefore (c (left i)).1 (c i).1 (c (right i)).1) :
    cup2Fc n hn (move (cup2System n hn) c i) = cup2Fc n hn c := by
  rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout, hfc]

lemma cup2Psi_lt_of_localPsi_lt (n : Nat) (hn : 4 ≤ n) (c : Config (cup2Spec n hn)) (i : Fin n)
    {out : Nat}
    (hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = out)
    (hpsi : localPsiAfter n i (c (left i)).1 (c i).1 (c (right i)).1 out <
      localPsiBefore n i (c (left i)).1 (c i).1 (c (right i)).1) :
    cup2Psi n hn (move (cup2System n hn) c i) < cup2Psi n hn c := by
  rw [cup2Psi_move_split n hn c i, cup2Psi_split n hn c i, cup2Psi_rest_move_eq n hn c i, hout]
  omega

lemma cup2BadStepNonneg_decreases (n : Nat) (hn : 4 ≤ n)
    {c' c : Config (cup2Spec n hn)} (hstep : cup2BadStepNonneg n hn c' c) :
    Prod.Lex (· < ·) (· < ·)
      (cup2NonnegMeasure n hn c') (cup2NonnegMeasure n hn c) := by
  rcases hstep with ⟨hbad, hfc_nonneg⟩
  rcases hbad with ⟨_hc'_bad, _hc_bad, ⟨i, hpriv, rfl⟩⟩
  let L := (c (left i)).1
  let S := (c i).1
  let R := (c (right i)).1
  have hpriv_val : cup2OutVal n i L S R ≠ S := by
    simpa [L, S, R, privileged, cup2System, cup2Trans_val, Fin.ne_iff_vne] using hpriv
  by_cases h0 : i.1 = 0
  · have hL : L < 2 := by
      simpa [L, cup2Spec, cup2M_left_bot hn h0] using (c (left i)).2
    have hS : S < 2 := by
      simpa [S, cup2Spec, cup2M_eq_two_of_endpoint (n := n) (i := i) (Or.inl h0)] using (c i).2
    have hR : R < 3 := by
      simpa [R, cup2Spec, cup2M_right_bot hn h0] using (c (right i)).2
    have hout : cup2OutVal n i L S R = TBotVal L S R := by
      simp [L, S, R, cup2OutVal, h0]
    have hfc_local : localFcBefore L S R ≤ localFcAfter L S R (TBotVal L S R) := by
      have h := hfc_nonneg
      rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout] at h
      have h' : localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 ≤
          localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 (TBotVal L S R) := by
        omega
      simpa [L, S, R] using h'
    have hpriv_local : TBotVal L S R ≠ S := by simpa [hout] using hpriv_val
    rcases bot_local_nonneg_progress n hn i h0 hL hS hR hfc_local hpriv_local with hlt | ⟨heq, hpsi⟩
    · have hfirst := cup2First_lt_of_localFc_lt n hn c i hout (by simpa [L, S, R] using hlt)
      simpa [cup2NonnegMeasure] using
        (Prod.Lex.left (cup2Psi n hn (move (cup2System n hn) c i)) (cup2Psi n hn c) hfirst)
    · have hfc_eq := cup2Fc_eq_of_localFc_eq n hn c i hout (by simpa [L, S, R] using heq)
      have hpsi_lt := cup2Psi_lt_of_localPsi_lt n hn c i hout (by simpa [L, S, R] using hpsi)
      simpa [cup2NonnegMeasure, hfc_eq] using
        (Prod.Lex.right (a := n - cup2Fc n hn c) hpsi_lt)
  · by_cases h1 : i.1 = 1
    · have hL : L < 2 := by
        simpa [L, cup2Spec, cup2M_left_low hn h1] using (c (left i)).2
      have hS : S < 3 := by
        simpa [S, cup2Spec, cup2M_self_low hn h1] using (c i).2
      have hR : R < 3 := by
        simpa [R, cup2Spec, cup2M_right_low hn h1] using (c (right i)).2
      have hout : cup2OutVal n i L S R = TLowVal L S R := by
        simp [L, S, R, cup2OutVal, h1]
      have hfc_local : localFcBefore L S R ≤ localFcAfter L S R (TLowVal L S R) := by
        have h := hfc_nonneg
        rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout] at h
        have h' : localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 ≤
            localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 (TLowVal L S R) := by
          omega
        simpa [L, S, R] using h'
      have hpriv_local : TLowVal L S R ≠ S := by simpa [hout] using hpriv_val
      rcases low_local_nonneg_progress n hn i h1 hL hS hR hfc_local hpriv_local with ⟨heq, hpsi⟩
      have hfc_eq := cup2Fc_eq_of_localFc_eq n hn c i hout (by simpa [L, S, R] using heq)
      have hpsi_lt := cup2Psi_lt_of_localPsi_lt n hn c i hout (by simpa [L, S, R] using hpsi)
      simpa [cup2NonnegMeasure, hfc_eq] using
        (Prod.Lex.right (a := n - cup2Fc n hn c) hpsi_lt)
    · by_cases htop : i.1 + 1 = n
      · have hL : L < 3 := by
          simpa [L, cup2Spec, cup2M_left_top hn htop] using (c (left i)).2
        have hS : S < 2 := by
          simpa [S, cup2Spec, cup2M_eq_two_of_endpoint (n := n) (i := i) (Or.inr htop)] using (c i).2
        have hR : R < 2 := by
          simpa [R, cup2Spec, cup2M_right_top hn htop] using (c (right i)).2
        have hout : cup2OutVal n i L S R = TTopVal L S R := by
          simp [L, S, R, cup2OutVal, h0, h1, htop]
        have hfc_local : localFcBefore L S R ≤ localFcAfter L S R (TTopVal L S R) := by
          have h := hfc_nonneg
          rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout] at h
          have h' : localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 ≤
              localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 (TTopVal L S R) := by
            omega
          simpa [L, S, R] using h'
        have hpriv_local : TTopVal L S R ≠ S := by simpa [hout] using hpriv_val
        rcases top_local_nonneg_progress n hn i htop hL hS hR hfc_local hpriv_local with hlt | ⟨heq, hpsi⟩
        · have hfirst := cup2First_lt_of_localFc_lt n hn c i hout (by simpa [L, S, R] using hlt)
          simpa [cup2NonnegMeasure] using
            (Prod.Lex.left (cup2Psi n hn (move (cup2System n hn) c i)) (cup2Psi n hn c) hfirst)
        · have hfc_eq := cup2Fc_eq_of_localFc_eq n hn c i hout (by simpa [L, S, R] using heq)
          have hpsi_lt := cup2Psi_lt_of_localPsi_lt n hn c i hout (by simpa [L, S, R] using hpsi)
          simpa [cup2NonnegMeasure, hfc_eq] using
            (Prod.Lex.right (a := n - cup2Fc n hn c) hpsi_lt)
      · by_cases hhigh : i.1 + 2 = n
        · have hL : L < 3 := by
            simpa [L, cup2Spec, cup2M_left_high hn hhigh] using (c (left i)).2
          have hS : S < 3 := by
            simpa [S, cup2Spec, cup2M_self_high hn hhigh] using (c i).2
          have hR : R < 2 := by
            simpa [R, cup2Spec, cup2M_right_high hn hhigh] using (c (right i)).2
          have hout : cup2OutVal n i L S R = THighVal L S R := by
            simp [L, S, R, cup2OutVal, h0, h1, htop, hhigh]
          have hfc_local : localFcBefore L S R ≤ localFcAfter L S R (THighVal L S R) := by
            have h := hfc_nonneg
            rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout] at h
            have h' : localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 ≤
                localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 (THighVal L S R) := by
              omega
            simpa [L, S, R] using h'
          have hpriv_local : THighVal L S R ≠ S := by simpa [hout] using hpriv_val
          rcases high_local_nonneg_progress n hn i hhigh hL hS hR hfc_local hpriv_local with hlt | ⟨heq, hpsi⟩
          · have hfirst := cup2First_lt_of_localFc_lt n hn c i hout (by simpa [L, S, R] using hlt)
            simpa [cup2NonnegMeasure] using
              (Prod.Lex.left (cup2Psi n hn (move (cup2System n hn) c i)) (cup2Psi n hn c) hfirst)
          · have hfc_eq := cup2Fc_eq_of_localFc_eq n hn c i hout (by simpa [L, S, R] using heq)
            have hpsi_lt := cup2Psi_lt_of_localPsi_lt n hn c i hout (by simpa [L, S, R] using hpsi)
            simpa [cup2NonnegMeasure, hfc_eq] using
              (Prod.Lex.right (a := n - cup2Fc n hn c) hpsi_lt)
        · have hL : L < 3 := by
            simpa [L, cup2Spec, cup2M_left_mid hn h0 h1 htop] using (c (left i)).2
          have hS : S < 3 := by
            simpa [S, cup2Spec, cup2M_self_mid hn h0 htop] using (c i).2
          have hR : R < 3 := by
            simpa [R, cup2Spec, cup2M_right_mid hn h0 htop hhigh] using (c (right i)).2
          have hout : cup2OutVal n i L S R = TMidVal L S R := by
            simp [L, S, R, cup2OutVal, h0, h1, htop, hhigh]
          have hfc_local : localFcBefore L S R ≤ localFcAfter L S R (TMidVal L S R) := by
            have h := hfc_nonneg
            rw [cup2Fc_move_split n hn c i, cup2Fc_split n hn c i, cup2Fc_rest_move_eq n hn c i, hout] at h
            have h' : localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 ≤
                localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 (TMidVal L S R) := by
              omega
            simpa [L, S, R] using h'
          have hpriv_local : TMidVal L S R ≠ S := by simpa [hout] using hpriv_val
          rcases mid_local_nonneg_progress n hn i h0 h1 htop hhigh hL hS hR hfc_local hpriv_local with hlt | ⟨heq, hpsi⟩
          · have hfirst := cup2First_lt_of_localFc_lt n hn c i hout (by simpa [L, S, R] using hlt)
            simpa [cup2NonnegMeasure] using
              (Prod.Lex.left (cup2Psi n hn (move (cup2System n hn) c i)) (cup2Psi n hn c) hfirst)
          · have hfc_eq := cup2Fc_eq_of_localFc_eq n hn c i hout (by simpa [L, S, R] using heq)
            have hpsi_lt := cup2Psi_lt_of_localPsi_lt n hn c i hout (by simpa [L, S, R] using hpsi)
            simpa [cup2NonnegMeasure, hfc_eq] using
              (Prod.Lex.right (a := n - cup2Fc n hn c) hpsi_lt)

theorem cup2BadStepNonneg_wf (n : Nat) (hn : 4 ≤ n) :
    WellFounded (cup2BadStepNonneg n hn) := by
  let r :=
    InvImage (Prod.Lex (· < ·) (· < ·)) (cup2NonnegMeasure n hn)
  refine Subrelation.wf (r := r) ?_ ?_
  · intro c' c h
    exact cup2BadStepNonneg_decreases n hn h
  · exact InvImage.wf (cup2NonnegMeasure n hn)
      (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

end LeanMn
