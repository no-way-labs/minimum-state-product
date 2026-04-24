import LeanMn.Convergence.Interior
import LeanMn.Convergence.SixTuple
import LeanMn.Convergence.PhiFullTP
import LeanMn.Cycle

namespace LeanMn

open scoped BigOperators

abbrev PosType := Fin 7

def P0 : PosType := ⟨0, by omega⟩
def P1 : PosType := ⟨1, by omega⟩
def P2 : PosType := ⟨2, by omega⟩
def Pn3 : PosType := ⟨3, by omega⟩
def Pn2 : PosType := ⟨4, by omega⟩
def Pn1 : PosType := ⟨5, by omega⟩
def mid : PosType := ⟨6, by omega⟩

def posType (n : Nat) (_hn : 9 ≤ n) (j : Fin n) : PosType :=
  if j.1 = 0 then
    P0
  else if j.1 = 1 then
    P1
  else if j.1 = 2 then
    P2
  else if j.1 = n - 3 then
    Pn3
  else if j.1 = n - 2 then
    Pn2
  else if j.1 = n - 1 then
    Pn1
  else
    mid

private def wP0 (L S R : Fin 3) : Int :=
  match L.1, S.1, R.1 with
  | 0, 0, 0 => 5
  | 0, 0, 1 => 5
  | 0, 0, 2 => 5
  | 0, 1, 0 => -5
  | 0, 1, 1 => -5
  | 0, 1, 2 => -1
  | 0, 2, 0 => -5
  | 0, 2, 1 => -5
  | 0, 2, 2 => -5
  | 1, 0, 0 => -5
  | 1, 0, 1 => 1
  | 1, 0, 2 => -5
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 5
  | 1, 2, 0 => -5
  | 1, 2, 1 => -5
  | 1, 2, 2 => -5
  | 2, 0, 0 => -5
  | 2, 0, 1 => -5
  | 2, 0, 2 => -5
  | 2, 1, 0 => -5
  | 2, 1, 1 => -5
  | 2, 1, 2 => -5
  | 2, 2, 0 => -5
  | 2, 2, 1 => -5
  | 2, 2, 2 => -5
  | _, _, _ => 0

private def wP1 (L S R : Fin 3) : Int :=
  match L.1, S.1, R.1 with
  | 0, 0, 0 => -3
  | 0, 0, 1 => -5
  | 0, 0, 2 => -3
  | 0, 1, 0 => 5
  | 0, 1, 1 => 5
  | 0, 1, 2 => 5
  | 0, 2, 0 => -1
  | 0, 2, 1 => 1
  | 0, 2, 2 => 5
  | 1, 0, 0 => 5
  | 1, 0, 1 => -1
  | 1, 0, 2 => 5
  | 1, 1, 0 => -5
  | 1, 1, 1 => -5
  | 1, 1, 2 => 3
  | 1, 2, 0 => 3
  | 1, 2, 1 => 5
  | 1, 2, 2 => -3
  | 2, 0, 0 => -5
  | 2, 0, 1 => -5
  | 2, 0, 2 => -5
  | 2, 1, 0 => -5
  | 2, 1, 1 => -5
  | 2, 1, 2 => -5
  | 2, 2, 0 => -5
  | 2, 2, 1 => -5
  | 2, 2, 2 => -5
  | _, _, _ => 0

private def wP2 (L S R : Fin 3) : Int :=
  match L.1, S.1, R.1 with
  | 0, 0, 0 => -5
  | 0, 0, 2 => -3
  | 0, 1, 0 => 5
  | 0, 1, 1 => 5
  | 0, 1, 2 => 5
  | 0, 2, 0 => 5
  | 0, 2, 1 => 5
  | 0, 2, 2 => 1
  | 1, 0, 0 => 3
  | 1, 0, 1 => -3
  | 1, 0, 2 => 5
  | 1, 1, 0 => -5
  | 1, 1, 1 => -5
  | 1, 1, 2 => 3
  | 1, 2, 0 => 5
  | 1, 2, 1 => 5
  | 1, 2, 2 => -5
  | 2, 0, 0 => -5
  | 2, 0, 1 => 5
  | 2, 0, 2 => 5
  | 2, 1, 0 => 5
  | 2, 1, 1 => 5
  | 2, 1, 2 => 5
  | 2, 2, 0 => 3
  | 2, 2, 2 => -5
  | _, _, _ => 0

private def wPn3 (L S R : Fin 3) : Int :=
  match L.1, S.1, R.1 with
  | 0, 0, 0 => -5
  | 0, 0, 1 => 5
  | 0, 0, 2 => -1
  | 0, 1, 0 => 5
  | 0, 1, 1 => 1
  | 0, 1, 2 => 1
  | 0, 2, 1 => 5
  | 0, 2, 2 => 5
  | 1, 0, 0 => 1
  | 1, 0, 1 => 5
  | 1, 0, 2 => 5
  | 1, 1, 0 => -1
  | 1, 1, 1 => -5
  | 1, 1, 2 => -5
  | 1, 2, 0 => 5
  | 1, 2, 1 => 5
  | 1, 2, 2 => -5
  | 2, 0, 0 => -5
  | 2, 0, 1 => -3
  | 2, 0, 2 => 5
  | 2, 1, 0 => 5
  | 2, 1, 1 => 1
  | 2, 1, 2 => 1
  | 2, 2, 1 => 5
  | 2, 2, 2 => -5
  | _, _, _ => 0

private def wPn2 (L S R : Fin 3) : Int :=
  match L.1, S.1, R.1 with
  | 0, 0, 0 => -5
  | 0, 0, 1 => -3
  | 0, 0, 2 => -5
  | 0, 1, 0 => 5
  | 0, 1, 1 => 5
  | 0, 1, 2 => -5
  | 0, 2, 0 => 3
  | 0, 2, 1 => 5
  | 0, 2, 2 => -5
  | 1, 0, 0 => 3
  | 1, 0, 1 => 5
  | 1, 0, 2 => -5
  | 1, 1, 0 => -5
  | 1, 1, 1 => -5
  | 1, 1, 2 => -5
  | 1, 2, 0 => -1
  | 1, 2, 1 => -5
  | 1, 2, 2 => -5
  | 2, 0, 0 => 3
  | 2, 0, 1 => 5
  | 2, 0, 2 => -5
  | 2, 1, 0 => 5
  | 2, 1, 1 => 5
  | 2, 1, 2 => -5
  | 2, 2, 0 => -1
  | 2, 2, 1 => -5
  | 2, 2, 2 => -5
  | _, _, _ => 0

private def wPn1 (L S R : Fin 3) : Int :=
  match L.1, S.1, R.1 with
  | 0, 0, 0 => -5
  | 0, 0, 1 => -5
  | 0, 0, 2 => -5
  | 0, 1, 0 => 5
  | 0, 1, 1 => 5
  | 0, 1, 2 => -5
  | 0, 2, 0 => -5
  | 0, 2, 1 => -5
  | 0, 2, 2 => -5
  | 1, 0, 0 => 5
  | 1, 0, 1 => 5
  | 1, 0, 2 => -5
  | 1, 1, 0 => -3
  | 1, 1, 1 => -3
  | 1, 1, 2 => -5
  | 1, 2, 0 => -5
  | 1, 2, 1 => -5
  | 1, 2, 2 => -5
  | 2, 0, 0 => 5
  | 2, 0, 1 => 5
  | 2, 0, 2 => -5
  | 2, 1, 0 => -5
  | 2, 1, 1 => -5
  | 2, 1, 2 => -5
  | 2, 2, 0 => -5
  | 2, 2, 1 => -5
  | 2, 2, 2 => -5
  | _, _, _ => 0

private def wMid (L S R : Fin 3) : Int :=
  match L.1, S.1, R.1 with
  | 0, 0, 0 => -5
  | 0, 0, 1 => 5
  | 0, 0, 2 => 3
  | 0, 1, 0 => 5
  | 0, 1, 1 => -3
  | 0, 1, 2 => -5
  | 0, 2, 0 => -3
  | 0, 2, 1 => 5
  | 1, 0, 0 => -5
  | 1, 0, 1 => 5
  | 1, 0, 2 => 1
  | 1, 1, 0 => 5
  | 1, 1, 1 => -3
  | 1, 1, 2 => -5
  | 1, 2, 0 => -3
  | 1, 2, 1 => 5
  | 2, 0, 0 => -5
  | 2, 0, 1 => 5
  | 2, 0, 2 => 5
  | 2, 1, 0 => 5
  | 2, 1, 1 => -3
  | 2, 1, 2 => -5
  | 2, 2, 0 => -5
  | 2, 2, 1 => 3
  | 2, 2, 2 => -2
  | _, _, _ => 0

/-- Syntactic boundary/local weight table. Unlisted entries are zero. -/
def w (p : Fin 7) (L S R : Fin 3) : Int :=
  match p.1 with
  | 0 => wP0 L S R
  | 1 => wP1 L S R
  | 2 => wP2 L S R
  | 3 => wPn3 L S R
  | 4 => wPn2 L S R
  | 5 => wPn1 L S R
  | 6 => wMid L S R
  | _ => 0

def stateAsFin3 (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) (i : Fin n) : Fin 3 :=
  ⟨(c i).1, by
    have hi : (c i).1 < cup2M n i := (c i).2
    unfold cup2M at hi
    split_ifs at hi <;> omega⟩

/-- The syntactic potential `Ψ(c) = Σ_j w(posType(j), c[j-1], c[j], c[j+1])`. -/
def Ψ (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Int :=
  ∑ j : Fin n,
    w (posType n hn9 j)
      (stateAsFin3 n hn4 c (left j))
      (stateAsFin3 n hn4 c j)
      (stateAsFin3 n hn4 c (right j))

abbrev syntheticPotential := Ψ

private def up2 (x : Fin 2) : Fin 3 :=
  ⟨x.1, by omega⟩

@[simp] private theorem up2_val (x : Fin 2) : (up2 x).1 = x.1 := rfl

private def ΨTerm (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (j : Fin n) : Int :=
  w (posType n hn9 j)
    (stateAsFin3 n hn4 c (left j))
    (stateAsFin3 n hn4 c j)
    (stateAsFin3 n hn4 c (right j))

private def ΨOutAsFin3 (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) : Fin 3 :=
  ⟨cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1, by
    have hlt : (move (cup2System n hn4) c i i).1 < cup2M n i := (move (cup2System n hn4) c i i).2
    rw [move_apply_self_val n hn4 c i] at hlt
    have hM : cup2M n i ≤ 3 := by
      unfold cup2M
      split_ifs <;> omega
    omega⟩

private def ΨLocalBefore (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) : Int :=
  ΨTerm n hn4 hn9 c (left i) +
    ΨTerm n hn4 hn9 c i +
      ΨTerm n hn4 hn9 c (right i)

private def ΨLocalAfter (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) : Int :=
  ΨTerm n hn4 hn9 (move (cup2System n hn4) c i) (left i) +
    ΨTerm n hn4 hn9 (move (cup2System n hn4) c i) i +
      ΨTerm n hn4 hn9 (move (cup2System n hn4) c i) (right i)

private def ΨTripleComplement {n : Nat} (i : Fin n) : Finset (Fin n) :=
  (((Finset.univ.erase (left i)).erase i).erase (right i))

private lemma left_ne_right_of_ge4 {n : Nat} (hn4 : 4 ≤ n) (i : Fin n) :
    left i ≠ right i := by
  intro h
  have hval := congrArg Fin.val h
  by_cases h0 : i.1 = 0
  · rw [left_val, right_val, h0, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hval
    omega
  · by_cases htop : i.1 + 1 = n
    · rw [left_val_of_ne_zero h0, right_val_of_top htop] at hval
      omega
    · rw [left_val_of_ne_zero h0, right_val_of_not_top htop] at hval
      omega

private lemma mem_ΨTripleComplement_iff {n : Nat} (i j : Fin n) :
    j ∈ ΨTripleComplement i ↔ j ≠ left i ∧ j ≠ i ∧ j ≠ right i := by
  unfold ΨTripleComplement
  simp [and_assoc, and_left_comm, and_comm]

private lemma ΨTerm_move_eq_of_mem_ΨTripleComplement
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i j : Fin n)
    (hj : j ∈ ΨTripleComplement i) :
    ΨTerm n hn4 hn9 (move (cup2System n hn4) c i) j =
      ΨTerm n hn4 hn9 c j := by
  have hn2 : 2 ≤ n := by omega
  have hjl : j ≠ left i := (mem_ΨTripleComplement_iff i j).mp hj |>.1
  have hji : j ≠ i := (mem_ΨTripleComplement_iff i j).mp hj |>.2.1
  have hjr : j ≠ right i := (mem_ΨTripleComplement_iff i j).mp hj |>.2.2
  have hleft : left j ≠ i := by
    intro h
    have h' := congrArg right h
    simpa using hjr (right_left hn2 j ▸ h')
  have hright : right j ≠ i := by
    intro h
    have h' := congrArg left h
    simpa using hjl (left_right hn2 j ▸ h')
  unfold ΨTerm stateAsFin3
  simp [move, hleft, hji, hright]

private lemma sum_univ_eq_ΨTripleComplement {n : Nat} {α : Type*} [AddCommMonoid α]
    (hn4 : 4 ≤ n) (f : Fin n → α) (i : Fin n) :
    (∑ j : Fin n, f j) =
      f (left i) + f i + f (right i) + Finset.sum (ΨTripleComplement i) f := by
  have hn2 : 2 ≤ n := by omega
  have hli : left i ∈ Finset.univ := Finset.mem_univ (left i)
  rw [← Finset.add_sum_erase (Finset.univ) f hli]
  have himem : i ∈ Finset.univ.erase (left i) := by
    simp only [Finset.mem_erase, Finset.mem_univ]
    exact ⟨fun h => left_ne_self hn2 i h.symm, trivial⟩
  rw [← Finset.add_sum_erase (Finset.univ.erase (left i)) f himem]
  have hright_ne_left : right i ≠ left i := by
    intro h
    exact left_ne_right_of_ge4 hn4 i h.symm
  have hrmem : right i ∈ (Finset.univ.erase (left i)).erase i := by
    simp only [Finset.mem_erase, Finset.mem_univ]
    exact ⟨right_ne_self hn2 i, hright_ne_left, trivial⟩
  rw [← Finset.add_sum_erase ((Finset.univ.erase (left i)).erase i) f hrmem]
  simp [ΨTripleComplement, add_assoc, add_left_comm, add_comm]

private lemma Ψ_split (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) :
    Ψ n hn4 hn9 c =
      ΨLocalBefore n hn4 hn9 c i +
        Finset.sum (ΨTripleComplement i) (ΨTerm n hn4 hn9 c) := by
  change (∑ j : Fin n, ΨTerm n hn4 hn9 c j) =
    ΨLocalBefore n hn4 hn9 c i +
      Finset.sum (ΨTripleComplement i) (ΨTerm n hn4 hn9 c)
  rw [sum_univ_eq_ΨTripleComplement hn4 (ΨTerm n hn4 hn9 c) i]
  unfold ΨLocalBefore
  ac_rfl

private lemma Ψ_move_split (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) :
    Ψ n hn4 hn9 (move (cup2System n hn4) c i) =
      ΨLocalAfter n hn4 hn9 c i +
        Finset.sum (ΨTripleComplement i)
          (ΨTerm n hn4 hn9 (move (cup2System n hn4) c i)) := by
  change (∑ j : Fin n, ΨTerm n hn4 hn9 (move (cup2System n hn4) c i) j) =
    ΨLocalAfter n hn4 hn9 c i +
      Finset.sum (ΨTripleComplement i)
        (ΨTerm n hn4 hn9 (move (cup2System n hn4) c i))
  rw [sum_univ_eq_ΨTripleComplement hn4
    (ΨTerm n hn4 hn9 (move (cup2System n hn4) c i)) i]
  unfold ΨLocalAfter
  ac_rfl

private lemma Ψ_rest_move_eq (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) :
    Finset.sum (ΨTripleComplement i) (ΨTerm n hn4 hn9 (move (cup2System n hn4) c i)) =
      Finset.sum (ΨTripleComplement i) (ΨTerm n hn4 hn9 c) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact ΨTerm_move_eq_of_mem_ΨTripleComplement n hn4 hn9 c i j hj

@[simp] private lemma posType_boundaryIdx0 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (cup2BoundaryIdx0 n hn9) = P0 := by
  simp [posType, cup2BoundaryIdx0]

@[simp] private lemma posType_boundaryIdx1 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (cup2BoundaryIdx1 n hn9) = P1 := by
  simp [posType, cup2BoundaryIdx1]

@[simp] private lemma posType_boundaryIdx2 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (cup2BoundaryIdx2 n hn9) = P2 := by
  simp [posType, cup2BoundaryIdx2]

@[simp] private lemma posType_right_boundaryIdx2 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (right (cup2BoundaryIdx2 n hn9)) = mid := by
  have h3 : (right (cup2BoundaryIdx2 n hn9)).1 = 3 := by
    have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdx2]
      omega
    rw [right_val_of_not_top htop]
    simp [cup2BoundaryIdx2]
  have hr : right (cup2BoundaryIdx2 n hn9) = ⟨3, by omega⟩ := by
    apply Fin.ext
    simpa using h3
  rw [hr]
  have hN3 : ¬ (3 = n - 3) := by omega
  have hN2 : ¬ (3 = n - 2) := by omega
  have hN1 : ¬ (3 = n - 1) := by omega
  simp [posType, hN3, hN2, hN1]

@[simp] private lemma posType_boundaryIdxN3 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (cup2BoundaryIdxN3 n hn9) = Pn3 := by
  have h0 : ¬ (n - 3 = 0) := by omega
  have h1 : ¬ (n - 3 = 1) := by omega
  have h2 : ¬ (n - 3 = 2) := by omega
  simp [posType, cup2BoundaryIdxN3, h0, h1, h2]

@[simp] private lemma posType_boundaryIdxN2 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (cup2BoundaryIdxN2 n hn9) = Pn2 := by
  have h0 : ¬ (n - 2 = 0) := by omega
  have h1 : ¬ (n - 2 = 1) := by omega
  have h2 : ¬ (n - 2 = 2) := by omega
  have hN3 : ¬ (n - 2 = n - 3) := by omega
  simp [posType, cup2BoundaryIdxN2, h0, h1, h2, hN3]

@[simp] private lemma posType_boundaryIdxN1 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (cup2BoundaryIdxN1 n hn9) = Pn1 := by
  have h0 : ¬ (n - 1 = 0) := by omega
  have h1 : ¬ (n - 1 = 1) := by omega
  have h2 : ¬ (n - 1 = 2) := by omega
  have hN3 : ¬ (n - 1 = n - 3) := by omega
  have hN2 : ¬ (n - 1 = n - 2) := by omega
  simp [posType, cup2BoundaryIdxN1, h0, h1, h2, hN3, hN2]

@[simp] private lemma posType_left_boundaryIdxN3 (n : Nat) (hn9 : 9 ≤ n) :
    posType n hn9 (left (cup2BoundaryIdxN3 n hn9)) = mid := by
  have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
    simp [cup2BoundaryIdxN3]
    omega
  have hmid : (left (cup2BoundaryIdxN3 n hn9)).1 = n - 4 := by
    rw [left_val_of_ne_zero h0]
    simp [cup2BoundaryIdxN3]
    omega
  have hl : left (cup2BoundaryIdxN3 n hn9) = ⟨n - 4, by omega⟩ := by
    apply Fin.ext
    simpa using hmid
  rw [hl]
  have h0' : ¬ (n - 4 = 0) := by omega
  have h1' : ¬ (n - 4 = 1) := by omega
  have h2' : ¬ (n - 4 = 2) := by omega
  have hN3' : ¬ (n - 4 = n - 3) := by omega
  have hN2' : ¬ (n - 4 = n - 2) := by omega
  have hN1' : ¬ (n - 4 = n - 1) := by omega
  simp [posType, h0', h1', h2', hN3', hN2', hN1']

@[simp] private lemma stateAsFin3_boundaryIdx0 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    stateAsFin3 n hn4 c (cup2BoundaryIdx0 n hn9) =
      up2 (cup2Boundary6 n hn4 hn9 c).c0 := by
  apply Fin.ext
  simp [stateAsFin3, cup2Boundary6, up2, cup2BoundaryIdx0]

@[simp] private lemma stateAsFin3_boundaryIdx1 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    stateAsFin3 n hn4 c (cup2BoundaryIdx1 n hn9) =
      (cup2Boundary6 n hn4 hn9 c).c1 := by
  apply Fin.ext
  simp [stateAsFin3, cup2Boundary6, cup2BoundaryIdx1]

@[simp] private lemma stateAsFin3_boundaryIdx2 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    stateAsFin3 n hn4 c (cup2BoundaryIdx2 n hn9) =
      (cup2Boundary6 n hn4 hn9 c).c2 := by
  apply Fin.ext
  simp [stateAsFin3, cup2Boundary6, cup2BoundaryIdx2]

@[simp] private lemma stateAsFin3_boundaryIdxN3 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    stateAsFin3 n hn4 c (cup2BoundaryIdxN3 n hn9) =
      (cup2Boundary6 n hn4 hn9 c).cN3 := by
  apply Fin.ext
  simp [stateAsFin3, cup2Boundary6, cup2BoundaryIdxN3]

@[simp] private lemma stateAsFin3_boundaryIdxN2 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    stateAsFin3 n hn4 c (cup2BoundaryIdxN2 n hn9) =
      (cup2Boundary6 n hn4 hn9 c).cN2 := by
  apply Fin.ext
  simp [stateAsFin3, cup2Boundary6, cup2BoundaryIdxN2]

@[simp] private lemma stateAsFin3_boundaryIdxN1 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    stateAsFin3 n hn4 c (cup2BoundaryIdxN1 n hn9) =
      up2 (cup2Boundary6 n hn4 hn9 c).cN1 := by
  apply Fin.ext
  simp [stateAsFin3, cup2Boundary6, up2, cup2BoundaryIdxN1]

@[simp] private lemma stateAsFin3_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) (i j : Fin n)
    (hji : j ≠ i) :
    stateAsFin3 n hn4 (move (cup2System n hn4) c i) j =
      stateAsFin3 n hn4 c j := by
  apply Fin.ext
  simp [stateAsFin3, move_apply_ne, hji]

private lemma cup2Boundary6_move_eq_boundarySuccP0
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
      boundarySuccP0 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idx0 n hn4 hn9 c]
  ext
  · simp [boundarySuccP0, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx0 n hn9)
    have hright : (c (right (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx0 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]

private lemma cup2Boundary6_move_eq_boundarySuccP1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
      boundarySuccP1 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idx1 n hn4 hn9 c]
  ext
  · simp [boundarySuccP1]
  · simp [boundarySuccP1, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx1 n hn9)
    have hright : (c (right (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx1 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]

private lemma cup2Boundary6_move_eq_boundarySuccP2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
      boundarySuccP2 (cup2Boundary6 n hn4 hn9 c)
        (stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))) := by
  rw [cup2Boundary6_move_idx2 n hn4 hn9 c]
  ext
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2, stateAsFin3, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx2 n hn9)
    rw [hleft]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]

private lemma cup2Boundary6_move_eq_boundarySuccPN3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
      boundarySuccPN3 (cup2Boundary6 n hn4 hn9 c)
        (stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))) := by
  rw [cup2Boundary6_move_idxN3 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3, stateAsFin3, cup2Boundary6, move_apply_self_val]
    have hright : (c (right (cup2BoundaryIdxN3 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN3 n hn9)
    rw [hright]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]

private lemma cup2Boundary6_move_eq_boundarySuccPN2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
      boundarySuccPN2 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idxN2 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN2 n hn9)
    have hright : (c (right (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN2 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccPN2]

private lemma cup2Boundary6_move_eq_boundarySuccPN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
      boundarySuccPN1 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idxN1 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN1 n hn9)
    have hright : (c (right (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN1 n hn9)
    rw [hleft, hright]

private def psiLocalP0Before (s : SixBoundary) : Int :=
  w Pn1 s.cN2 (up2 s.cN1) (up2 s.c0) +
    w P0 (up2 s.cN1) (up2 s.c0) s.c1 +
      w P1 (up2 s.c0) s.c1 s.c2

private def psiLocalP0After (s : SixBoundary) : Int :=
  let t := boundarySuccP0 s
  w Pn1 t.cN2 (up2 t.cN1) (up2 t.c0) +
    w P0 (up2 t.cN1) (up2 t.c0) t.c1 +
      w P1 (up2 t.c0) t.c1 t.c2

private def psiLocalP1Before (s : SixBoundary) (c3 : Fin 3) : Int :=
  w P0 (up2 s.cN1) (up2 s.c0) s.c1 +
    w P1 (up2 s.c0) s.c1 s.c2 +
      w P2 s.c1 s.c2 c3

private def psiLocalP1After (s : SixBoundary) (c3 : Fin 3) : Int :=
  let t := boundarySuccP1 s
  w P0 (up2 t.cN1) (up2 t.c0) t.c1 +
    w P1 (up2 t.c0) t.c1 t.c2 +
      w P2 t.c1 t.c2 c3

private def psiLocalP2Before (s : SixBoundary) (c3 c4 : Fin 3) : Int :=
  w P1 (up2 s.c0) s.c1 s.c2 +
    w P2 s.c1 s.c2 c3 +
      w mid s.c2 c3 c4

private def psiLocalP2After (s : SixBoundary) (c3 c4 : Fin 3) : Int :=
  let t := boundarySuccP2 s c3
  w P1 (up2 t.c0) t.c1 t.c2 +
    w P2 t.c1 t.c2 c3 +
      w mid t.c2 c3 c4

private def psiLocalPN3Before (s : SixBoundary) (cn5 cn4 : Fin 3) : Int :=
  w mid cn5 cn4 s.cN3 +
    w Pn3 cn4 s.cN3 s.cN2 +
      w Pn2 s.cN3 s.cN2 (up2 s.cN1)

private def psiLocalPN3After (s : SixBoundary) (cn5 cn4 : Fin 3) : Int :=
  let t := boundarySuccPN3 s cn4
  w mid cn5 cn4 t.cN3 +
    w Pn3 cn4 t.cN3 t.cN2 +
      w Pn2 t.cN3 t.cN2 (up2 t.cN1)

private def psiLocalPN2Before (s : SixBoundary) (cn4 : Fin 3) : Int :=
  w Pn3 cn4 s.cN3 s.cN2 +
    w Pn2 s.cN3 s.cN2 (up2 s.cN1) +
      w Pn1 s.cN2 (up2 s.cN1) (up2 s.c0)

private def psiLocalPN2After (s : SixBoundary) (cn4 : Fin 3) : Int :=
  let t := boundarySuccPN2 s
  w Pn3 cn4 t.cN3 t.cN2 +
    w Pn2 t.cN3 t.cN2 (up2 t.cN1) +
      w Pn1 t.cN2 (up2 t.cN1) (up2 t.c0)

private def psiLocalPN1Before (s : SixBoundary) : Int :=
  w Pn2 s.cN3 s.cN2 (up2 s.cN1) +
    w Pn1 s.cN2 (up2 s.cN1) (up2 s.c0) +
      w P0 (up2 s.cN1) (up2 s.c0) s.c1

private def psiLocalPN1After (s : SixBoundary) : Int :=
  let t := boundarySuccPN1 s
  w Pn2 t.cN3 t.cN2 (up2 t.cN1) +
    w Pn1 t.cN2 (up2 t.cN1) (up2 t.c0) +
      w P0 (up2 t.cN1) (up2 t.c0) t.c1

private def f0 : Fin 3 := ⟨0, by omega⟩
private def f1 : Fin 3 := ⟨1, by omega⟩
private def f2 : Fin 3 := ⟨2, by omega⟩

set_option maxRecDepth 100000 in
private theorem bad_boundary_Ψ_drop_at_P0 :
    ∀ s : SixBoundary,
      (boundarySuccP0 s).encode ≠ s.encode →
      psiLocalP0After s < psiLocalP0Before s := by
  decide

set_option maxRecDepth 100000 in
private theorem bad_boundary_Ψ_drop_at_P1 :
    ∀ s : SixBoundary, ∀ c3 : Fin 3,
      (boundarySuccP1 s).encode ≠ s.encode →
      psiLocalP1After s c3 < psiLocalP1Before s c3 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem bad_boundary_Ψ_drop_at_P2 :
    ∀ s : SixBoundary, ∀ c3 : Fin 3,
      (boundarySuccP2 s c3).encode ≠ s.encode →
      psiLocalP2After s c3 f0 < psiLocalP2Before s c3 f0 ∧
        psiLocalP2After s c3 f1 < psiLocalP2Before s c3 f1 ∧
        psiLocalP2After s c3 f2 < psiLocalP2Before s c3 f2 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem bad_boundary_Ψ_drop_at_PN3 :
    ∀ s : SixBoundary, ∀ cn4 : Fin 3,
      (boundarySuccPN3 s cn4).encode ≠ s.encode →
      psiLocalPN3After s f0 cn4 < psiLocalPN3Before s f0 cn4 ∧
        psiLocalPN3After s f1 cn4 < psiLocalPN3Before s f1 cn4 ∧
        psiLocalPN3After s f2 cn4 < psiLocalPN3Before s f2 cn4 := by
  decide

set_option maxRecDepth 100000 in
private theorem bad_boundary_Ψ_drop_at_PN2 :
    ∀ s : SixBoundary, ∀ cn4 : Fin 3,
      (boundarySuccPN2 s).encode ≠ s.encode →
      psiLocalPN2After s cn4 < psiLocalPN2Before s cn4 := by
  decide

set_option maxRecDepth 100000 in
private theorem bad_boundary_Ψ_drop_at_PN1 :
    ∀ s : SixBoundary,
      (boundarySuccPN1 s).encode ≠ s.encode →
      psiLocalPN1After s < psiLocalPN1Before s := by
  decide

/-- Any bad step whose boundary projection changes forces a strict drop in the
syntactic potential. The proof is a finite local case check over all changed
boundary transitions. -/
theorem bad_boundary_all_Ψ_drop
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hbad : badStep (cup2System n hn4) (cup2GoodCycle n hn4) c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c) :
    Ψ n hn4 hn9 c' < Ψ n hn4 hn9 c := by
  rcases hbad.2.2 with ⟨i, hpriv, rfl⟩
  have hlocal :
      ΨLocalAfter n hn4 hn9 c i < ΨLocalBefore n hn4 hn9 c i := by
    have hbdry := cup2BoundaryState_changed_implies_boundary_index n hn4 hn9 c i hchange
    rcases hbdry with hle2 | hgeN3
    · by_cases hi0 : i.1 = 0
      · have hi : i = cup2BoundaryIdx0 n hn9 := by
          apply Fin.ext
          simp [cup2BoundaryIdx0, hi0]
        subst hi
        let s := cup2Boundary6 n hn4 hn9 c
        have hb6 :
            cup2Boundary6 n hn4 hn9
                (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
              boundarySuccP0 s := by
          simpa [s] using cup2Boundary6_move_eq_boundarySuccP0 n hn4 hn9 c
        have hchange' : (boundarySuccP0 s).encode ≠ s.encode := by
          simpa [cup2BoundaryState, s, hb6] using hchange
        have hdrop := bad_boundary_Ψ_drop_at_P0 s hchange'
        simpa [ΨLocalAfter, ΨLocalBefore, psiLocalP0After, psiLocalP0Before, ΨTerm, s, hb6]
          using hdrop
      · by_cases hi1 : i.1 = 1
        · have hi : i = cup2BoundaryIdx1 n hn9 := by
            apply Fin.ext
            simp [cup2BoundaryIdx1, hi1]
          subst hi
          let s := cup2Boundary6 n hn4 hn9 c
          let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
          have hb6 :
              cup2Boundary6 n hn4 hn9
                  (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
                boundarySuccP1 s := by
            simpa [s] using cup2Boundary6_move_eq_boundarySuccP1 n hn4 hn9 c
          have hchange' : (boundarySuccP1 s).encode ≠ s.encode := by
            simpa [cup2BoundaryState, s, hb6] using hchange
          have hc3_ne : right (cup2BoundaryIdx2 n hn9) ≠ cup2BoundaryIdx1 n hn9 := by
            intro h
            have hval := congrArg Fin.val h
            have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
              simp [cup2BoundaryIdx2]
              omega
            rw [right_val_of_not_top htop] at hval
            simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval
          have hc3 :
              stateAsFin3 n hn4
                  (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
                  (right (cup2BoundaryIdx2 n hn9)) = c3 := by
            simpa [c3] using
              stateAsFin3_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9)
                (right (cup2BoundaryIdx2 n hn9)) hc3_ne
          have hdrop := bad_boundary_Ψ_drop_at_P1 s c3 hchange'
          simpa [ΨLocalAfter, ΨLocalBefore, psiLocalP1After, psiLocalP1Before, ΨTerm, s, c3, hb6,
            hc3, left_right_eq_self]
            using hdrop
        · have hi2 : i.1 = 2 := by omega
          have hi : i = cup2BoundaryIdx2 n hn9 := by
            apply Fin.ext
            simp [cup2BoundaryIdx2, hi2]
          subst hi
          let s := cup2Boundary6 n hn4 hn9 c
          let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
          let c4 := stateAsFin3 n hn4 c (right (right (cup2BoundaryIdx2 n hn9)))
          have hb6 :
              cup2Boundary6 n hn4 hn9
                  (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
                boundarySuccP2 s c3 := by
            simpa [s, c3] using cup2Boundary6_move_eq_boundarySuccP2 n hn4 hn9 c
          have hchange' : (boundarySuccP2 s c3).encode ≠ s.encode := by
            simpa [cup2BoundaryState, s, c3, hb6] using hchange
          have hc3_ne : right (cup2BoundaryIdx2 n hn9) ≠ cup2BoundaryIdx2 n hn9 := by
            intro h
            have hval := congrArg Fin.val h
            have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
              simp [cup2BoundaryIdx2]
              omega
            rw [right_val_of_not_top htop] at hval
            simp [cup2BoundaryIdx2] at hval
          have hc4_ne : right (right (cup2BoundaryIdx2 n hn9)) ≠ cup2BoundaryIdx2 n hn9 := by
            intro h
            have hval := congrArg Fin.val h
            have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
              simp [cup2BoundaryIdx2]
              omega
            have htop' : (right (cup2BoundaryIdx2 n hn9)).1 + 1 ≠ n := by
              rw [right_val_of_not_top htop]
              simp [cup2BoundaryIdx2]
              omega
            rw [right_val_of_not_top htop', right_val_of_not_top htop] at hval
            simp [cup2BoundaryIdx2] at hval
          have hc3 :
              stateAsFin3 n hn4
                  (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))
                  (right (cup2BoundaryIdx2 n hn9)) = c3 := by
            simpa [c3] using
              stateAsFin3_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9)
                (right (cup2BoundaryIdx2 n hn9)) hc3_ne
          have hc4 :
              stateAsFin3 n hn4
                  (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))
                  (right (right (cup2BoundaryIdx2 n hn9))) = c4 := by
            simpa [c4] using
              stateAsFin3_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9)
                (right (right (cup2BoundaryIdx2 n hn9))) hc4_ne
          have hdrop3 := bad_boundary_Ψ_drop_at_P2 s c3 hchange'
          have hdrop : psiLocalP2After s c3 c4 < psiLocalP2Before s c3 c4 := by
            have hc4_cases : c4 = f0 ∨ c4 = f1 ∨ c4 = f2 := by
              have hc4v : c4.1 = 0 ∨ c4.1 = 1 ∨ c4.1 = 2 := by omega
              rcases hc4v with h | h | h
              · left
                apply Fin.ext
                simpa [f0] using h
              · right
                left
                apply Fin.ext
                simpa [f1] using h
              · right
                right
                apply Fin.ext
                simpa [f2] using h
            rcases hc4_cases with h | h | h
            · simpa [h] using hdrop3.1
            · simpa [h] using hdrop3.2.1
            · simpa [h] using hdrop3.2.2
          simpa [ΨLocalAfter, ΨLocalBefore, psiLocalP2After, psiLocalP2Before, ΨTerm, s, c3, c4,
            hb6, hc3, hc4, left_right_eq_self]
            using hdrop
    · by_cases hiN3 : i.1 = n - 3
      · have hi : i = cup2BoundaryIdxN3 n hn9 := by
          apply Fin.ext
          simp [cup2BoundaryIdxN3, hiN3]
        subst hi
        let s := cup2Boundary6 n hn4 hn9 c
        let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
        let cn5 := stateAsFin3 n hn4 c (left (left (cup2BoundaryIdxN3 n hn9)))
        have hb6 :
            cup2Boundary6 n hn4 hn9
                (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
              boundarySuccPN3 s cn4 := by
          simpa [s, cn4] using cup2Boundary6_move_eq_boundarySuccPN3 n hn4 hn9 c
        have hchange' : (boundarySuccPN3 s cn4).encode ≠ s.encode := by
          simpa [cup2BoundaryState, s, cn4, hb6] using hchange
        have hcn4_ne : left (cup2BoundaryIdxN3 n hn9) ≠ cup2BoundaryIdxN3 n hn9 := by
          intro h
          have hval := congrArg Fin.val h
          have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
            simp [cup2BoundaryIdxN3]
            omega
          rw [left_val_of_ne_zero h0] at hval
          simp [cup2BoundaryIdxN3] at hval
          omega
        have hcn5_ne : left (left (cup2BoundaryIdxN3 n hn9)) ≠ cup2BoundaryIdxN3 n hn9 := by
          intro h
          have hval := congrArg Fin.val h
          have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
            simp [cup2BoundaryIdxN3]
            omega
          have h0' : (left (cup2BoundaryIdxN3 n hn9)).1 ≠ 0 := by
            rw [left_val_of_ne_zero h0]
            simp [cup2BoundaryIdxN3]
            omega
          rw [left_val_of_ne_zero h0', left_val_of_ne_zero h0] at hval
          simp [cup2BoundaryIdxN3] at hval
          omega
        have hcn4 :
            stateAsFin3 n hn4
                (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))
                (left (cup2BoundaryIdxN3 n hn9)) = cn4 := by
          simpa [cn4] using
            stateAsFin3_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9)
              (left (cup2BoundaryIdxN3 n hn9)) hcn4_ne
        have hcn5 :
            stateAsFin3 n hn4
                (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))
                (left (left (cup2BoundaryIdxN3 n hn9))) = cn5 := by
          simpa [cn5] using
            stateAsFin3_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9)
              (left (left (cup2BoundaryIdxN3 n hn9))) hcn5_ne
        have hdrop3 := bad_boundary_Ψ_drop_at_PN3 s cn4 hchange'
        have hdrop : psiLocalPN3After s cn5 cn4 < psiLocalPN3Before s cn5 cn4 := by
          have hcn5_cases : cn5 = f0 ∨ cn5 = f1 ∨ cn5 = f2 := by
            have hcn5v : cn5.1 = 0 ∨ cn5.1 = 1 ∨ cn5.1 = 2 := by omega
            rcases hcn5v with h | h | h
            · left
              apply Fin.ext
              simpa [f0] using h
            · right
              left
              apply Fin.ext
              simpa [f1] using h
            · right
              right
              apply Fin.ext
              simpa [f2] using h
          rcases hcn5_cases with h | h | h
          · simpa [h] using hdrop3.1
          · simpa [h] using hdrop3.2.1
          · simpa [h] using hdrop3.2.2
        simpa [ΨLocalAfter, ΨLocalBefore, psiLocalPN3After, psiLocalPN3Before, ΨTerm, s, cn4, cn5,
          hb6, hcn4, hcn5, right_left_eq_self]
          using hdrop
      · by_cases hiN2 : i.1 = n - 2
        · have hi : i = cup2BoundaryIdxN2 n hn9 := by
            apply Fin.ext
            simp [cup2BoundaryIdxN2, hiN2]
          subst hi
          let s := cup2Boundary6 n hn4 hn9 c
          let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
          have hb6 :
              cup2Boundary6 n hn4 hn9
                  (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
                boundarySuccPN2 s := by
            simpa [s] using cup2Boundary6_move_eq_boundarySuccPN2 n hn4 hn9 c
          have hchange' : (boundarySuccPN2 s).encode ≠ s.encode := by
            simpa [cup2BoundaryState, s, hb6] using hchange
          have hcn4_ne : left (cup2BoundaryIdxN3 n hn9) ≠ cup2BoundaryIdxN2 n hn9 := by
            intro h
            have hval := congrArg Fin.val h
            have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
              simp [cup2BoundaryIdxN3]
              omega
            rw [left_val_of_ne_zero h0] at hval
            simp [cup2BoundaryIdxN2, cup2BoundaryIdxN3] at hval
            omega
          have hcn4 :
              stateAsFin3 n hn4
                  (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))
                  (left (cup2BoundaryIdxN3 n hn9)) = cn4 := by
            simpa [cn4] using
              stateAsFin3_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9)
                (left (cup2BoundaryIdxN3 n hn9)) hcn4_ne
          have hdrop := bad_boundary_Ψ_drop_at_PN2 s cn4 hchange'
          simpa [ΨLocalAfter, ΨLocalBefore, psiLocalPN2After, psiLocalPN2Before, ΨTerm, s, cn4,
            hb6, hcn4, right_left_eq_self]
            using hdrop
        · have hiN1 : i.1 = n - 1 := by omega
          have hi : i = cup2BoundaryIdxN1 n hn9 := by
            apply Fin.ext
            simp [cup2BoundaryIdxN1, hiN1]
          subst hi
          let s := cup2Boundary6 n hn4 hn9 c
          have hb6 :
              cup2Boundary6 n hn4 hn9
                  (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
                boundarySuccPN1 s := by
            simpa [s] using cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c
          have hchange' : (boundarySuccPN1 s).encode ≠ s.encode := by
            simpa [cup2BoundaryState, s, hb6] using hchange
          have hdrop := bad_boundary_Ψ_drop_at_PN1 s hchange'
          simpa [ΨLocalAfter, ΨLocalBefore, psiLocalPN1After, psiLocalPN1Before, ΨTerm, s, hb6]
            using hdrop
  rw [Ψ_move_split n hn4 hn9 c i, Ψ_split n hn4 hn9 c i, Ψ_rest_move_eq n hn4 hn9 c i]
  omega

/-- Any bad step whose boundary projection changes outside the 617-edge relation
forces a strict drop in the syntactic potential. -/
theorem bad_boundary_non_dag_Ψ_drop
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hbad : badStep (cup2System n hn4) (cup2GoodCycle n hn4) c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (_hnonDAG : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    Ψ n hn4 hn9 c' < Ψ n hn4 hn9 c := by
  exact bad_boundary_all_Ψ_drop n hn4 hn9 hbad hchange

/-- Outer TP-preserving bad-step layer where `Ψ` replaces `PhiFull`.
    The inner `cup2CPhiStep` well-foundedness proof is unchanged. -/
def cup2SyntheticOuterStep (n : Nat) (hn4 : 4 ≤ n)
    (c' c : Config (cup2Spec n hn4)) : Prop :=
  badStep (cup2System n hn4) (cup2GoodCycle n hn4) c' c ∧
    cup2TpInvariant n hn4 c' = cup2TpInvariant n hn4 c

/-- Every TP-preserving bad step is either a boundary-changing 617-edge step,
    a boundary-changing non-617 step on which `Ψ` strictly drops,
    or a boundary-fixed step. -/
theorem cup2SyntheticOuterStep_cases
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2SyntheticOuterStep n hn4 c' c) :
    ((cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c) ∧
        sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
          (cup2BoundaryState n hn4 hn9 c)) ∨
      ((cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c) ∧
        ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
          (cup2BoundaryState n hn4 hn9 c) ∧
        Ψ n hn4 hn9 c' < Ψ n hn4 hn9 c) ∨
      cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c := by
  rcases hstep with ⟨hbad, _htp⟩
  by_cases hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c
  · exact Or.inr (Or.inr hfixed)
  · by_cases hedge : sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)
    · exact Or.inl ⟨hfixed, hedge⟩
    · exact Or.inr (Or.inl ⟨hfixed, hedge,
        bad_boundary_non_dag_Ψ_drop n hn4 hn9 hbad hfixed hedge⟩)

end LeanMn
