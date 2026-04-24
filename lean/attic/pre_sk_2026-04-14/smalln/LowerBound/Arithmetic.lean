import LeanMn.LowerBound.GoodCycleBasics
import LeanMn.SmallN.LowerBound.Core
import Mathlib.Algebra.BigOperators.Fin

namespace LeanMn.SmallN.LowerBound

/-- The exact multiset shapes below the `n = 5` target, listed in nondecreasing order. -/
def n5CanonicalProfileMultisets : List (List Nat) :=
  [
    [2, 2, 2, 2, 2],
    [2, 2, 2, 2, 3],
    [2, 2, 2, 2, 4],
    [2, 2, 2, 3, 3],
    [2, 2, 2, 2, 5]
  ]

/-- The exact multiset shapes below the `n = 6` target, listed in nondecreasing order. -/
def n6CanonicalProfileMultisets : List (List Nat) :=
  [
    [2, 2, 2, 2, 2, 2],
    [2, 2, 2, 2, 2, 3],
    [2, 2, 2, 2, 2, 4],
    [2, 2, 2, 2, 3, 3],
    [2, 2, 2, 2, 2, 5],
    [2, 2, 2, 2, 2, 6],
    [2, 2, 2, 2, 3, 4],
    [2, 2, 2, 3, 3, 3],
    [2, 2, 2, 2, 2, 7],
    [2, 2, 2, 2, 3, 5],
    [2, 2, 2, 2, 2, 8],
    [2, 2, 2, 2, 4, 4]
  ]

structure N5Offset where
  x0 : Fin 4
  x1 : Fin 4
  x2 : Fin 4
  x3 : Fin 4
  x4 : Fin 4
deriving DecidableEq, Fintype, Repr

structure N6Offset where
  x0 : Fin 7
  x1 : Fin 7
  x2 : Fin 7
  x3 : Fin 7
  x4 : Fin 7
  x5 : Fin 7
deriving DecidableEq, Fintype, Repr

def N5Offset.toProfile (t : N5Offset) : List Nat :=
  [t.x0.val + 2, t.x1.val + 2, t.x2.val + 2, t.x3.val + 2, t.x4.val + 2]

def N6Offset.toProfile (t : N6Offset) : List Nat :=
  [t.x0.val + 2, t.x1.val + 2, t.x2.val + 2, t.x3.val + 2, t.x4.val + 2, t.x5.val + 2]

/-- Exact ordered `n = 5` profiles with product below `96`. -/
def n5ExactProfiles : Finset (List Nat) :=
  (Finset.univ.image N5Offset.toProfile).filter fun xs => xs.prod < n5Target

/-- Exact ordered `n = 6` profiles with product below `288`. -/
def n6ExactProfiles : Finset (List Nat) :=
  (Finset.univ.image N6Offset.toProfile).filter fun xs => xs.prod < n6Target

private theorem n5_coord_le_five
    (m : Fin 5 → Nat) (hm : ∀ i, 2 ≤ m i)
    (hsub : m 0 * m 1 * m 2 * m 3 * m 4 < n5Target)
    (i : Fin 5) :
    m i ≤ 5 := by
  by_contra hgt
  have hi : 6 ≤ m i := by omega
  fin_cases i
  · have h1 := hm 1; have h2 := hm 2; have h3 := hm 3; have h4 := hm 4
    have hbound :
        96 ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
      calc
        96 ≤ 6 * 2 * 2 * 2 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul hi h1)
                h2)
              h3)
            h4
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h2 := hm 2; have h3 := hm 3; have h4 := hm 4
    have hbound :
        96 ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
      calc
        96 ≤ 2 * 6 * 2 * 2 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul h0 hi)
                h2)
              h3)
            h4
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h1 := hm 1; have h3 := hm 3; have h4 := hm 4
    have hbound :
        96 ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
      calc
        96 ≤ 2 * 2 * 6 * 2 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul h0 h1)
                hi)
              h3)
            h4
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h1 := hm 1; have h2 := hm 2; have h4 := hm 4
    have hbound :
        96 ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
      calc
        96 ≤ 2 * 2 * 2 * 6 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul h0 h1)
                h2)
              hi)
            h4
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h1 := hm 1; have h2 := hm 2; have h3 := hm 3
    have hbound :
        96 ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
      calc
        96 ≤ 2 * 2 * 2 * 2 * 6 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul h0 h1)
                h2)
              h3)
            hi
    exact (Nat.not_lt.mpr hbound) hsub

private theorem n6_coord_le_eight
    (m : Fin 6 → Nat) (hm : ∀ i, 2 ≤ m i)
    (hsub : m 0 * m 1 * m 2 * m 3 * m 4 * m 5 < n6Target)
    (i : Fin 6) :
    m i ≤ 8 := by
  by_contra hgt
  have hi : 9 ≤ m i := by omega
  fin_cases i
  · have h1 := hm 1; have h2 := hm 2; have h3 := hm 3; have h4 := hm 4; have h5 := hm 5
    have hbound :
        288 ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
      calc
        288 ≤ 9 * 2 * 2 * 2 * 2 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul
                  (Nat.mul_le_mul hi h1)
                  h2)
                h3)
              h4)
            h5
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h2 := hm 2; have h3 := hm 3; have h4 := hm 4; have h5 := hm 5
    have hbound :
        288 ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
      calc
        288 ≤ 2 * 9 * 2 * 2 * 2 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul
                  (Nat.mul_le_mul h0 hi)
                  h2)
                h3)
              h4)
            h5
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h1 := hm 1; have h3 := hm 3; have h4 := hm 4; have h5 := hm 5
    have hbound :
        288 ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
      calc
        288 ≤ 2 * 2 * 9 * 2 * 2 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul
                  (Nat.mul_le_mul h0 h1)
                  hi)
                h3)
              h4)
            h5
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h1 := hm 1; have h2 := hm 2; have h4 := hm 4; have h5 := hm 5
    have hbound :
        288 ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
      calc
        288 ≤ 2 * 2 * 2 * 9 * 2 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul
                  (Nat.mul_le_mul h0 h1)
                  h2)
                hi)
              h4)
            h5
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h1 := hm 1; have h2 := hm 2; have h3 := hm 3; have h5 := hm 5
    have hbound :
        288 ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
      calc
        288 ≤ 2 * 2 * 2 * 2 * 9 * 2 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul
                  (Nat.mul_le_mul h0 h1)
                  h2)
                h3)
              hi)
            h5
    exact (Nat.not_lt.mpr hbound) hsub
  · have h0 := hm 0; have h1 := hm 1; have h2 := hm 2; have h3 := hm 3; have h4 := hm 4
    have hbound :
        288 ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
      calc
        288 ≤ 2 * 2 * 2 * 2 * 2 * 9 := by norm_num
        _ ≤ m 0 * m 1 * m 2 * m 3 * m 4 * m 5 := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul
                  (Nat.mul_le_mul h0 h1)
                  h2)
                h3)
              h4)
            hi
    exact (Nat.not_lt.mpr hbound) hsub

theorem n5_profile_mem_exactProfiles
    (m : Fin 5 → Nat) (hm : ∀ i, 2 ≤ m i)
    (hsub : m 0 * m 1 * m 2 * m 3 * m 4 < n5Target) :
    n5ProfileList m ∈ n5ExactProfiles := by
  let t : N5Offset := {
    x0 := ⟨m 0 - 2, by
      have h0 := hm 0
      have h0' := n5_coord_le_five m hm hsub 0
      omega⟩
    x1 := ⟨m 1 - 2, by
      have h1 := hm 1
      have h1' := n5_coord_le_five m hm hsub 1
      omega⟩
    x2 := ⟨m 2 - 2, by
      have h2 := hm 2
      have h2' := n5_coord_le_five m hm hsub 2
      omega⟩
    x3 := ⟨m 3 - 2, by
      have h3 := hm 3
      have h3' := n5_coord_le_five m hm hsub 3
      omega⟩
    x4 := ⟨m 4 - 2, by
      have h4 := hm 4
      have h4' := n5_coord_le_five m hm hsub 4
      omega⟩
  }
  have ht : t.toProfile = n5ProfileList m := by
    simp [N5Offset.toProfile, n5ProfileList, t,
      Nat.sub_add_cancel (hm 0), Nat.sub_add_cancel (hm 1), Nat.sub_add_cancel (hm 2),
      Nat.sub_add_cancel (hm 3), Nat.sub_add_cancel (hm 4)]
  refine Finset.mem_filter.mpr ?_
  refine ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩
  · simpa [ht, n5Target, n5ProfileList, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsub

theorem n6_profile_mem_exactProfiles
    (m : Fin 6 → Nat) (hm : ∀ i, 2 ≤ m i)
    (hsub : m 0 * m 1 * m 2 * m 3 * m 4 * m 5 < n6Target) :
    n6ProfileList m ∈ n6ExactProfiles := by
  let t : N6Offset := {
    x0 := ⟨m 0 - 2, by
      have h0 := hm 0
      have h0' := n6_coord_le_eight m hm hsub 0
      omega⟩
    x1 := ⟨m 1 - 2, by
      have h1 := hm 1
      have h1' := n6_coord_le_eight m hm hsub 1
      omega⟩
    x2 := ⟨m 2 - 2, by
      have h2 := hm 2
      have h2' := n6_coord_le_eight m hm hsub 2
      omega⟩
    x3 := ⟨m 3 - 2, by
      have h3 := hm 3
      have h3' := n6_coord_le_eight m hm hsub 3
      omega⟩
    x4 := ⟨m 4 - 2, by
      have h4 := hm 4
      have h4' := n6_coord_le_eight m hm hsub 4
      omega⟩
    x5 := ⟨m 5 - 2, by
      have h5 := hm 5
      have h5' := n6_coord_le_eight m hm hsub 5
      omega⟩
  }
  have ht : t.toProfile = n6ProfileList m := by
    simp [N6Offset.toProfile, n6ProfileList, t,
      Nat.sub_add_cancel (hm 0), Nat.sub_add_cancel (hm 1), Nat.sub_add_cancel (hm 2),
      Nat.sub_add_cancel (hm 3), Nat.sub_add_cancel (hm 4), Nat.sub_add_cancel (hm 5)]
  refine Finset.mem_filter.mpr ?_
  refine ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩
  · simpa [ht, n6Target, n6ProfileList, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsub

end LeanMn.SmallN.LowerBound
