import LeanMn.Ring
import Mathlib.Data.List.OfFn

namespace LeanMn.SmallN.LowerBound

/-- Small-`n` lower-bound targets for `n = 5,6,7,8`. -/
def n5Target : Nat := 96
def n6Target : Nat := 288
def n7Target : Nat := 864
def n8Target : Nat := 2592

/-- The ordered state profile of a ring specification. -/
def profileList (rs : RingSpec) : List Nat :=
  List.ofFn rs.m

/-- Ordered `n = 5` profiles are convenient enough to name directly. -/
def n5ProfileList (m : Fin 5 → Nat) : List Nat :=
  [m 0, m 1, m 2, m 3, m 4]

/-- Ordered `n = 6` profiles are convenient enough to name directly. -/
def n6ProfileList (m : Fin 6 → Nat) : List Nat :=
  [m 0, m 1, m 2, m 3, m 4, m 5]

@[simp] theorem n5Target_value : n5Target = 96 := rfl
@[simp] theorem n6Target_value : n6Target = 288 := rfl
@[simp] theorem n7Target_value : n7Target = 864 := rfl
@[simp] theorem n8Target_value : n8Target = 2592 := rfl

@[simp] theorem n5ProfileList_length (m : Fin 5 → Nat) :
    (n5ProfileList m).length = 5 := by
  simp [n5ProfileList]

@[simp] theorem n6ProfileList_length (m : Fin 6 → Nat) :
    (n6ProfileList m).length = 6 := by
  simp [n6ProfileList]

end LeanMn.SmallN.LowerBound
