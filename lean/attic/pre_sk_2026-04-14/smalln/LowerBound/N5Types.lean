import LeanMn.SmallN.LowerBound.Arithmetic

namespace LeanMn.SmallN.LowerBound

inductive N5ProfileTag where
  | allBinary
  | fourBinary3
  | fourBinary4
  | tailA
  | tailB
  | fourBinary5
  deriving DecidableEq, Fintype, Repr

/-- The six `n = 5` sub-threshold profile classes up to cyclic rotation. -/
def N5ProfileTag.representative : N5ProfileTag → List Nat
  | .allBinary => [2, 2, 2, 2, 2]
  | .fourBinary3 => [2, 2, 2, 2, 3]
  | .fourBinary4 => [2, 2, 2, 2, 4]
  | .tailA => [2, 2, 2, 3, 3]
  | .tailB => [2, 2, 3, 2, 3]
  | .fourBinary5 => [2, 2, 2, 2, 5]

/-- The six `n = 5` sub-threshold profile classes up to cyclic rotation. -/
def n5RotationProfiles : List (List Nat) :=
  [
    N5ProfileTag.representative .allBinary,
    N5ProfileTag.representative .fourBinary3,
    N5ProfileTag.representative .fourBinary4,
    N5ProfileTag.representative .tailA,
    N5ProfileTag.representative .tailB,
    N5ProfileTag.representative .fourBinary5
  ]

def N5ProfileTag.rotationOrbitList (tag : N5ProfileTag) : List (List Nat) :=
  (List.range 5).map fun k => (N5ProfileTag.representative tag).rotate k

def N5ProfileTag.rotationOrbitSet (tag : N5ProfileTag) : Finset (List Nat) :=
  (N5ProfileTag.rotationOrbitList tag).toFinset

def n5RotationOrbitList : List (List Nat) :=
  ((n5RotationProfiles.map fun xs =>
      (List.range 5).map fun k => xs.rotate k).foldr List.append []).eraseDups

def n5RotationOrbitSet : Finset (List Nat) :=
  n5RotationOrbitList.toFinset

theorem n5ExactProfiles_eq_rotationOrbitSet :
    n5ExactProfiles = n5RotationOrbitSet := by
  native_decide

def n5TaggedProfileSet : Finset (List Nat) :=
  ((Finset.univ : Finset N5ProfileTag).biUnion N5ProfileTag.rotationOrbitSet)

theorem n5ExactProfiles_eq_taggedProfileSet :
    n5ExactProfiles = n5TaggedProfileSet := by
  native_decide

def n5ProfileTag? (xs : List Nat) : Option N5ProfileTag :=
  if xs ∈ N5ProfileTag.rotationOrbitSet .allBinary then
    some .allBinary
  else if xs ∈ N5ProfileTag.rotationOrbitSet .fourBinary3 then
    some .fourBinary3
  else if xs ∈ N5ProfileTag.rotationOrbitSet .fourBinary4 then
    some .fourBinary4
  else if xs ∈ N5ProfileTag.rotationOrbitSet .tailA then
    some .tailA
  else if xs ∈ N5ProfileTag.rotationOrbitSet .tailB then
    some .tailB
  else if xs ∈ N5ProfileTag.rotationOrbitSet .fourBinary5 then
    some .fourBinary5
  else
    none

theorem n5ProfileTag?_spec {xs : List Nat} {tag : N5ProfileTag}
    (h : n5ProfileTag? xs = some tag) :
    xs ∈ N5ProfileTag.rotationOrbitSet tag := by
  cases tag <;> unfold n5ProfileTag? at h <;> split_ifs at h <;> simp_all [N5ProfileTag.rotationOrbitSet]

end LeanMn.SmallN.LowerBound
