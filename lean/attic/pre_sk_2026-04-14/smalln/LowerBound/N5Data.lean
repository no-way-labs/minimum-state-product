import LeanMn.SmallN.LowerBound.N5Types

namespace LeanMn.SmallN.LowerBound

noncomputable def n5ExactProfilesList : List (List Nat) :=
  n5ExactProfiles.toList

theorem n5ExactProfiles_card :
    n5ExactProfiles.card = 26 := by
  native_decide

theorem n5RotationOrbitSet_card :
    n5RotationOrbitSet.card = 26 := by
  rw [← n5ExactProfiles_eq_rotationOrbitSet]
  exact n5ExactProfiles_card

end LeanMn.SmallN.LowerBound
