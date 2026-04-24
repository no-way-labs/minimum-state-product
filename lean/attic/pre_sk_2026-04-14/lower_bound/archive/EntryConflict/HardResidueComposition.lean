namespace LeanMn

/--
The `LeftSameHardResidue`, `LeftCrossHardResidue`, `RightCrossHardResidue`,
and `RightSameHardResidue` names in `AllNormalFormFalse` are local
`let ... : Prop := ...` aliases, so the extracted theorem is generic over the
corresponding propositions.
-/
theorem hard_residue_boundary_composition_false
    {LeftSameHardResidue LeftCrossHardResidue
      RightCrossHardResidue RightSameHardResidue : Prop} :
    LeftSameHardResidue ∨ LeftCrossHardResidue ∨
      RightCrossHardResidue ∨ RightSameHardResidue → False := by
  intro hhard
  sorry

end LeanMn
