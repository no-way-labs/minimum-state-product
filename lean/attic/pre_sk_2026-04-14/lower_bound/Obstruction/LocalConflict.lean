/-
  Obstruction/LocalConflict.lean — Local role collision (entry conflict) as obstruction.

  Re-exports `hasEntryConflict` and `entryConflict_impossible` from GoodCycleBasics,
  and provides helpers that package entry conflict into the Obstruction type.
-/
import LeanMn.LowerBound.Obstruction.Core

namespace LeanMn

variable {sys : System}

/-- An entry conflict gives the left disjunct of Obstruction. -/
theorem entryConflict_gives_obstruction
    (gc : GoodCycle sys) (h : hasEntryConflict gc) :
    Obstruction sys gc :=
  Or.inl h

/-- An entry conflict directly contradicts convergence. -/
theorem entryConflict_not_converges
    (gc : GoodCycle sys) (h : hasEntryConflict gc) :
    ¬converges sys gc :=
  fun _ => entryConflict_impossible gc h

end LeanMn
