/-
  Obstruction/Core.lean — Unified obstruction interface for the lower bound proof.

  Two modes of impossibility:
  - Mode A: hasEntryConflict (local role collision) — already in GoodCycleBasics.lean
  - Mode B: GlobalObstruction (global alternative orbit / trap)

  Every sub-threshold convergent good cycle must produce one of these.
-/
import LeanMn.LowerBound.MNU

namespace LeanMn

variable {sys : System}

/-- A global obstruction to convergence: a structural reason why the system
    cannot converge to the given good cycle, beyond local role collision.

    Constructors:
    - `shadowTrap`: a closed cycle of non-good configurations that traps the adversary
    - (future: disjointGoodCycle, returnCone) -/
inductive GlobalObstruction (sys : System) (gc : GoodCycle sys) : Prop
  | shadowTrap (st : ShadowTrap sys gc) : GlobalObstruction sys gc

/-- A global obstruction implies non-convergence. -/
theorem GlobalObstruction.not_converges
    (h : GlobalObstruction sys gc) :
    ¬converges sys gc := by
  cases h with
  | shadowTrap st => exact shadowTrap_not_converges gc st

/-- The unified obstruction disjunction: either local role collision or global trap. -/
def Obstruction (sys : System) (gc : GoodCycle sys) : Prop :=
  hasEntryConflict gc ∨ GlobalObstruction sys gc

/-- Any obstruction under convergence yields False. -/
theorem Obstruction.impossible
    (gc : GoodCycle sys) (hconv : converges sys gc)
    (h : Obstruction sys gc) :
    False := by
  rcases h with hec | hglob
  · exact entryConflict_impossible gc hec
  · exact hglob.not_converges hconv

end LeanMn
