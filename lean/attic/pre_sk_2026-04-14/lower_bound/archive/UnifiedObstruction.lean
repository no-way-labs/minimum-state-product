/-
  UnifiedObstruction.lean — Unified obstruction strategy for the lower bound.

  States the master theorem: every sub-threshold good cycle must produce
  either a local role collision (hasEntryConflict) or a global trap
  (GlobalObstruction).

  The body of `unavoidable_obstruction` is sorry'd — this is the Phase 3
  target. Once proved, it replaces the cycle-type dispatch in
  ZeroWindingAssembly/CaseObstructionsCore.

  Architecture:
    Theorem.lean → UnifiedObstruction.lean → Obstruction/{Core, GlobalTrap, LocalConflict}
-/
import LeanMn.LowerBound.Obstruction.Core
import LeanMn.LowerBound.Obstruction.GlobalTrap
import LeanMn.LowerBound.Obstruction.LocalConflict

namespace LeanMn

variable {sys : System}

/-- **Unavoidable Obstruction Theorem.**
    Every good cycle in a sub-threshold system with n ≥ 9 and ≥ 3 binary
    processors must exhibit either a local role collision or a global trap.

    This is the central theorem of the lower bound proof. Its body is the
    Phase 3 target — internal cycle-type analysis is allowed as private
    search, but the public interface returns only the obstruction disjunction. -/
theorem unavoidable_obstruction
    (hn : sys.rs.n ≥ 9)
    (gc : GoodCycle sys)
    (hsub : subThreshold sys.rs) :
    Obstruction sys gc := by
  sorry -- Phase 3: prove every sub-threshold good cycle has EC or global trap

/-- **Lower bound via unified obstruction.**
    Assembly: `unavoidable_obstruction` gives EC ∨ GlobalObstruction,
    then `Obstruction.impossible` closes it. -/
theorem subThreshold_impossible_unified
    (hn : sys.rs.n ≥ 9)
    (gc : GoodCycle sys)
    (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) :
    False :=
  Obstruction.impossible gc hconv (unavoidable_obstruction hn gc hsub)

end LeanMn
