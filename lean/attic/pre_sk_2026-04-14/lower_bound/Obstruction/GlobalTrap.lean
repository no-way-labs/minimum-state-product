/-
  Obstruction/GlobalTrap.lean — Constructors for GlobalObstruction from proven machinery.

  Currently provides one constructor: wrapping the Shadow Cycle Mirror Theorem
  (Shadow/Theorem.lean) to produce a GlobalObstruction for any WaterfallCycle
  on a ring with n ≥ 5 and ≥ 3 binary processors.
-/
import LeanMn.LowerBound.Obstruction.Core
import LeanMn.LowerBound.Shadow.Theorem

namespace LeanMn

variable {sys : System}

/-- The shadow cycle mirror theorem produces a GlobalObstruction for any
    WaterfallCycle in a system with ≥ 3 binary processors and n ≥ 5. -/
theorem shadow_gives_globalObstruction
    (wc : WaterfallCycle sys)
    (hn : sys.rs.n ≥ 5)
    (_h3bin : hasGe3Binary sys.rs) :
    GlobalObstruction sys wc.toGoodCycle := by
  let sc := canonicalShadowConstruction wc
  have hentry := canonicalShadow_entry_of_local_context wc (by omega)
  have hclosure : shadowClosure sc := by
    simpa [sc] using canonicalShadowClosure_of_entryCore wc (by omega) hentry
  have hdistinct : shadowDistinct sc := by
    simpa [sc] using canonicalShadowDistinct wc (by omega)
  have hdisjoint : shadowDisjoint sc := by
    simpa [sc] using canonicalShadowDisjoint wc (by omega)
  rcases shadow_gives_trap wc sc hclosure hdistinct hdisjoint with ⟨st, _⟩
  exact GlobalObstruction.shadowTrap st

/-- Corollary: any WaterfallCycle with ≥ 3 binary and n ≥ 5 produces an
    Obstruction (the right disjunct). -/
theorem shadow_gives_obstruction
    (wc : WaterfallCycle sys)
    (hn : sys.rs.n ≥ 5)
    (h3bin : hasGe3Binary sys.rs) :
    Obstruction sys wc.toGoodCycle :=
  Or.inr (shadow_gives_globalObstruction wc hn h3bin)

end LeanMn
