/-
  Quick test: can native_decide evaluate cup2PhiFull at n=9?
-/
import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SixTuple

namespace LeanMn

-- Test: is cup2CPhiStep decidable at n=9?
-- First, a trivial test: check that cup2PhiFull is computable at a specific config
-- We just need native_decide to not time out.

-- Step 1: Small test — check a single value
-- example : cup2PhiFull 5 (by omega) (fun _ => ⟨0, by omega⟩) = 0 := by native_decide

-- Step 2: Try the actual bridge at n=9
-- This quantifies over all configs, which is expensive.
-- Let's test just the statement shape first.

-- For cphi_bridge, we need: for all configs c and movers i at n=9,
-- if it's a CPhiStep that changes the boundary, then the 6-tuple edge is in the 617 set.
-- But CPhiStep involves cup2PhiFull, and evaluating that for each config pair is expensive.

-- Alternative approach: just check that for boundary-changing TP-preserving bad steps,
-- either the 6-tuple edge is in the 617 set, or cup2PhiFull drops.
-- This avoids needing the full CPhiStep predicate.

theorem cphi_bridge_n9_full :
    ∀ (c : Config (cup2Spec 9 (by omega))) (i : Fin 9),
    privileged (cup2System 9 (by omega)) c i →
    ¬ (c ∈ (cup2GoodCycle 9 (by omega)).configs) →
    ¬ (move (cup2System 9 (by omega)) c i ∈ (cup2GoodCycle 9 (by omega)).configs) →
    cup2TpInvariant 9 (by omega) (move (cup2System 9 (by omega)) c i) =
      cup2TpInvariant 9 (by omega) c →
    cup2BoundaryState 9 (by omega) (by omega)
      (move (cup2System 9 (by omega)) c i) ≠
      cup2BoundaryState 9 (by omega) (by omega) c →
    -- Either the 6-tuple edge is valid, or cup2PhiFull drops
    sixTupleEdge
      (cup2BoundaryState 9 (by omega) (by omega) (move (cup2System 9 (by omega)) c i))
      (cup2BoundaryState 9 (by omega) (by omega) c) ∨
    cup2PhiFull 9 (by omega) (move (cup2System 9 (by omega)) c i) <
      cup2PhiFull 9 (by omega) c := by
  native_decide

end LeanMn
