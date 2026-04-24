/-
  Convergence/Cup2Converges.lean — Unconditional CUP-2 convergence for all n ≥ 4

  Combines:
  - Computational convergence proofs for n = 4..8 (SmallN/Cup2Convergence.lean)
  - Analytical convergence for n ≥ 9 via two-level potential (Main.lean)
-/
import LeanMn.Convergence.Main
import LeanMn.SmallN.Cup2Convergence

namespace LeanMn

/-! ### Unconditional CUP-2 convergence for all n ≥ 4 -/

theorem cup2Converges (n : Nat) (hn : 4 ≤ n) :
    converges (cup2System n hn) (cup2GoodCycle n hn) := by
  by_cases h9 : 9 ≤ n
  · exact cup2Converges_ge9 n hn h9
  · push_neg at h9
    -- n ∈ {4, 5, 6, 7, 8}
    interval_cases n <;> first
      | exact cup2Converges4
      | exact cup2Converges5
      | exact cup2Converges6
      | exact cup2Converges7
      | exact cup2Converges8

end LeanMn
