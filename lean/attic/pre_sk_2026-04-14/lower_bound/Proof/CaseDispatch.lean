/-
  CaseDispatch.lean — Top-level case split for the lower bound

  Routes to case theorems: SafeProcessor, ZeroWinding, Sweep, OddWinding.
  ZERO CALLBACKS. Each case takes its hypothesis directly.
-/
import LeanMn.LowerBound.Proof.SafeProcessor
import LeanMn.LowerBound.Proof.ZeroWinding
import LeanMn.LowerBound.Proof.Sweep
import LeanMn.LowerBound.Proof.OddWinding

namespace LeanMn

variable {sys : System}

/-- **Sub-threshold impossibility.**

    Any good cycle in a converging sub-threshold system with n ≥ 9 is
    impossible. Routes to case theorems without callbacks.

    Case decomposition:
    1. Safe processor exists → safeProcessor_false
    2. Zero winding, cw = 0 → zeroWinding_cw0_false
    3. Zero winding, cw > 0 → zeroWinding_cwPos_false
    4. Sweep → sweep_false
    5. Odd winding → oddWinding_false -/
theorem subThreshold_impossible
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    (hconv : converges sys gc) (hsub : subThreshold sys.rs) : False := by
  have h3bin := subThreshold_ge3_binary sys.rs hsub
  -- Case 1: safe processor
  by_cases hsafe : ∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q
  · obtain ⟨q, hq⟩ := hsafe
    exact safeProcessor_false (by omega) gc hconv q hq
  · by_cases hzero : gc.zeroWinding
    · by_cases hcw : gc.cwStepCount = 0
      · -- Case 2: zero winding, cw = 0 (all-stay)
        exact zeroWinding_cw0_false (by omega) gc hconv hzero hcw
      · -- Case 3: zero winding, cw > 0
        exact zeroWinding_cwPos_false hn gc hconv hsafe hsub h3bin hzero (by omega)
    · by_cases hsweep : gc.isSweep
      · -- Case 4: sweep
        exact sweep_false hn gc hconv hsafe hsub h3bin hsweep
      · -- Case 5: odd winding (the only remaining case)
        rcases gc.zeroWinding_or_isOddWinding_of_not_sweep hsweep with hzw | hodd
        · exact absurd hzw hzero
        · by_cases hunif : gc.uniformDirection
          · exact absurd ⟨hunif, hodd⟩
              (gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary h3bin)
          · exact oddWinding_false hn gc hconv hsafe hsub h3bin hodd hunif

end LeanMn
