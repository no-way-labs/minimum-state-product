/-
  Obstruction/NonZeroWinding.lean — Live non-zero-winding obstruction interfaces

  These are the de-archived sweep / odd-winding obstruction fronts used by
  both the case files and the non-consecutive split. The archive wrappers
  were structurally removed in Phase 1; the remaining math now lives here.
-/
import LeanMn.LowerBound.CycleTypes
import LeanMn.LowerBound.Proof.SafeProcessor

namespace LeanMn

variable {sys : System}

/-- Contrapositive: non-zero winding forbids a safe processor. -/
private theorem no_safeProcessor_of_nonZeroWinding
    (gc : GoodCycle sys) (hnonzero : ¬gc.zeroWinding) :
    ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q := by
  intro ⟨q, hq⟩
  exact hnonzero (safeProcessor_implies_zeroWinding gc q hq)

/-- **Sweep obstruction.**

    Live replacement for the old archive wrapper. Under `isSweep`, a
    converging sub-threshold good cycle with `n ≥ 9` and `≥ 3` binary
    processors is impossible. -/
theorem nonZeroWinding_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hnonzero : ¬gc.zeroWinding) :
    False := by
  -- TODO (Phase 4): rebuild the live non-zero-winding closure here.
  -- This is the single shared sweep/odd obstruction front.
  sorry

/-- **Sweep obstruction.**

    Live replacement for the old archive wrapper. Under `isSweep`, a
    converging sub-threshold good cycle with `n ≥ 9` and `≥ 3` binary
    processors is impossible. -/
theorem sweep_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hsweep : gc.isSweep)
    (_h3bin : hasGe3Binary sys.rs) :
    False := by
  apply nonZeroWinding_obstruction hn gc hconv hsub
  intro hzero
  unfold GoodCycle.zeroWinding at hzero
  unfold GoodCycle.isSweep at hsweep
  have h0 : (totalDisplacement gc).natAbs = 0 := by
    rw [hzero]
    decide
  omega

/-- **Odd-winding non-uniform obstruction.**

    Live replacement for the old archive wrapper. Under odd winding and
    non-uniform direction, a converging sub-threshold good cycle with
    `n ≥ 9` and `≥ 3` binary processors is impossible. -/
theorem oddWinding_nonUniform_obstruction
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (hodd : gc.isOddWinding)
    (_hnonunif : ¬gc.uniformDirection) (_h3bin : hasGe3Binary sys.rs) :
    False := by
  apply nonZeroWinding_obstruction hn gc hconv hsub
  intro hzero
  unfold GoodCycle.zeroWinding at hzero
  unfold GoodCycle.isOddWinding at hodd
  have h0 : (totalDisplacement gc).natAbs = 0 := by
    rw [hzero]
    decide
  omega

end LeanMn
