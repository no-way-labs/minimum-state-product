/-
  NormalFormBridge.lean — Bridge theorems to break PhaseExtraction ↔ CaseObstructionsCore cycle

  Provides `palindromic_phase_ec_bridge` and `subThreshold_binary_core_false_bridge`
  with explicit cycle-type callbacks. The proof bodies are sorry'd — they are
  identical to `palindromic_phase_ec` and `subThreshold_binary_core_false` in
  PhaseExtraction.lean. The sorry disappears when the palindromic proof is ported.

  Import chain:
    NormalFormBridge imports PhaseExtractionBase (safe, no cycle)
    CaseObstructionsCore imports NormalFormBridge (safe, NormalFormBridge doesn't import COC)
-/
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase
import LeanMn.LowerBound.Archive.EntryConflict.PhaseExtractionClean

namespace LeanMn

variable {sys : System}

/-- Bridge version of `palindromic_phase_ec` from PhaseExtraction.lean.

    For a ternary processor t with both binary neighbors, in a phase interval
    where no mechanism (Both-Even, Toggle-FR-L, Toggle-FR-R) triggers,
    derive `hasEntryConflict gc` using the cycle-type callbacks.

    The 4 callbacks break the import cycle: they are proved in
    CaseObstructionsCore.lean and threaded through from callers there.

    The sorry here is the palindromic proof body — when filled, all
    downstream sorrys in CaseObstructionsCore close automatically. -/
theorem palindromic_phase_ec_bridge
    (gc : GoodCycle sys)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2)
    (hbR : sys.rs.m (right t) = 2)
    (phase : TernaryPhase gc t)
    (hnormal : let J := gc.intervalFireCount (left t) phase.a.val phase.s.val
               let K := gc.intervalFireCount (right t) phase.a.val phase.s.val
               ¬((Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)))
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hn : sys.rs.n ≥ 9)
    (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    -- The 4 cycle-type callbacks:
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    hasEntryConflict gc := by
  exfalso
  exact subThreshold_binary_core_false_clean gc hn hsub h3bin hconv hno_safe
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

/-- Bridge version of `subThreshold_binary_core_false` from PhaseExtraction.lean.

    For any good cycle on a sub-threshold ring with ≥ 3 binary processors,
    derive False using phase extraction + the 4 cycle-type callbacks.

    Routes through both_binary_neighbors_false (when a sandwiched ternary
    with both binary neighbors fires) or no_firing_both_binary_neighbors_false
    (when no such processor fires). -/
theorem subThreshold_binary_core_false_bridge
    (gc : GoodCycle sys) (hn : sys.rs.n ≥ 9)
    (hsub : subThreshold sys.rs)
    (h3bin : hasGe3Binary sys.rs)
    (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    -- The 4 cycle-type callbacks:
    (hConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hNonConsecZW : gc.zeroWinding → 0 < gc.cwStepCount →
      (¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) → False)
    (hSweepFalse : gc.isSweep → False)
    (hOddNonUnifFalse : gc.isOddWinding → ¬gc.uniformDirection → False) :
    False := by
  exact subThreshold_binary_core_false_clean gc hn hsub h3bin hconv hno_safe
    hConsecZW hNonConsecZW hSweepFalse hOddNonUnifFalse

end LeanMn
