/-
  LowerBound/SK/PhaseChange.lean — Phase change at n=9 (T5)

  Targets doc reference:
    docs/lean_docs/sk/sk_invariant_lean_targets_2026-04-14.md §3 (T5)

  T5 records the regime split: the canonical CLB witness for n ≥ 9 has
  k = 2 binary positions (endpoints only), so T2 (which requires k ≥ 3)
  does not apply to it directly. The witness is handled by T4 instead.
-/
import LeanMn.LowerBound.SK.Witness
import LeanMn.LowerBound.SK.BinaryCubeProj

namespace LeanMn.SK

/-- The CLB witness at `n ≥ 9` has exactly 2 binary positions: the
    two endpoints `0` and `n - 1`. -/
theorem witness_binary_count
    (n : Nat) (hn : 9 ≤ n) :
    ((List.finRange n).filter
      (fun i => witnessMs n hn i == 2)).length = 2 := by
  sorry

end LeanMn.SK
