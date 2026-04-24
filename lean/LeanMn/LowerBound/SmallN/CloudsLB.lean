/-
  LowerBound/SmallN/CloudsLB.lean — Small-n lower bound via the Clouds theorem

  Instantiates the regime-independent SK framework in
  `LowerBound/SK/CloudsTheorem.lean` against the **sharp** small-n
  bound `M_n = 32 · 3^(n-4)` for `n ∈ {5, 6, 7, 8}`.

  **Why small-n needs its own wrapper.** At small `n`, sharp `M_n`
  is strictly less than `4 · 3^(n-2)` (the n≥9 bound). Valid
  self-stabilizing systems exist in the gap
  `[32·3^(n-4), 4·3^(n-2))` at small `n`, e.g.
    - n=5: ms=(2,2,2,3,4), product 96
    - n=6: ms=(2,2,2,3,3,3) family, product 216
    - n=7: ms=(2,2,2,2,3,3,3), product 432
    - n=8: ms=(2,2,2,3,3,3,3,3), product 1944
  Applying the n≥9 form of the Clouds theorem to a small-n system in
  the gap would falsely conclude `¬ valid`, contradicting the known
  small-n upper-bound witnesses. The wrapper must therefore dispatch
  on the strict `< 32·3^(n-4)` premise.

  Companion file: `LeanMn.LowerBound.LargeN.CloudsLB` handles `n ≥ 9`.
-/
import LeanMn.LowerBound.SK.CloudsTheorem

namespace LeanMn.LowerBound.SmallN

open LeanMn LeanMn.SK

/-- Small-n M_n lower bound (Clouds form). For `n ∈ {5, 6, 7, 8}`
    and any system with state product strictly less than the sharp
    `M_n = 32 · 3^(n-4)`, the system is not valid.

    Proof: `sk_nonempty_small_n` delivers a sink in every good cycle's
    SK; T1 soundness (`not_converges_of_SK_nonempty`) converts the
    sink into non-convergence, contradicting `valid`. -/
theorem M_n_lower_clouds_small_n
    (sys : System) (hn_lo : 5 ≤ sys.rs.n) (hn_hi : sys.rs.n ≤ 8)
    (hsub : stateProduct sys.rs < 32 * 3 ^ (sys.rs.n - 4)) :
    ¬ valid sys := by
  intro hvalid
  obtain ⟨gc, hconv⟩ := hvalid
  exact not_converges_of_SK_nonempty gc
    (sk_nonempty_small_n gc hsub hn_lo hn_hi) hconv

end LeanMn.LowerBound.SmallN
