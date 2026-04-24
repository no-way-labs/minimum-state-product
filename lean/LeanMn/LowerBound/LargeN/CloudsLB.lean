/-
  LowerBound/LargeN/CloudsLB.lean — n≥9 lower bound via the Clouds theorem

  Instantiates the regime-independent SK framework in
  `LowerBound/SK/CloudsTheorem.lean` against the n≥9 bound
  `M_n = 4 · 3^(n-2)`. At `n ≥ 9` this matches the sharp M_n,
  so there is no gap (unlike the small-n regime handled in
  `LowerBound/SmallN/CloudsLB.lean`).

  This is the full-Clouds n≥9 `M_n_lower`: `(SK gc).Nonempty`
  → `¬ converges gc` (T1 soundness) → `¬ valid`.
-/
import LeanMn.LowerBound.SK.CloudsTheorem

namespace LeanMn.LowerBound.LargeN

open LeanMn LeanMn.SK

variable {sys : System}

/-- n≥9 M_n lower bound (Clouds form). For `n ≥ 9` and any system
    with state product strictly less than `4 · 3^(n-2)`, the system
    is not valid.

    Proof: `sk_nonempty_large_n` delivers a sink in every good cycle's
    SK; T1 soundness (`not_converges_of_SK_nonempty`) converts the
    sink into non-convergence, contradicting `valid`. -/
theorem M_n_lower_clouds_large_n
    (sys : System) (hn : 9 ≤ sys.rs.n)
    (hsub : stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)) :
    ¬ valid sys := by
  intro hvalid
  obtain ⟨gc, hconv⟩ := hvalid
  exact not_converges_of_SK_nonempty gc (sk_nonempty_large_n gc hsub hn) hconv

end LeanMn.LowerBound.LargeN
