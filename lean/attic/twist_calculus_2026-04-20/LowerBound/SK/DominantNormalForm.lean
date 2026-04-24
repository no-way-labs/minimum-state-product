/-
  LowerBound/SK/DominantNormalForm.lean — Theorem A (DTNF, forward).

  Frozen signature: docs/lean_docs/sk/sk_theorem_package_freeze_2026-04-19.md §1.
  Slate reference: docs/lean_docs/sk/sk_twist_calculus_slate_2026-04-19.md §1.

  Forward DTNF only (Conjecture A′ = converse realisability is out
  of scope). The theorem is sorry-gated pending a combinatorial
  proof on the tube digraph; downstream users of DTNF (CTCL.lean)
  consume the `DominantWitness` structure directly.
-/
import LeanMn.LowerBound.SK.TwistCalculus
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LeanMn.SK.TwistCalculus

/-! ## Dominant witness

  In the dominant regime (DTNF-forward) a min closed anchored threading
  has exactly four `R_k` twists and two `L_k` twists with stretch
  balance `Σ kR = Σ kL`. -/

/-- A **DominantWitness** records the stretch multi-indices of the
    four R-twists and two L-twists, plus two facts:

    * `balance` — `Σ kR = Σ kL` (stretch-balance closure law);
    * `charge_decomp` — `totalCharge = 4 + Σ kR + 2 − Σ kL`,
      the explicit decomposition that `CTCL_from_witness` consumes.

    Existence of this structure is the statement of DTNF-forward. -/
structure DominantWitness (t : TwistData) where
  kR : Fin 4 → ℕ
  kL : Fin 2 → ℕ
  balance : (∑ i, (kR i : ℤ)) = (∑ j, (kL j : ℤ))
  charge_decomp :
    t.totalCharge = 4 + (∑ i, (kR i : ℤ)) + 2 - (∑ j, (kL j : ℤ))

/-! ## DTNF forward theorem

  Every min closed anchored threading in the dominant regime admits a
  `DominantWitness`. This is the forward DTNF statement.

  Proof is **open** (combinatorial, on the tube digraph). -/

/-- **DTNF-forward (conjectural).** -/
theorem DTNF_forward {t : TwistData} (h : t.isDominant) :
    Nonempty (DominantWitness t) := by
  sorry

end LeanMn.SK.TwistCalculus
