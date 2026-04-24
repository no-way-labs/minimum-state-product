/-
  LowerBound/SK/CTCL.lean — Theorem B (Twist Charge Conservation Law).

  Frozen signature: docs/lean_docs/sk/sk_theorem_package_freeze_2026-04-19.md §2.
  Slate reference: docs/lean_docs/sk/sk_twist_calculus_slate_2026-04-19.md §2′.
  DTNF ⇒ CTCL-dominant proof: docs/lean_docs/sk/sk_ctcl_from_dtnf_2026-04-19.md.

  * `CTCL_from_witness` — proved, no sorry.
  * `CTCL_dominant` — proved modulo `DTNF_forward`.
  * `CTCL_fold` — sorry-gated (open research target).
-/
import LeanMn.LowerBound.SK.DominantNormalForm

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LeanMn.SK.TwistCalculus

/-! ## CTCL from a dominant witness (no sorry)

  Given a `DominantWitness` for `t`, the total twist charge is 6.
  This is the DTNF ⇒ CTCL-dominant algebraic step:

      Σ χ = Σ_R (1 + kR_i) + Σ_L (1 − kL_j)
          = 4 + Σ kR + 2 − Σ kL
          = 6 + (Σ kR − Σ kL)
          = 6                                       (by balance). -/

theorem CTCL_from_witness {t : TwistData} (w : DominantWitness t) :
    t.totalCharge = 6 := by
  rw [w.charge_decomp, w.balance]
  ring

/-! ## CTCL-dominant (proved modulo DTNF) -/

/-- **CTCL-dominant.** Every dominant-regime min closed threading has
    total twist charge 6. Consequence of `DTNF_forward` and
    `CTCL_from_witness`. -/
theorem CTCL_dominant {t : TwistData} (h : t.isDominant) :
    t.totalCharge = 6 := by
  obtain ⟨w⟩ := DTNF_forward h
  exact CTCL_from_witness w

/-! ## CTCL-fold (open research target) -/

/-- **CTCL-fold (conjectural).** Every fold-regime min closed
    threading has total twist charge 6. The compensation mechanism
    forcing `Σ_F χ(F) = −X` to be matched by R/L excess `+6 + X` is
    UNEXPLAINED. See slate §2′.5, questions CTCL-FOLD-1/2/3. -/
theorem CTCL_fold {t : TwistData} (h : t.isFold) :
    t.totalCharge = 6 := by
  sorry

end LeanMn.SK.TwistCalculus
