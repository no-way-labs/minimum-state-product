/-
  SmallN/Theorem.lean — Exact M_n theorems (post pre-SK attic, 2026-04-14)

  Currently states only the n = 4 exact value.

  - M_4 = 24 (witness: ms=(2,2,2,3)). Both directions are proved
    (see `SmallN.Defs` for the witness and `SmallN.LB2222` for the lower
    bound, which is sorry-free).

  The general M_n = 4·3^(n-2) lower bound for n ≥ 5 will be provided by
  the new SK-based formalization in `LeanMn/LowerBound/SK/`. Once that
  lands, M_5..M_8 (and the parametric M_n for n ≥ 9) will be added here
  as corollaries.

  See `docs/lean_docs/lb_sk_restart_plan_2026-04-14.md`.
-/
import LeanMn.SmallN.Defs
import LeanMn.LowerBound.SmallN.LB2222

namespace LeanMn

/-! ### Upper bound: existence of witness systems -/

theorem M_4_upper : ∃ sys : System, valid sys ∧ sys.rs.n = 4 ∧ stateProduct sys.rs = 24 :=
  ⟨w4optSystem, w4opt_valid, rfl, w4opt_stateProduct⟩

/-! ### Lower bound -/

theorem M_4_lower (sys : System) (hn : sys.rs.n = 4) (hsub : stateProduct sys.rs < 24) :
    ¬valid sys :=
  M_4_lower_proved sys hn hsub

/-! ### Exact value: M_4 = 24 -/

theorem M_4_eq_24 :
    (∃ sys : System, valid sys ∧ sys.rs.n = 4 ∧ stateProduct sys.rs = 24) ∧
    (∀ sys : System, sys.rs.n = 4 → stateProduct sys.rs < 24 → ¬valid sys) :=
  ⟨M_4_upper, M_4_lower⟩

end LeanMn
