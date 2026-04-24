/-
  Theorem.lean — Master Lower Bound Theorem (Renovated)

  Imports only CaseDispatch. Zero callbacks. Clean architecture.

  M_n ≥ 4·3^(n-2) for n ≥ 9: no system with product < 4·3^(n-2)
  is self-stabilizing.
-/
import LeanMn.LowerBound.Proof.CaseDispatch

namespace LeanMn

variable {sys : System}

/-- **Lower Bound Theorem (renovated).** For n ≥ 9, no system with state
    product < 4·3^(n-2) is self-stabilizing.

    Proof: subThreshold_impossible shows any good cycle in a converging
    sub-threshold system leads to False (case split: safe processor, ZW cw=0,
    ZW cw>0, sweep, odd winding). -/
theorem lower_bound_theorem_v2
    (hn : sys.rs.n ≥ 9)
    (hsub : subThreshold sys.rs) :
    ¬valid sys := by
  intro ⟨gc, hconv⟩
  exact subThreshold_impossible hn gc hconv hsub

/-- **M_n Theorem (n ≥ 9, renovated).** The minimum state product for
    self-stabilizing token rings on n processors is at least 4·3^(n-2). -/
theorem M_n_lower_bound_v2
    (rs : RingSpec) (hn : rs.n ≥ 9)
    (hsub : stateProduct rs < 4 * 3 ^ (rs.n - 2))
    (sys : System) (hrs : sys.rs = rs) :
    ¬valid sys := by
  have hsub' : subThreshold sys.rs := by unfold subThreshold; rw [hrs]; exact hsub
  have hn' : sys.rs.n ≥ 9 := by rw [hrs]; exact hn
  exact lower_bound_theorem_v2 hn' hsub'

end LeanMn
