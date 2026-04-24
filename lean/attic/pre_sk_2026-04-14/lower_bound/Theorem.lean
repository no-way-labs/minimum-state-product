/-
  Theorem.lean — Lower Bound Assembly (Renovated)

  Master theorem: for n ≥ 9, no system with state product < 4·3^(n-2)
  is self-stabilizing (i.e., M_n ≥ 4·3^(n-2)).

  Architecture (zero callbacks):
    Theorem.lean → CaseDispatch.lean (Proof/)
      ├── SafeProcessor.lean  — Cases A+B (sorry-free)
      ├── ZeroWinding.lean    — Case C (palindromic chain)
      ├── Sweep.lean          — Case D (IsolatedFirings + ShadowOrbit)
      └── OddWinding.lean     — Case E (phase extraction + NormalFormEC)
-/
import LeanMn.LowerBound.Proof.CaseDispatch

namespace LeanMn

variable {sys : System}

/-- **Lower Bound Theorem.** For n ≥ 9, no system with state product < 4·3^(n-2)
    is self-stabilizing. Equivalently, M_n ≥ 4·3^(n-2).

    Proof: `subThreshold_impossible` shows any good cycle in a converging
    sub-threshold system leads to False (case split: safe processor, ZW cw=0,
    ZW cw>0, sweep, odd winding). -/
theorem lower_bound_theorem
    (hn : sys.rs.n ≥ 9)
    (hsub : subThreshold sys.rs) :
    ¬valid sys := by
  intro ⟨gc, hconv⟩
  exact subThreshold_impossible hn gc hconv hsub

/-- **M_n Theorem (n ≥ 9).** The minimum state product for self-stabilizing
    token rings on n processors is exactly 4·3^(n-2).

    This theorem states the lower bound direction: M_n ≥ 4·3^(n-2).
    The upper bound (M_n ≤ 4·3^(n-2)) is proved by the CUP-2 construction
    in the upper bound track. -/
theorem M_n_lower_bound
    (rs : RingSpec) (hn : rs.n ≥ 9)
    (hsub : stateProduct rs < 4 * 3 ^ (rs.n - 2))
    (sys : System) (hrs : sys.rs = rs) :
    ¬valid sys := by
  have hsub' : subThreshold sys.rs := by unfold subThreshold; rw [hrs]; exact hsub
  have hn' : sys.rs.n ≥ 9 := by rw [hrs]; exact hn
  exact lower_bound_theorem hn' hsub'

end LeanMn
