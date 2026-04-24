import LeanMn.SmallN.Cup2Convergence
import LeanMn.SmallN.Defs

namespace LeanMn

theorem cup2_valid_of_converges (n : Nat) (hn : 4 ≤ n)
    (hconv : converges (cup2System n hn) (cup2GoodCycle n hn)) :
    valid (cup2System n hn) :=
  ⟨cup2GoodCycle n hn, hconv⟩

theorem upper_bound_of_cup2_converges (n : Nat) (hn : 4 ≤ n)
    (hconv : converges (cup2System n hn) (cup2GoodCycle n hn)) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 4 * 3 ^ (n - 2) :=
  ⟨cup2System n hn, cup2_valid_of_converges n hn hconv, cup2_stateProduct n hn⟩

theorem upper_bound_of_cup2_validity (n : Nat) (hn : 4 ≤ n)
    (hvalid : valid (cup2System n hn)) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 4 * 3 ^ (n - 2) :=
  ⟨cup2System n hn, hvalid, cup2_stateProduct n hn⟩

/-! ### Explicit small-n upper bound (tighter: 32·3^(n-4) for n ∈ {5..8}) -/

theorem upper_bound_small (n : Nat) (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 32 * 3 ^ (n - 4) := by
  interval_cases n
  · refine ⟨w5System, w5_valid, ?_⟩
    simpa using w5_stateProduct
  · refine ⟨w6System, w6_valid, ?_⟩
    simpa using w6_stateProduct
  · refine ⟨w7System, w7_valid, ?_⟩
    simpa using w7_stateProduct
  · refine ⟨w8System, w8_valid, ?_⟩
    simpa using w8_stateProduct

/-! ### CUP-2 certificate upper bound at 4·3^(n-2) for n ∈ {4..10}

    Uses the per-n rank certificates from `LeanMn/SmallN/Cup2Convergence.lean`
    (closed by `native_decide +revert` on pre-computed rank tables).

    For n ≥ 11 the paper cites Dijkstra's classical `3^n` construction;
    no Lean theorem is provided. -/

theorem upper_bound_cert (n : Nat) (h4 : 4 ≤ n) (h10 : n ≤ 10) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 4 * 3 ^ (n - 2) := by
  have hconv : converges (cup2System n h4) (cup2GoodCycle n h4) := by
    interval_cases n
    · exact cup2Converges4
    · exact cup2Converges5
    · exact cup2Converges6
    · exact cup2Converges7
    · exact cup2Converges8
    · exact cup2Converges9
    · exact cup2Converges10
  exact upper_bound_of_cup2_converges n h4 hconv

end LeanMn
