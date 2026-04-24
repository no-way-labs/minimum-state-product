import LeanMn.Dijkstra
import LeanMn.Tables
import LeanMn.System
import LeanMn.Cycle
import LeanMn.UpperBound
import LeanMn.SmallN.Theorem
import LeanMn.LowerBound

namespace LeanMn

theorem claim_3_3_1 :
    privilegedEntries.length = 45 ∧
      copyNeighborEntries.length = 40 ∧
        anomalousEntries.length = 5 := by
  constructor
  · exact claim_3_3_1_privileged_count
  constructor
  · exact claim_3_3_1_copyNeighbor_count
  · exact claim_3_3_1_anomalous_count

theorem cup2_phase1_summary (n : Nat) (hn : 4 ≤ n) :
    allEntriesWellFormed = true ∧
      privilegedEntries.length = 45 ∧
        copyNeighborEntries.length = 40 ∧
          anomalousEntries.length = 5 ∧
            stateProduct (cup2Spec n hn) = 4 * 3 ^ (n - 2) := by
  constructor
  · exact claim_3_1_1
  constructor
  · exact claim_3_3_1_privileged_count
  constructor
  · exact claim_3_3_1_copyNeighbor_count
  constructor
  · exact claim_3_3_1_anomalous_count
  · exact cup2_stateProduct n hn

theorem upper_bound_of_cup2_validity' (n : Nat) (hn : 4 ≤ n)
    (hvalid : valid (cup2System n hn)) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 4 * 3 ^ (n - 2) :=
  upper_bound_of_cup2_validity n hn hvalid

/-- Small-n upper bound: for 5 ≤ n ≤ 8, there exists a valid
self-stabilizing system with state product exactly 32·3^(n-4). -/
theorem upper_bound_small' (n : Nat) (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 32 * 3 ^ (n - 4) :=
  upper_bound_small n h5 h8

/-- CUP-2 certificate upper bound: for 4 ≤ n ≤ 10, there exists a valid
self-stabilizing system with state product exactly 4·3^(n-2). Closed
via per-n rank certificates. For n ≥ 11, paper cites Dijkstra (1974)
classical `3^n` construction. -/
theorem upper_bound_cert' (n : Nat) (h4 : 4 ≤ n) (h10 : n ≤ 10) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 4 * 3 ^ (n - 2) :=
  upper_bound_cert n h4 h10

end LeanMn
