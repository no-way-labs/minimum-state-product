/-
  LowerBound/SK/EdgeMajorityB2.lean — Conjecture B'' scaffold

  Skeleton Lean file for the Hamming-2 edge-majority obligation
  identified by `partial_dynamical_invariants_lean_scoping.md`.

  Given a good cycle `gc`, this file would define:
  - `B2MinusCycle gc`: the Hamming-2 ball around the cycle, minus
    cycle configs.
  - The forced-NG undirected edge count on `B2MinusCycle gc`.
  - The connected-component count.
  - The β₁ identity `|E| − |V| + C ≥ 1` ⇒ `SK gc .Nonempty`.

  The analytical hypothesis `edge_majority_of_sub_threshold` is left
  UNPROVEN — it is the central open problem of the partial-
  dynamical invariants program. NOT shippable as an axiom (per
  `feedback_no_axioms`).

  Status: scoped only. Definitions and theorem statements pending
  full formalization in a future session.
-/
import LeanMn.LowerBound.SK.PartialDet

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LeanMn.SK

variable {sys : System}

/-!
## Hamming distance to the cycle

`hammingDistSys c c'` is the number of positions where `c` and `c'`
differ. `distToCycle gc c` is the minimum Hamming distance from `c`
to any cycle config of `gc`.
-/

noncomputable def hammingDistSys (c c' : Config sys.rs) : ℕ :=
  ((Finset.univ : Finset (Fin sys.rs.n)).filter
    (fun i => c i ≠ c' i)).card

noncomputable def distToCycle (gc : GoodCycle sys) (c : Config sys.rs) : ℕ :=
  (gc.configs.toFinset.image (hammingDistSys c)).min.getD 0

/-- The Hamming-2 ball around the cycle, minus cycle configs. -/
noncomputable def B2MinusCycle (gc : GoodCycle sys) :
    Finset (Config sys.rs) :=
  (Finset.univ : Finset (Config sys.rs)).filter fun c =>
    NonGood gc c ∧ distToCycle gc c ≤ 2

/-!
## Forced-NG subgraph statistics on B_2 \ cycle

These are the three quantities of the β₁ identity:
  β_1 = |E_forced| − |V_forced| + |components_forced|.

Full definitions deferred. The key claims are stated as theorems
without proof to mark the obligations.
-/

/-- The undirected forced edges with both endpoints in `B2MinusCycle`.
    Skeleton — full definition pending. -/
noncomputable def forcedEdgesIn (gc : GoodCycle sys) :
    Finset (Sym2 (Config sys.rs)) :=
  ∅  -- TODO: collect (Sym2.mk c c') for each c, c' ∈ B2MinusCycle gc
     -- with c' ∈ forcedNeighbors (detOf gc) c.

/-- Number of connected components of the undirected forced-NG subgraph
    on B2MinusCycle. Skeleton. -/
noncomputable def forcedComponents (gc : GoodCycle sys) : ℕ :=
  0  -- TODO

/-!
## The β₁ identity and bridge to SK

The graph-theoretic facts:
  1. `β_1 = |E| − |V| + |components|` (Euler-characteristic identity).
  2. `β_1 ≥ 1` ⇔ the graph contains a directed cycle.
  3. A directed cycle in forced-NG | B_2 \ cycle, packaged as a
     finset, satisfies the hypothesis of
     `sk_nonempty_of_closed_forced_subset`.

The chain (1) ⇒ (2) ⇒ (3) ⇒ `SK.Nonempty` is the Lean target.
-/

/-- Conjecture B'' (Edge-Majority for sub-threshold candidates).

    Open analytical statement: for every good cycle from the
    Dijkstra enumeration with sub-threshold product, the forced-NG
    subgraph on `B_2 \ cycle` has
    `|forcedEdgesIn| + forcedComponents ≥ |B2MinusCycle| + 1`.

    This is equivalent to `β_1(forced-NG | B_2 \ cycle) ≥ 1`,
    equivalent to a directed cycle existing in the forced subgraph,
    equivalent to `SK gc .Nonempty` (via `sk_nonempty_of_...`).

    Empirical: TRUE on 63/63 records of the corpus with margin
    ≥ 178 (`axis_c_edge_majority_results.json`,
    `axis_c_cube_complex_betti_results.json`).

    Analytically OPEN. Per `feedback_no_axioms` not shippable as
    `axiom`. Stated here as a `theorem` with `sorry` to mark the
    obligation. -/
theorem edge_majority_of_sub_threshold (gc : GoodCycle sys)
    -- TODO: replace with the precise sub-threshold predicate
    (h_sub : True)
    (h_n : sys.rs.n ≥ 9) :
    (forcedEdgesIn gc).card + forcedComponents gc ≥
      (B2MinusCycle gc).card + 1 := by
  sorry

/-- Final deliverable, conditional on the open analytical core:
    sub-threshold ⇒ SK gc nonempty ⇒ no convergent extension. -/
theorem sk_nonempty_of_sub_threshold (gc : GoodCycle sys)
    (h_sub : True)
    (h_n : sys.rs.n ≥ 9) :
    (SK gc).Nonempty := by
  -- 1. Apply edge_majority_of_sub_threshold to get
  --    |E| + C ≥ |V| + 1, i.e. β_1 ≥ 1.
  -- 2. Show β_1 ≥ 1 ⇒ forcedEdgesIn contains a cycle.
  -- 3. Package the cycle as a closed forced subset of NonGood.
  -- 4. Apply sk_nonempty_of_closed_forced_subset.
  sorry

/-- Headline corollary: sub-threshold ⇒ no convergent system. -/
theorem not_converges_of_sub_threshold (gc : GoodCycle sys)
    (h_sub : True)
    (h_n : sys.rs.n ≥ 9) :
    ¬ converges sys gc := by
  exact not_converges_of_partial_det_sk_nonempty gc
    (sk_nonempty_of_sub_threshold gc h_sub h_n)

end LeanMn.SK
