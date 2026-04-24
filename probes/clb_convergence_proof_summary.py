#!/usr/bin/env python3
"""
CUP-2 CONVERGENCE PROOF: Complete Status & Framework
=====================================================

THEOREM (Target): The CUP-2 self-stabilizing token ring system converges
from ANY initial configuration for ALL n ≥ 4.

The system: ms = (2, 3, ..., 3, 2), product = 4·3^(n-2).
Five fixed lookup tables (87 entries), completely n-independent.
Good configs: (n+2)(n+3)/2 - 5.

PROOF STATUS:
=============

[PROVED ANALYTICALLY - Steps 1-3]
  These reduce "full graph is DAG" to "excursion graph is DAG":

  Step 1: The Δfc≤0 subgraph is a DAG.
    Proof: The pair (fc, Ψ) where fc = frontier count and Ψ = Q-potential
    is a valid DAG potential. fc ≥ 0 and Ψ ≥ 0, both bounded.
    Every Δfc≤0 transition decreases (fc, Ψ) lexicographically.

  Step 2: Every cycle in the bad-config graph uses an anomalous edge.
    Proof: By Step 1, the Δfc≤0 subgraph (all non-anomalous transitions)
    is a DAG. So any cycle must include at least one Δfc>0 (anomalous) edge.

  Step 3: The full graph has a cycle iff the excursion graph has a cycle.
    Proof: The excursion graph has nodes = anomalous source configs,
    edges = (src, tgt) where tgt is reachable from the anomalous target
    of src via a Δfc≤0 path. Standard DAG+shortcut equivalence.

[PROVED ANALYTICALLY - Step 4a]
  Δint(2,1) ≥ 0 on all excursion edges.

  Definition: int(2,1)(c) = Σ_{j=2}^{n-3} j · 𝟙(c[j]=2, c[j+1]=1)
  (position-weighted interior (2,1) pair count)

  Proof: Exhaustive analysis of all T_mid entries:
    - 13 T_mid entries fire with Δfc ≤ 0 (all are copy_L or copy_R)
    - NONE of these create interior (2,1) pairs
    - 2 destroy interior (2,1) pairs, 11 are neutral
    - T_high Δfc≤0 entries: 0 create (2,1) at position n-3
    - T_bot, T_low, T_top: only affect boundary pairs
  Since no Δfc≤0 step creates interior (2,1) pairs, and the
  anomalous step is an n-independent table lookup, int(2,1) is
  non-increasing on every excursion edge.

  CONSEQUENCE: In any potential excursion graph cycle, every edge
  must have Δint(2,1) = 0. These are "zero edges".

[VERIFIED COMPUTATIONALLY - Steps 4b-4d]

  Step 4b: The pair potential Φ(c) = Σⱼ g(j, c[j], c[j+1]) with
    42 free variables (34 boundary + 8 interior, excluding α(2,1))
    and position weight φ=j is FEASIBLE for each n = 5, 6, ..., 12.

    The LP min ||w||₁ s.t. A·w ≥ 1 is feasible for each n individually.

  Step 4c: The joint LP across n=5..12 is FEASIBLE.
    787,579 unique constraint vectors from n=5..11.
    3,755,052 unique constraint vectors from n=5..12.
    A SINGLE weight vector satisfies ALL constraints simultaneously.
    Joint ||w||₁ grows: 252 (n≤11) → 978 (n≤12).

  Step 4d: The excursion graph is computationally verified to be a
    DAG for all n = 5, 6, ..., 12.
    (State spaces: up to 4·3^10 = 236,196 configs at n=12)

WHAT REMAINS OPEN:
==================

  Step 4e: Proving LP feasibility for ALL n ≥ 5.

  OBSTACLE: The pair potential weights must GROW with n (~1.9x per n).
  No fixed finite weight vector works for all n.

  ROOT CAUSE: The "comparison transducer" (9 states, 59 edges) that
  models the cascade through the interior has NEGATIVE-WEIGHT CYCLES.
  Specifically, the cycle (0,0,1,0) → (0,1,0,1) → (1,0,1,1) has
  h-sum = -0.227 with the joint weights. This requires α(0,0) ≥ α(1,1),
  but the constraint structure requires α(0,0) < α(1,1).

  The LP with non-negative cycle constraints is INFEASIBLE, proving
  that no weight vector can simultaneously satisfy the zero-edge
  constraints AND have non-negative comparison cycles.

KEY STRUCTURAL FINDINGS:
========================

1. UNIQUE SINK: The excursion graph has exactly one sink:
   (0, 0, 2, 0, ..., 0) for all n ≥ 6. Max rank = 2(n-4).

2. MONOTONICITY CHAIN:
   Level 0: Δint(2,1) ≥ 0 on ALL excursion edges (PROVED)
   Level 1: Δint(2,0) ≥ 0 on zero edges (Δint(2,1)=0) (VERIFIED n≤11)
   No more monotone pairs after Level 1.
   Chain eliminates 63-82% of edges.

3. CASCADE TRANSDUCER: The interior cascade is a 3-state machine
   (states: last written value ∈ {0,1,2}). The comparison transducer
   (src vs tgt) has 9 states and 59 transitions, stable across n.

4. BOUNDARY TYPE CONVERGENCE: The number of distinct boundary
   constraint types converges: ~4,328 cumulative through n=11.

5. INTERIOR PAIR BOUNDS: On zero edges:
   - Δint(2,0) ≥ 0 (verified n≤11)
   - Δint(0,1) ≥ -2 (bounded, n-independent)
   - Other pairs: ranges grow with n

SUGGESTED PROOF APPROACHES:
============================

A. CASCADE AUTOMATON ANALYSIS: The cascade creates a specific
   pattern of pair changes at each interior position, determined by
   a 3-state automaton. If the automaton's "effect function" can be
   analyzed to show that the per-position contributions sum to ≥ 1
   when combined with the boundary contribution, the proof is complete.
   Challenge: the position weighting φ=j makes the sum position-dependent.

B. BOUNDARY-TYPE DECOMPOSITION: For each boundary type (finite set),
   prove that the cascade from that boundary type produces constraints
   satisfiable by the per-type weight vector. Since boundary types
   converge, this is a finite check per type.
   Challenge: the interior cascade reaches all positions, and the
   per-type constraint depends on the interior configuration.

C. INDUCTION ON n: Assume DAG for n, prove for n+1. The new system
   has one more T_mid position. Show the new excursion edges don't
   create cycles by relating to the n system.
   Challenge: the good set depends on n, and the relationship between
   the n and n+1 excursion graphs is complex.

D. MODIFIED POTENTIAL: Use a non-linear or multi-dimensional potential
   instead of the pair potential. Candidates:
   - Run-based potential (tracks lengths of equal-value runs)
   - Hierarchical potential (level-by-level analysis)
   - Configuration-space potential (direct ordering)
   Challenge: finding a universal ordering that works for all n.

E. DIRECT GRAPH ARGUMENT: Show that no cycle can exist by analyzing
   the structure of anomalous sources and the cascade dynamics.
   The unique sink property suggests a "drainage" argument.
   Challenge: making this rigorous for arbitrary n.

SCRIPTS HISTORY (proof33-48):
==============================
- proof33: Cascade structure analysis (step traces)
- proof34: Δint(2,1) monotonicity discovery + two-component potential
- proof35: Complete verification framework (n=5..12)
- proof36: ANALYTICAL proof of Δint(2,1) ≥ 0
- proof37: Zero-edge structure (boundary-only anomalous)
- proof38: Interior change boundedness (grows, not bounded)
- proof39: Boundary-only weights (infeasible n≥7), Δint(2,0) analysis
- proof40: Cross-n weight transfer, JOINT LP FEASIBLE n=5..11
- proof41: n=12 verification, weight stability (grows ~4x)
- proof42: Weight scaling law, interior contribution decomposition
- proof43: Iterated monotonicity chain ((2,1), (2,0), then stuck)
- proof44: Double-zero edges, T_mid(2,2,0)→0 creates (2,0)
- proof45: Minimal interior variables (no single/pair suffices)
- proof46: Cascade automaton (3 states, 9 comparison states, 59 edges)
- proof47: Comparison graph cycle search (too slow)
- proof48: Bellman-Ford negative cycle detection → FOUND
           LP with cycle constraints → INFEASIBLE
           This closes the pumping argument approach.
"""


def main():
    print("=" * 70)
    print("CUP-2 CONVERGENCE PROOF: STATUS SUMMARY")
    print("=" * 70)
    print()
    print("PROVED ANALYTICALLY:")
    print("  1. Δfc≤0 subgraph is DAG (fc, Ψ potential)")
    print("  2. Every cycle needs anomalous edge")
    print("  3. Cycle ⟺ excursion graph cycle")
    print("  4a. Δint(2,1) ≥ 0 on ALL excursion edges")
    print()
    print("VERIFIED COMPUTATIONALLY:")
    print("  4b. Per-n pair potential LP feasible (n=5..12)")
    print("  4c. Joint LP across n=5..12 feasible (3.75M constraints)")
    print("  4d. Excursion graph is DAG for n=5..12")
    print()
    print("OPEN:")
    print("  4e. LP feasibility / DAG property for ALL n ≥ 5")
    print()
    print("NEGATIVE RESULTS:")
    print("  - No universal pair potential weights (comparison graph")
    print("    has negative cycles, LP+cycles INFEASIBLE)")
    print("  - Boundary-only weights insufficient (n≥7)")
    print("  - No 1 or 2 interior variables sufficient (n≥7)")
    print("  - Monotonicity chain stops at 2 levels ((2,1), (2,0))")
    print()
    print("STRONGEST EVIDENCE FOR ALL-n:")
    print("  - Joint LP feasible through n=12 (236K configs)")
    print("  - Boundary types converge (~4,328)")
    print("  - Cascade automaton finite (3 states)")
    print("  - Comparison transducer finite (9 states, 59 edges)")
    print("  - Weight scaling predictable (~1.9x per n)")


if __name__ == '__main__':
    main()
