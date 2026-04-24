# CUP-2 Convergence Proof Framework

## System
- ms = (2, 3, ..., 3, 2), product = 4*3^(n-2)
- 5 fixed lookup tables (T_bot, T_low, T_mid, T_high, T_top), 87 entries total
- Completely n-independent rules
- Verified valid for n = 5..18

## Goal
Prove: the bad-config transition graph is a DAG (acyclic) for ALL n >= 5.

## Proof Architecture: Multi-Layer Monotonicity Chain

The proof reduces convergence to 3 layers on the **excursion graph**.

### Excursion Graph
Nodes = bad configs that are anomalous sources (have a transition where
output != L and output != R). Edges (u,v) exist when: u makes an anomalous
step to some b, and v is reachable from b via delta_fc <= 0 transitions,
and v is also an anomalous source.

Any cycle in the full transition graph implies a cycle in the excursion graph.

### The 5 Anomalous Entries
Only 5 of the 87 table entries produce anomalous transitions:
1. T_bot(0,0,0) -> 1  (P0: context all-zero)
2. T_bot(1,1,2) -> 0  (P0: context one-one-two)
3. T_mid(2,1,1) -> 0  (Interior: context two-one-one, the liveness fix)
4. T_high(1,1,1) -> 2  (P(n-2): context all-one)
5. T_top(2,0,0) -> 1  (P(n-1): context two-zero-zero)

### Layer 0: int(2,1) Non-Decrease
**Quantity**: int_21(c) = #{j in [2, n-3] : c[j]=2, c[j+1]=1}
(count of interior 2->1 transitions)

**Claim**: For ALL excursion edges (u,v): int_21(v) >= int_21(u).

**Status**: VERIFIED computationally n=5..12. Analytical proof OPEN.

### Layer 1: int_j(2,0) Non-Increase (on Layer 0 zero-edges)
**Quantity**: int_j20(c) = sum{j in [2, n-3] : c[j]=2, c[j+1]=0} * j
(position-weighted count of interior 2->0 transitions)

**Claim**: For excursion edges with delta_int_21 = 0: int_j20(v) <= int_j20(u).

**Status**: VERIFIED computationally n=5..12. Analytical proof OPEN.

### Layer 2: jdz Subgraph is DAG
**Definition**: jdz = {(u,v) in excursion graph : delta_int_21 = 0 AND delta_int_j20 = 0}

**Claim**: The jdz subgraph is a DAG.

**Status**: VERIFIED computationally n=5..12. Analytical proof OPEN.

### Why These 3 Layers Suffice
Layers 0-1 give: the pair (int_21, -int_j20) is lexicographically non-decreasing
on all excursion edges, with strict increase except on jdz edges.
Layer 2 handles the residual jdz subgraph.
Combined: the excursion graph is a DAG -> the full transition graph is a DAG -> convergence.

## Deep Structure of the jdz Subgraph (Layer 2)

### Decomposition by Preserved Quantities
The jdz graph decomposes into **independent components** indexed by (int_21, int_j20).
Both quantities are preserved (delta = 0) on jdz edges by definition.

**No additional preserved quantities exist**: tested all pair counts (a,b),
weighted pair counts j^k*(a,b), value counts, boundary positions,
linear combinations. Only int pair(2,0), int pair(2,1), and their
j-weighted versions are preserved — exactly what defines jdz.

### fc Range on jdz Edges
- delta_fc ranges from -(n-3) to +2 on jdz edges
- Upper bound +2 is EXACT for all n >= 6
- Most edges (~70%) are fc-decreasing

### KEY STRUCTURAL PROPERTY: delta_fc >= 0 Subgraph has Rank <= 3

**Verified for n = 5, 6, 7, 8, 9, 10, 11, 12.**

Within EVERY (int_21, int_j20) component, the subgraph consisting of
only the non-fc-decreasing edges (delta_fc >= 0) is a DAG with
maximum rank (longest path) at most 3.

Additionally:
- The delta_fc = 0 subgraph has rank <= 3
- Per-fc-level subgraphs (edges grouped by source fc) have rank <= 3
- The delta_fc > 0 subgraph has rank <= 3

This bound is INDEPENDENT OF n.

### Rank-3 Path Structure
Rank-3 paths (length exactly 3 in the delta_fc >= 0 subgraph) have
stereotyped structure:

**Dominant pattern** (63-96% of rank-3 paths):
  bot(0,0,0)->1  -->  high(1,1,1)->2  -->  bot(1,1,2)->0

Meaning:
1. P0: 0->1 (bot entry fires, all-zero context)
2. P(n-2): 1->2 (high entry fires, all-one context)
3. P0: 1->0 (bot entry fires again, context (1,1,2))

**Other rank-3 patterns**: permutations of {bot(1,1,2)->0, mid(2,1,1)->0, high(1,1,1)->2}

### Dead-End Property
ALL rank-3 path endpoints share:
- Boundary = (0, 2, 2, 1) — that is, P0=0, P1=2, P(n-2)=2, P(n-1)=1
- ZERO outgoing jdz edges (global dead ends, not just delta_fc>=0 dead ends)

This is universal across n=7..12.

### Rank-3 Path Starting Points
Start boundaries: predominantly (0,0,0,0) and (0,0,1,0).

### Max Total fc Gain
Along any path in the delta_fc >= 0 subgraph: max total fc gain <= 4.
(Verified n=5..11. At most 22 paths achieve gain=4 even at n=11.)

### Boundary Automaton
The boundary 4-tuple (P0, P1, P(n-2), P(n-1)) has 34 observed states and
139 observed transitions in the delta_fc >= 0 subgraph (stable from n=10 onward).
The boundary graph itself is NOT a DAG (has cycles and self-loops).
The rank <= 3 property relies on INTERIOR structure, not just boundary.

## Full DAG Rank of jdz Components
- n=5: 2, n=6: 3, n=7: 5, n=8: 7, n=9: 8, n=10: 10, n=11: 11, n=12: 13
- Grows approximately as n+1
- Consistent with: full_rank ~ fc_range + up_rank ~ (n-3) + 3 + 1 = n+1

## Approaches That Don't Work

### Simple Potential Functions
No linear combination alpha*fc + beta*rank_up works:
- For delta_fc >= 0 edges: rank_up decreases by >= 1, but fc increases by up to 2
- For delta_fc < 0 edges: fc decreases, but rank_up can increase by up to 3
- No coefficient balances both requirements simultaneously

### Fixed-Parameter Position-Pair Potentials
Per-n LP gives strict decrease, but delta -> 0 as n -> infinity.
All polynomial parametrizations (linear through quartic), relative positions,
harmonic bases, extended boundaries: same geometric decay.
Total parameter budget determines delta; ceiling ~78 for >=90 parameters.

### Small-Integer Pair-Count Combinations
Exhaustive search over 4-term integer combinations in [-3,3]:
none monotone on jdz edges beyond n=5.

## Open Lemmas (What's Needed to Complete the Proof)

### Lemma A: Layer 0 Monotonicity
For all excursion edges (u,v): int_21(v) >= int_21(u).
*Approach*: Case analysis on which anomalous entry drives the excursion,
combined with the delta_fc <= 0 chain structure.

### Lemma B: Layer 1 Monotonicity
For zero-int_21 excursion edges (u,v): int_j20(v) <= int_j20(u).
*Approach*: Similar case analysis, restricted to the 5 anomalous entries
with the constraint delta_int_21 = 0.

### Lemma C: Layer 2 (jdz DAG)
The jdz subgraph is a DAG.
*Most promising approach*: Prove rank <= 3 in the delta_fc >= 0 subgraph
analytically (via case analysis on anomalous entry sequences), then use
the bounded non-fc-decreasing structure + fc descent for the full DAG.

**Specifically**: Show that any path of length >= 4 in the delta_fc >= 0
subgraph leads to a contradiction. The rank-3 paths have stereotyped
entry sequences (bot->high->bot dominant pattern), and after 3 such steps
the boundary reaches (0,2,2,1) from which no further non-fc-decreasing
excursion can begin.

## Key Scripts
- proof62-66: LP analysis, delta decay, structural analysis
- proof67: per-(int_21, int_j20) decomposition verification
- proof68: preserved quantity search (confirms only int(2,0), int(2,1) preserved)
- proof69: **KEY** delta_fc >= 0 rank <= 3 discovery
- proof70: path structure, max gain analysis
- proof71: **KEY** rank-3 entry sequences, boundary (0,2,2,1) dead-end property
- proof72: boundary automaton analysis (not DAG, has self-loops)
