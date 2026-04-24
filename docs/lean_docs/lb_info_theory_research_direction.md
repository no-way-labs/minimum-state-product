# Information-Theoretic Lower Bound — Research Direction

Date: April 5, 2026
Status: Exploratory. Not yet a proof strategy. Preserving for future work.

## The question

Is there an information-theoretic proof that the minimum state product for
self-stabilizing token rings is 4·3^(n-2)?

The current proof uses combinatorial case analysis (entry conflict, shadow
cycles, phase extraction). This document asks whether a capacity argument
could replace or subsume the combinatorial approach.

## Background: self-stabilizing token rings

A token ring is n processors on a cycle. Processor i has m_i possible states
(values 0 to m_i - 1). The state product is P = Π m_i.

Each processor has a local transition function:

```
f_i : m_{i-1} × m_i × m_{i+1} → m_i
```

This is a lookup table: processor i sees its left neighbor, itself, and its
right neighbor, and the table says what its new value should be. Processor i
is "privileged" when f_i(L, S, R) ≠ S (the function wants to change i's value).

A system is self-stabilizing if:
1. There exists a good cycle (closed orbit of configs with unique privilege)
2. From any config, no matter how an adversary (daemon) chooses which
   privileged processor fires, the system eventually reaches the good cycle

The proved result: M_n = 4·3^(n-2) for n ≥ 9. No system with product below
this threshold can self-stabilize.

## The analogy: transition functions as a communication channel

The transition tables encode a "routing plan" — instructions for guiding every
possible configuration toward the good cycle. The tables are the channel. The
routing plan is the message.

- **Channel capacity**: determined by table sizes. Processor i's table has
  m_{i-1} × m_i × m_{i+1} entries, each storing one of m_i values. Total
  capacity ≈ Σ_i (table_size_i × log2(m_i)) bits.

- **Message**: a complete adversary-resilient convergence plan for all P - CL
  non-good configs.

- **Threshold**: the minimum P where channel capacity ≥ message size.

If this analogy were precise, the lower bound proof would be: below 4·3^(n-2),
the channel can't carry the message. One inequality.

## What the RA investigation found

### Raw Shannon capacity does NOT predict the threshold

Table capacity grows linearly in n (~42.8n bits for the threshold multiset).
Config space grows exponentially (P = 4·3^(n-2)). The capacity-per-config
ratio goes to zero for all systems, yet valid systems exist at every n.

Dijkstra's Solution 3 (ms = (3,3,...,3), product = 3^n) has worse capacity
ratios than sub-threshold systems, yet works perfectly. Raw bit counting is
not the bottleneck.

The reason: convergence constraints are massively structured and correlated.
They are not independent bits of information. The transition function exploits
this structure — one table entry controls thousands of configs simultaneously.

### The context utilization crossover IS real

The most informative quantity found:

```
utilization = (CL × n) / Σ_i (m_{i-1} × m_i × m_{i+1})
```

This measures: total context appearances across all processors and all cycle
steps, divided by total available context slots.

- utilization < 1: every context at every processor CAN be unique (no forced
  reuse between good-cycle steps)
- utilization > 1: some contexts MUST be reused (pigeonhole)

For the threshold multiset (2,3,...,3,2), utilization crosses 1.0 at n ≈ 8.44.

This coincides exactly with the known phase transition:
- n = 5..8: M_n = 32·3^(n-4) (no forced context reuse)
- n ≥ 9: M_n = 4·3^(n-2) (forced context reuse)

This is the one clean information-theoretic signal in the data.

### Forced reuse ≠ forced conflict

Context reuse (same (L,S,R) at a processor appearing at two different cycle
steps) does not automatically create an entry conflict. If both appearances
are non-mover steps, no conflict arises — the function consistently says
"stay" at both.

The threshold system CUP-2 at n=9 has CL=25 but only 12 contexts at its
binary endpoint procs. Contexts must repeat. But the system threads the
needle: repeated contexts are always in the same role (both mover or both
non-mover).

So the counting threshold identifies WHERE reuse is forced, but not WHY
conflict is forced. The "why" is structural: the topology of the mover walk
projected onto local context spaces makes role-consistent reuse impossible
at sub-threshold products.

### DOF vs constraints

Degrees of freedom (total table entries) vs constraints (P configs + CL cycle
constraints):

- n=4, threshold: DOF/constraints = 1.30 (over-determined, but structure
  makes it solvable)
- n=5, threshold: DOF/constraints = 0.77 (under-determined!)
- n=9, threshold: DOF/constraints = 0.02 (massively under-determined)

Systems exist despite being under-determined because constraints are not
independent — they share table entries (the "fan-out" effect). One entry
controls P / (m_{i-1} × m_i × m_{i+1}) configs simultaneously.

### Self-stabilization probability

For random transition functions:
- n=2, ms=(2,2): 3.9% are valid (info = 4.68 bits)
- n=3, ms=(2,2,2): 0.077% are valid (info = 10.35 bits)
- n≥4: zero valid systems found in 1000+ samples for any multiset

The probability drops super-exponentially. This means the "message" size
grows much faster than the "channel" capacity. But this doesn't prove the
threshold — it just confirms that self-stabilization is an exponentially
rare property of transition function tuples.

## The better framing: zero-error capacity

The RA's key insight: the right analogy is not Shannon capacity (tolerating
noise) but **zero-error capacity** (requiring perfect disambiguation).

### Confusability graphs

At processor i, define a graph on the local context space {(L,S,R)}:

- Two contexts are **confusable** if one appears as a mover context and
  the other as a non-mover context in the good cycle, and they have the
  same (L,S,R) values.

Actually, more precisely: an entry conflict occurs when the SAME context
appears at both a mover step and a non-mover step. So the "confusability"
is between different STEPS of the cycle, not between different contexts.

A better formulation: define a bipartite graph:
- Left vertices: mover appearances (step k where proc i fires)
- Right vertices: non-mover appearances (step k where proc i doesn't fire)
- Edge between left k₁ and right k₂ if the context (L,S,R) at proc i is
  identical at steps k₁ and k₂

Entry conflict exists iff this bipartite graph has an edge. The system is
safe at proc i iff this graph is edge-free — i.e., the mover and non-mover
context sets are completely disjoint.

Self-stabilization requires this graph to be edge-free at EVERY processor
simultaneously. The question becomes: can the good cycle be designed so that
every processor's mover/non-mover context sets are disjoint?

### Connection to graph coloring

This resembles a graph coloring / independent set problem. The good cycle
must be a "walk" through the product config space such that its projection
onto each processor's local context space separates mover and non-mover
appearances.

The threshold would correspond to: the minimum product where such a walk
exists. Below it, every walk must create an edge in some processor's
bipartite graph.

### Connection to Lovász theta

The zero-error capacity of a graph is bounded by the Lovász theta function.
If we could formulate the self-stabilization problem as a zero-error coding
problem on the confusability graph, Lovász-type bounds might give the
threshold directly.

This is speculative but could be a clean theoretical contribution.

## Research plan

### Phase 1: formalize the confusability graph

For concrete systems at n=5, 7, 9:
1. Build the bipartite mover/non-mover graph at each processor
2. Measure: edge density, independence number, chromatic number
3. Compare valid vs invalid systems
4. Check whether the chromatic number transitions at the threshold

### Phase 2: the packing interpretation

Reformulate: the good cycle defines a walk of length CL through the config
space. At each step, the mover projects onto one processor's context space.
The walk must be "context-avoiding" — no mover projection coincides with a
non-mover projection at the same processor.

This is a constrained walk problem in a product graph. The threshold is the
minimum product size where a context-avoiding walk of sufficient length exists.

Study this as a combinatorial packing / graph walk problem.

### Phase 3: Lovász theta bounds

Attempt to compute or bound the zero-error capacity of the confusability
graph for token ring systems. Compare with the known threshold.

If the Lovász theta of the confusability graph equals or bounds 4·3^(n-2),
this would give an entirely new proof of the lower bound.

### Phase 4: connect to the existing proof

Even if a full information-theoretic proof is hard, partial results might
simplify the existing proof:
- A capacity bound that handles most cases, reducing the case analysis
- A structural theorem about context-avoiding walks that subsumes several
  entry-conflict mechanisms
- A unified explanation for WHY the threshold takes the form 4·3^(n-2)

## Relation to the current proof effort

This research direction is INDEPENDENT of the current Lean formalization.
The current proof uses combinatorial case analysis (entry conflict + shadow
cycles) and is close to complete (7 sorrys, concentrated in sorry 6).

The information-theoretic approach would be a second, potentially cleaner
proof — or at minimum, a theoretical explanation for the threshold value.
It should not block or delay the current formalization effort.

## Key scripts and data

All in `probes/`:
- `ra12_info_theory.py` — table capacity, fan-out, random sampling
- `ra12_info_theory2.py` — analytical formulas, exhaustive n=3, DOF/constraints
- `ra12_info_theory3.py` — context overlap analysis, utilization ratio
- `ra12_info_theory4.py` — utilization crossover, pigeonhole analysis

Key data points:
- Context utilization crossover at n ≈ 8.44 for threshold multiset
- n=3 exhaustive: 12,843 / 16,777,216 valid systems
- Fan-out at n=9 binary proc: 729 configs per table entry

## What a new researcher would need

1. Familiarity with self-stabilizing systems (Dijkstra 1974, Dolev 2000)
2. The token ring model (Ring.lean, Dijkstra.lean in the Lean codebase)
3. Zero-error information theory (Shannon 1956, Lovász 1979)
4. Graph theory: chromatic number, independence number, theta function
5. The verified threshold: M_n = 4·3^(n-2) for n ≥ 9

The concrete question: can the Lovász theta (or a related bound) of the
mover/non-mover confusability graph on the local context space of a token
ring processor reproduce the threshold 4·3^(n-2)?

## Broader significance

If the information-theoretic framing works, it would:
1. Provide a conceptual explanation for the threshold (channel capacity of
   local transition functions on a ring)
2. Potentially generalize to other network topologies (not just rings)
3. Connect self-stabilization theory to zero-error information theory
4. Suggest that M_n is a fundamental constant of distributed computing,
   analogous to channel capacity in communication

The Anna Karenina observation: valid systems are all alike (they satisfy a
global routing constraint), but invalid systems each fail differently (the
constraint is violated at different points for different reasons). The
information-theoretic approach would explain WHY there's exactly one way to
succeed and many ways to fail — the routing constraint is tight at the
threshold, with zero slack for error.
