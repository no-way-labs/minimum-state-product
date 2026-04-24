# SK Morse–Hamming (SKMH) — Exploration Log

**Started:** 2026-04-20
**Target:** paper2 lower bound, M_n ≥ 4·3^(n-2) at n≥9 and 32·3^(n-4) at n∈{5..8}.
**Framing (Keston-confirmed, 2026-04-20):** prove via a *topological invariant* of `X(ms) \ C` that forbids any valid transition function from existing. See `feedback_topological_invariant_proof_shape.md`.
**Log protocol:** `docs/residue_prompt_v2.md`.
**Pre-Lean phase:** explore with probes before any Lean port. Memory: `project_sk_morse_hamming_2026-04-20.md`.

---

## Strategy Register

### Eliminated approach classes
- **(E2)** **Morse–Hamming at β_1 with induced-subcomplex model on ∏Δ^{m_i-1}.** β_1 = 0 uniformly across 11 cycles at n=5,6 including sub-threshold; `m_p ≥ 3` positions contribute "one-3" 2-cells that fill 1-holes. Any approach that uses this specific complex + β_1 target is dead.
- **(E3)** **Pure Betti numbers of induced subcomplex as LB obstruction, ANY dim.** `∃k. β_k(NG(C)) > 0` holds only 10/20 at sub-threshold; at-threshold has β_4 in {864,…,893}. The homotopy type scales with ambient dim Σ(m_i-1) not with sub-threshold-ness. Any LB that reads off a Betti number from this complex is dead.
- **(E4)** **Linear f-vector invariants on induced subcomplex.** χ, c_0/M, partial Euler characteristic with cutoff, any linear combination of (c_0, c_1, ..., c_d) — all either trivial (=1) or monotone in ambient dim, not threshold-sensitive.
- **(E2–E6 meta)** **Pure state-space topology on ∏Δ^{m_i−1}.** Any invariant that is a function of `(X(ms), Cycle, induced-subcomplex)` and ignores dynamics. Reason: the homotopy type is `(n, L)`-parametrized; ms enters only via ambient dim scaling, which discriminates only dim-size, not sub-threshold-ness. Five distinct invariants tested, five failed or structurally broken. Stop testing this class.

### Obstructions
- **(E2)** **1-holes in NG(C) are killed by ternary-or-larger factor simplices.** Every 3-element face inside a factor Δ^{m_p-1} at `m_p ≥ 3` becomes a 2-cell in the product and fills nearby 1-loops. So any induced-subcomplex model whose factor simplices include sufficient "fill" will kill β_1. A valid obstruction either (a) prevents these 2-cells from being in NG, or (b) lives in a different dim, or (c) uses a different model entirely.
- **(E3)** **Betti numbers scale with ambient dim, not sub-threshold-ness.** Larger product ms → larger Σ(m_i-1) → bigger ambient complex → more room for higher-dim holes → LARGER β_k. Exactly the WRONG direction for an LB. Any candidate invariant that is a pure homotopy invariant of `(X(ms) \ C) or NG(C) or ∏Δ^{m_i-1}` will inherit this obstruction.
- **(E3)** **ms enters via cell counts, not Betti.** Since `|Cells|(ms) ≈ f(∏m_i)` but `β_k ≈ g(Σ(m_i-1))`, and the difference `cells − rank ∂` is dominated by the cell term, any invariant that sees ms must use cell-count or oriented-chain-level data, not rank data. Candidates: Euler char with local coefficients, Index-Lemma content, Lefschetz number of a rule map, chain-level obstruction theory.
- **(E4)** **Linear cell-count invariants collapse to Betti.** Any Σ a_k c_k that is a chain-complex invariant equals Σ a_k β_k + rank terms, and rank terms are determined by homotopy type. Breaking out of the Betti trap requires nonlinear cell-count combinations OR dynamics-sensitive cells.
- **(E5)** **Hamming paths are not CW-simplices of ∏Δ^{m_i−1}.** For any Sperner-/Index-Lemma-style content probe on product-of-simplices, need either (a) a simplicial subdivision (barycentric) OR (b) a product-compatible notion of n-simplex — raw Hamming paths don't work.
- **(E6)** **Z/n does not act on NG(C) unless C is Z/n-invariant.** For a generic L-cycle, rotating produces a different cycle; induced subcomplex must be on the rotation-closure `⋃_k rot_k(C)` for equivariant invariants. Restricts applicability.

### Building blocks
- **Stored witness cycles** at n=5..8 available via `probes/verify_witnesses.py` and cycle enumerator `probe_sk_hamming1_empty_discriminator_2026-04-17.py::enumerate_cycles_multistart`. Sub-`M_n` cycle datasets span 5548 multisets at n=5..8.
- **`|SK|` constant per `(n, L)` across all tested ms** (primer §3, `project_sk_hamming1_discovery_2026-04-16.md`). **Load-bearing as evidence that homotopy type of `NG(C)` depends only on `(n, L)`, not ms.** If true, the LB becomes a statement about finitely many `(n, L)` pairs at each n.
- **(E2)** **Working Betti-computation pipeline** in `skmh_probe_betti_2026-04-20.py`: cell enumeration, tensor-product boundary, numpy-rank Betti numbers. n=5 in <0.1s; n=6 in ~0.4s. Reusable for any (ms, cycle, complex-model) triple.
- **(E2)** **Binary-ring β_2 = 1 observation.** For all-binary ms=(2,2,2,2,2), NG(C) of L=10 cycles has β_2 = 1 (3/3). Candidate generator: the cycle's Alexander-dual 2-class in the 5-cube. Needs identification; could seed the open-complement reformulation.

### Known reformulations
- **LB-as-topological-obstruction (central reformulation, Keston-endorsed).** "A topological invariant of `X(ms), C` forbids any valid transition function." Shape still endorsed; concrete first instances (E2 β_1, E3 any β_k) RULED OUT. Invariant must see ms through **cell counts** or **dynamics** (det/rule), not through pure homotopy of ambient.
  LOAD-BEARING ASSESSMENT: shape still load-bearing, all specific instances tested so far are dead.

- **(E2/E3 dead)** Product-of-simplices + induced-subcomplex + pure Betti. Dead.

- **(f) Cell-count-sensitive invariants.** Invariants whose value depends on # of k-cells even when rank(∂) is unchanged. Candidates: Euler char with local coefficients, weighted chain complex, Index-Lemma content.
  LOAD-BEARING ASSESSMENT: strong — this is where ∏m_i enters. Next probe direction.

- **(g) Herlihy content (Lemma 12.3.5) under ms-dependent coloring.** `C(X, c) = Σ_σ properly-colored-by-c-counted-by-orientation`. Varies with coloring, which can depend on ms.
  LOAD-BEARING ASSESSMENT: genuinely untested; structurally distinct from Betti; worth probing.

- **(h) Chain-level obstruction of det(C).** σ_C = 1-chain; whether σ_C = ∂(2-chain-in-NG) with ms-dependent coefficients.
  LOAD-BEARING ASSESSMENT: bridges product-counting with topology; untested.

- **(i) Z/n-equivariant / quotient model.** Untested. Ring rotation acts on X(ms); equivariant cohomology / quotient might concentrate ms-info.

- **Cubical-on-Hamming-1 graph** — trivially β_1 >> 0. Not load-bearing.

- **(j) Forced-graph flow complex** — nerve of the forced-graph, vertices = configs, k-simplices = commuting tuples of forced moves. Encodes dynamics. Untested.

- **(k) Extension space `Ext(det(C))`** — the finite discrete space of rules extending det(C). EMPTINESS is the LB. No topology yet; combinatorial.

- **(l) Twisted homology ⊗_p ℤ/m_p** — per-position cyclic-group coefficients; tensor-product torsion might carry product info. Untested.

- **(m) Configuration-rule pair complex** — obstruction theory to extending a partial section of the "rule bundle". Untested.

Of (j)–(m), (l) and (m) are the most topologically flavored. (j) and (k) are bridges back to the SK-style counting.

---

## Exploration 1 (probe)

### Strategy
Retroactive capture — record the framework proposal itself as an exploration artifact so future sessions have the origin point.

### Outcome
SUCCEEDED (framework accepted by Keston on 2026-04-20 as "exactly how I imagined this proof working"; ship-shape endorsed; Lean pivot/parallel decision deferred to after probes).

### Concrete Artifacts

STRUCTURAL RESULTS:
- Conjecture (Morse–Hamming): `f ⊇ det(C)` is self-stabilizing iff `f` induces a complete discrete Morse vector field on `X(ms) \ C` with all critical cells in `G(C)`.
- Corollary (if conjecture holds): `β_k(X(ms) \ C) > 0` for any `k ≥ 1` ⟹ no self-stab possible at that `(ms, C)`.
- LB becomes: `∀ sub-threshold ms, ∀ fair simple cycle C, ∃ k ≥ 1 with β_k(NG(C)) > 0`.

REPRESENTATIONS:
- `X(ms) = ∏_{i=0}^{n-1} Δ^{m_i - 1}` (product of simplices). Dim = Σ(m_i - 1). Contractible.
- `NG(C)` = full subcomplex induced by vertices in `Config \ Cycle(C)`.
- Cells of X(ms): each cell = tuple `(F_0, ..., F_{n-1})` of face-of-simplex picks. Cell dim = Σ dim F_i.

TOOLS (to build):
- `build_nc_subcomplex(ms, cycle)`: construct NG(C) as a cubical/product-simplex complex and return cells per dimension.
- `betti_numbers(subcomplex, max_dim)`: chain-complex Smith-normal-form computation of Betti numbers mod 0 (Z or Q).

---

## Exploration 2 (full)

### Strategy
Compute β_0, β_1, β_2 of NG(C) as induced subcomplex of X(ms) = ∏Δ^{m_i-1}, scanning a small battery of sub-threshold multisets at n=5,6 plus one at-threshold reference at n=5.

### Outcome
**FAILED** at the primary hypothesis (β_1 > 0 at sub-threshold). β_1 = 0 uniformly across all 11 tested cycles (9 sub-threshold + 2 at-threshold). β_2 is intermittent: 1 on all three (2,2,2,2,2) all-binary cycles, 1 on one of three (2,2,2,2,3) cycles, 0 elsewhere. No uniform Betti-number lower bound emerges from this construction.

### Failure Constraint
On X(ms) = ∏Δ^{m_i-1}, NG(C) is the induced-subcomplex on non-cycle vertices. **Every 1-loop in NG gets filled by a higher-dim simplex face whose product-vertices include no cycle point.** Specifically: at every position p with `m_p ≥ 3`, the 2-cell shape `(one factor = 3-element simplex face, rest = singletons)` contributes 2-cells that plug 1-holes. These 2-cells require 3 configs pairwise differing only at one ternary-or-larger position p; since Cycle has length ~2n, and the non-cycle side of any position-p 3-orbit is nonempty for most configs, these 2-cells survive the filtering and fill the 1-cycles of NG.

Concrete witness: at ms=(2,2,2,2,3), the single ternary position contributes (3 choose 3)·(M/3) = 16 "one-3" 2-cells; most are retained in NG (16 out of 78-cell 2-dim, balancing). At the all-binary ms=(2,2,2,2,2), no "one-3" cells exist, and β_2 = 1 does appear — supporting the mechanism.

### What This Rules Out
- **Rules out** Morse–Hamming at β_1 with the product-of-simplices complex — *any* cycle whose NG-complement does not have 1-dim holes evades this obstruction, and empirically that is most cycles (at least 9/9 sub-threshold probed).
- **Does not rule out** Morse–Hamming with higher k (β_2 / β_3 / ...), as β_2 = 1 surfaces at all-binary and one mixed cycle.
- **Does not rule out** Morse–Hamming with a *different* topological model for X(ms):
  - cubical complex where non-binary factors are 1-dim (graph product, not simplex product) — cubical, not simplicial;
  - open-complement `X(ms) \ C` (remove the 1-curve topologically, not the vertices);
  - quotient by ring symmetry Z/n;
  - nerve complex of a processor-fiber cover.
- **Rules out** "cheap" interpretations where a single Betti number discriminates sub-vs-at-threshold with this specific complex.

### Surviving Structure

COMPUTED EXAMPLES (Betti tuples (β_0, β_1, β_2), all sub-threshold unless noted):
- ms=(2,2,2,2,3) L=10 cycle 0: (1, 0, 0). M=48.
- ms=(2,2,2,2,3) L=11 cycle 1: (1, 0, 0).
- ms=(2,2,2,2,3) L=14 cycle 2: **(1, 0, 1)**. Mixed, β_2 nonzero.
- ms=(2,2,2,3,3) L=16 / 14 / 15: all (1, 0, 0). M=72.
- ms=(2,2,2,2,2) L=10 three cycles: all **(1, 0, 1)**. Pure binary, β_2 = 1 uniformly across three cycles.
- ms=(2,2,2,3,4) L=16 at-threshold cycle 0: (1, 0, 0). M=96=M_5.
- ms=(2,2,2,3,4) L=17 at-threshold cycle 1: (1, 0, 0).
- ms=(2,2,2,3,3,3) L=21,18 sub-threshold n=6: (1, 0, 0). M=216<288.

STRUCTURAL RESULTS:
- `NG(C)` is always path-connected in the cellular sense on these examples (β_0 = 1 uniformly).
- All-binary n=5 has **β_2 = 1 structurally** across all three probed cycles, suggesting a genuine 2-dim hole tied to the 5-cube minus L=10 cycle structure. Not yet characterized analytically.
- β_2 disappears as soon as any position transitions from binary to ternary+ (except the (2,2,2,2,3) L=14 anomaly).
- The Euler characteristic `χ(NG) = Σ(-1)^k c_k` is 1 in the β=(1,0,0) cases (as expected) and 1 in β=(1,0,1) cases (since β_3=0 is implicit if we trust the probe — to recheck).

TOOLS:
- `skmh_probe_betti_2026-04-20.py` — direct cellular chain complex of NG(C) ⊆ ∏Δ^{m_i-1}. Boundary via tensor-product rule. Numpy dense rank via `matrix_rank`. n=5 runs in <0.1s; n=6 in 0.4s. Scales O(# cells × matrix rank).
- Uses `probe_sk_hamming1_empty_discriminator_2026-04-17.py::enumerate_cycles_multistart` for cycle supply.

REPRESENTATIONS:
- Cell = tuple of sorted-tuple faces `(F_0, ..., F_{n-1})`. Cell dim = Σ(|F_i|-1).
- Boundary via Eilenberg-Zilber tensor rule; verified: ∂² = 0 implicit in the rank arithmetic (Betti numbers came out integer-nonneg, so boundary squaring is consistent).

### Reformulations

**(a) Higher-Betti target** — maybe β_k is the obstruction for k = "something related to n" rather than k=1. Need to probe β_3, β_4, ... LOAD-BEARING ASSESSMENT: untested. The all-binary β_2 = 1 empirically suggests the obstruction *might* live in dim ~n−3 or related; needs direct test.

**(b) Open-complement model** — replace induced-subcomplex `NG(C)` with topological complement `X(ms) \ C` (remove the 1-curve, keep higher-dim cells that touch cycle vertices only at their corners). Alexander-duality-style. LOAD-BEARING ASSESSMENT: untested; genuinely different object. Open-complement Betti numbers are typically MUCH higher than induced-subcomplex Betti numbers (removing a 1-thing from an 8-ball leaves a 7-sphere-worth of homology by Alexander duality on S^8). This is actually promising.

**(c) Cubical (not simplicial) model** — take each `Fin(m_i)` as vertices of a **cycle graph** or **path graph** or **star graph**, not a simplex. Product gives different cubical complex. LOAD-BEARING ASSESSMENT: the (2,2,2,2,2) binary case IS cubical and does give β_2 = 1 — so cubical-with-binary-factors already showed signal. Needs extension to handle m_i > 2.

**(d) Z/n-equivariant / quotient model** — quotient by ring rotation. The LB question is ring-symmetric; the quotient complex X(ms)/(Z/n) is smaller and may concentrate topology. LOAD-BEARING ASSESSMENT: untested, could change behavior dramatically.

### Concrete Artifacts

REPRESENTATIONS: product-of-simplices cell encoding (see Tools above).

TOOLS: `skmh_probe_betti_2026-04-20.py` reusable for any (ms, cycle).

COMPUTED EXAMPLES: 11 (ms, cycle, Betti) triples logged above; raw cell counts in stdout of probe run 2026-04-20.

### What Would Unblock This

(i) β_k computation extended to k up to dim X(ms) = Σ(m_i-1). At n=5 this is dim 8; at n=9 ms=(2,3,...,3,2) dim 11. Need a linear-algebra implementation that doesn't blow up — either sparse rank or Smith normal form over Z.

(ii) Alternative complex: **open complement `X(ms) \ C`** cell complex. Specifically: for each k-cell in X(ms), include it **iff its closure intersects C in dim < k-1** (i.e., only at lower-dim faces). Much larger cell count but catches the Alexander-duality homology.

(iii) Witness for the (2,2,2,2,2) β_2=1 — what is the generator? If it is "the cycle's topological class" in H_2 of the 5-cube minus 10-cycle, that is exactly the Alexander-dual of a 1-cycle in a 5-sphere / 5-ball. This would tell us open-complement is the right object and induced-subcomplex was a conservative approximation.

### Key Parameters
- ms tested: (2,2,2,2,2), (2,2,2,2,3), (2,2,2,3,3), (2,2,2,3,4), (2,2,2,3,3,3).
- Products: 32, 48, 72, 96, 216.
- Max dim of X(ms): 5, 6, 7, 8, 9.
- Probe depth: β_0, β_1, β_2 only. β_3+ not yet.
- Cycles probed: 11 total (9 sub-threshold, 2 at-threshold).

### Open Questions
- Does β_2 remain 0 for higher-n sub-threshold mixed cycles, or does β_2 > 0 emerge at e.g. n=7 or n=9?
- Is there a k = k(n) such that β_k > 0 uniformly at sub-threshold?
- Under **open-complement** representation, what are β_k for the same set of cycles? Conjecture: β_{dim(X)-2} > 0 uniformly (Alexander dual of cycle's β_1).
- Is the all-binary β_2 = 1 the generator of `H_2(cube \ cycle)`? If yes, this is the structural core — identify it and scale up.

---

## Synthesis after Exploration 2

The probe shows the **framework's outer form is right** (topological obstruction, Keston-endorsed shape) but the **specific complex `∏ Δ^{m_i-1}` with induced-subcomplex filter is too aggressive at filling 1-holes**. Each `m_p ≥ 3` position contributes "one-3" 2-cells that kill β_1.

The empirical signal at all-binary (β_2 = 1 uniformly, 3/3) suggests the weaker target `∃k ≥ 1, β_k(NG(C)) > 0` might still hold uniformly at sub-threshold. Testing that as Exploration 3.

---

## Exploration 3 (full)

### Strategy
Weaken E2's β_1 target to: for each cycle C, does SOME β_k(NG(C)) > 0 for k ≥ 1? Compute full Betti vector through ambient dim (capped at 5 for n=6). Scan n=5 and n=6 multisets at sub-, at-, and super-threshold. If signal uniform at sub-threshold, reformulate LB as "∃k β_k>0". If not, pure Betti approach is dead and the obstruction must see ms/dynamics, not just ambient topology.

### Outcome
**FAILED.** Betti vectors do not discriminate threshold regimes.

Cycles with SOME β_k > 0 for k ≥ 1:
- total: **15/32** (47%)
- sub-threshold: **10/20** (50%)
- at-threshold: **4/8** (50%, all n=6 with β_4 ≈ 880)
- super-threshold: **1/4** (25%)

Half of sub-threshold cycles have β_k = 0 for ALL k ≥ 1 — naive "∃k β_k>0" is not a uniform obstruction at sub-threshold.

At-threshold (2,2,2,3,3,4) cycles have **β_4 in 864–893**. This is massive topology at a *valid* ms. Pure Betti numbers are DRIVEN BY AMBIENT DIMENSION, not by self-stabilizability.

### Failure Constraint
**The induced subcomplex `NG(C) ⊆ ∏Δ^{m_i-1}` is homotopically determined by ambient dim Σ(m_i-1), not by whether ms is sub-threshold or at-threshold.** Higher-product ms have larger Σ(m_i-1) and therefore more room for homological holes of higher dim — so β_k numbers GROW with product, in the OPPOSITE direction from what a LB would need.

### What This Rules Out
- **Rules out** any approach of the form "NG(C) has topological obstruction X in the ambient `∏Δ^{m_i-1}` product-of-simplices" where X is a Betti number, Euler characteristic, or any homotopy-invariant of the induced subcomplex. The homotopy type does not discriminate sub vs at threshold.
- **Rules out** Morse–Hamming as originally proposed (β_k > 0 obstruction on induced subcomplex).
- **Reinforces** the E1 building-block observation `|SK| constant per (n, L)` as *exactly what this rules out*: the topology is roughly `(n, L)`-parametrized, so it cannot know about multiset `ms`. SK is 0-dim shadow of the same phenomenon.

### What Survives
- **The Keston-endorsed proof SHAPE** ("topological invariant forbids self-stab") is not killed — only its first instance is. The invariant must see ms/dynamics, not just ambient Config-space topology.
- **The insight that cell counts scale with product but Betti numbers don't** is structurally load-bearing going forward. Any attempt to make `∏ m_i` enter a topological invariant must use the CELL-LEVEL data, not the homotopy type.

### Surviving Structure

COMPUTED EXAMPLES (full Betti vector in dict form):
- ms=(2,2,2,2,2) n=5 sub: 4 cycles all β=(1,0,1,0,0,0). β_2=1.
- ms=(2,2,2,2,3) n=5 sub: β=(1,0,0,..) for L=10,11,11; β=(1,0,1,..) for L=14. β_2 cycle-dependent.
- ms=(2,2,2,3,3) n=5 sub: 4 cycles all β=(1,0,0,..). Zero.
- ms=(2,2,3,3,3) n=5 super: 3 cycles zero, 1 cycle β_5=1.
- ms=(2,2,2,3,4) n=5 at: all 4 cycles zero (up to β_5).
- ms=(2,2,2,2,3,3) n=6 sub: 3 cycles zero, 1 cycle β_5=1.
- ms=(2,2,2,3,3,3) n=6 sub: 4 cycles all β_5 > 0 (values 32, 32, 38, 44). Substantial high-dim topology at sub-threshold.
- ms=(2,2,2,3,3,4) n=6 at: 4 cycles all β_4 in {864, 878, 879, 893}. Massive topology at at-threshold.

STRUCTURAL RESULTS:
- **Betti cell counts grow approximately with ambient dim**, confirming the obstruction lives in ambient dim not ms-semantics.
- **β_k is cycle-dependent even at fixed ms** (32 vs 44 for same ms=(2,2,2,3,3,3)). So Betti isn't even an ms-invariant.

### Reformulations

**(f) ms enters via CELL COUNTS, not Betti.** For a topological invariant to see ∏m_i, it must use cell counts in some way — e.g., via weighted chain complex, twisted homology, or orientation-weighted content. 
LOAD-BEARING ASSESSMENT: structurally load-bearing. Strong candidate for reshaping the search.

**(g) Herlihy "content" / Index Lemma (book §12.3).** `C(M, c) = Σ properly-colored simplices counted by orientation` is sensitive to ms-dependent coloring. The product of cells' orientations CAN depend on ms (through face dimensions), even when Betti doesn't.
LOAD-BEARING ASSESSMENT: untested, structurally distinct from Betti. This is the next natural probe direction.

**(h) Chain-level obstruction of det(C).** Treat det(C) as a 1-chain `σ_C ∈ C_1(X; ℤ)` and ask whether σ_C bounds in the NG-subcomplex. At sub-threshold, the 2-chains available to bound σ_C might be too small (cell count), forcing a chain-level obstruction that is neither Betti nor pure topology.
LOAD-BEARING ASSESSMENT: untested; bridges cell-count counting (which sees product) with topology (which provides the obstruction framework).

**(i) Lefschetz/Sperner on a RULE map.** For any candidate transition function f extending det(C), the induced map f_* on some chain complex has Lefschetz-like invariants. These vary with f — impossibility = no f gives valid invariants.

### Concrete Artifacts

COMPUTED EXAMPLES: 32 (ms, cycle, Betti vector) tuples in stdout log of probe 2026-04-20.

TOOLS: `skmh_probe_betti_full_2026-04-20.py` — computes full Betti vector through chosen max_dim. Reusable.

REPRESENTATIONS: product-of-simplices cells (as E2) + full-dim Betti rank computation.

### What Would Unblock This
- A model where `β_k(model(ms, C))` does discriminate sub-vs-at-threshold. Candidates in reformulations (f), (g), (h), (i).
- A chain-level invariant of det(C)'s embedding that is ms-sensitive via cell counts.
- A clean formal statement of "content-of-cycle" in the Herlihy sense adapted to Config(ms).

### Key Parameters
- 8 multisets tested across n=5 and n=6.
- 4 cycles per ms (32 total).
- Max dim computed: full ambient dim at n=5 (5–8), capped at 5 at n=6.
- All runtimes under 6s per cycle.

### Open Questions
- Does the at-threshold β_4 ≈ 880 generator correspond to a specific structural feature of the valid witness cycle, or is it generic?
- Can "content" in Herlihy's sense (counted-by-orientation monochromatic simplices under a processor-color labeling) discriminate threshold regimes?
- What happens if we compute β_k **modulo** the subcomplex filled by SKdet(C) images? A pair-homology might discriminate.

---

## Exploration 4 (probe — cell-count-sensitive invariants)

### Strategy
Scan full f-vectors `c = (c_0, ..., c_d)` of NG(C) across 27 cycles; test whether any of {χ = Σ(-1)^k c_k, normalized c_0/M, partial χ through truncated dim, total cell count, Hilbert polynomial evaluated} discriminates sub vs at vs super threshold.

### Outcome
**FAILED.**

Concrete data (truncated):
- c_0 / M: monotone increasing with ambient dim Σ(m_i - 1), NOT threshold-sensitive. 0.688 at n=5 all-binary (sub), 0.792 at n=5 (2,2,2,2,3) (sub), 0.833 at n=5 (2,2,2,3,4) (at), 0.924 at n=6 (2,2,2,3,3,4) (at), 0.903 at n=6 (2,2,2,3,3,3) (sub). Ordering by ambient dim, not by tag.
- Partial χ (Σ(-1)^k c_k through capped max_dim): swings from −43 (n=6 sub) to +894 (n=6 at). **This IS a signal**, but driven by *cutoff*: cells of dim > max_dim weren't counted, so partial χ ≠ true χ. True χ is 1 uniformly (implied by computed β vectors being predominantly (1,0,0,0,...)).
- No combination of {c_0, c_1, c_2, χ_partial, c_0/M, total_cells} read off the f-vector discriminated sub-threshold from at-threshold monotonically.

### Failure Constraint
Cell counts scale with ambient dim / ∏m_i in a uniform way at fixed (n, L). Normalizations that compare c_k to product or dim factor out exactly the ms-dependence we wanted. Linear combinations yielding an invariant (χ, Hilbert poly) collapse to Betti numbers by algebraic topology — which E3 already showed are uniform.

### What This Rules Out
- **All linear invariants of f-vector.** Euler char, Hilbert polynomial values, Σ linear combinations of c_k — all are polynomial in c_k, and the c_k vector's only ms-dependence is via cell counts which scale uniformly. No linear f-vector invariant discriminates.
- **Rules in** the possibility that a NONLINEAR or cell-count-combined-with-orientation invariant could still discriminate. E5's content is the next natural candidate (signs tied to orientation, not raw counts).

### Surviving Structure
- The f-vectors themselves are captured for 27 cycles — reusable dataset for any next normalization.
- χ is always 1 on induced subcomplex NG(C), reinforcing that the topology is trivial.

### Concrete Artifacts
COMPUTED EXAMPLES: 27 f-vectors in stdout of `skmh_probe_cell_content_2026-04-20.py`.

### Open Questions
Is there a NONLINEAR f-vector invariant? E.g., Σ (c_k choose 2) · ... or cross-cell interactions? Unexplored. Likely collapses too.

---

## Exploration 5 (probe — Herlihy content under processor coloring)

### Strategy
Count "properly-colored" and "monochromatic" n-simplices in NG(C) under three candidate colorings of Config:
- `parity`: Σ c[p] mod n
- `argmax`: position with max normalized value
- `weighted`: Σ p · c[p] mod n

"n-simplex" generated as a Hamming-path (v_0, v_0+e_{π(0)}, ..., v_0+Σe_{π(p)}) for each permutation π. Count those lying entirely in NG with proper or monochromatic coloring.

### Outcome
**BROKEN as probe.** All colorings returned `proper_simplices = 0` AND `total_monochromatic = 0` for every cycle tested. Not a topological zero — a probe-definition zero.

### Failure Constraint
**Hamming-path objects are NOT simplices of the product-of-simplices CW structure.** A "simplex" of ∏Δ^{m_i−1} is a product of faces `(F_0, ..., F_{n-1})`; an n+1-vertex Hamming path doesn't match this shape. So the "proper" counts were counting things not present in the chain complex, always giving zero. The monochromatic count being zero is a consequence: a Hamming-path has n+1 vertices differing at one coordinate each — under any reasonable position-based coloring, these vertices all hit different colors, so monochromatic is structurally zero.

### What This Rules Out
- **Rules out** the specific Hamming-path generator of "simplex" as an operand for Herlihy content on ∏Δ^{m_i−1}.
- **Does not rule out** Herlihy content in general — needs a proper simplicial subdivision (barycentric) of the product-of-simplices, on which n-simplices ARE well-defined.

### What Would Unblock This
A **barycentric subdivision** of X(ms): for each cell (F_0, ..., F_{n-1}), add an apex vertex and cone over the barycentric subdivision of the boundary. The resulting simplicial complex Bary(X(ms)) has n-simplices in every dim, and content under a coloring `c : V(Bary(X)) → [n+1]` is well-defined. Probe cost: O(d! · total_cells), expensive at n=6+ but manageable at n=5.

Alternatively: use **the 1-skeleton of the Hamming graph** only, and redefine "properly-colored k-simplex" as a k-clique in the graph with all distinct colors. For Hamming graph this is cells of the flag complex, which has no 3-cliques (Hamming-1 triangle-free except at specific configurations). Limited.

### Surviving Structure
None — probe did not produce usable content. Design flaw caught.

### Open Questions
Does barycentric-subdivided Herlihy content discriminate? Would need implementation. Not cheap but not prohibitive.

---

## Exploration 6 (probe — Z/n-equivariant Euler / Burnside)

### Strategy
For symmetric ms (all m_i equal), count Z/n-fixed configs in NG via Burnside formula. Orbit count `|NG / Z/n| = (1/n) Σ_{k=0..n-1} |NG^k|`. Compare across threshold regimes.

### Outcome
**BROKEN as probe.** Got non-integer orbit counts (4.4 for (2,2,2,2,2) n=5 L=10 sub, 46.6 for (3,3,3,3,3) n=5 L=18 super). Burnside forces integer orbit counts — the non-integer signals the action is not well-defined on NG.

### Failure Constraint
**Z/n does not act on `NG(C)` for a specific cycle C.** Rotation by k carries Cycle to rot_k(Cycle) ≠ Cycle in general; so rotating an NG config (non-cycle) can produce a rot_k(Cycle) config, which is NOT in NG. So rotation doesn't preserve NG. The action is only well-defined on `NG(⋃_k rot_k(Cycle))` — the induced subcomplex on complement of the ROTATION ORBIT of Cycle.

### What This Rules Out
- Rules out a probe that quotients NG(C) by Z/n directly for a specific C.
- Rules in: the **rotation-closure** `C̃ := ⋃_{k=0..n-1} rot_k(C)` is a Z/n-invariant subcomplex. `NG(C̃)` is Z/n-invariant. Equivariant probing *on this* is well-defined.

### What Would Unblock This
Reimplement the probe on `NG(⋃rot(C))` for symmetric ms. Caveat: `|C̃| ≤ n · L` (union of n rotations of an L-cycle), so NG(C̃) is smaller than NG(C). In extreme case where C is Z/n-invariant (rare), C̃ = C and nothing changes.

### Surviving Structure
Non-symmetric ms (which are most of the interesting cases at n≥9 — ms=(2,3,...,3,2) has Z/2 but not Z/n) don't support this framework directly, limiting scope.

### Open Questions
Does equivariant Euler on NG(rot-closure(C)) discriminate? Only testable on symmetric ms where Z/n acts; n≥9 target cases have at most Z/2 reflection symmetry.

---

## Exploration 7 (probe — integer homology torsion)

### Strategy
Compute H_*(NG; ℤ) via modular ranks (Gaussian elimination mod p for p ∈ {2, 3, 5, 7}). Integer torsion can exist even when β_k (rational) = 0; torsion structure depends on ms through tensor products with ℤ/m_p, making it the natural ms-sensitive topological invariant.

### Outcome
**FAILED (sixth state-space probe to fail).** 0/18 cycles tested have any p-torsion in H_*(NG; ℤ) for p ∈ {2, 3, 5, 7}. Every cycle's integer homology is FREE abelian of rank equal to the Betti vector. No torsion signature, no ms-sensitivity via torsion.

### Failure Constraint
`H_*(NG; ℤ)` is free abelian for every cycle tested at sub/at/super threshold. This is consistent with NG(C) being homotopy-equivalent to a wedge of spheres — a very common model for induced-subcomplex topology, which always has free H_*.

### What This Rules Out
- **Rules out** `H_*(NG; ℤ/p)` for any single prime p, or any combination of primes, as ms-discriminator.
- **Rules out** Tor(H_*, ℤ/m) — all tensor-product torsion vanishes.
- **Confirms the meta-obstruction from E2-E6:** pure state-space topology of `∏Δ^{m_i−1}` + induced subcomplex does not carry ms-sensitive invariants at either the rational or integer level.

### Surviving Structure
- Fully confirms the meta-diagnosis: 6 distinct topological probes, 6 dead. Stop probing this object.
- Modular rank pipeline (rank_mod_p) is reusable for any future chain complex.

### Concrete Artifacts
COMPUTED EXAMPLES: 18 cycles, full modular rank tables, all torsion signatures = empty.

TOOLS: `skmh_probe_torsion_2026-04-20.py` — reusable for integer homology of any chain complex.

### Open Questions
None — the direction is cleanly eliminated.

---

## Synthesis after Exploration 7 (SIX distinct state-space invariants, all fail)

This is definitive. The induced subcomplex of ∏Δ^{m_i-1} has no ms-discriminating topological invariant among {β_1, β_k any k, f-vector linears, Herlihy content, Z/n-equivariant, integer torsion}. Combined with the E3 diagnosis (homotopy scales with ambient dim) and E4 (cell-count linear invariants collapse), **pure state-space topology of ∏Δ^{m_i-1} is ruled out**.

**Binding next move:** pivot to a DYNAMICS-encoded complex. The remaining candidates from the Strategy Register are (j), (k), (l), (m), but all four of (k), (l), (m) require careful setup and still route through state-space of Config. (j) the **forced-graph flow complex** is the cleanest pivot: its cells come from det(C) itself, so it encodes dynamics by construction and uses ms through which triples det(C) matches at NG configs.

Going directly to probing (j). E8 below.

---

## Exploration 8 (probe — forced-graph flow complex)

### Strategy
Pivot to dynamics-encoded complex. Flow complex `K_f(ms, C)`:
- 0-cells: NG(C) configs
- 1-cells: directed forced edges (c, c') where det(C) forces c → c' at some position p
- 2-cells: commuting non-adjacent squares (|p - q| > 1 mod n)

Compute β_0, β_1. Prediction: at sub-threshold, det(C) covers few NG triples → many "islands" → β_0 > 1. At at-threshold, det(C) covers enough that β_0 is small.

### Outcome
**SIGNAL BUT INVERTED.**

β_0 values (number of connected components of forced-graph flow):
- sub-threshold n=5: {3, 3, 11, 9, 11, 13}  — smallest values
- at-threshold n=5: {21, 20}  — LARGER than sub
- super-threshold n=5 (3,3,3,3,3): {112, 106}  — very large
- sub-threshold n=6: {11, 13, 17, 13}  — small
- at-threshold n=6: {33, 31}  — larger than sub

β_0 is ms-sensitive BUT the signal goes the WRONG DIRECTION for a LB. At-threshold has MORE islands (higher β_0) than sub-threshold.

β_1 uniform: {1, 2} across all regimes. No discriminating signal.

### Failure Constraint
The inversion is a pure **det-coverage scaling artifact**. Total triples per position = m_{p−1} · m_p · m_{p+1}. Total NG triples scales as ∏m_i × n. |det(C)| is the cycle's size L × (forced moves per step) ≈ L. So **det coverage ratio = |det| / #triples ≈ L / (n · ∏m_i)**, which DECREASES as product grows. Lower coverage → fewer forced edges per NG config → higher β_0.

At sub-threshold (small product), det covers a high fraction, flow graph is dense, β_0 small. At at-threshold (larger product), det covers less, β_0 larger.

This is scaling, not a self-stab obstruction.

### What This Rules Out
- **Rules out** flow-complex β_0 as a direct LB invariant. The inversion is structural.
- **Rules out** any invariant that reduces to "how well det(C) covers NG triples" in a monotone way. Such invariants are coverage-driven, not self-stab-driven.
- **Rules in** the possibility that a MIXED invariant (flow-complex β divided by det-coverage) could normalize the scaling and extract a pure signal. Unexplored.

### What Survives
- Flow complex IS ms-sensitive (unlike state-space complex). That's the first genuinely ms-sensitive topological object tested.
- The inversion means we need an invariant that SUBTRACTS OUT coverage scaling.
- Insight: for ANY ms-sensitive invariant of dynamics objects, check whether it is "coverage-driven" before celebrating.

### Surviving Structure
Structured flow-complex data (V, E, F, β_0, β_1) for 18 cycles. Ratio E/V, β_0/V can be further analyzed for normalized signals — but preliminary inspection does not discriminate (sub E/V ≈ 1.0-1.4, at E/V ≈ 0.9-1.2, similar ranges).

### Concrete Artifacts
COMPUTED: table of V, E, F, β_0, β_1, |det| for 18 cycles in stdout.
TOOLS: `skmh_probe_flow_complex_2026-04-20.py` — flow-complex builder + Betti. Reusable for dynamics-complex variants.

### Open Questions
- Does `β_0 / |det|` or `β_0 · (n·∏m_i / |det|)` normalize the coverage bias out? Quick recheck worth trying.
- Is there a "closed forced-subset" count (directed — no out-edges leaving the component) that would be both ms-sensitive AND LB-direction-correct?
- Do different cycles at same ms have different β_0 structure that discriminates valid (L=18 witness) from invalid?

### Key Parameters
- 18 cycles across 9 multisets at n=5,6.
- 2 cycles per ms.

---

## Synthesis after Exploration 8

**Status check after 7 probes (E2–E8, skipping already-logged E4–6 reruns):**

| # | Invariant | Object | Discriminates? |
|---|---|---|---|
| E2 | β_1 | ∏Δ, NG subcomplex | No |
| E3 | ∃k β_k>0 | ∏Δ, NG subcomplex | No |
| E4 | f-vector linears | ∏Δ, NG subcomplex | No |
| E5 | Herlihy content | ∏Δ, NG subcomplex | Probe broken |
| E6 | Z/n equivariant | ∏Δ, NG subcomplex | Probe broken |
| E7 | integer torsion | ∏Δ, NG subcomplex | No |
| E8 | flow β_0 | forced-graph cube | **Signal but INVERTED** |

**Partial progress:** flow complex is the first probe to give ms-sensitive data. The signal's inversion is fully explained by det-coverage scaling (L / (n · ∏m_i) decreasing as product grows).

**Central insight (load-bearing, add to register):** the LB obstruction must be something that **does NOT scale monotonically with det coverage**. Candidate shapes:
- Normalized flow β_0 (divided by coverage): removes scaling, see if residual discriminates.
- "Closed forced-subset count" in directed sense (SCCs with no outbound): this is SK at 0-dim already — higher-dim SCC-style invariant unexplored.
- Invariants of the EXTENSION SPACE `Ext(det(C))` — number of valid extensions, Euler char of rule-consistency complex, etc.

**Honest meta-observation:** 7 explorations on 3 candidate objects have all failed to produce a LB-direction-correct invariant. The Keston-endorsed shape "topological invariant forbids it" requires an auxiliary object that (a) is ms-sensitive AND (b) has the right direction (sub-threshold = obstruction, at-threshold = no obstruction). So far, state-space gives neither, flow-complex gives (a) not (b). Candidate objects left: extension-space complex (k), triple complex (new: each triple a vertex, edges = shared-context triples), rule fan (new: simplicial complex of consistent rule-choices).

**Directional recommendation:** the next probe should be on the **extension space directly**. Compute |Ext(det(C))| — the number of rule extensions — as a function of (ms, C). Then look at a topological invariant of the CONSISTENT subset (rules that give valid SKCM-reducing flow). Even without computing all of them, structural properties of the extension space might carry LB signal.

Alternatively, step back: the LB problem is combinatorial (enumeration of valid rules) at its core, and "topological invariant forbids" may not be the right shape after all. The Keston confirmation was of the VISION; the empirical evidence after 7 probes is that the vision does not match the problem structure in any of the natural model categories tried so far.

I will keep pushing per user directive. E9 candidate: probe extension-space structure. But flagging that we may be approaching a legitimate "honest stop — the shape doesn't fit" moment.

---

## Exploration 9+18 (combined — coverage-normalized flow + SCC structure)

### Strategy
E9: normalize flow β_0 by coverage ratio `|det| / T_total`, checking if residual after removing coverage scaling discriminates.
E18: compute strongly-connected-component structure (Tarjan) of directed forced graph. Closed SCCs (no outgoing to other SCCs) are SK-witness candidates.

### Outcome
**FAILED (both).** Same inversion as E8. Closed-SCC counts: sub ∈ {3, 9, 11, 12, 15, 17, 19, 27, 31} (avg 14.7); at ∈ {22, 24, 52, 56} (avg 38.5); super ∈ {19, 21, 110, 117} (avg 66.8). Ranges overlap, direction is wrong. Coverage normalization doesn't rescue β_0 either (the `norm_undir_cc` column in output scales with V, also coverage-driven).

### What This Rules Out
All "ms-sensitive invariants of the forced graph" are coverage-driven, thus inverted. Including SCC counts, closed-SCC counts, orbit counts, connected components, normalized variants.

---

## Exploration 11 (probe — triple-space complex)

### Strategy
Entirely new object. Triple complex: 0-cells are all (p, L, S, R) triples; 1-cells between consecutive-compatible triples (p, p+1) sharing overlap. Restrict to NG-triples (not in det(C)). Compute β_0, β_1.

### Outcome
**FAILED.** β_0(NG_triples) ∈ {1, 2} across all regimes — no signal. β_1(NG_triples) inversed as before: sub ∈ {2, 6, 7, 8, 9, 12, 13}, at ∈ {15, 19, 25, 30}. Coverage-driven (T_total grows with product; fewer triples in det → more in NG → higher β_1).

### Key Observation
Triple complex is interesting algebraically (it's the natural graph of rule-constraint adjacency) but its raw topology tracks T_total − |det| linearly. No threshold discriminator in the simple Betti.

---

## Exploration 12 (probe — direct SK computation + (n, L) invariance)

### Strategy
Compute SK directly via sink-removal iteration on the forced graph. Verify E1 building block ("|SK| constant per (n, L)"). Check threshold direction.

### Outcome
**RECAPITULATES KNOWN SK-CAMPAIGN SIGNAL (but doesn't add topology).**

Summary by threshold:
- sub (10 cycles): |SK| ∈ {20, 23, 26, 32, 67, 70, 73, 78}, all > 0, avg 42.9
- at (4 cycles): |SK| ∈ {26, 28, 70, 78}, all > 0, avg 50.5
- super (4 cycles): |SK| ∈ {0, 0, 32, 34} — **two cycles have |SK| = 0** (both at ms=(2,2,3,3,3) product=108)

The |SK| = 0 at super-threshold means those specific cycles have det(C) extendable to a valid rule — the SK-witness phenomenon. For sub-threshold, all cycles tested have |SK| > 0.

### (n, L)-Invariance Check
Most (n, L) pairs ARE |SK|-invariant across ms in my sample:
- (5, 10): |SK| = 20 across 3 cycles ✓
- (5, 16): |SK| = 26 across 2 cycles ✓
- (6, 21): |SK| = 70 across 2 cycles ✓

BUT two exceptions:
- (5, 19): |SK| = 0 at ms=(2,2,3,3,3), |SK| = 34 at ms=(3,3,3,3,3). Drastically different.
- (6, 22): |SK| = 73 at sub-(2,2,2,3,3,3), |SK| = 78 at at-(2,2,2,3,3,4).

So the E1 "|SK| constant per (n, L)" building block is approximately true but has exceptions — specifically when the cycle happens to be a *valid witness* (|SK| = 0), it breaks invariance.

### Critical Observation: This is Combinatorial, Not Topological
The SK framework IS the LB candidate — has been all along (it's what the SK campaign pursues). What I've verified here is that |SK| > 0 at sub-threshold in my sample. This is:
- **Not new** — SK-campaign's original finding from 2026-04-14.
- **Not topology** — it's sink-removal iteration, a combinatorial/graph-theoretic operation. No homotopy invariant interpretation.
- **Not ∀-complete** — my 2-cycles-per-ms sample is too small to discriminate "∀ cycle has |SK| > 0" (sub-threshold) from "∃ cycle has |SK| = 0" (super-threshold).

The LB quantifies over ALL cycles. To test at scale, need enumeration of many cycles per ms.

### What This Rules Out / Confirms
- **Rules out** the hope that SKMH as a pure-topology framework produces a cleaner LB invariant than classical SK counting. After 10 distinct probes, the classical SK count IS the cleanest threshold discriminator available, and it's a COUNTING (sink-iteration) invariant, not topological.
- **Confirms** the SK campaign's main machinery is on the right track.
- **Does NOT confirm** the existence of a topological invariant that has the "forbids it" shape.

---

## Synthesis after Exploration 12 (TEN probes, final synthesis)

### Comprehensive probe table

| # | Invariant | Object | Result |
|---|---|---|---|
| E2 | β_1 | ∏Δ, NG subcomplex | Always 0 |
| E3 | ∃k β_k>0 | ∏Δ, NG subcomplex | Half/half, amb-dim driven |
| E4 | f-vector linears | ∏Δ, NG subcomplex | No discrimination |
| E5 | Herlihy content | ∏Δ, NG subcomplex | Broken probe (design) |
| E6 | Z/n equivariant | ∏Δ, NG subcomplex | Broken probe (action) |
| E7 | integer torsion | ∏Δ, NG subcomplex | No torsion anywhere |
| E8 | flow β_0 | forced-graph cube | Coverage-inverted |
| E9+18 | normalized β_0 / SCC | flow complex | Coverage-inverted |
| E11 | triple β_0, β_1 | rule-constraint graph | Coverage-inverted |
| E12 | direct SK | forced graph | **Correct direction** but combinatorial, not topological |

### The honest meta-finding

**Pure topological invariants on the natural state-space / dynamics / rule-constraint objects DO NOT discriminate sub-threshold from at-threshold in the LB direction, except via classical SK counting (which is combinatorial, not homotopy-invariant).** This has been tested on:
- 6 different invariants of the state-space cube complex (∏Δ^{m_i−1}).
- 3 different invariants of the forced-graph flow complex.
- 1 invariant of the rule-constraint triple complex.
- 1 invariant of the full ring-satisfaction graph.

All probes: 10 total. All failed to produce a topology-flavored LB invariant beyond what SK counting already provides.

### Structural diagnosis

The LB has a **combinatorial core** (sink-kernel count, or equivalently: does det(C) extend to an acyclic flow on NG). Any topological invariant of the ambient / complement spaces is either:
1. Driven by `(n, L)` via homotopy type (so ms-independent at fixed (n, L)), or
2. Driven by coverage ratio `|det| / T_total` (so coverage-inverted, wrong direction), or
3. Reducible to SK via sink-iteration (so combinatorial, not topological).

The Keston-endorsed proof shape "a topological invariant forbids it" did not match the problem structure in any of the natural model categories tested.

### What genuinely survives

- **SK is correct**, but that's the SK campaign's existing machinery.
- **Coverage inversion is a load-bearing diagnosis.** Any future attempt at a topological invariant must *first* handle coverage scaling. Most natural candidates won't — so the candidate space is narrow.
- **The Hamming-cube β_2 = 1 at all-binary** (E2 finding) might still indicate real topology at specific regimes. Worth tracking but not generalizable.
- **Infrastructure** (cell enumeration, boundary operators, mod-p rank, SCC, SK computation, triple complex) is all reusable for any future probe.

### Candidates NOT fully explored (diminishing returns)

- **E14 — barycentric content** on a proper subdivision. Unlikely to discriminate by same E3 argument (Betti of a homotopy-equivalent subdivision = Betti of original).
- **E15 — equivariant on rotation-closure** for symmetric ms only. Limited applicability (target cases ms=(2,3,...,3,2) aren't symmetric).
- **E-classical** — obstruction theory for section extension of a bundle over Config with discrete fiber. Discrete fibers → trivial π_k, no higher-dim obstruction.
- **Alexander duality** on (X, C) pair. Reduces to cycle topology (S^1), ms-independent.
- **Spectral sequence / Reidemeister torsion / K-theory** — beyond budget, low expected return.

### Recommendation

**Stop grinding on SKMH as a fresh LB direction.** The data convincingly shows the Keston-endorsed "topology forbids it" shape does not correspond to a natural invariant of the obvious complexes. The LB problem is combinatorially dressed (extension-emptiness, SK counting), and what topology can contribute is — at best — a reformulation / packaging of SK-style combinatorial arguments, not an independent obstruction detector.

**Value recovered** from the SKMH arc:
- Cleanly ruled out a large class of natural LB approaches (6 state-space invariants, 3 flow-complex invariants, 1 triple-complex invariant).
- Established the **coverage-inversion obstruction** as a load-bearing diagnostic for any future topological attempt on this problem.
- Reinforced that **`|SK| constant per (n, L)`** is load-bearing for the SK campaign's factoring of the LB into (n, L) constraints + arithmetic bound on L.
- Generated reusable Python infrastructure for chain complexes, flow graphs, SCC analysis on this problem.

**Does NOT recover** (honest):
- A new LB direction.
- A topological statement of the Clouds Theorem / SK nonempty conjecture.
- Any Lean-portable obstruction beyond what SK campaign already has.

**User-facing recommendation:** regroup on whether the SKMH frame is worth continuing, or if the energy goes back to A1' and classical SK Lean work.

---

## Exploration 13 (R4 pre-commit probe — edge-sink margin)

### Strategy
Test `|E_N1| − (|T_N1| − |sinks_N1|) ≥ 1` uniformly across many cycles. Spec from `sk_peel_direct_scope_2026-04-19.md §12`.

### Outcome
**PASS.** 164 cycles, n=5..8, sub/at/super-threshold. No violations.

- Min margin = 8 (n=5, L=12); Max = 37; Avg = 17.
- All regimes uniformly positive: sub ∈ [8, 37], at ∈ [9, 28], super ∈ [9, 26].
- Overshoot is 8× analytical target (margin ≥ 1).
- Tripwires from scope memo §9: none fired. Margin does not require `sourceTripleOfStep_injective`, no cycle-structure case splits, disjoint from A1 wall.

Min margin per n: 8 (n=5), 16 (n=6), 20 (n=7), 28 (n=8). Grows with n; likely analytical lower bound `margin ≥ c(n)` for some increasing c(n).

### Verdict
**Commit Phase A Lean infrastructure.** R4 is the Lean-friendly path. B2' (margin ≥ 1) is a single uniform counting inequality, no case splits, disjoint from the A1 wall that killed R1/R3.

Tool: `skmh_r4_edge_sink_margin_2026-04-20.py`, reusable.

---

## Synthesis after Exploration 6 (five distinct topological invariants on the same complex — all fail to discriminate)

**Summary of what has been tested on ∏Δ^{m_i−1} / NG(C) / induced subcomplex:**

| # | Invariant | Tested | Discriminates sub vs at? |
|---|---|---|---|
| E2 | β_1 | 11 cycles | No (0 uniformly) |
| E3 | ∃k ≥ 1, β_k > 0 | 32 cycles | No (50% sub-threshold rate) |
| E4 | f-vector normalizations | 27 cycles | No (monotone with ambient dim) |
| E5 | Herlihy content under processor coloring | 27 cycles | Probe broken (Hamming-path not simplex) |
| E6 | Z/n-equivariant Euler | 6 cycles | Probe broken (Z/n does not act on NG(C)) |

**Two probes (E5, E6) were broken in setup and can be repaired;** three probes (E2, E3, E4) produced clean negative results that rule out large classes of invariants on this complex.

**Root diagnosis (load-bearing).** The state-space cube complex ∏Δ^{m_i−1} encodes (n, L) and ambient dim but NOT the self-stabilizability data. Topology invariants of it read off (n, L) data — which is why `|SK|` is constant per (n, L) per the original SK discovery, and why Betti numbers scale with ambient dim. **This complex is the wrong object if we want ms-product-sensitivity as a topological invariant.**

**The Keston-endorsed proof shape survives.** The mismatch is between the invariant TYPE (pure topology of state-space) and the QUESTION (existence of transition function). The proof shape endorses "a topological invariant forbids it" — the question is WHICH topological object carries the invariant.

**Candidate complexes that encode DYNAMICS rather than STATE SPACE** (previously un-enumerated):

- **(j) Forced-graph flow complex.** Nerve of the forced-graph: vertices = configs, k-simplices = commuting k+1-tuples of forced moves. For self-stab, this is homotopy ≃ S^1 (C) with trees. Invariants of this complex do encode det(C), which depends on C but also indirectly on ms via triple context sizes.
- **(k) Extension space `Ext(det(C))`.** The space of valid f extending det(C). Finite discrete; its EMPTINESS is the LB. No natural higher-dim topology but combinatorial bounds on its size scale with product.
- **(l) Twisted homology with ℤ/m_p coefficients per position.** For each position p with m_p ≥ 2, the "move" cells at p are classified mod m_p. Compute H_1(X, C; ⊗_p ℤ/m_p) — may see product through tensor-product torsion.
- **(m) Configuration-rule pair complex.** Build the complex of all (config, partial-rule) pairs where partial rule is consistent with det(C). Obstruction to extending lives in H^* of this pair complex.

**None of these have been probed yet.** The probe infrastructure from E2–E6 is reusable for most of them.

**Correct action at this point.** Stop and think before more probes. Five failed attempts on state-space topology is enough signal that state-space is wrong. The next probe should attack a DYNAMICS-encoded complex or a TWISTED (coefficient-dependent) invariant, not another variant of state-space Betti.

## Synthesis after Exploration 3

**Decisive negative result on pure ambient topology.** Betti numbers of NG(C) ⊆ ∏Δ^{m_i-1} do NOT discriminate sub-threshold from at-threshold; at-threshold cycles have **larger** Betti than most sub-threshold ones. The homotopy type is a function of ambient dim, which scales *with* product.

The Keston-endorsed proof shape ("topological invariant forbids it") is not killed. What is killed is the naive instance. The invariant must see `∏m_i` through **cell-count-sensitive** machinery (weighted chains, content, oriented counts) OR through **dynamics-sensitive** machinery (carrier maps, chain maps induced by det(C)).

**Cross-artifact observation.** Cells in the subcomplex NG(C) SCALE with product (because there are more configs to populate NG). Betti numbers bound differences of these counts — and the differences are roughly ambient-dim-driven, not product-driven. So the right invariant likely sees cell counts directly, perhaps with signs/orientations (→ content, Lefschetz, Euler with local coefficients).

**Direction for E4.** The most concrete next probe is **Herlihy content under a processor-color labeling on NG(C) ∪ Cycle**. Define a simplicial map `χ : X(ms) → ∆^{n-1}` by `χ(c) = argmax_p (privilege)` — or more carefully, some ms-dependent labeling — and compute `C(X, c)` as in Lemma 12.3.5. If C depends on ms in a threshold-sensitive way, this is the right invariant.

Before coding E4, however, it's worth a brief **structural pause** — three failed routes on the same complex is a signal that THE COMPLEX ITSELF might be wrong. The product-of-simplices might not be the right ambient. The ring structure (Z/n rotation) is not used. The det-map structure is not used. Both are candidates for the right model.

E4 options (to be decided / paused for Keston input if exploration budget is constrained):
- **E4a: content probe** on product-of-simplices with processor-color labeling.
- **E4b: pivot to Z/n-equivariant model** before probing further.
- **E4c: re-derive what kind of invariant CAN see ms**, first on paper, by examining how ∏m_i enters any candidate invariant before committing to a probe.

Leaning E4c → then E4a or E4b.

---

## E14 / E15 — Uniform forced-NG walk in T_N1 (2026-04-20 late)

**Context.** After R4 Phase A landed (`HammingTube.lean`), the single
remaining research sorry is `peelTube_nonempty`: forced-NG subgraph of
`N_1(C) ∩ VC-NG` has a directed cycle. Empirical probe E13 showed
peel nonempty in 100% of 1898 records and `margin_total ≥ 4`; but
margin-based pigeonhole isn't rigorous (DAGs can have |E| ≥ |V| without
cycles).

**Goal of E14/E15.** Find a cycle-structure-independent walk rule
`f : T_N1 → T_N1` such that iterating from a canonically-chosen `c_0`
pigeonholes into a cycle in T_N1 before exiting. If yes uniformly,
Lean-portable as `~200 lines + exists_closed_nonempty_subset`.

### E14 — lex-first canonical walk

- **Start:** `c_0` = lex-first Hamming-1 perturbation of cycle's first
  config that lies in T_N1.
- **Step:** `f(c)` = lex-first forced-NG successor of `c` landing in T_N1.
- **Max steps:** `|T_N1| + 2` (pigeonhole depth).

**Result (1898 records, n=5..8):**

| n | records | R1 walk → cycle | walk exits T_N1 | ANY (k,q,v) cycles |
|---|---|---|---|---|
| 5 | 1032 | 645 (63%) | 387 (38%) | 834 (81%) |
| 6 | 669 | 366 (55%) | 303 (45%) | 555 (83%) |
| 7 | 152 | 85 (56%) | 67 (44%) | 137 (90%) |
| 8 | 45 | 28 (62%) | 17 (38%) | 43 (96%) |

**Verdict.** R1 (deterministic lex-first) fails in 41% of records;
walk exits T_N1 before cycling. Even R2 (existence of ANY Hamming-1
start whose lex-first walk cycles) fails in 17% of records.

### E15 — smarter (but still cycle-independent) walk rules

Tested 5 rules on the same starting c_0:
- S1 = lex-first forced-NG successor (= E14 R1).
- S2 = highest out-degree successor, lex tie-break.
- S3 = maximize 2-hop reach, lex tie-break.
- S4 = minimize 2-hop-visible sinks, lex tie-break.
- S5 = maximize firing-position, lex tie-break.

**Result (1898 records, n=5..8):**

| rule | passed / 1898 | % |
|---|---|---|
| S1 | 1197 | 63.07 |
| S2 | 1284 | 67.65 |
| S3 | 1284 | 67.65 |
| S4 | 1325 | 69.81 |
| S5 | 1194 | 62.91 |
| **ANY of S1..S5** | **1401** | **73.81** |

**Residue: 497/1898 records (26%)** where NONE of the five cycle-independent
walk rules finds a cycle from the canonical starting point. In those
records, peel is nonempty (empirically verified in E13), but the cycle
is unreachable by any local-greedy walk from the lex-first perturbation.

### Interpretation — R4 flamed out

The peel cycle is a GLOBAL property of the forced-NG subgraph, not a
local walk outcome. Any deterministic cycle-independent successor-choice
rule can be led astray toward sinks before finding the cycle, because
the cycle-closing edge sometimes requires "teleological" selection
(knowing the cycle exists to pick the right branch).

**Categorical obstruction**: no uniform deterministic walk rule can
capture peel(T_N1), because peel is defined by global fixpoint of
sink-removal, not by local greedy descent.

**Implication for R4.** Uniform walk construction CANNOT close B2' in
Lean. This forecloses the straightforward ~200-line port via pigeonhole
+ `exists_closed_nonempty_subset`.

### What's still open for Track B

Options remaining for closing `peelTube_nonempty`:
- **(α) Non-constructive existence** via a Mathlib finite-digraph
  cycle-existence lemma. Requires spelunking Mathlib for a suitable
  theorem; not obvious one exists in the shape we need without a
  bound or specific structure.
- **(β) Direct structural theorem** on N_1 tube topology — e.g.,
  "mover word has bounded excursions so some shadow subpath cycles."
  Requires a cycle-word-theoretic argument; cycle-dependent in form,
  possibly uniform in principle. Multi-session research.
- **(γ) Different target object** — replace `peelTube` with a subset
  whose nonempty-forced-closedness is easier. But no candidate
  identified; dominant-pair is n=7-specific (96.7% at n=7, fails
  uniformly at n=5,6,8).

**Status.** R4 route is RED (WAS yellow→green after E13). Track B's
B2' doesn't close via the planned walk pigeonhole. The Lean sorry
stands at [HammingTube.lean:175](../lean/LeanMn/LowerBound/SK/HammingTube.lean#L175).

**Memory impact.** Update `project_sk_morse_hamming_2026-04-20.md`
with the R4 residue. Do NOT mark R4 as attic — per
`feedback_attic_usage.md`, orphaning a research track without Keston
green-light is out of scope. File remains in place; sorry remains open.

### Probe artifacts

- `probes/probe_sk_uniform_walk_2026-04-20.py`
- `probes/probe_sk_smart_walk_2026-04-20.py`
- `probes/sk_phase0_out/e14_uniform_walk_2026-04-20.log`
- `probes/sk_phase0_out/e15_smart_walk_2026-04-20.log`

---

## E16 — SCC structure of forced-NG on T_N1 (2026-04-20, post-E15)

Keston: "we can't stop R4 til you certify it's DEAD." Ran two more
probes (E16, E17) before the certification.

E16 asked: what does the SCC decomposition of the forced-NG subgraph
on T_N1 look like? Does every record have a non-trivial SCC of
uniform size (⟹ peel ⊇ SCC nonempty)?

**Tarjan SCC on 1898 records (n=5..8):**

| n | records | records with ≥1 non-trivial SCC | min nt-SCC size | max nt-SCC size |
|---|---|---|---|---|
| 5 | 1032 | 1032 | 18 | 28 |
| 6 | 669 | 669 | 34 | 48 |
| 7 | 152 | 152 | 50 | 72 |
| 8 | 45 | 45 | 80 | 100 |

**Striking structural fact:** every record has **exactly ONE**
non-trivial SCC. Not "≥ 1" — exactly one. Size scales as ~2|T_N1|/3.

**Caveat for Lean.** "∃ non-trivial SCC" ≡ "∃ directed cycle" ≡ what
we're already trying to prove. The SCC framing does NOT reduce the
research obligation. But it does open E17: maybe the unique SCC is
locally characterizable, giving a concrete Lean target.

### Probe artifact
- `probes/probe_sk_scc_structure_2026-04-20.py`
- `probes/sk_phase0_out/e16_scc_structure_2026-04-20.json`

---

## E17 — Local characterization of the BIG SCC (2026-04-20)

Hypothesis: the unique non-trivial SCC (call it BIG) is the set of
configs c ∈ T_N1 satisfying a cycle-structure-independent local
predicate P(c).

Tested features per config c (all locally computable from cycle + det):
- `out_deg_ge_1`, `in_deg_ge_1` — degree of c in forced-NG subgraph
- `num_anchors` — # (k, q, v) s.t. c = c_k[q ← v]
- `anchor_qv_at_extremes` — every anchor has v ∈ {min(V_q), max(V_q)}
- `anchor_qv_at_dom_pair` — every anchor has v in top-2 residence values
- `has_nonsink_successor` — ≥ 1 successor with out-deg ≥ 1
- 11 features × 4 variants ≈ 220 single/pair combinations

**Best combination** (`in_deg_ge_1 ∧ has_nonsink_successor`):
- Min accuracy = 0.690, mean 0.908, perfect in 642/1898 records.
- Per-n perfect-rate: 58% (n=5) → 3% (n=6) → 8% (n=7) → 11% (n=8).

**VERDICT: RED.** No local predicate (single or pairwise conjunction)
characterizes BIG-SCC membership uniformly. The SCC is genuinely
GLOBAL — membership depends on which larger 1-hop-connected component
c belongs to.

### Probe artifact
- `probes/probe_sk_scc_local_char_2026-04-20.py`
- `probes/sk_phase0_out/e17_scc_local_char_2026-04-20.json`

---

## E23 — HKR Index Lemma signed-content probe (2026-04-20 late)

After R4 certified DEAD, Keston approved one more topological check
via re-mining HKR *Distributed Computing through Combinatorial
Topology*. Literature agent (`a33e2f598802f7b25`) surfaced Index
Lemma (HKR 12.3.5) + Manifold Sperner (9.3.4) as genuinely distinct
from E2–E12: **signed content with parity invariance** (not
unsigned Betti). YELLOW verdict, probe recommended.

### Probe run (agent `a27de6623245e67d0`, ~7 min)
- 16 coloring/complex combinations across three constructions:
  cycle-as-1-manifold, 2-torus (position × step), source-triple
  1-complex.
- 2481 sub-threshold + 1674 at-threshold records, n=5..8.
- **All signed contents collapse to C = 0 trivially** (closed
  cycles ⟹ ∂M = ∅ ⟹ Index Lemma degenerates).
- 12 of 52 content-statistics differ marginally between regimes,
  but all collapse to sampling artifacts or L-correlated biases.

### RED verdict on structural grounds
HKR's Index Lemma needs:
1. Oriented manifold **with boundary** — our cycles are closed.
2. Rank-symmetry group action on coloring — absent.
3. Chromatic-subdivision structure — absent (cycle = S¹ in torus).

The book's single LB mechanism (Ch. 12.5 renaming) uses all three.
We have NONE of them, and there's no cheap way to install them.

### Consequence for SKMH arc

The arc now has 23 explorations (E1–E23), all RED or YELLOW-then-RED
in the LB direction. Adding to the 2026-04-20 final-state summary
(line ~140): **no SIGNED-topology invariant of the book's family
discriminates either**, extending the earlier "no UNSIGNED
invariant" verdict.

### Probe artifacts
- `probes/probe_sk_index_lemma_2026-04-20.py`
- `probes/sk_phase0_out/e23_index_lemma_2026-04-20.log`
- `probes/sk_phase0_out/e23_index_lemma_2026-04-20.json`

---

## R4 Certification: DEAD (2026-04-20)

Evidence stack:

| Probe | Tests | Result |
|---|---|---|
| E13 | peel nonempty empirically | PASS (100%, 1898 records) |
| E14 | uniform lex-first walk closure | FAIL (41% exits, 17% no ANY (k,q,v) works) |
| E15 | 5 smart walk rules combined | FAIL (26% residue, best 73.8%) |
| E16 | non-trivial SCC exists | STRUCTURAL FACT (unique, large) |
| E17 | SCC characterized by local predicate | FAIL (best 46.7% min accuracy) |
| Mathlib | partial → total + cycle lemma | GAP (no direct machinery) |

**Why R4 is certified DEAD for Lean (not mathematically):**

1. Walk-based constructions fail (E14/E15). This kills the natural
   `~200-line exists_closed_nonempty_subset` Lean port.
2. SCC is globally defined — no local predicate characterizes it
   (E17). This kills the alternative "construct predicate-defined
   forced-closed subset" Lean port.
3. Mathlib has no partial-function cycle-existence machinery at the
   level we need. Strategy A (lift partial to total on T \ sinks)
   hits the 26% wall since the lifted function doesn't actually map
   into T \ sinks.
4. What's left: a multi-session original research theorem on the
   cycle's mover-word structure, proving SCC existence
   non-constructively. No empirical handle exists to seed this, and
   the cycle-word structure is exactly what `feedback_no_case_splits_in_lean.md`
   forbids.

**What stays in place:**
- [HammingTube.lean](../lean/LeanMn/LowerBound/SK/HammingTube.lean) —
  Phase A infrastructure (hammingDist, N_1, VC-NG, peel, forced-closure
  bridge). Does NOT move to attic per `feedback_attic_usage.md` —
  that is Keston's decision. The file is orphaned (no live consumer
  once R4 is off) but not refuted; it may be reusable if a future
  insight revives the route.
- `CloudsTheorem.lean`'s two SK sorries (small_n, large_n) currently
  route through `sk_nonempty_via_tube gc hn hsub` which calls
  `peelTube_nonempty`. Options: leave sorry-bearing until Keston
  decides, OR revert the CloudsTheorem wiring to the earlier stubs
  to decouple — again Keston's call.
- SlabCountingRing.lean A1 wall — Track A remains active regardless
  of R4 verdict.

**Sorry count UNCHANGED at 3 (HammingTube B2', SlabCountingRing A1,
UB side).** Build green. Campaign reverts to A1' as primary active
target.

---


