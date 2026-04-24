# Candidate B'' — Morse–Hamming attack memo (attack 2)

**Written:** 2026-04-22. **Supersedes:** attack1 §§1–2 (girth-n
structural hook is dead at n ≥ 10). **Source data:**
`axis_c_candidate_c_betti_*`, `axis_c_cube_complex_betti_*`.

---

## 0. Recap — where we are after attack 1

Attack 1 (length-n girth + 4-window mover multiset) died at A3
scale-up: girth varies wildly (4, >15, >15, >15) at n=10/11, so the
n=9 "length-n cycle" is a numerical coincidence, not a mechanism.
What DOES survive after A1–A4 and the combined C+β₁ probe:

| invariant | min | max | corpus |
|---|---|---|---|
| SK_2 nonempty (`r* = 2`) | true | true | 63 |
| β₁_directed(forced-NG \| B_2) | **93** | 595 | 63 |
| β₁_undirected(forced-NG \| B_2) | **178** | 1738 | 63 |
| β₁_hamming(X\|B_2 \ cycle) | 465 | 14919 | 63 |
| β₁_hamming(X \ cycle, full complement) | 673 | 53834 | 63 |
| avg out-deg in B_2 | 0.997 | 1.846 | 63 |

Every sub-threshold candidate has a **very rich** topological cycle
space in its forced 2-tube — not barely nonzero, substantially so.

---

## 1. The target theorem

**Conjecture B''.** For every candidate `(m, cycle, movers, det)`
produced by the enumeration pipeline with `n ≥ 9` and `∏ m_i <
4·3^{n−2}`,

> `β₁_undirected(forced-NG | B_2(cycle) \ cycle) ≥ 1`.

Equivalent formulations:
- The forced-NG subgraph on `B_2(cycle) \ cycle` is not a forest.
- The number of undirected edges in forced-NG on B_2 is at least the
  number of vertices minus the number of connected components.
- `SK_2(det) ≠ ∅`  (equivalent via the existence-of-cycle ⇔
  forced-closed-subset theorem).

The empirical margin is enormous (≥ 178 vs ≥ 1), which is useful:
any moderately sloppy uniform argument that shows "E ≥ V" has room.

---

## 2. The Forman gradient construction

### 2.1 The cube complex `X(ms)`

Vertices: `V = ∏ Z_{m_i}`, indexed by configs.
1-cells: Hamming-1 pairs `{c, c'}` where `c` and `c'` differ in
exactly one coordinate.
2-cells: "squares" — unordered 4-tuples `{c, c + e_p(a), c + e_q(b),
c + e_p(a) + e_q(b)}` for distinct positions `p ≠ q` and values
`a ≠ c[p]`, `b ≠ c[q]`.
Higher k-cells similarly.

`X(ms)` is the standard product cube complex. It is contractible
(product of contractible intervals).

### 2.2 Removing the good cycle

Let `C ⊆ V` be the set of good-cycle configs. Form the subcomplex
`X(ms) \ C` by removing the cycle vertices and every cell incident
to them. This complex has

- `β_0(X \ C) ≥ 1` — the complement is nonempty.
- `β_1(X \ C)` — empirically 673–53834 on the corpus, so nonzero by
  a wide margin.

Geometric interpretation: each removed vertex creates (conjecturally,
roughly) a "hole" in the contractible cube, and the loops around
these holes are the β_1 generators.

### 2.3 The forced-NG subgraph

The forced-NG directed graph sits inside `X(ms) \ C`: its undirected
underlying graph is a subgraph of the 1-skeleton of `X \ C`.

**Critical observation.** Forced-NG's undirected β_1 is
`|E_forced| − |V_forced| + (#components)`. This reduces
Conjecture B'' to the **β_1 identity**:

>     |E_forced| − |V_B_2| + |components_forced| ≥ 1.

Per M2+M3 data (`axis_c_edge_majority_*`), the naive
"|E_forced| ≥ |V_B_2|" fails on some records (`[2,2,2,2,2,2,2,20]`
has E/V = 0.997 < 1). Components vary widely (2–182 on the corpus).
What DOES hold uniformly is the full β_1 identity, with
`β_1 ≥ 178` on every record.

### 2.3' The "β_1 is determined by the cycle" signal (corrected 2026-04-23)

On the family `[2, 2, 2, 2, 2, 2, 2, k]` for k = 2..20 (same 7
binaries, varying last state count), **β_1 = 178 exactly for every
k**. The extra configs added as k grows contribute isolated
components (no edges among them) but no new topological loops.

**Scope of invariance (corrected).** Corpus-wide sweep on the
97-record canonical corpus (see `paper_upgrade_3/
beta1_corpus_invariance.md`):

- 0/10 valid witnesses are INVARIANT (all LINEAR).
- 0/7 n=9 Table-7 sub-threshold records are INVARIANT (all LINEAR).
- 28/62 n ≤ 8 sub-threshold records are INVARIANT.

The interpretation "β_1 is a function of the cycle + det" holds ONLY
in the restricted regime of binary-dominated small-n sub-threshold
records. For valid witnesses and for n=9 sub-threshold, β_1 grows
linearly under ambient-m extension with slopes that scale with
cycle length.

**Mechanism (proved).** Let the p-slice at extension position p be
the forced-NG subgraph induced on `{c ∈ B_2 : c[p] = v_new}`. Under
partial det (cycle-visited triples only), no forced edge crosses the
p-slice boundary: positions p-1, p, p+1 have local contexts involving
v_new, which are not in det's domain. So the slice β_1 equals β_1 of
the cycle's forced-move structure restricted to positions q ∉ {p-1,
p, p+1}, induced on slice vertices. **The slope of β_1 under
extension of m_p equals β_1(p-slice)** — verified on 20/20 tests
(INVARIANT + LINEAR + MIXED) via `probe_beta1_slice_structure.py`.

**Invariance ⇔ p-slice is a forest** ⇔ the cycle's forced-move
restriction at positions q ∉ {p-1, p, p+1} creates no closed walks
on slice vertices. At valid witnesses the det is FULL, so the slice
inherits a dense forced-graph and is never a forest. At n=9 Table-7
sub, the partial det still produces dense-enough slices for
non-forest structure.

**Corrected slopes.** Re-measured on the deterministic probe at
n=8:

| family               | old claim | measured slope |
|----------------------|-----------|---------------|
| `[2^6, 3, k]`        | slope 7   | **slope 4**   |
| `[2^6, 4, k]`        | slope 11  | **slope 0** (invariant) |
| `[2^7, k]`           | constant β_1 = 178 | confirmed (slope 0) |
| `[2^5, 3, 3, k]`     | —         | slope 0 (invariant at β_1 = 241) |
| `[2^7, 2, k]` (n=9)  | —         | slope 0 (invariant at β_1 = 254) |

Reproducible via `probe_beta1_family_invariance.py`.

**Analytical target rescoped.** The "cycle-determined subgraph
`G_core(cycle, det)` with β_1 bounded below by a cycle quantity" plan
was built on a universality claim that the sweep disproves. The
replacement load-bearing claim is **β_1_base ≥ 11 uniformly across
all 92 analyzable records** (valid or sub-threshold). Conjecture B''
(β_1 > 0 on sub-threshold) is supported unconditionally at the base
ambient; invariance is a *side observation* with a known mechanism,
not the topological distinguisher.

### 2.4 A Forman gradient that witnesses the claim

On the undirected Hamming graph `H = 1-skeleton of X(ms)`, a natural
Forman gradient uses a lexicographic order:

1. Pick any total order `<` on configs (e.g., lexicographic).
2. For each config `c`, pair `c` with the smallest-`<` neighbor `c' <
   c` in `H` that has not already been paired.
3. Unpaired vertices = critical 0-cells.
4. Unpaired edges = critical 1-cells.

For the FORCED-NG subgraph on `B_2(cycle) \ cycle`, choose the order
to align with det: pair `c` with the det-image `c' = applyForced(c)`
when that image is in `B_2 \ cycle`. An unpaired edge becomes a
critical 1-cell exactly when it forms a cycle closure or a missing
det entry.

The Forman pairing satisfies `β_1(subgraph) = #critical 1-cells −
#critical 0-cells + #components`. This is a straightforward graph
identity, but rephrasing it via a discrete Morse function lets us
carry the argument to higher-dimensional variants without rewriting.

### 2.5 Higher-dimensional extension (2-cells and Morse inequalities)

If we extend to 2-cells (fill squares in the cube complex), the
Morse inequality becomes `β_1 ≤ #crit_1 − #crit_2`. For the
analytical argument, higher-dimensional fillings can only
DECREASE β_1, so the 1-skeleton β_1 is an UPPER bound on the
"topological" β_1 of `X \ C`, not a lower bound.

> **Important subtlety.** The empirically measured β_1 (≥ 178 for
> forced, ≥ 465 for ambient) is on the 1-skeleton. The TRUE β_1 of
> the cube complex is smaller — but whether it's still ≥ 1 uniformly
> depends on how many of the 2-cells of `X(ms)` are present in
> `X \ C | B_2`. This is a secondary computation.

For Conjecture B'' as stated (β_1 of forced-NG as a graph), the
1-skeleton is the right complex. The Forman gradient and Morse
inequalities are a clean framing, even though the final claim is
equivalent to SK_2 nonemptiness.

---

## 3. The analytical attack

### 3.1 Step A — reduce to edge-majority

Conjecture B'' ⇔ (single-component forced-NG in B_2) `|E| ≥ |V|`
⇔ (multi-component) `|E| ≥ |V| − C + 1`.

Empirically `C_forced ≤ C_hamming` and the Hamming graph on B_2 is
connected (`C_hamming = 1` in all 63 records). If we can show
`C_forced ≤ C` uniformly for some fixed small `C`, the edge-majority
claim becomes the real target.

### 3.2 Step B — count forced edges

For each position `p` and each cycle-config context `(l, s, r)`,
det's forced image `det[p, l, s, r] = v ≠ s` contributes a forced
edge `c → c'` for every `c ∈ B_2 \ cycle` with local context
`(l, s, r)` at position `p` and `c' = applyMove(c, p, v) ∈
B_2 \ cycle`.

The total edge count is thus:

    |E_forced| = Σ over (p, l, s, r) with det defined and v ≠ s
                 [# of c ∈ B_2 \ cycle with local context (p, l, s, r)
                  and c' ∈ B_2 \ cycle]

`B_2(cycle)` is a union of Hamming-balls around cycle configs; its
size scales like `|cycle| · O(n · max m_i)` at radius 2, roughly
polynomial in `n`.

Det coverage: det is defined at each cycle-visited context, so
|det-defined| ≈ `n · L` (one per cycle step, per non-mover
position). At L ≈ O(n²) (CLB-class cycles), |det-defined| ≈ n³.

Each det entry contributes O(some polynomial) edges into B_2 via
contexts that agree at (l, s, r). A precise count depends on the
multiset `m` and cycle geometry, but empirically stays O(V_B_2) —
yielding the observed E/V ratio ~ 1–2.

**The analytical target.** Prove that the sum above is ≥ V_B_2
uniformly in `(m, cycle, movers, det)` satisfying `∏ m < 4·3^{n-2}`.

### 3.3 Step C — the cycle-core identity (retracted 2026-04-23)

**This step is retracted.** The 2.3' universality claim on which this
construction rests fails on 64/92 analyzable corpus records. In
particular, β_1 grows linearly under ambient-m extension on every
valid witness and every n=9 Table-7 sub record. The "G_core
determined by (cycle, det) alone, inflation-invariant" picture does
not generalize.

What survives: a **corpus-wide lower bound** `β_1_base ≥ 11` on the
base ambient, which is an unconditional form of Conjecture B'' at
the tested records without any `G_core` detour. The load-bearing
claim is now positivity at the base ambient, not an inflation-
invariant cycle-determined quantity.

A **replacement target** for Step C is the positivity side
directly — prove `β_1(forced-NG | B_2) ≥ 1` at sub-threshold without
routing through G_core. The p-slice mechanism (invariance ⇔ forest)
is a separate local observation and does not discriminate
sub-threshold from valid (both have forest and non-forest slices
depending on cycle geometry).

Empirical anchor (corrected): on the pure-binary-plus-one-large
family `[2^7, k]`, β_1 = 178 constant for k ≥ 2 at n=8; this is a
property of the binary-dominated n=8 sub-threshold regime, NOT
universal.

**Candidate inequality.** Let `L = |cycle|`, `D = |det-defined with
v ≠ s|`, and `V_core = |{c : det has an entry at c's local context
for some position}|`. Then:

>     β_1(G_core) = D − V_core + C_core ≥ 1,

where `C_core` is the number of connected components of G_core.
All three quantities (D, V_core, C_core) are functions of
(cycle, movers) only — NOT of ∏ m_i.

The sub-threshold constraint `∏ m < M_n` does NOT appear directly.
Instead, it appears via the existence of a good cycle: at sharp
threshold `∏ m = M_n`, the cycle is the valid system's convergent
cycle; at sub-threshold, the cycle exists but completes into no
valid system. The edge-count D is well-defined either way; the
question is whether D ≥ V_core − C_core + 1 structurally, without
regard to ∏ m.

**This is an important simplification.** We have reduced Conjecture
B'' from a `∏ m`-dependent inequality to a `(cycle, movers)`
inequality. The analytical proof is now in the realm of good-cycle
combinatorics, which has been extensively studied in the CLB /
CUP-2 development.

### 3.4 What sub-threshold actually imposes

At sub-threshold, the candidate `(cycle, movers, det)` must be such
that NO completion `f` of det to a total transition function yields
a valid system. The β_1(G_core) ≥ 1 fact is a topological
obstruction witness — it shows some G_core-trajectory is
inescapable, hence no f can converge.

But β_1(G_core) ≥ 1 is *always* true if the cycle is non-trivial
(L ≥ 3), because det-defined edges naturally form short cycles. The
REAL obligation is:

>     β_1(G_core) ≥ 1 ⇒ SK nonempty in G_core ⇒ SK nonempty in
>     forced-NG ⇒ SK nonempty in full forced-NG, regardless of
>     extension.

The first two implications are graph-theoretic (β_1 ≥ 1 ⇒ cycle
exists ⇒ sink kernel nonempty). The third is the PartialDet.lean
monotonicity bridge already shipped.

So **the entire Morse–Hamming chain reduces to: β_1(G_core) ≥ 1 for
every cycle + det arising from sub-threshold enumeration**.

### 3.4 Kill criteria

- If Step C analysis shows that `|E_forced|/|V_B_2|` can dip below
  1 at some worst-case sub-threshold configuration (even
  hypothetically, not in the corpus), the edge-majority route dies
  and we pivot to a sharper counting argument that uses
  `C_forced ≤ C_hamming − k` for some specific `k`.
- If the sub-threshold inequality needs case-splits on
  `(k_binary, state multiset, cycle length class)`, per
  `feedback_no_case_splits_in_lean` the route dies.
- Attempts: 3 total at the edge-majority lemma, then pivot to the
  higher-dimensional Morse formulation with 2-cells.

---

## 4. Pre-committed probes

### 4.1 Probe M1 — DONE

Measured `β_1_hamming(B_2 \ cycle)`, `β_1_forced(B_2)`, and ratio.
Results: β_1_forced uniformly ≥ 178, ratio median 11%.

### 4.2 Probe M2 — "Tree + margin" decomposition

For each record, compute:
- A spanning tree `T` of the undirected forced-NG subgraph on
  `B_2 \ cycle` (one per component).
- `|E_forced| − |T|` = number of non-tree edges = β_1_forced.

If `|E_forced| − |V| + C_forced` is consistently ~O(|V_B_2|), the
cycle basis is rich and the edge-majority route is comfortable.

### 4.3 Probe M3 — `C_forced` vs `C_hamming`

For each record, compute the number of connected components of
forced-NG | B_2 (undirected). `C_hamming = 1` on all records; the
question is whether `C_forced` can grow — if so, the edge-majority
shift from "|E| ≥ |V|" to "|E| ≥ |V| − C + 1" bites.

Quick integration: both M2 and M3 are cheap — extend the M1 probe.

### 4.4 Probe M4 — the 2-cell count

Count how many 2-cells of `X(ms)` lie inside `X \ C | B_2`. If the
2-cell count is small compared to β_1_hamming, the cube complex
β_1 after filling is still large, and the Morse argument survives
higher-dimensional fillings. This is the cleanest measure of
"topological signal is robust to filling."

---

## 5. Lean artifact plan

The edge-majority lemma is the first Lean-side deliverable:

> **Lemma (edge-majority).** Let `gc : GoodCycle sys` with
> `∏ sys.rs.m < 4·3^{sys.rs.n-2}`. Let `B2 : Finset (Config)` be the
> Hamming-2 ball around `gc.configs` minus cycle configs. Then
> `|edges of forcedNeighbors on B2| ≥ |B2| − |components B2| + 1`.

From the edge-majority lemma + graph-theoretic fact "|E| ≥ |V| − C
+ 1 ⇒ cycle exists", chain to `sk_nonempty_of_closed_forced_subset`
(already in SinkKernel.lean) via the explicit cycle witness. Final
consumer: `not_converges_of_partial_det_sk_nonempty`.

Target file: `lean/LeanMn/LowerBound/SK/PartialDet2TubeMorse.lean`.

---

## 6. Binding constraints respected

- `feedback_no_case_splits_in_lean` — the edge-majority claim is
  uniform in `(n, k_bin, state multiset)`. If the counting argument
  requires a split, route dies.
- `feedback_no_axioms`, `feedback_no_native_decide` — the
  sub-threshold inequality must be a genuine analytical fact, not a
  finite-corpus assertion.
- `feedback_deep_research_over_cheap` — the Forman framing is deeper
  than girth / mover-pattern probes; it connects to discrete Morse
  theory and classical algebraic topology. This is the "right"
  shape.
- `feedback_topological_invariant_proof_shape` — β₁ of a chain
  complex restricted to `X(ms) \ C` is a topological invariant;
  non-vanishing forbids convergence. Matches Keston's stated
  preference verbatim.

---

## 7. Scheduling

| step | depends on | estimated effort |
|---|---|---|
| M2 + M3 probes (single file) | — | 1 session |
| Edge-majority inequality attempt #1 | M2, M3 data | 1–2 sessions |
| M4 probe (2-cells) | — | 1 session |
| Lean port of edge-majority | attempt #1 success | 1 session |

Attempt #1 success criterion: a uniform counting argument showing
`|E_forced| ≥ |V_B_2|` for every sub-threshold candidate, with no
case-splits, grounded in one or two concrete combinatorial
identities relating `|B_2|`, `L`, and det coverage.

## 8. Open questions, in order

1. Is `C_forced = 1` uniformly (no edge-majority degradation), or
   does it grow on some records? (Probe M3.)
2. What is the precise constant in `|E_forced| / |V_B_2|` as a
   function of `(m, cycle length)` at sub-threshold? (M2 + a
   regression on corpus data.)
3. Does filling 2-cells reduce β_1 to below 178? If so, by how much?
   (M4.) The "Morse robustness" question.
4. Can the edge-majority inequality be proven for arbitrary
   (not just sub-threshold) candidates, with a stronger sub-threshold
   statement obtained later? Or does sub-threshold enter at the
   counting step directly?
