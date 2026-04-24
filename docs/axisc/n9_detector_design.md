# Design doc — a ternary-strip-native detector for n ≥ 9

**Written:** 2026-04-22. **Status:** design, unbuilt. **Author context:**
follows the strengthening task #1 result that the C1 lifted-circulation
LP gives 4 false-negative sub-threshold verdicts on non-adjacent 3-binary
orderings of `{2^3, 3^5, 4}` at n = 9, product = 7776 (see task #1
artifacts listed in §0 below).

---

## 0. Onboarding — read these first (in order)

A reader who wants to act on this doc needs the problem, the witnesses,
the dead-ends catalog, the existing detector, and the task #1 counter-
example data. All paths are relative to the STAGE repo root.

### Problem + witnesses (start here if unfamiliar)

- **`docs/p2.md`** — problem statement, Dijkstra's three solutions,
  Knuth's 1985 question, history through 2024. Defines `M_n`,
  configurations, privilege, good cycles, the central daemon.
- **`docs/witness_primer.md`** — record-holding constructions:
  small-n `M_n = 32·3^{n-4}` absorber witnesses for n ∈ {5..8},
  the CLB ternary-strip witness `ms = (2, 3, ..., 3, 2)` at
  `4·3^{n-2}` for n ≥ 5, the CUP-2 Lean-checked siblings for
  n ∈ {4..10}, the phase transition at n = 9. §3–§5 are the
  ternary-strip material this doc centers on.
- **`docs/arg_lcm/paper.md`** — ARG-LCM dispatch paper (draft).
  Rules out ARG's 1985 LCM bound as the n = 9 transition
  mechanism via scope (absorbers are adjacent-binary; ARG's
  hypothesis is non-adjacent) and insensitivity (LCM-functional
  constant or strictly nested between n = 8 and n = 9 on
  non-adjacent orientations). The 4 task-#1 counterexamples lie
  exactly in this non-adjacent zone.

### LB history + the detector's prior arc

- **`lean/docs/lb_all_paths_history.md`** — the single most
  important reference. §0 (preliminaries + glossary + the two
  sharp frontier statements), §1 (pre-SK case-split architecture,
  retired), §2 (SK pivot), §3 (five-route SK arc R1–R5, all RED),
  §4 (transport-lift / twist-calculus attic), §5 (R4 peel-direct
  certified dead), §6 (A1 target-injectivity broken), §7 (SKMH
  topological arc, retired), §8 (two open frontiers:
  `peelTube_nonempty_{small,large}_n` and A1'), §9 (current
  posture and binding constraints), §10 (topological revival Waves
  1–6, retired as detector-only). Any proposal here is judged
  against the §9 resumption gates and the §10.9 "what any future
  topological revival must clear" list.
- **`lean/docs/topo_revival/wave2/…`** through **`wave6/…`** —
  the circulation-LP arc's primary sources. Wave 2 defined the
  C1 LP and fixed the Lean `peelTube_nonempty` threshold. Wave 3
  hardened it. Wave 4 dispositive-tested the arithmetic pivot.
  Wave 5 ran the terminal probe queue. Wave 6 ran the T+sided-
  only probe (T2 empirical GREEN) — this is the "cheap live
  route" of §2 below.

### The paper

- **`papers/draft1/src/main.tex`** — the paper under construction.
  §6 (`sec:detector`) is the current detector write-up; §6.3 is
  Table 2 (`tab:corpus`, the 29-record stratified corpus) and
  the "asymmetric in n" caveat that the task #1 n = 8 extension
  updates; §6.4 is the restricted-feasibility observation (the
  c_self = 0 claim that drives the "cheap live route" below);
  §7 (`sec:landscape`) is the obstruction catalog; §7.1 Family 1
  is the current circulation decomposition; Appendix C is the
  exhaustive-certificate scaffold; `rem:phase-scope` fixes what
  "phase transition" means.
- **`lean/docs/paper_upgrade_1/strengthening_work.md`** — the
  upgrade program this doc sits inside. Task #1 (the one that
  surfaced the 4 counterexamples) is the first item; tasks #5,
  #6, and the present doc branch out from its outcome.

### Task #1 artifacts (this doc's direct input)

- **`lean/docs/paper_upgrade_1/probe_strengthening1_n8_subthreshold.py`**
  — the n = 8 and n = 9 Table 7 probe driver. Reusable
  `enumerate_compositions`, `canonical_orderings`,
  `enumerate_cycles`, `build_lifted_graph`, and
  `solve_circulation_lp`.
- **`lean/docs/paper_upgrade_1/run1_stdout.log`** — the first run's
  stdout, with per-record cycle-length and feasibility lines.
  Source of the 59/59 n = 8 separation and the 4 n = 9
  counterexamples.
- **`lean/docs/paper_upgrade_1/phase1_n8_sub_corpus.json`** —
  full corpus JSON (one record per ordering, incl. LP verdict,
  edge-type histogram, lifted graph sizes).
- **`lean/docs/paper_upgrade_1/phase1_n8_summary.md`** — the
  human-readable summary with implications for the paper.
- **`lean/docs/paper_upgrade_1/probe_strengthening1_counterexample_analysis.py`**
  — the counterexample inspector that surfaces the adjacency
  signature split referenced in §7 of this doc.

### Lean-side surfaces (for the eventual Lean port)

- **`lean/LeanMn/LowerBound/SK/HammingTube.lean:169, 190`** —
  `peelTube_nonempty_small_n` and `peelTube_nonempty_large_n`,
  the two research-open sorries that any detector would ultimately
  need to close.
- **`lean/LeanMn/LowerBound/SK/SlabCountingRing.lean:492`** —
  `sourceTripleOfStep_injective` (A1'), the second frontier sorry.
- **`lean/LeanMn/LowerBound/SK/CloudsTheorem.lean:418, 445`** —
  the consumer wiring `sk_nonempty_{small,large}_n`.

### Binding memories (do not violate — see §6 below)

The following live in the agent's auto-memory
(`~/.claude/projects/-Users-keston-Github-sandbox-internal/memory/`);
they are project-level feedback from prior sessions and override any
design choice below that conflicts.

- `feedback_no_case_splits_in_lean.md` — case-split proofs in Lean
  on this project are blocked.
- `feedback_no_axioms.md` — no axioms without cited published
  papers; no `native_decide` as a proof.
- `feedback_no_ship_with_sorries.md` — no paper/DK-letter ship while
  any sorry remains.
- `feedback_attic_usage.md` — do not import from `attic/` or `Attic/`;
  they are graveyards.
- `feedback_topological_invariant_proof_shape.md` — Keston's stated
  proof-shape preference: "a topological invariant forbids it."
  Axis E is the only axis below that nominally fits this preference;
  the others are computational detectors whose role is to empirically
  separate the corpus, not to be the proof.
- `feedback_push_past_saturation.md` — if every invariant in a family
  saturates at the same value, that's evidence of a hidden compact
  object, not a reason to stop.
- `feedback_deep_research_over_cheap.md` — cheap reformulations on
  paper 2 usually dead-end; deep structural research is what unlocks.

### Tools

- **`claude/verifier.py`** — `verify_system(ms, fs)`, the gold-
  standard five-property check. Every witness file round-trips
  through this.
- **`claude/verify_witnesses.py`** — small-n witnesses
  `witness_n5..witness_n8`.
- **`claude/clb_witness_8748.py`**, **`clb_verify_8748.py`** — the
  CLB ternary-strip witness at n = 9 and its verifier.

---

## 1. Motivation — why a new detector at n ≥ 9 specifically

The C1 circulation LP (paper §6; `probe_wave4_combined_2026-05-03.py`)
was designed when the valid-witness reference corpus at n ∈ {5..8} was
the small-n absorber family (class 4: 3-binary + one ≥ 4-state
processor). Its discrimination is sharp on that family: w5..w8 are
0/4 LP-feasible, sub-threshold candidates at n ∈ {5..7} are 19/19
LP-feasible, and the strengthening #1 extension shows n = 8
sub-threshold is 59/59 LP-feasible.

At n ≥ 9 the witness family changes: the saturating construction is the
CLB / CUP-2 ternary-strip witness on `ms = (2, 3, ..., 3, 2)` (see
`docs/witness_primer.md` §3–§5). The good cycle is an up–down bounce
of length `3n − 2` with endpoint-binary firings; the interior is
all-ternary; the mover sequence is `(0, 1, ..., n−1, n−2, ..., 1)`
periodically. The phase transition at n = 9 (paper §3.2) is exactly
the crossover from absorber-family witnesses (competitive through
n = 8) to ternary-strip witnesses (competitive from n = 9 on).

**Empirical evidence that the current detector is absorber-tuned.** The
4 counterexamples at n = 9 from task #1 are non-adjacent 3-binary
orientations of `{2^3, 3^5, 4}` — structurally absorber-shaped in the
sense of class-4 multisets (3 binaries + one ≥4 processor), but at
n = 9 the absorber family is NOT competitive (`M_9 = 4 · 3^7 = 8748`,
not `4 · 3^7 / (3/2) = 5832` or anything smaller). These candidates
are sub-threshold yet the C1 LP returns infeasible — the circulation
mechanism the LP encodes does not see the non-extension that RC + AC
exhaustive verification proves at this product.

The working hypothesis: the C1 LP captures a circulation signature
specific to candidate cycles that compete *against* absorber
structure. It misses candidates whose (C, μ) shape aligns with absorber
structure but sit at a product where absorbers don't extend. The n ≥ 9
detector should instead contrast candidate cycles against the
ternary-strip (C, μ) shape.

## 2. What we inherit — known dead ends and one cheap live route

Before proposing new routes, the design has to respect the existing
dead-ends catalog (`lb_all_paths_history.md` §§1–7) so we don't
rediscover them.

**Dead routes that any n ≥ 9 detector must avoid re-embedding.**

- **Twist-calculus / DTNF / CTCL / FRL** (`lb_all_paths_history.md` §4).
  Retired 2026-04-20, attic. Forced-closure probe FAIL outcome 3
  (escape rate grows linearly in n). Any detector built on twist-
  geometry invariants of the cycle reinvents this wall.
- **Pure-structural routes (R1 direct, R2 quotient, R5 CDO #1)** —
  reduce to A1 target-injectivity. Don't frame a new detector as
  "match the cycle's source-triple structure alone."
- **Det-only routes (CDO #2)** — explicit counterexample: det without
  (C, μ) leaves room for non-extending structures. Don't frame as
  "check the determined dictionary directly."
- **R4 peel-direct / local walk rules** — 26% residue on best-of-5
  uniform walk rules; E17 local-predicate accuracy ≤ 46.7%. A detector
  that picks a greedy walk rule reinvents this wall.
- **Ambient topological invariants** (π_1, H_1, linking matrices,
  Lefschetz, Cheeger, spectral gap) — `(n, L)`-parametrized; scale
  with ambient dim; coverage inversion (§0.6 of history doc). Don't
  build around a Betti-number check.
- **Cheap arithmetic separators** — any regression that rediscovers
  the threshold condition via feature-engineering is tautological
  (Wave 4 calibration note §10.6).

**One cheap live route already identified — RUN AND CERTIFIED RED (2026-04-22).**
Wave 6 T2: restricted LP with **c_self edges forbidden** is feasible on
19/19 of the n = 5..7 sub-threshold corpus and zero on valid witnesses.
We ran this variant on the 4 n = 9 counterexamples via
`probe_strengthening1_counterexample_analysis.py`; result: **0/4 recover**
— all four counterexamples remain LP-infeasible under T+sided-only
(identical objective = 0, support size = 0 as under C1). Transport-only
also 0/4. The n ≥ 9 detector cannot be obtained by restricting C1's
edge set; a genuinely different construction is required. See
`phase1_counterexample_analysis.json` for per-record objective values.
Axis A template-match and Axis B complement-LP below are the next-cheapest
live options.

## 3. Design axes for a genuinely new detector

If T+sided-only fails to recover the 4 counterexamples, the following
are the design axes to consider. Each is paired with a pre-commit kill
criterion so a probe that surfaces the route's obstruction can stop
before burning budget.

### Axis A — ternary-strip template-match

**Idea.** Compute a structural distance between the candidate good
cycle and the canonical ternary-strip cycle at the same n. Reject (flag
as "sub-threshold, non-extending") when the distance exceeds a
pre-committed threshold.

**Concrete candidates.**

- **Mover-sequence edit distance** to the ternary-strip bounce
  `(0, 1, ..., n−1, n−2, ..., 1, 0, 1, ...)`. Normalize by cycle
  length.
- **Bounce-pattern alignment** — does the candidate have two
  monotone sub-passes (up-sweep + down-sweep) on some index
  permutation? If so, estimate parameters and compare to the
  strip's closed form.
- **Endpoint-binary vs interior-ternary agreement.** The strip
  witness fires binaries only at cycle endpoints. Measure the
  fraction of binary-proc fires that lie in "endpoint-like"
  positions of the candidate cycle.

**Kill criterion.** Distance between candidate and strip-template is
empirically uncorrelated with feasibility on the 29-record corpus, or
signal inverts with coverage (cf. §0.6 history doc). Pre-commit:
ρ(distance, feasibility) must be ≥ 0.6 on the existing 29-record
corpus before extending to n = 9.

**Risk.** Template-matching typically loses at the transition: at
n = 9 the strip is sharp but at n = 5..8 it's super-threshold, so the
sub-threshold candidates at lower n don't share its shape either. May
require an n-keyed template rather than a uniform one.

### Axis B — "complement-LP" against the strip's lifted graph

**Idea.** Instead of building the lifted graph on the candidate's
Hamming-1 tube, build it on the **ternary-strip witness's lifted
graph** at the same n, and test whether the candidate's det dictionary
can embed as a subgraph that preserves circulation infeasibility.

**Concrete shape.**

1. Fix the strip's good cycle `C_strip(n)` and its det dictionary.
2. Build the lifted graph `G_strip(n)` on `T_N1(C_strip)` — this is
   LP-infeasible at every n (strip is valid).
3. For a candidate cycle `C` at sub-threshold product, embed `det(C)`
   into the rule-slot geometry of `C_strip` by some canonical
   identification (e.g., position-preserving rotation, or nearest-
   neighbor matching on the common rule-triple lattice).
4. Test whether the embedded det preserves infeasibility of
   `G_strip(n)`. If the embedded det generates a circulation in the
   lifted graph, flag as "detector fires — no extension possible."

**Kill criterion.** The embedding is not uniquely defined (there are
multiple canonical identifications at different orderings, and the
candidate's ms differs from the strip's ms). If embedding choice
changes LP verdict on > 10% of corpus records, the detector is not
well-posed; abandon.

**Risk.** The strip witness at n = 9 has product 8748 and the
counterexamples are at 7776 — different ms, different moduli per
position. Embedding across ms is the hard part; this might reduce to
absorber-template issues via the back door.

### Axis C — direction-covariant circulation on the forced-NG graph (not the tube)

**Idea.** Drop the Hamming-1 tube restriction. Run circulation LP on
the **full forced-NG graph** of the candidate system — i.e., the graph
of non-good configs under the forced-successor relation from the
candidate det dictionary. Feasibility there = a directed cycle in the
full forced graph = SK nonempty directly.

**Why this might catch what C1 misses.** C1 restricts to configs at
Hamming distance 1 from the good cycle. The 4 counterexamples may
have their non-extension witness *outside* the 1-tube — the SK is
nonempty but no nonempty subset of SK lies in `N_1Tube ∩ VC-NG`. This
is consistent with the empirical observation that peel ⊇ non-trivial
SCC and `|SK| / |NonGood|` grows with n (the 1-tube captures
progressively less).

**Implementation.** Build `forced_graph_NG`: for each config
`c ∈ NG`, for each processor `p`, if `det(p, c[p-1], c[p], c[p+1])`
is a move (different from `c[p]`), add edge `c → apply-move(c, p)`.
Restrict to edges where target is also in NG. Run circulation LP
(or just max-subgraph-with-no-sinks which computes SK directly;
standard fixpoint iteration).

**Kill criterion.** `|NG|` at n = 9 is `∏ m − L = 7776 − L ≈ 7700`,
and the sink-peeling iteration is O(|NG| · n) per round with O(|NG|)
rounds. Wall-clock per record ≈ minutes. If n = 9 counterexample SK
is empty, the candidate det genuinely has no peel witness and the
detector class (C1, full, T+sided, ...) is not the LB mechanism at
this multiset — move to axis D.

**Risk.** This is basically the SK-itself detector, which is
combinatorial, not algebraic/topological (see SKMH verdict, §7
history doc). If SK captures the phenomenon exactly, we've
reinvented the problem not the detector. But if SK separates
cleanly at n = 9, that at least gives a computable upper oracle
for the LB, which is still useful.

### Axis D — Farkas-pair detector (LP + LP)

**Idea.** Run two LPs per record and classify by which is feasible.

1. **LP-A** (current C1): circulation on the 1-tube. Feasible ⇒
   "strong sub-threshold signal."
2. **LP-B** (complement): LP that encodes "the candidate's det
   extends to a valid f_i at every non-good config." Specifically:
   for every `c ∈ NG`, there's an assignment `f_i(c[i-1], c[i],
   c[i+1])` consistent with `det(C)` and the fairness constraint.
   Feasible ⇒ "extension possible, sub-threshold signal absent."

Record is "detector fires" iff LP-A feasible **OR** LP-B infeasible.
The two LPs are expected to be contrapositive: LP-A feasible ⇒ peel
exists ⇒ no convergence ⇒ no f extension ⇒ LP-B infeasible. The
Farkas-pair detector makes the implication testable.

**Why this might catch the 4 counterexamples.** If LP-B is infeasible
on the 4 non-adjacent {2^3, 3^5, 4} orderings (as it should be, since
they don't extend to valid systems), the combined detector fires even
when LP-A doesn't.

**Kill criterion.** If LP-A feasible ⇒ LP-B infeasible on the 29-
record corpus (expected), the two LPs are redundant and LP-B is the
stronger detector. Sufficient to run LP-B alone. Need to verify LP-B's
sensitivity ≥ LP-A on the corpus before concluding.

**Risk.** LP-B's constraint count is O(`∏ m · n · max m`) which is
hundreds of thousands at n = 9 — heavier than LP-A. But still
polynomial; no fundamental obstruction.

### Axis E — (C, μ) × det interaction invariant

**Idea.** Per `lb_all_paths_history.md` §3 and §9 resumption gate #2
("attacks (C, μ) × det interaction directly"), the n ≥ 9 detector
should be an invariant of the joint object `(C, μ, det)`, not any
projection.

**Concrete candidate — coupled spectral gap.** For the candidate
system, build the bipartite incidence matrix of cycle-steps × rule-
slots (step `k` covers slot `(mov_k, triple_k)`). The matrix rank
and its null-space dimension depend jointly on (C, μ, det). At the
ternary-strip witness, this matrix has closed-form rank; at sub-
threshold candidates, the rank should differ systematically.

**Kill criterion.** Rank signal driven by `(n, L)` alone (so scales
with ambient dim, replicating the ambient-topological failure mode
in §10.1). Pre-commit: rank-difference must correlate with
feasibility after controlling for L.

**Risk.** This is the hardest axis and matches the region where prior
approaches hit the A1 wall. But it's the one that satisfies the
history doc's explicit resumption criteria.

## 4. Recommended order of attack (updated 2026-04-22 after T+sided RED)

0. **T+sided-only LP on the 4 counterexamples** — ~~cheap~~ DONE,
   **RED**. 0/4 recovered. Axis 1 closed; move to Axis C.
1. **Axis C full-forced-NG detector** on the 4 counterexamples +
   the 29-record corpus. This is SK direct — maximal sensitivity, but
   computationally heavier. Purely computational; no new math required.
   Now the highest-EV first move. Kill: if SK is nonempty on all 4
   counterexamples, the detector works but is a combinatorial oracle
   (sink-peeling), not a topological invariant; useful as a
   false-negative-free detector for the paper's §6 claim, but still
   leaves the analytical program open. If SK is empty on any of the 4,
   the candidate `det(C)` genuinely has no peel witness — which would
   mean the non-extension of this multiset lives in a structural
   mechanism *outside* SK entirely, a substantial finding for the
   paper's §7 open-questions section.
2. **Axis A template-match** — a cheap pre-commit probe using the
   adjacency signature already computed (phase1_counterexample_
   analysis.json). On the 9 n = 9 Table 7 records the signature
   `(k_bin = 3, bin_adj_pairs = 0)` perfectly separates the 4
   infeasibles from the 1 feasible at `{2^3, 3^5, 4}`, but predicts
   infeasibility for `(2,3,2,3,2,3,2,3,6) ∈ {2^4, 3^4, 6}` which is
   LP-feasible — so the signature is a detector **on the k = 3 binary
   sub-family only**, not universally. Still useful as a restricted
   classifier to pair with axis 1 or to augment §6.
3. **Axis D Farkas-pair** — requires building LP-B, which is new code
   but standard LP. Medium cost; medium upside.
4. **Axis B complement-LP** — conceptually appealing but the embedding
   question is nontrivial. Do only if 1–3 are inconclusive.
5. **Axis E coupled spectral gap** — hardest; defer until 1–4 either
   succeed (in which case unnecessary) or fail structurally (in which
   case the (C, μ) × det framing is the only remaining handle).

## 5. Paper-integration posture

If any of axes 1–4 succeed in recovering the 4 counterexamples without
breaking existing separation, the paper's §6 updates as:

- §6.3 Table 2 adds the n = 8 sub-threshold row (59/59) from task #1.
- §6.3 the "asymmetric in n" caveat softens to "sub-threshold coverage
  is extended to n = 8 (full); n = 9 sub-threshold is tested on the
  three Table 7 multisets, with a localized failure class at
  non-adjacent 3-binary orientations of `{2^3, 3^5, 4}` that is
  recovered by the n ≥ 9 detector form of §6.4a (new subsection)."
- §6.4 adds a subsection §6.4a on the n ≥ 9 detector form (whichever
  axis fires).
- §7 open questions keeps the analytical proof of the detector's
  separation claim as open; the n ≥ 9 detector form doesn't close the
  analytical gap, it only shifts the empirical separation to hold
  across the full corpus.

If all of axes 1–4 fail on the 4 counterexamples, the paper's honest
framing is: "the C1 LP detector separates the 29-record corpus and
the n = 8 sub-threshold extension (59 records), but has a localized
failure class at n = 9 on non-adjacent 3-binary orientations of
`{2^3, 3^5, 4}`. This failure localizes exactly the sub-family where
ARG's 1985 LCM bound also goes silent. The detector is therefore a
sufficient-for-n-≤-8 mechanism, not a universal one; a universal
n ≥ 9 detector remains open." This is the strengthening doc's case
(b) outcome honestly stated.

## 6. Pre-commit constraints (binding, from project memory)

- `feedback_no_case_splits_in_lean.md` — the detector's *analytical*
  form must be uniform-in-n or pivot at STOP. Proving a detector
  separates via case-split on (k binary, position, modulus) is land
  war in Asia. Empirical separation is still informative, but Lean
  ship remains gated on a uniform structural argument.
- `feedback_no_axioms.md` — no `native_decide` on the detector's
  correctness. Finite-check for one (n, ms) is acceptable as a
  consistency test; asserting separation as an axiom is not.
- `feedback_attic_usage.md` — do not resurrect attic files
  (twist_calculus, pre_sk, SK/Attic). Their failure modes are
  documented; re-running them just wastes budget.
- `feedback_no_ship_with_sorries.md` — the detector being empirical
  does not count toward sorry closure. No paper-ship / DK-letter on
  the detector alone until the corresponding peelTube_nonempty sorry
  closes via a proof.

## 7. Data already collected (2026-04-22 addendum)

`probe_strengthening1_counterexample_analysis.py` has run. Output:
`phase1_counterexample_analysis.json`. Headline patterns:

- **4 counterexamples** all at `{2^3, 3^5, 4}`, all with
  `bin_adj_pairs = 0`, `min_bin_gap = 2`, `L ∈ {44, 47}`. LP
  objective is exactly `0.0`, support size 0 — the LP is cleanly
  certifying no circulation exists, not a numerical edge case.
- **1 feasible at `{2^3, 3^5, 4}`** — `(2,2,3,3,2,3,4,3,3)`, L=51,
  `bin_adj_pairs = 1`, `min_bin_gap = 1`. Adjacent binaries.
  C1 objective -51.
- **4 feasible at `{2^4, 3^4, 6}`** — adjacency signatures mixed:
  `(2,3,2,3,2,3,2,3,6)` has `bin_adj_pairs = 0, min_bin_gap = 2`
  (non-adjacent) yet LP-feasible (obj = -68). So the signature
  `bin_adj_pairs = 0` is **not** a universal predictor of
  infeasibility; the k = 3 binary count is essential to the failure.
- **T+sided-only preserves exact separation**: 5/5 feasibles stay
  feasible (same support size), 4/4 infeasibles stay infeasible.
  c_self edges contribute no circulation on any of these 9 records.
- **transport-only is 0/9 feasible** — expected; removes the only
  edges capable of closing a non-transport cycle.
- **`{2^5, 3^3, 9}` coverage gap**: no cycle found in 28 canonical
  orderings within 15s budget per ordering. May be structural (no
  fair single-priv cycle at this multiset at L ≤ 54), or may need
  a larger budget. Not informative for LP separation either way.

Edge-type histograms (C1) per counterexample:

| ms                             | transport | c_right | c_self | c_left |
|--------------------------------|-----------|---------|--------|--------|
| `[2,3,2,3,3,3,2,3,4]`          | 485       | 89      | 73     | 50     |
| `[2,3,2,3,3,3,2,4,3]`          | 486       | 79      | 65     | 38     |
| `[2,3,2,3,2,3,3,3,4]`          | 485       | 85      | 54     | 41     |
| `[2,3,2,3,3,3,3,2,4]`          | 457       | 74      | 40     | 35     |

These edge counts are *comparable* to the feasible records of the
same multisets — the counterexamples are not structurally starved
of lifted edges. The infeasibility is a topological property of
the particular edge routing, not an edge-count phenomenon.

## 8. The "adjacent binary" signature as a standalone detector

A toy separator `n_bin == 3 AND bin_adj_pairs == 0 AND product < M_n`
correctly flags all 4 counterexamples as non-extending, and correctly
abstains on all 5 LP-feasible n = 9 records. This is the Axis A
template-match operationalized for the present data.

Limitations:
- Empirical only on the 9-record n = 9 Table 7 sweep; no proof this
  generalizes to arbitrary n.
- Conflates two orthogonal properties of the paper's claim: (a) the
  LP's actual computation (circulation on lifted 1-tube graph), and
  (b) a classify_binary-adjacency rule. Using (b) in the detector
  means abandoning the paper's mechanism and just reporting ARG's
  hypothesis zone directly.
- Does not apply to k ≠ 3 multisets. At k = 4 binaries the non-
  adjacent family is not an infeasibility zone on the `{2^4, 3^4, 6}`
  evidence.

So the signature is a useful pre-commit label for "records where C1 is
known to fail," but it is not a ship-ready detector by itself.
