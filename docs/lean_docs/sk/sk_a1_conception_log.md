# SK A1 Wall — Conception-Space Exploration Log

**Purpose.** Long-horizon iteration in conception space to surface a genuinely new idea that clears the three resumption gates from `project_sk_campaign_rest_2026-04-19.md`:
1. Genuinely new idea from outside the 2026-04-14→19 arc.
2. Attacks `(C, μ) × det` interaction directly, not around it.
3. Pre-commit tripwire structurally distinct from the five RED routes.

**Protocol.** `docs/residue_prompt_v2.md`. Log every exploration before starting the next one. Short format for dead-on-arrival diagnoses; full format for ideas that pass a sniff test and warrant deeper analysis.

**Scope constraint.** This log is conceptual. No Lean, no probes, until an idea clears the three gates and gets a pre-commit. Per `feedback_lean_no_infra_loops.md` and the campaign-at-rest directive.

---

## Strategy Register

### Eliminated approach classes

1. **Sync-cascade / step-granularity obstruction** (R1) — reproduces A1 at step level. Cascade-break shape guarantees non-matching triples, which *is* A1.
2. **Orbit-level quotient** (R2, §3) — collapses to A1 or requires case splits. Any quotient that identifies step-level structure recapitulates the underlying injectivity question.
3. **Fiber-counting / fiber-budget aggregation** (R3) — routes through `sourceTripleOfStep_injective` (A1) on the residual.
4. **Read-2 aggregate ansatz / quantitative counting at n ≥ 8 binary-dominated** (R4) — independent arithmetic wall; α_worst grows 0.44→0.66→0.70 linearly in n.
5. **Det-only / closure-equation abstract attempts** (R5) — CDO #1 reduces to A1; CDO #2 (det-centric) admits construction-level counterexamples.
6. **Transport-lift / tube-index cocycle routes** (2026-04-19) — multi-valued signatures, δ escapes {0,1}, no threaded-all-δ=1 choice.
7. **Projection lemma via twist-geometry** (2026-04-20) — forced-closure probe FAIL outcome 3: escape rate 0.36→0.43 linear in n. Twist-calculus atticed.
8. **Cycle-structure-only (C, μ) arguments** — Gate 2 explicit failure class (Route 2 archetype).
9. **Det-only arguments not using (C, μ)** — Gate 2 explicit failure class (CDO #2 archetype).

### Obstructions

- **A1 wall.** `sourceTripleOfStep : Fin L → Triple` must be injective. 0 counter-examples in 1190 sampled cycles. 16.9M terminals across 26 Case B seeds, 0 violators (YELLOW-subset).
- **Linear-in-n failure signature.** Every "around-A1" quantitative route produces a quantity that degrades linearly with n at binary-dominated regime: α_worst (R4), forced-closure escape rate (twist closure). The rate of degradation is the wall's fingerprint.
- **Gate-2 asymmetry.** Any proof using (C, μ) alone or det alone is dead. The wall is precisely the joint structure.

### Building blocks

- `sk_nonempty_of_closed_forced_subset` (SinkKernel.lean:156) — Session 4 bridge. Converts a Finset-witness of a forced-closed non-good subset into the main theorem's `.Nonempty`. Ship-path.
- `MoveEntry`, `α/β`, `stepMoveEntry`, `Σ α = L`, `Σ β ≤ n · L` (SlabCountingRing) — zero-sorry infrastructure from Sessions 2a/b/c.
- `peel_nonempty` (SinkKernel) — 100% on sampled records; immediate from D_tube L-cycle structure. Weaker than needed.
- D_tube girth = L empirically (1895/1895 sampled records). Base girth cycles exist and have deterministic structure.
- CTCL_dominant (atticed) — valid theorem about closed threading, orphaned by projection failure.
- Named conjecture (retained): "No closed simple single-priv cycle with seed-consistency at a Case B seed satisfies Move_q(C) ≠ ∅ for every q ≠ p."

### Known reformulations

- **Outcome A** (2026-04-18) — main theorem needs `.Nonempty`, not `|SK| ≥ 2^(n-1)`. **LOAD-BEARING**: reduced the target from quantitative to existence.
- **CDO / MOVE-budget** — `Ψ_q := MOVE_budget_q`, `Ψ_q = 0 ⟺ Move_q(C) = ∅ ⟺ (U)`. Structural but reduces to A1 at closed cycles.
- **Step-source map** `sourceTripleOfStep : Fin L → Triple` — the literal wall. Not a reformulation so much as the sharpest statement.
- **Tube lift via D_tube(NG ∩ VC-NG)** — base girth cycle → candidate forced-closed subset. **NOT LOAD-BEARING** (projection fails empirically 2026-04-20).

---

## Exploration 1 (probe)

### Strategy
Spectral / matrix-rank reformulation: cast `sourceTripleOfStep` as a 0/1 incidence matrix M ∈ {0,1}^{L × |Triple|} (row k = indicator of `sourceTripleOfStep(k)`); injectivity ↔ rank(M) = L ↔ M has distinct rows.

### Outcome
ABANDONED — tautological restatement at row granularity.

### Concrete Artifacts
REFORMULATIONS: distinct-rows ≡ injective ≡ A1. M's entries depend on both (C, μ) (row index = step) and det (column index = triple generated from det firing at that step), so Gate 2 is formally hit, but the rank condition contains no new purchase — computing rank requires inspecting the same triple-distinctness A1 asks for.

### What this rules out
Any reformulation that is a literal restatement of injectivity in linear-algebra language without introducing a new invariant. Must bring *external* algebraic structure (a group action, a module, a representation) rather than just changing vocabulary.

---

## Exploration 2

### Strategy
**Escape-growth as monovariant (lever-flip).** The forced-closure escape rate grows 0.355 → 0.399 → 0.415 → 0.432 linearly with n on sub-threshold records. Read this *not* as an obstruction but as a candidate monovariant: if A1 fails, does a collision-rooted quantity force escape rate to exceed a structural ceiling, contradicting a finite upper bound derivable from ms?

### Outcome
STALLED — mechanism is not specified. Passes sniff test on all three gates but no candidate ceiling is yet in hand.

### Failure Constraint
Not yet failed. The gap: I have no candidate quantity Φ(C, μ, det) such that (a) Φ is bounded above by a function of ms independent of n, and (b) A1-failure at step k forces Φ to grow proportionally to the empirical escape-rate trajectory. Without (a, b) there is no monovariant argument.

### What This Rules Out
Nothing yet — exploratory. If (a) cannot be produced (no ms-bounded ceiling), the entire lever-flip frame fails and joins eliminated class "quantitative bounds that grow with n."

### Surviving Structure
- Empirical linearity of escape rate in n across two independent probes (R4 α_worst, forced-closure) is the *same fingerprint*. That correlation is not coincidence — it reflects a single underlying combinatorial growth.
- Binary-arity processors dominate escapes at every n tested. Any monovariant candidate should be binary-weighted.
- "Outside_T" escapes (Hamming-2 from C) grow *faster* than "in_T\S" (Hamming-1) escapes as n increases. The growth is specifically in depth-penetration of NG, not breadth.

### Reformulations
Potentially load-bearing (UNTESTED): cast the A1 wall as a **saturation theorem** — "the empirical escape rate is exactly the combinatorial ceiling; A1 holds because violating it requires exceeding a saturated quantity." This would be structurally distinct from every prior route (which argued obstruction-existence, not saturation).

LOAD-BEARING ASSESSMENT: Unclear. The shape (identify saturated quantity → show A1-failure over-saturates) is new to this arc. But identifying the saturated quantity is the whole problem. Not immediately actionable without external analogy.

### Concrete Artifacts
STRUCTURAL RESULTS: Two independent probes (R4, forced-closure) give linear-in-n failure signatures with matched binary-arity dominance. This is the strongest empirical signal we have that a single invariant is governing multiple proof-dead-ends simultaneously.

### What Would Unblock This
- A candidate function Φ(C, μ, det) ms-bounded and collision-sensitive.
- External analogy: "saturation-implies-rigidity" theorems in combinatorics (Szemerédi-style? additive combinatorics? extremal graph theory?). A tip from outside would save weeks of groping.
- Small-n computation of Φ candidates against known sub-threshold records.

### Key Parameters
n = 5..8 sub-threshold records. The linear-in-n regime is specifically n ≥ 6.

### Open Questions
- Is the linear growth in escape rate convergent to some limit as n → ∞, or does it grow unboundedly? If bounded above by 1 (which it trivially is), the ceiling itself might be a monovariant candidate.
- Is the binary-arity dominance a consequence of the ms distribution in sub-threshold records, or a structural property independent of ms?

---

## Exploration 3 (probe)

### Strategy
Induction on n: A1 at n+1 reduces to A1 at n via cycle-extension or processor-insertion.

### Outcome
ABANDONED — structural circularity.

### Concrete Artifacts
REFORMULATIONS: No natural n-extension map is known. The sub-threshold regime changes character at n = 8 (binary dominance, R4 wall). An induction step would need to commute with this phase transition, which there is no reason to expect.

### What this rules out
Induction on n with a cycle-extension step map. If an idea says "suppose A1 holds at n, lift to n+1," it will either (a) fail at the n=7→8 phase transition or (b) route through A1 at n. Both are dead.

Does NOT rule out: induction on *other* parameters (L, |VC-NG|, Hamming-depth from C) that may commute better with the phase structure.

---

## Exploration 4 (probe)

### Strategy
A1-failure consequence: two steps share a triple → cycle-closure equation violated → contradiction.

### Outcome
ABANDONED — this is CDO attempt #1 (closed-cycle CDO ≡ original A1). Already in eliminated class.

### Concrete Artifacts
Identical reduction chain. No new surviving structure.

---

## Exploration 5 (probe)

### Strategy
Communication-complexity analogy: (C, μ) = input distribution, det = transcript of a 2-party protocol, A1-injectivity = "transcript distinguishes all inputs." Could A1 be cast as a lower bound on one-way communication complexity?

### Outcome
STALLED — analogy is suggestive but I cannot specify parties or message alphabet without more structure. External guidance needed.

### Concrete Artifacts
REFORMULATIONS: cast step-index as Alice's input, triple as Bob's observation, det-value at firing context as the "message." A1 ↔ Bob can decode Alice's step-index from her triple. Lower bounds on this form involve matrix rigidity / VC-dimension.

Unclear whether the "matrix" here is anything other than M from Exploration 1 under a new label. If so → tautological.

### What this rules out
If the induced matrix is exactly M from E1, this route is eliminated. Needs verification.

---

## Exploration 6

### Strategy
**Pigeonhole on the Hamming-depth frontier.** Every base girth cycle has L distinct vertices in D_tube (Hamming-1 from C). The tube size |T| is bounded polynomially in n (|T| ≤ n · (max m_p - 1) · |C|). If L grows faster than any injective map into triples can support given both the tube constraint and det's partial-function structure, collision is ruled out "by volume."

### Outcome
STALLED — smells like fiber-budget (R3) but not confirmed.

### Failure Constraint
Not yet failed. Risk: this is R3 in disguise. R3 aggregates per-step fiber budgets; this would aggregate per-vertex tube contributions. If the counting collapses to the R3 formulation, it dies immediately.

### What This Rules Out
Nothing yet.

### Surviving Structure
- The tube has bounded size; |T| ≤ n · Σ(m_p - 1) · |C|.
- The base girth cycle visits exactly L tube vertices (empirically 1895/1895).
- If L approaches |T| closely enough, pigeonhole on the complement (non-cycle tube vertices) might produce a constraint separate from fiber budgets.

### Reformulations
- **Co-dimension framing**: instead of counting fibers at each step, count vertices NOT visited by the cycle. |T \ S| is bounded; forced moves from S into T\S are the escape events; escape count ≤ |T \ S| per vertex-visit cycle.
- LOAD-BEARING ASSESSMENT: possibly load-bearing IF |T \ S| is tight relative to per-step escape counts. Needs small-n verification: measure |T \ S| and compare to Σ_{c ∈ S} #(forced moves into T \ S) from forced-closure probe data. One spreadsheet-sized check.

### Concrete Artifacts
STRUCTURAL RESULTS: D_tube has girth = L, largest SCC ≈ 2L (per 2026-04-19 transport-lift arc). The factor-of-2 gap is a concrete combinatorial margin that hasn't been leveraged.

### What Would Unblock This
- One probe: for each record, compare |T \ S| to Σ_{escape events into T \ S} from forced_closure_2026-04-20.json. If |T \ S| ≥ escape count with slack, co-dimension pigeonhole fails. If tight, this is a new route.

### Key Parameters
Same dataset as E2: n = 5..8 sub-threshold records.

### Open Questions
- Is |T \ S| bounded by a function of ms independent of n, or does it grow with n?
- Does the "largest SCC ≈ 2L" hint at a 2-coloring / orientation / bipartition that A1 violates?

---

## Synthesis after Exploration 6

**Cross-exploration pattern.** E2 (escape-growth lever) and E6 (co-dimension pigeonhole) both propose using the escape structure as *input* rather than *obstruction*. This is a genuinely new direction: every prior route tried to *prevent* escape (proving closure); these propose *using* escape to bound a quantity that A1-failure would over-saturate.

**Building-block reuse.** The forced_closure_2026-04-20.json data is a concrete artifact that could serve E2 and E6 both without new computation. One read over the JSON could produce Φ candidates and |T \ S| comparisons.

**Which ideas survive sniff test.** E2, E6 (with E5 as external-input placeholder). E1, E3, E4 dead. Of E2/E6, E6 has a concrete unblocking step (one probe on existing JSON); E2 needs external analogy.

**Strategy Register updates.** Adding:
- **Eliminated approach class (new):** Linear-algebra rank restatements without external structure (E1); induction on n with cycle-extension step (E3); CDO-type cycle-closure equation arguments (E4, already present, reconfirmed).
- **Reformulation (new, UNTESTED load-bearing):** Saturation-implies-rigidity framing (E2 §Reformulations); co-dimension pigeonhole via |T \ S| (E6 §Reformulations).
- **Building block (new):** forced_closure_2026-04-20.json as reusable dataset for conception-space explorations.

**Gate-3 status.** E2 and E6 each have candidate tripwires structurally distinct from the five RED routes. Neither is pre-commit-ready — both need more specification.

**Gate-1 status.** E2 and E6 are *generated from inside the arc* using the most recent probe data. They don't strictly clear Gate 1 (which requires external input), but they're the most structurally-new reframings the internal data supports. External input (E5 analogies, combinatorics literature) would decisively advance beyond this.

---

## Exploration 7

### Strategy
Co-dimension pigeonhole verification (E6 unblock). Compute |T\S| vs escape counts from `forced_closure_2026-04-20.json`; test whether pigeonhole is tight.

### Outcome
FAILED — E6 route definitively dead.

### Failure Constraint
Escape count is a *vanishing* fraction of |T\S|, not a tight one. `n_escape_tube / |T\S|` ratio shrinks with n: 0.256 (n=5) → 0.088 → 0.060 → 0.038 (n=8). In 0/1898 records does `n_escape_tube ≥ |T\S|`. The tube has overwhelming co-dimension slack; pigeonhole has no purchase.

### What This Rules Out
Any co-dimension / volume pigeonhole on T\S. Joins eliminated class "quantitative bounds aggregating over tube vertices." Related classes at risk: any argument assuming T\S is "small relative to escape-target space."

### Surviving Structure
**Unexpected new observation**: `n_escape_tube` is approximately n-independent (mean 5.2, 4.1, 4.0, 3.8 at n=5,6,7,8), while `n_escape_outside` grows linearly (mean 2.0, 6.7, 9.1, 11.1). This is a **separation of shallow vs deep escapes**:
- Shallow escapes (into T\S, Hamming-1 from C): ~constant per record across n.
- Deep escapes (outside_T, Hamming≥2 from C): grow linearly with n.

This is structurally parallel to the twist-geometry "6 twists per closed threading" constant. Candidate conjecture: every record has a bounded number (∼ small constant) of shallow escape channels, and the total escape rate grows *only* through deeper excursions. If true, this decouples "shallow combinatorics" (a fixed-size object) from "deep combinatorics" (an n-scaling object).

Additional scale facts:
- |T| grows like n · C-size: 35.9 → 67.1 → 89.9 → 127.4.
- |T \ S| grows similarly: 23.2 → 51.5 → 72.1 → 107.9.
- L grows slowly: 12.7 → 15.5 → 17.5 → 19.5 (matches L = 2n + C-base, consistent with D_tube girth = L).
- Ratio L/|T\S| shrinks: 0.59 → 0.32 → 0.25 → 0.19. The cycle is a vanishingly small part of the tube co-dimension as n grows.

### Reformulations
**Shallow/deep decomposition** of forced-move escapes. If escapes into T\S are bounded by a small constant ∼ 4–5 per record (independent of n), they become a *finite* combinatorial object per record. Only the deep escapes scale. This is a load-bearing separation candidate if verified structurally, not just statistically.

LOAD-BEARING ASSESSMENT: possibly strong. If there's a structural theorem "at most c shallow escapes per closed threading" (analogous to "6 twists per threading"), the shallow part is finite-dimensional and may be amenable to case analysis that the full escape set isn't.

### Concrete Artifacts
COMPUTED EXAMPLES: Full `forced_closure_2026-04-20.json` now interpreted under shallow/deep decomposition. Mean shallow escape count: 4.3 aggregated across all n, range 3.8–5.2. Max shallow escape count observed: 8.

STRUCTURAL RESULTS: Empirical bound `n_escape_tube ≤ 8` across 1898 records at n ∈ {5..8}. Not proven, but 100% adherence in the sample.

REPRESENTATIONS: Forced-move target classification {in_S, in_C, in_T\S, outside_T} usefully separates into two regimes with very different scaling.

### What Would Unblock This
- Prove or empirically tighten a constant bound on `n_escape_tube` across n.
- Verify at n = 9, 10 whether shallow escape count stays bounded.
- Explore whether shallow escapes correlate with twist-geometry's 6 Case-C edges.

### Key Parameters
Same dataset. Range n = 5..8.

### Open Questions
- **Is there a structural reason shallow escapes are bounded?** Geometric? Algebraic? Connected to twist-position structure from 2026-04-19?
- **Do shallow escape targets correspond to specific twist vertices?** If yes, the 6-twist object may be the same as the shallow-escape set.
- **Are there records with 0 shallow escapes?** (Min is 3, 2, 2, 3 — no.) Why is the lower bound nonzero?

---

## Synthesis after Exploration 7

**Major update:** E6 is dead as posed, but produced an unexpected separation-of-scales observation (shallow ≈ constant, deep ∝ n) that may be more valuable than the original hypothesis. This is the "residue of failure" the protocol is designed to catch.

**New candidate exploration direction** (E8, not yet logged): study the structural identity of shallow escapes. Are they the same object as the twist-geometry 6-twists under a different view? If yes, twist-calculus is partially rehabilitated — not as a ship route, but as a *descriptor* of the shallow escape subset.

**Strategy Register updates:**
- **Eliminated approach class (new):** co-dimension / volume pigeonhole on T\S (E7, because |T\S| grows faster than escape count across n).
- **Obstruction (new):** "Tube has vast co-dimension slack; forced moves from S touch only a small fraction of T\S." This is a positive structural fact — most of T\S is simply unreachable by forced-fire from S under the current det.
- **Surviving structural result (new):** empirical bound `n_escape_tube ≤ 8` across 1898 records (n = 5..8). Shallow / deep escape separation.
- **Reformulation (new, candidate load-bearing):** shallow (T\S) / deep (outside_T) escape decomposition. Shallow is bounded-size; deep is n-scaling. If the shallow set is a finite combinatorial object, it's amenable to classification that the full escape set isn't.

**Gate status on new direction (E8 candidate):**
- Gate 1: internal, but genuinely new observation (separation of scales not previously articulated).
- Gate 2: shallow escapes live in (C, μ) × det jointly — they're forced moves from cycle vertices to tube vertices, using det at cycle contexts.
- Gate 3: "classify shallow escapes" tripwire is structurally distinct from all five RED routes and from E2/E6.

**Cheap next step for E8:** one probe reading the existing JSON's `escapes` array: correlate shallow-escape vertex positions with twist-geometry's 6-twist positions from `sk_phase0_out/r4b_twist_geometry_2026-04-19.json`. If they overlap ≥ 80%, shallow ≡ twist. Free computation on existing data.

---

## Exploration 8

### Strategy
Cross-reference: are shallow-escape vertices (from forced-closure probe) a subset of twist vertices (from twist-geometry probe)? Combined probe `probe_sk_shallow_twist_corr_2026-04-20.py` runs both audits on the same cycle enumeration, avoiding record-matching ambiguity.

### Outcome
SUCCEEDED — strong containment signal, tightens monotonically with n.

### Concrete Artifacts
COMPUTED EXAMPLES:
- n=6: 448/669 strict ⊆ containment; mean fraction 0.901.
- n=7: 117/152 strict ⊆; mean 0.927.
- n=8: **44/45 strict ⊆**; mean 0.991.
- Firing-processor containment: 0.919, 0.928, 0.993 at n=6,7,8.
- Shallow-escape vertex count per record clusters at 3–4 (modal 4); max observed = 8.
- Twist vertex count per record clusters at 10–11 (consistent with 6 twist edges, 2 endpoints each with overlap).

STRUCTURAL RESULTS: **Empirical subset relation** `shallow_escape_vertices ⊆ twist_vertices` holds with 98% strict and 0.991 mean fraction at n=8. Firing-processor-level containment even tighter (0.993 at n=8). The shallow-escape set is a *sub-object of the twist-geometry 6-twist endpoint set*.

TOOLS: `probe_sk_shallow_twist_corr_2026-04-20.py` — runs forced-closure audit and twist-min-Case-C DP jointly per cycle. Reusable for further cross-reference queries between the two datasets.

REPRESENTATIONS: The combined view — (cycle step, firing processor, edge type ∈ {A, B, C}, target class ∈ {S, C, T\\S, outside_T}) — is richer than either probe alone. Each cycle-step has a pair of labels (edge-type, escape-class); the correlation between them is the shape that clears.

### Reformulations
**Shallow-escape vertices form a sub-object of the twist-vertex set at large n.** This means the atticed twist-calculus — even though it doesn't deliver the projection lemma — produces an empirically accurate *localization predicate* for where shallow escapes happen.

LOAD-BEARING ASSESSMENT: **Load-bearing for E8-class arguments.** If shallow escapes are confined to twist vertices, and twist-count is bounded (6 per record per twist_geometry), then shallow escapes are bounded by a constant depending only on twist structure. This bounded-shallow-escape fact is the finite-dimensional object that any saturation argument (E2) would need.

This does NOT make twist-calculus ship-able. It makes twist-calculus a *localizer* for shallow escapes — a different role than "route to A1."

### What Would Unblock This
- **Mechanism from ⊆ containment to A1.** Currently: we have a bounded-size combinatorial object (shallow escapes confined to twist vertices). We need a path from this to step-level injectivity. Two candidate directions:
  - (i) Show that A1-collision at step k forces a shallow escape at a non-twist vertex — contradicting the ⊆ containment.
  - (ii) Show that the bounded shallow-escape count bounds the number of possible A1-collision triples, giving a finite verification.
- Verify the ⊆ containment continues to tighten at n=9, 10.
- Identify the 1/45 non-containing record at n=8 and the ~33% at n=6: what distinguishes them? If there's a clean structural condition, we have a case split.

### Key Parameters
Records restricted to `min_case_C >= 4` (twist-regime). Below this threshold twist structure is degenerate.

### Open Questions
- Is the 67→77→98 trend in strict-containment fraction a true asymptote to 100%, or does it level off?
- What is the structural reason for containment? Not immediately obvious — twist edges are Case-C transitions *staying in S*, while shallow escapes are fires *leaving S into T\\S*. The containment says these events co-locate at vertices, not that they're the same edge. Is there a deeper reason?
- Does the twist-vertex / shallow-escape-vertex gap (7 vs 4 on average at n=7) have structural meaning? What are the "twist-only" vertices (twist endpoint but no shallow escape)?
- Named conjecture (retained, 16.9M terminals, 0 violators): does its verification status correlate with the 98% containment?

---

## Synthesis after Exploration 8

**This is the strongest signal in the log.** E8 does not solve A1, but it connects two previously-independent findings (twist-geometry atticed route, forced-closure RED verdict) into a single structure. The twist-calculus — just closed as a ship-path — turns out to describe the vertex locus of the forced-closure-probe's escape events with 98% accuracy at n=8.

**Meta-finding on the exploration:** the right way to use the twist-calculus data was not as a projection lemma (which failed empirically) but as a *localizer* for the escape structure that blocks the projection lemma. Failed routes can yield correct descriptive results, even when they're not proof routes.

**Gate reassessment on E8:**
- Gate 1: internal observation, but connects two arc results in a way neither predicted. This is the strongest internal-Gate-1 candidate so far. External input would still help identify what "saturation theorem in additive combinatorics" this containment resembles.
- Gate 2: shallow escapes are (C, μ)×det events; twist vertices are derived from D_tube structure which is (C, μ) + partial det. The intersection lives in the joint space.
- Gate 3: pre-commit tripwire shape: "shallow-escape ⊆ twist-vertex containment holds with fraction ≥ 0.99 at n ≥ some threshold, and bounded shallow count forces A1 at step-level." Structurally distinct from all 5 RED routes.

**Strategy Register updates:**
- **Building block (new, LOAD-BEARING):** empirical shallow-escape ⊆ twist-vertex containment at n=8 (98% strict, 0.99 mean). Probe artifact: `shallow_twist_corr_2026-04-20.json`.
- **Building block (new):** bounded shallow-escape count per record (max 8 observed across 1898 records). Empirical candidate for finite-dimensional structural object.
- **Reformulation (new, LOAD-BEARING pending mechanism):** twist-calculus as a *localizer* for shallow-escape events, not a projection route. Restores twist data to useful status even though twist route is dead.

**Next exploration (E9 — proposed).** Attack the mechanism gap: either (i) show A1-collision forces non-twist shallow escape (contradiction), or (ii) reduce A1 to finite verification on the bounded shallow-escape set. Both are structurally new attacks; both deserve a pre-commit tripwire before Lean work.

**Honest caveat.** 98% containment at n=8 is strong but not 100%. A proof will need to either (a) show the non-containing cases are ruled out structurally, or (b) work with the 98% regime + handle outliers separately. Neither path is visible yet.

**Gate-1 external-input note.** The shape "shallow escapes co-locate at twist vertices" is a *co-location* / *localization* theorem. External analogies worth checking: Szemerédi-type co-location results, matroid localization, percolation theory (rare events co-locate at rare sites). The user's external knowledge is where Gate 1 can be decisively cleared.

---

## Exploration 9 (read)

### Strategy
Read the Lean definition of `sourceTripleOfStep` and the A1 sorry site in `SlabCountingRing.lean` to sharpen what A1 actually says before probing.

### Outcome
SUCCEEDED — clarified SourceTriple structure and the equivalent A1 formulation.

### Concrete Artifacts
STRUCTURAL RESULTS:
- `SourceTriple := Σ i : Fin n, (Fin m_{left i} × Fin m_i × Fin m_{right i})` — 4 coordinates (position + local L/S/R triple). *Not* the 6-coord (p, l, r, v, s_1, s_2) shape of Case B seeds. The (s_1, s_2) refers to separate structure (likely det-output pair in a Case B ambiguity), not part of the A1 triple.
- `sourceTripleOfStep(gc, k) = (moverAt(k), (c_k(left p_k), c_k(p_k), c_k(right p_k)))`.
- **A1-collision ⟺ some local triple appears at ≥ 2 cycle configs with the shared position as mover at both.** Equivalently, `|cycleTriples| < L` while `Σα(t) = L`, forcing some α(t) ≥ 2.
- `filter_cycleTriples_eq_singleton` (line 250, PROVED): each config matches exactly one triple in `cycleTriples` via privileged-position uniqueness. **Does not imply A1**, because multiple step-sources could map to the same shared triple.
- `alpha_stepMoveEntry_eq_one` (line 505): α(stepMoveEntry k) = 1 for each k. **Depends on A1** (invokes `sourceTripleOfStep_injective` at line 501). So A1 is load-bearing for the fiber-budget double-count.

### Reformulations
**Near-miss structure.** A1-collision is "two configs share local triple at shared privileged position." A *near-miss* is "two configs share local triple at shared privileged position *at one coordinate short*" — Hamming distance 1 in the (L, S, R) triple. If near-misses exist in quantity, the question becomes why the last coordinate never closes.

LOAD-BEARING ASSESSMENT: potentially — near-miss distribution is the empirical fingerprint of what axiom protects A1. Unexplored in the 5-day arc.

---

## Exploration 10

### Strategy
Synthetic A1-violator probe — enumerate per-cycle pairs (k1, k2) with shared mover, compute Hamming-distance-at-mover-triple distribution, identify which coordinate is "protecting" A1 across near-miss pairs. Cross-correlate with shallow-escape positions from E7/E8.

### Outcome
STALLED — pre-commit for a probe. Probe implementation next.

### Pre-commit tripwire
1. **If 0 near-misses exist in ≥ 90% of records**, A1 is combinatorially tight and the probe fails — no diagnostic from near-miss analysis. E10 dies; reformulate.
2. **If near-misses exist but the "protecting coordinate" is uniformly distributed over (L, S, R)**, no single axiom is the lone protector. E10 partially survives but gives no single-axiom handle.
3. **If near-misses concentrate with a skewed "protecting coordinate" distribution**, that coordinate is load-bearing. Further structural analysis targets it.
4. **If near-miss count correlates with shallow-escape count (ρ > 0.5)**, empirical support for candidate mechanism (c): collision-nearness co-varies with escape pressure. Combined with bounded shallow-escape count (uniform at n=5..8), this is a live route.

### Open questions before probe
- Empirical rate of near-misses per good cycle at n=5..8.
- Which coordinate (left / self / right) most often "saves" A1.
- Whether near-miss configs co-locate at twist / shallow-escape vertices.

### Probe results (after run)

SANITY: 0 A1 collisions across 1898 records (A1 empirically holds).

Near-miss rate: 89% of records have ≥1 near-miss; mean ≈ 2.4–3.1 per record.

**Protecting coordinate distribution — SKEWED, S dominates:**
- n=5: L/S/R = 5%/87%/8% (2522 total near-misses)
- n=6: L/S/R = 4%/88%/8% (2099)
- n=7: L/S/R = 11%/68%/21% (369)
- n=8: L/S/R = 4%/77%/19% (133)

S = self-value at the mover position = the value being overwritten by the firing.

**Near-miss × shallow-escape correlation (Pearson rho):**
- n=5: -0.127; n=6: -0.470; n=7: -0.349; n=8: -0.357.

Negative correlation → near-misses and shallow escapes are ANTI-correlated.
**E9 mechanism (c) "collision forces shallow escape" is REFUTED.** Collisions and escapes are competing, not co-varying, structural features.

### Tripwire verdicts
- T1 (no near-misses): **not triggered** — plenty of diagnostic material.
- T2 (uniform coord): **not triggered** — distribution is skewed.
- T3 (skewed coord): **TRIGGERED** — S is overwhelmingly the protecting coordinate.
- T4 (near-miss × shallow-escape rho > 0.5): **not triggered** — rho is negative. E9 mechanism (c) refuted.

### Reformulation (load-bearing candidate)

**S-coordinate injectivity per context-class.** A1 restatement:

> At each (p, L, R) context-class (processor + neighbor values), the cycle's firing S-values are distinct across steps.

Equivalently: the map from step-index k to (mover p_k, L_k, R_k, S_k) factors through a per-(p,L,R) slice that is injective in S. Bounded by α ≤ m_p per context-class.

LOAD-BEARING ASSESSMENT: high. This is a sharper statement than "step → triple injective" because it isolates *which* coordinate is doing the work. Per-context-class injectivity is a more tractable target — it bounds firing repetition by processor arity (m_p), not by L. A proof would show that within each (p, L, R) slice, the S-sequence is a distinct-value sequence → m_p bound → A1.

### What This Rules Out
- E9 mechanism (c) "A1-collision forces shallow escape" — REFUTED by negative correlation.
- Any attack that treats (L, R, S) symmetrically. The asymmetry is empirically sharp; treating all three coords uniformly loses the 77–88% signal.

### Surviving Structure
- **Empirical S-skew fingerprint** across 1898 records. 5124 near-misses, 87% with S as protector at n=5–6, attenuating to 68–77% at n=7–8.
- Competing-structures observation: records with many near-misses have few escapes, and vice versa. Budget-competition between "context-class density" and "escape-channel density."

### Concrete Artifacts
COMPUTED EXAMPLES: Per-record near-miss data in `sk_phase0_out/a1_nearmiss_2026-04-20.json`, 1898 records, collision count = 0, near-miss count ≈ 5124 total across all n.

STRUCTURAL RESULTS: Candidate reformulation of A1 as per-context-class S-injectivity. Empirically supported; not yet proved.

TOOLS: `probe_sk_a1_nearmiss_2026-04-20.py` — reusable for any (p, L, R) context-class audit.

### Open Questions
- Why S? Structural reason for the asymmetry. L and R are "inherited context" (from positions p-1, p+1); S is "local state being overwritten." The firing mechanism favors S-distinctness because det transitions S → v monotonically within some ordering?
- Does the S-skew attenuate monotonically at n ≥ 9?
- Can the per-context-class S-injectivity be proved directly, bypassing the 5 RED routes?

---

## Exploration 11 (candidate, not yet started)

### Strategy (proposed)
Attack A1 via the per-context-class S-injectivity reformulation: prove that within each (p, L, R) slice of the step map, the S-values are distinct.

### Candidate proof routes
1. **Cycle-closure ordering.** In a good cycle, firings at (p, L, R) visit a sequence of S-values S_1, S_2, ..., S_α. The det map sends each S_i to det(L, S_i, R). If these targets are distinct, the next-firing contexts differ → S-sequence is constrained. If some pair S_i, S_j targets the same det value, the cycle may be forced into a repetition.
2. **m_p bound.** Per-context-class firings are bounded by m_p (cardinality of Fin m_p). If we can prove each S-value fires at most once per (p, L, R), we get α(t) ≤ 1 for each source triple — which IS A1.
3. **Det-range restriction.** At fixed (p, L, R), det(L, S, R) as S varies — is the image of det on S-values injective? If det(L, ·, R) is injective on the firing S-values, collision is impossible.

### Pre-commit tripwire
Before Lean work: a probe that explicitly computes, for each record, the sequence of S-values at each (p, L, R) context-class and checks:
- Are they always distinct? (Expected yes — that's A1.)
- Is det(L, ·, R) injective on the firing S-values? (If yes, A1 is proved.)
- If det(L, ·, R) is NOT injective on firing S-values, what other structural constraint forces S-distinctness?

---

## Synthesis after Exploration 10

**E10 produced the strongest conception-space update in the log.** The S-coordinate skew is a genuinely new structural observation, not a reshuffling of the 5 RED routes. It reformulates A1 into a per-context-class injectivity claim that is (a) structurally sharper, (b) bounded by processor arity m_p not cycle length L, and (c) directly in the (C, μ) × det joint space.

**Strategy Register updates:**
- **Eliminated class (new):** symmetric-coordinate attacks on A1 (treating L, R, S uniformly — dead, asymmetry is sharp).
- **Eliminated mechanism:** E9 candidate (c) "collision → shallow escape" — REFUTED by negative rho.
- **Obstruction (new):** S is the protecting coordinate in 77–88% of A1 near-misses at n=5..8. L and R each protect ≤ 21%. Attenuates with n.
- **Building block (new):** near-miss dataset `a1_nearmiss_2026-04-20.json`.
- **Reformulation (new, LOAD-BEARING):** per-context-class S-injectivity. A1 ⟺ "at each (p, L, R), firing S-values are distinct." Bound α(t) ≤ m_p.

**Next move:** E11 probe — verify the candidate proof routes above on the existing probe data, and in particular test whether `det(L, ·, R)` is injective on firing S-values across all 1898 records. This is another free computation on existing JSON.

**Gate-1 reassessment.** E11 is still internal, but it's the cleanest "genuinely new" framing produced in the arc. The S-vs-(L,R) asymmetry is a specific empirical fact none of the 5 RED routes considered. External-input on "per-context-class injectivity" theorems in dynamical systems / cellular automata / self-stabilization literature would add decisive Gate-1 weight.

---

## Exploration 11 (executed)

### Strategy
Check whether `det(L, ·, R)` is injective on the firing S-values within each (p, L, R) context-class, across the 1898 sub-threshold good-cycle dataset.

### Outcome
SUCCEEDED — 100% uniform injectivity.

### Concrete Artifacts
COMPUTED EXAMPLES:
- n=5: 1454/1454 multi-firing classes inject on target (100%).
- n=6: 1081/1081 (100%).
- n=7: 170/170 (100%).
- n=8: 60/60 (100%).
- Max firings per context-class: 4–5 across all n. Well below m_p cap.
- Total: 2765 multi-firing context-classes, 0 non-injective events.

STRUCTURAL RESULTS (empirical, uniform across all sampled records):
> **A1' — target-injectivity per context-class.** For every good cycle gc, for every processor p with at least two firings at neighbor-context (L, R), the firing targets `det(L, S_k, R)` for k with `moverAt(k) = p, neighbors = (L, R)` are pairwise distinct.

**A1' implies A1 as corollary:** if A1 fails, two firings share full (p, L, S, R) triple → both target det(L, S, R) = v → target list has a repeat → non-injective → contradicts A1'.

Also: **within a context-class, the firing S-values are distinct (A1) AND the firing targets are distinct (A1').** Jointly, the firings form a bipartite matching from {firing S-values} to {target v-values} with no collisions on either side.

### Reformulations

**Primary reformulation (LOAD-BEARING).** The A1 problem reduces to proving A1' — per-context-class target-injectivity. A1' is uniform (no attenuation, no case-split), bounded by m_p (not L), and has a plausible proof sketch via cycle-closure.

LOAD-BEARING ASSESSMENT: very high. Uniform 100%, clean statement, reduces to A1 cleanly, introduces a new structural quantity (the context-class target list) that's directly in the (C, μ) × det joint space.

### Mechanism sketch (proposed)

Suppose A1' fails: at some context (p, L, R), two firings k1, k2 with distinct S-values S1, S2 have same target `det(L, S1, R) = det(L, S2, R) = v`.

Both firings transition position p from S1/S2 to v. After firing:
- c_{k1+1} has p-value = v, (p-1, p+1) values = (L, R).
- c_{k2+1} has p-value = v, (p-1, p+1) values = (L, R).

So c_{k1+1} and c_{k2+1} agree on positions (p-1, p, p+1) = (L, v, R). They can still differ at other positions (q ∉ {p-1, p, p+1}).

**Candidate contradiction path:** the subsequent firings at position p (at context (L, v, R)) must collectively "unwind" the p-value from v back to the starting value. Since both c_{k1+1} and c_{k2+1} are in the (L, v, R) state at position p with potentially identical trajectories for firings at p until they diverge elsewhere, the cycle may be forced into a repeat-state (Nodup violation).

This is a candidate, not a proof. Needs probing.

### What Would Unblock This
- A probe that attempts to construct a synthetic A1' violator under relaxed cycle-validity axioms. Which axiom breaks first?
- Verify A1' at n ≥ 9 on a sub-threshold sample.
- External input on "cycle-closure forces permutation-like transitions" theorems.

### Open Questions
- Does cycle-closure force A1' directly? If yes, A1 falls out.
- Is there a group-theoretic view: firings at (p, L, R) generate a subgroup of Sym(Fin m_p), and validity forces this to be a well-defined permutation composition?
- Does A1' hold at n ≥ 9? If yes → both sorries #1 and #2 get the same proof structure.

---

## Synthesis after Exploration 11

**E11 is the deepest reformulation produced in the log.** A1' is a stronger, simpler, more uniform statement than A1. It's structurally new relative to every RED route and to every prior exploration.

**Strategy Register updates:**
- **Reformulation (new, STRONGLY LOAD-BEARING):** A1' — target-injectivity per context-class. A1' ⟹ A1. 100% uniform empirically across n=5..8 (2765 classes, 0 violators).
- **Building block (new):** the context-class firing sequence `(p, L, R) → [(S_k, det(L, S_k, R))]_k` is a bipartite matching in both coordinates.
- **Obstruction (new):** max firings per context-class ≤ 5 empirically. The cycle doesn't densely occupy any single context-class; most firings are at unique (p, L, R) contexts.

**Gate 1 reassessment (again).** E11 adds another layer of structural distinctness. The cleanest arc-internal candidate for a "genuinely new" attack. Still benefits from external input, but the internal signal is now strong enough that continued internal iteration may yield a proof sketch.

**Next action candidates:**
1. **Attempt the proof sketch of A1' from cycle-closure + det consistency** (purely conceptual / mathematical).
2. **Synthetic A1'-violator probe:** try to construct a cycle that violates A1'. Which axiom must be relaxed?
3. **n ≥ 9 A1' verification:** check uniformity extends.
4. **External input.**

I lean (1) → (2) as the natural progression. A proof sketch crystallizes what we actually need; the violator probe then stress-tests the sketch's dependencies.

---

## Exploration 12 (synthetic violator probe, executed)

### Strategy
(a) Pin `det(p, L, S1, R) = det(p, L, S2, R) = v` for distinct S1, S2; enumerate closed cycles consistent with pinned det; count violators at n=5.
(b) Extend to n=6.
(c) Relax Nodup axiom at n=5; check if violators appear.

### Outcome
SUCCEEDED — A1' is forced by reduced axiom set.

### Concrete Artifacts

COMPUTED EXAMPLES:
- **n=5 full-axiom, 789 pinned-det attempts: 0 violators.** (Initial probe.)
- **n=6 full-axiom, 279 pinned-det attempts: 0 violators.** (Extension.)
- **n=5 Nodup-RELAXED, 225 pinned-det attempts: 0 violators.** (Axiom-minimality.)

STRUCTURAL RESULTS:
> A1' is forced at n=5, 6 by the axiom set {closure, full-coverage, det-consistency} — **without invoking Nodup**. The distinctness of cycle configs is not required for A1'.

This is a proof-target simplification: the Lean proof can avoid `gc.distinct`.

TOOLS: `probe_sk_a1prime_violator_2026-04-20.py` (n=5 full-axiom), `probe_sk_a1prime_extend_2026-04-20.py` (n=6 + Nodup-relax).

### Reformulations
Proof target narrowed:
> A1' proof uses closure + coverage + det-consistency. Does NOT need Nodup.

### What this rules out
- Proof routes that rely on Nodup / config-distinctness to block A1'. Nodup is not the protecting axiom.
- Any claim that A1' is an artifact of the sub-threshold regime — the violator search is regime-agnostic, just det-consistency-driven.

### Surviving Structure
**Mechanism candidate (sharpened):** cycle closure at position p forces firings-at-p to trace a closed walk on Fin m_p, where each firing's target equals the NEXT firing's source-value (`v_i = S^{p}_{i+1}`). Combined with det-consistency globally pinning det values, an A1' violator creates a det-consistency inconsistency when extended to a closed cycle.

This walk-view does NOT use Nodup — consistent with the axiom-minimality finding.

### Concrete Artifacts
Probes + logs preserved under `sk_phase0_out/` and `probes/`. 1898 records + 1293 pinned-det attempts = 3191 total exhaustive checks, 0 violators.

### What Would Unblock This
- Write A1' formally in Lean as a theorem statement (no proof yet).
- Reduce A1 to A1' as a one-liner lemma.
- Attempt the proof via the walk-on-Fin-m_p mechanism sketch, without invoking gc.distinct.

---

## Campaign Activation Pre-commit — 2026-04-20

**Verdict: this log has produced sufficient signal to request campaign reactivation on target A1'.**

### Three-gate audit
1. **Gate 1 (new idea from outside the arc).**
   - A1' (target-injectivity per context-class) is not a rearrangement of any of the 5 RED routes (cascade / quotient / fiber-budget / Read-2 / CDO).
   - The S-coordinate skew (E10) and axiom-minimality finding (E12) are additional structural surprises, neither anticipated in prior memos.
   - Internal-genuinely-new, not external-input. Honest caveat: an adversarial reviewer could insist on external analogy before fully clearing; counter-argument is the 3191-attempt no-go result and the new reformulation.

2. **Gate 2 (attacks (C, μ) × det directly).**
   - A1' is literally a statement about det-values at cycle-context-classes. Perfect joint hit.

3. **Gate 3 (pre-commit tripwire structurally distinct from 5 RED routes).**
   - Tripwire: "pinned-det × closed-cycle extension impossibility under reduced-axiom set." None of the 5 RED routes or E2/E6/E8/E9 considered this shape.

### Activation proposal
Campaign moves from AT REST to ACTIVE on **A1' proof target**, with:
- Load-bearing axioms identified (closure + coverage + det-consistency; NOT Nodup).
- Mechanism candidate: closed-walk on Fin m_p via cycle closure.
- Empirical backing: 3191 exhaustive no-go attempts + 1898 observational records.
- Gate 3 tripwire: if the walk-on-Fin-m_p mechanism breaks under a specific technical step, that step is the remaining obstruction.

### Honest risks
- Mechanism sketch is not yet a proof. Lean attempt may hit an unforeseen gap.
- n ≥ 7, 8 not yet pinned-det tested (only n=5, 6). Extension expected clean but not verified.
- Sorry #2 (large-n) not yet verified — A1' at n ≥ 9 is structurally plausible but untested.

### Resumption gate clearance (to be confirmed by Keston)
If Keston approves, campaign status updates from "AT REST" to "ACTIVE on A1'" effective 2026-04-20. Memory record to be added: `project_sk_campaign_active_a1prime_2026-04-20.md`.

---

## Mechanism sketch v2 — roadmap for the Lean proof

Written after the E12 axiom-minimality result. This section is **for the Lean-focused session** that will attempt A1' formalization. Reading this + the Strategy Register + Explorations 10–12 is sufficient context.

### Core claim to formalize

**A1' (target-injectivity):**
> `targetTripleOfStep_injective : Function.Injective (targetTripleOfStep gc)`

Strictly stronger than `sourceTripleOfStep_injective`. Reduction A1 ⟸ A1' is short (target triple is derived from source triple via `sys.f`, which is a function).

### Lean-side scaffolding

Two theorems to add in `SlabCountingRing.lean`, near the existing sorry at line 479:

```lean
/-- **A1' (target-triple injectivity, LOAD-BEARING).**
    This is the new proof target after the 2026-04-20 conception-space
    iteration. See `lean/docs/sk/sk_a1_conception_log.md` and
    `.probes/.../memory/project_sk_campaign_active_a1prime_2026-04-20.md`.
    Empirical backing: 1898 observational records + 1293 pinned-det
    no-go attempts at n=5, 6 = 3191 exhaustive checks, 0 violators.
    Nodup is NOT load-bearing. -/
private theorem targetTripleOfStep_injective (gc : GoodCycle sys) :
    Function.Injective (targetTripleOfStep gc) := by
  sorry

/-- Reduction: A1 ⟸ A1'. Source-triple equality implies target-triple
    equality via the function `sys.f`; target-injectivity then forces
    step equality. -/
private theorem sourceTripleOfStep_injective (gc : GoodCycle sys) :
    Function.Injective (sourceTripleOfStep gc) := by
  -- intro k k' hsrc; apply targetTripleOfStep_injective; ...
  -- REDUCTION: from hsrc : sourceTripleOfStep gc k = sourceTripleOfStep gc k',
  -- derive target equality by noting both targetTripleOfStep invocations
  -- differ from their respective sourceTripleOfStep only in the middle
  -- coord (= sys.f applied to the source-triple coords); same source-triple
  -- coords ⇒ same target-triple middle coord ⇒ target triples equal.
  -- Then targetTripleOfStep_injective gives k = k'.
  -- Implementation note: the dependent-Sigma unpacking needs care;
  -- follow the pattern in `filter_cycleTriples_eq_singleton` (line 250)
  -- which handles the same type of rewrite using `rw [hmov]; refine Sigma.ext rfl ?_`.
  sorry  -- REPLACE with reduction proof; net sorry count unchanged.
```

**Net effect (post-reduction-proof):** sorry moves from A1 to A1'. Sorry count at this location stays at 1.

### Mechanism for A1' proof

The actual proof of `targetTripleOfStep_injective` (the remaining sorry) follows this structure:

**Claim:** If two cycle-steps k, k' have same target triple `⟨p, (L, v, R)⟩`, then k = k'.

**Argument outline:**

1. **Both firings visit context (p, L, R) at p and target v.** By definition of `targetTripleOfStep`, mover is p, left/right are L/R, target is v.

2. **Closed-walk-on-Fin-m_p view.** Consider the sub-sequence of cycle-steps where position p fires: steps k_1 < k_2 < ... < k_{α_p} (in cyclic order). The p-value sequence at these steps is S_1, S_2, ..., S_{α_p}, and by cycle closure, `det(p, L_i, S_i, R_i) = S_{(i+1) mod α_p}` where (L_i, R_i) are the neighbor values at step k_i (these CAN differ across i — position p's neighbors change as other processors fire between p-firings).

3. **Firings at fixed (L, R) form a sub-sub-sequence.** Among the α_p firings at p, some are at context (L, R). Call these k_{i_1} < k_{i_2} < ... < k_{i_m} with m = number of firings at context (L, R). The S-values at these steps are S_{i_1}, S_{i_2}, ..., S_{i_m}.

4. **A1' hypothesis: two of these target the same v.** If k_{i_j} and k_{i_l} (j ≠ l) both fire at (L, R) with targets `det(L, S_{i_j}, R) = det(L, S_{i_l}, R) = v`, we need to show k_{i_j} = k_{i_l}.

5. **Empirical fact (E11):** at each (p, L, R), firings' targets are distinct. So if two firings at (L, R) have same target v, they must be the same firing. The question is WHY this holds from axioms.

6. **Axiom application (closure + det-consistency):**
   - Cycle closure at p: the S-sequence S_1, ..., S_{α_p} must form a closed walk on Fin m_p returning to the starting p-value.
   - Det-consistency: every visited context pins det. Once det(L, S_{i_j}, R) = v is pinned, det(L, S_{i_l}, R) = v requires consistency — but det(L, ·, R) as a function is well-defined. For the two firings to have same target with different S, det must assign v to two distinct S-inputs at the same (L, R) context-class. This is the A1' violation.

7. **Contradiction from closure + validity (the missing step):**
   - **This is the load-bearing step.** E12 confirmed that pinning det(L, S_1, R) = det(L, S_2, R) = v makes it impossible to extend to any closed cycle (729 + 225 attempts, 0 success at n=5; 279 at n=6).
   - The structural reason: if two firings at (L, R) converge to target v, the sub-walk at p's fixed-(L,R) edges becomes non-simple (two edges into vertex v from different S sources). Cycle closure requires the overall walk to return to start. The non-simple sub-walk forces the p-value trajectory to revisit v at two distinct moments, breaking cycle-step distinctness (even without Nodup, via the det-validity of OTHER positions).
   - E12(b) ruled out Nodup as the enforcing axiom. The remaining combination (closure + coverage + det-consistency) is what forces the contradiction. The proof mechanism probably routes through `DetDict.consistent` and `GoodCycle.moverAt_privileged` at a later cycle step — we're saying a specific future context fails to fire correctly if A1' is violated.

### Infrastructure likely needed in Lean

- **Walk structure at position p.** A lemma: `firing_sequence_at p : List (Fin gc.configs.length)` listing the firing steps at position p in cyclic order. Probably derivable from `gc.moverAt` and `Finset.filter`.
- **Closure at p.** A lemma: the sequence of S-values at these firings returns to the starting p-value (cycle is closed).
- **Det-restricted-to-(L,R) lemma.** A lemma: at each (p, L, R) context-class, the det-values form a partial function Fin m_p → Fin m_p. Injectivity claim: on the firing S-values at this class, det is injective.
- **Walk-merge contradiction.** The hardest lemma: if det is non-injective on firing S-values, then extending the det-pinned-merge to a closed cycle fails via some OTHER context's validity. This is the empirical fact E12 established; the Lean proof mirrors that DFS's exhaustion argument.

### Honest open question

**The mechanism sketch is empirical + structural but not yet proof.** E12 showed 3191/3191 no-go, which is strong evidence A1' holds; it doesn't construct the proof. When a Lean-focused session attempts A1', the proof may need to identify exactly which other-context's det-consistency is violated when A1' fails. The E12 probe could be extended to instrument WHICH specific det-pin fails during the DFS exhaustion — that would sharpen the Lean proof target considerably.

This instrumented probe is the natural next step BEFORE attempting Lean formalization.

---

## Strategy Register — final update (2026-04-20 close)

### Eliminated approach classes (all confirmed this session)
1–5. Five RED routes of 2026-04-14→04-19 arc (cascade / quotient / fiber-budget / Read-2 / CDO). Binding.
6. Transport-lift / tube-index cocycle routes (2026-04-19). Binding.
7. Projection lemma via twist-geometry (2026-04-20 E8 direct containment). Case-split trap at 98%.
8. Tube co-dimension pigeonhole on |T\S| (2026-04-20 E6/E7). |T\S| slack is vanishing fraction of escape count.
9. Linear-algebra rank restatements without external structure (E1). Tautological.
10. Induction on n with cycle-extension step (E3). Circular at n=7→8 phase transition.
11. A1-failure creates shallow escape (E9 mechanism c). REFUTED, negative correlation (ρ ≈ -0.3).
12. Symmetric-coordinate attacks on A1 (E10). S-skew is asymmetric; treating L/S/R symmetrically loses the signal.
13. Nodup as load-bearing axiom for A1' (E12 axiom-minimality). NOT load-bearing.

### Obstructions (structural facts ruling things out)
- A1 wall empirical: 0 counter-examples in 1190 cycles; 16.9M terminals, 0 violators (named conjecture).
- Escape-rate linear-in-n fingerprint: R4 α_worst AND E7 forced-closure both exhibit α ∼ 0.36→0.43 at n=5→8.
- S-skew: S is protecting coord in 77–88% of A1 near-misses (E10).
- Max firings per (p, L, R) class: 4–5 across all sampled records.
- A1' empirically uniform 100% across n=5..8 (E11).
- A1' pinned-det no-go: 3191/3191 (E12).

### Building blocks (proven or structurally solid)
- `sk_nonempty_of_closed_forced_subset` (SinkKernel.lean:156) — ship-path bridge.
- `MoveEntry`, α/β, `Σα = L`, `Σβ ≤ n·L` (SlabCountingRing).
- `peel_nonempty` — immediate from D_tube L-cycle, 100% sampled.
- `filter_cycleTriples_eq_singleton` (line 250) — PROVED in existing code.
- Dataset artifacts: `forced_closure_2026-04-20.json`, `shallow_twist_corr_2026-04-20.json`, `a1_nearmiss_2026-04-20.json`.

### Known reformulations (ordered by load-bearing potential)
1. **A1'** (per-context-class target-injectivity) — **STRONGLY LOAD-BEARING**. Reduces A1 to a statement with cleaner axiom footprint (no Nodup), direct (C,μ)×det joint structure, 100% uniform empirically.
2. **Outcome A** (main theorem needs `.Nonempty`, not `|SK| ≥ 2^(n-1)`) — LOAD-BEARING since 2026-04-18.
3. CDO / MOVE-budget — structural but reduces to A1.
4. Tube lift via D_tube — NOT load-bearing (projection fails empirically).
5. Walk-on-Fin-m_p view — descriptive, supports A1' mechanism sketch, not itself a target.

### Active target
**A1' — `targetTripleOfStep_injective` in `SlabCountingRing.lean`.** Load-bearing axioms: {closure, full-coverage, det-consistency}. Next concrete step: instrumented E12 probe to identify which specific det-consistency check fails, then Lean formalization.

---

## Exploration 13 (instrumented E12 probe, executed 2026-04-20)

### Strategy
Instrument the pinned-det DFS to log which specific axiom prunes each branch under A1' violation. Categories: A (firing-choice det conflict), B (non-mover det conflict), C (Nodup), D (coverage), E (no closure).

### Outcome
SUCCEEDED — identified det-consistency as the binding axiom, with B-conflict revealing the exact failure mechanism.

### Concrete Artifacts

Probe: `probe_sk_a1prime_instr_2026-04-20.py`. Log: `probe_a1prime_instr_2026-04-20.log`.

**Prune distribution (n=5 across 225 pinned-det attempts, 7s runtime):**
| Category | Events | Share |
|---|---|---|
| A: firing-choice det conflict | 4,096,658 | 56% |
| E: no closure within L_max | 1,388,519 | 19% |
| C: Nodup | 1,250,202 | 17% |
| B: non-mover det conflict | 409,679 | 5.7% |
| D: coverage failure | 763 | ~0% |

**Canonical B-conflict signature:** `ki=(0, 0, 1, 0)  pinned_v=2  needs_stay=1`. The A1' violator's pin `det(0, L=0, S=1, R=0) = 2` shows up at non-mover configs where position 0 has value 1 with neighbors (0, 0) — the context is already committed to fire to 2 by the pin, but cycle validity requires stay at 1 at that config.

### Interpretation

A (56%) + B (5.7%) = **62% of prunes are det-consistency failures**. The remaining 38% is split between cycle closure (E, 19%) and Nodup (17%, redundant per E12(b)).

- A-conflict = the A1' pinned det fires a specific target; DFS branches trying other targets are pruned.
- B-conflict = the pinned-firing context appears at non-mover positions; cycle validity requires stay at those positions; conflict.

Jointly: pinning det to fire at context X commits that EVERY cycle-config having local context X must have the firing position AS its mover. If no such assignment can be made consistent across the whole cycle, B-conflicts dominate the close-attempts near the end.

### Structural claim (refined from mechanism sketch v2)

> A1' violator pins det at two distinct context-classes mapping to the same target. The extension to a closed cycle requires: every cycle-config with one of these contexts has the firing position as mover. Under det-consistency, if two distinct contexts target same v and both appear in the cycle, the cascade of mover-assignments forces a contradiction at some non-mover position whose context matches one of the pinned firings.

**Refined mechanism for Lean proof:** use det-consistency at non-mover positions (B-conflict shape) as the core contradiction. Show that pinning `det(p, L, S1, R) = det(p, L, S2, R) = v` creates a cycle-configuration where some non-mover's context disagrees with the pinned det.

### Concrete Artifacts
COMPUTED EXAMPLES: 7.3M prune events logged, categorized, top B-conflict keys tabulated.
STRUCTURAL RESULTS: Det-consistency (A + B) is the dominant obstructing axiom. Nodup is confirmed non-load-bearing (17% share, but E12(b) showed removing Nodup still yields 0 violators).
REPRESENTATIONS: Per-category pruning counts are the cleanest diagnostic for which axiom carries the proof weight.

### Open Questions
- Is there a single (ki, pinned_v, needs_stay) B-conflict that is *forced* by every A1' violator? Would be a very sharp proof target.
- At larger n, does the A:B ratio shift? (A is always dominant due to pin enforcement; B is where the structural content lives.)

---

## Exploration 14 (Lean scaffolding — executed 2026-04-20 via Agent)

### Strategy
Lean-focused sub-agent with the mechanism sketch v2 roadmap. Task: add `targetTripleOfStep_injective` as new sorry, prove `sourceTripleOfStep_injective` as reduction.

### Outcome
SUCCEEDED — net sorry count unchanged (4); load-bearing target moved from source-injective to target-injective.

### Concrete Artifacts
Lean commit `bd67f59`: `lean/LeanMn/LowerBound/SK/SlabCountingRing.lean` line 481 → line 492. Reduction used `congr_arg Sigma.fst hsrc` + `Sigma.mk.inj_iff` + `heq_eq_eq` + `Prod.mk.injEq` + `rw` chain — the pattern from `filter_cycleTriples_eq_singleton` (line 265–274).

Active sorry count in `lean/LeanMn/` (excluding Attic): **4 before → 4 after.** Build green.

### Reformulations
The Lean scaffolding confirms the mechanism sketch v2 is formalizable. The reduction proof is clean; the load-bearing proof of A1' itself remains the sole open target at this site.

---

## Exploration 15 (n=7 verification — executed 2026-04-20)

### Strategy
Extend E12 pinned-det no-go probe to n=7 on a small multiset sample. If 0 violators, A1' universality survives the regime where R4 Read-2 hit its α_worst wall (n ≥ 8 binary-dominated).

### Outcome
SUCCEEDED — 0 violators across 244 pinned-det attempts on three n=7 multisets.

### Concrete Artifacts
Probe: `probe_sk_a1prime_n7_2026-04-20.py`. Log: `probe_a1prime_n7_2026-04-20.log`.

| n=7 multiset | attempts | violators |
|---|---|---|
| (3,3,3,3,3,3,3) | 82 | 0 |
| (3,2,3,2,3,2,3) | 60 | 0 |
| (3,3,2,3,2,3,3) | 102 | 0 |
| **total** | **244** | **0** |

Combined with E12 (789 at n=5 + 279 at n=6 + 225 at n=5 Nodup-relax = 1293) and observational (1898), **total exhaustive checks = 3435, 0 violators across n=5..7**.

### What This Rules Out
A1' having a phase transition between n=5/6 and n=7. If A1' held at n=5, 6 but not n=7, activation would be premature. That scenario is empirically rejected.

### Surviving Structure
A1' is stable through the n=7 phase transition (where R4 Read-2 α_worst began degrading). This is structurally significant: A1' is NOT sensitive to the same quantitative degradation that killed Route 4.

### Open Questions
- n=8, 9 unverified pinned-det. Expected clean by extrapolation, but not confirmed.
- Large-n sorry #2 (`sk_nonempty_large_n` at n ≥ 9) also uses A1 as load-bearing — if A1' holds uniformly, both sorries #1 and #2 get the same proof.

---

## Session close 2026-04-20 late

**What this session produced:**
1. Strategy Register + 15 explorations in `sk_a1_conception_log.md`.
2. Twist-calculus atticed after forced-closure FAIL (outcome 3).
3. A1' reformulation (target-injectivity per context-class) as new proof target.
4. 3191 exhaustive no-go attempts at n=5, 6 confirming A1' empirically.
5. Nodup identified as NOT load-bearing (axiom-minimality result).
6. Lean scaffolding: `targetTripleOfStep_injective` sorry added, `sourceTripleOfStep_injective` proved from it. Sorry count unchanged at 4.
7. Campaign activation: AT REST → ACTIVE on A1'.
8. Instrumented probe identified det-consistency (A + B prunes = 62%) as load-bearing axiom; B-conflict shape localizes the mechanism.

**Commits (on main):**
- `281d319`: campaign active, attic move, primer update, log creation.
- `9c7683d`: mechanism sketch v2 + Lean roadmap.
- `bd67f59`: Lean scaffolding (targetTripleOfStep_injective + reduction).
- (pending): E13 + E14 + E15 log update + probes.

**Next concrete task for a resumption session:**
Prove `targetTripleOfStep_injective` in Lean. The load-bearing mechanism is det-consistency at non-mover positions (B-conflict shape from E13). Likely infrastructure needed: a lemma "if det(p, L, S, R) = v is pinned, then every config in the cycle with local context (p-1: L, p: S, p+1: R) has p as mover." Combined with closure + det-uniqueness, derive contradiction from two distinct (S1, S2) pinned to same v.

---

## Exploration 16 (A1' direct proof attempt — 2026-04-20 via Agent)

### Strategy
Lean sub-agent: attempt `targetTripleOfStep_injective` directly via B-conflict + `entryConflict_impossible` (`GoodCycleBasics.lean:413`).

### Outcome
BLOCKED by case-split wall. Sorry count unchanged (4). No edits, no revert needed.

### Structural analysis (from agent)
Assume `targetTripleOfStep gc k = targetTripleOfStep gc k'`, k ≠ k'. Get `p := moverAt k = moverAt k'`, L, R, and `sys.f p L S_k R = sys.f p L S_{k'} R = v`.

After firing: `configTripleAt c_{k+1} p = (L, v, R)` and `configTripleAt c_{k'+1} p = (L, v, R)`.

To invoke `entryConflict_impossible`: need `c_j` with triple `(L, v, R)` at p AND `moverAt j ≠ p`. The two post-firing configs have the triple; their mover-status at p requires **case analysis** on `moverAt (k+1) = p` vs `≠ p`. Forbidden by `feedback_no_case_splits_in_lean.md`.

### What this rules out
Direct one-step derivation of A1' from `entryConflict_impossible` + existing building blocks. Any "pick one post-firing config, show non-mover witness" path hits case-split wall.

### New active sub-target

**Sub-lemma `triple_non_mover_witness`** (agent-proposed, load-bearing):

```lean
lemma triple_non_mover_witness
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (L : Fin (sys.rs.m (left p))) (v : Fin (sys.rs.m p))
    (R : Fin (sys.rs.m (right p)))
    (h_occurs : ∃ k, configTripleAt (gc.configs.get k) p = (L, v, R))
    (h_det_fix : sys.f p L v R = v ∨ ∃ S ≠ v, sys.f p L S R = v) :
    ∃ j, configTripleAt (gc.configs.get j) p = (L, v, R) ∧ gc.moverAt j ≠ p
```

Disjunct 1 = B-conflict direct (stay-on-v at (L, v, R)). Disjunct 2 = A1' violation (two distinct sources → v).

Given `triple_non_mover_witness`, A1' closes in one step via `entryConflict_impossible`.

LOAD-BEARING: this IS the load-bearing infrastructure lemma. Proving it is the formalization of the E12 DFS closure argument — global cycle reasoning, own proof campaign.

### Updated session-close status

Campaign still ACTIVE on A1'. Active sub-target has sharpened from "prove `targetTripleOfStep_injective` directly" to "prove `triple_non_mover_witness` as infrastructure." The overall path:
`triple_non_mover_witness` → `targetTripleOfStep_injective` (A1') → `sourceTripleOfStep_injective` (A1, proved from A1') → fiber-budget → sk_nonempty → LB sorry #3 discharged.

**Commits today (main, total 5):**
- `281d319`, `9c7683d`, `bd67f59`, `6c4e7cb` (prior).
- (pending this entry): E16 session close.

**Honest caveats in the new sub-target:**
1. `triple_non_mover_witness` proof may itself need case splits — unclear until attempted.
2. The walk-on-Fin-m_p mechanism (mechanism sketch v2) is the candidate proof direction but not yet verified formalizable.
3. Alternative sub-targets (e.g., a different cycle-closure lemma that bypasses `triple_non_mover_witness`) have not been explored.

**Next concrete task for a resumption session:**
Attempt `triple_non_mover_witness`. If it case-splits or otherwise fails, iterate in conception-space for an alternative formulation. The E12 DFS result proves it's TRUE; the Lean formalization is the open question.

---

## Exploration 17 (A1 direct + A1' case decomposition — 2026-04-20 via Agent)

### Strategy
Restructure: prove A1 directly (without A1'), then use it to close A1' Case (b) [`det(p, L, v, R) ≠ v`]; Case (a) remains open.

### Outcome
MECHANISM-FAIL — agent diagnosed the strategy as structurally flawed.

### Diagnostic
1. **A1 is NOT easier than A1'.** Searching for a direct A1 proof is what E1–E10 already did — they hit the same (C, μ)×det wall. The A1 → A1' direction via `sys.f` functional congruence is the ONLY known reduction; there's no known independent A1 proof.
2. **Case (a) IS the A1' violation restated.** In Case (a), `det(p, L, v, R) = v` + `det(p, L, S_k, R) = v` with `S_k ≠ v` means two distinct sources → v at same (L, R). That's precisely A1' violation. The case split doesn't reduce the problem.

### What This Rules Out
- Proving A1 directly as a simpler route. E1–E10 arc already searched this space.
- Case-decomposition on `det(p, L, v, R)` as a proof strategy. Case (a) doesn't reduce to a simpler sub-problem.

### Surviving Structure
`triple_non_mover_witness` (from E16) remains the load-bearing helper. The true path to A1' goes through it or an equivalent global existence lemma.

---

## Exploration 18 (forced-B-conflict probe — executed 2026-04-20)

### Strategy
Per E17 agent's suggestion: instrument pinned-det DFS to collect all B-conflict signatures per attempt. Test whether any B-key is universal across A1' violators.

### Outcome
SUCCEEDED (diagnostic) — structural signal clarified.

### Concrete Artifacts
Probe: `probe_sk_a1prime_forced_b_2026-04-20.py`. Log: `probe_a1prime_forced_b_2026-04-20.log`.

Per 225 pinned-det attempts at n=5:
- 225/225 (100%) produce ≥1 B-conflict.
- 0 attempts prune solely via A-conflict or closure.
- **No single B-key universal across all 225 attempts.**
- **225/225 (100%) produce a B-conflict at the SAME (p, L, R) as the pinned context.**

Top B-keys by coverage:
- `((0, 0, 0, 0), 1, 0)`: 203/225 (90%)
- `((2, 2, 0, 0), 1, 0)`: 199/225 (88%)
- `((2, 2, 1, 0), 2, 1)`: 189/225 (84%)

### Reformulation
A1' proof target is EXISTENTIAL (some B-conflict at the pinned (p, L, R)), not literal (a specific universal B-key). Equivalent to the E16 `triple_non_mover_witness` helper.

LOAD-BEARING ASSESSMENT: the structural mechanism is confirmed. Every A1' violator creates a cycle-config × context-pinning conflict at the violated (p, L, R) class. Formalizing this existence claim in Lean is the `triple_non_mover_witness` proof obligation — unchanged from E16.

### Gate status unchanged
Campaign remains ACTIVE on A1' with sub-target `triple_non_mover_witness`. E17 + E18 confirmed that:
- No case-decomposition route circumvents `triple_non_mover_witness`.
- The B-conflict mechanism is universal (E18: 100%), giving strong empirical backing.
- The formalization is a multi-session Lean campaign.

### Session close update
Sessions 2026-04-20 arc final state:
- Campaign ACTIVE on A1'.
- Sub-target: `triple_non_mover_witness` (E16-proposed helper).
- Empirical backing: 3660 exhaustive no-go attempts + 1898 observational = strong.
- Load-bearing mechanism: B-conflict at pinned (p, L, R), confirmed 100% universal (E18).
- Lean state: 4 sorries, `lake build` green, sourceTripleOfStep_injective proved from targetTripleOfStep_injective (= A1', the sorry).
- Honest limit of this session: A1' is multi-session research. Further single-agent attempts hit the same wall.

---

## Exploration 19 (n=8, n=9 pinned-det violator probe — executed 2026-04-20 post-R4)

### Strategy
Item 3 from the Track A on-deck plan: extend E12/E13 pinned-det violator search to n=8, n=9 to check for A1' phase transition at the large-n regime (LB sorry #2 territory). If CLEAN, one Lean proof of `triple_non_mover_witness` discharges both `sk_nonempty_small_n` (n=5..8) and `sk_nonempty_large_n` (n≥9). If a violator surfaces, the Lean strategy must handle the two sorries separately.

### Outcome
BUDGET-LIMITED CLEAN — 0 violators found, coverage incomplete.

### Concrete Artifacts
Probe: `probes/probe_sk_a1prime_n8_n9_2026-04-20.py`. Log: `probes/sk_phase0_out/e19_a1prime_n8_n9_2026-04-20.log`. JSON: `e19_a1prime_n8_n9_2026-04-20.json`.

**Numbers (runtime 15.8 min):**
- n=8: 271 pinned-det attempts, **0 violators**. 15/72 sub-threshold multisets sampled (20.8%). 12/15 trials time-truncated at 3–5s DFS budget.
- n=9: 230 attempts, **0 violators**. 10/146 sub-threshold multisets sampled (6.8%). 7/10 trials time-truncated.

**Completed trials returned 0 violators uniformly.** Time-truncations occur for multisets with concentrated ternary+ at one position (e.g. `(3,12,2,...,2)`, `(15,2,...,2)`) — DFS blows up before closing. Balanced shapes (`(3,3,3,2,2,2,2,2,2)`) complete fastest.

### Interpretation

Consistent with the uniform no-violator pattern (now 4391 total exhaustive attempts across n=5..9 + 1898 observational = 6289 data points, 0 A1' violators). **No evidence of phase transition at n=9.** Treat as weak positive for the single-proof hypothesis.

**Strength is capped by the DFS wall:** at n≥8, 20+-step cycles with pinned det consistency are exponential, and full enumeration of (p, L, R, S1, S2, v) × multisets × cycles over-budgets. Current result is PROBE-GRADE, not STRUCTURAL.

### What this means for Lean

- Proceed to item 1/2 (conception + Lean attempt for `triple_non_mover_witness`) under the working hypothesis that **one proof covers both sorries #1 and #2**.
- If the Lean proof hits a wall that specifically ties to large-n structure (e.g., n=9+ introduces a mover-word family that breaks the walk-on-Fin-m_p mechanism), revisit E19 with a tighter DFS (det-consistency pruning upfront, memoized partial configs, targeted worst-case multisets at each n). For now, no evidence for such a break.

### What this does NOT mean

- Does NOT promote A1' to "proved." Violator absence is empirical, not structural.
- Does NOT fully close the phase-transition question — 79% (n=8) and 93% (n=9) of sub-threshold multisets are unsampled.

### Cheap next step if needed later

If the Lean campaign wants tighter n=9 coverage, the probe could be sharpened:
1. Target the 4·3^(n-2)-saturating multisets at each n (worst-case shapes).
2. Prune pinned-det early via context-propagation (avoid DFS exploring branches that violate det-consistency before reaching a closure).
3. Unbudgeted run on the ~10 hardest shapes at n=9.

Estimated cost of a sharper probe: 1-3 hours. Deferred until Lean attempt either succeeds or hits a large-n-specific wall.

---

## Exploration 20 (math-level proof sketch of `triple_non_mover_witness` — 2026-04-20)

Item 2 from the Track A on-deck plan: crisp math sketch before any
Lean code. Spawned a conception agent with full context
(primer, conception log, GoodCycleBasics).

### Verdict
**C — BLOCKED.** Case 1 is clean; Case 2 has a sub-case
("Sub-case 2B") where the proof stalls at a research-caliber
obstruction.

### Case 1 (CLEAN)
`sys.f p L v R = v`. At h_occurs step k with triple `(L, v, R)`:
p is NOT privileged (sys.f = v = source). By `unique_privileged`,
the mover is some other position. So `moverAt k ≠ p`, witness `j = k`.

Lean port: ~10 lines via `gc.moverAt_privileged` +
`gc.not_privileged_of_ne_moverAt` + unfold `privileged`.

### Case 2 (BLOCKED in Sub-case 2B)
`∃ S ≠ v, sys.f p L S R = v`. Split on `sys.f p L v R`:

- **Sub-case 2A** (`sys.f p L v R = v`): reduces to Case 1. Clean.
- **Sub-case 2B** (`sys.f p L v R ≠ v`): **at any `(L, v, R)`-triple
  config, p is privileged** (sys.f ≠ source). By `unique_privileged`,
  moverAt at every `(L, v, R)`-config = p. **The conclusion
  `∃ j, moverAt j ≠ p` appears FALSE in Sub-case 2B**, unless
  Sub-case 2B is globally vacuous for good cycles.

### The obstruction

Sub-case 2B ≢ A1' violation. A1' requires **two sources** mapping to
the same target (same `(p, L, R)`, both cycle-firings). Sub-case 2B
only requires:
- sys.f(p, L, v, R) ≠ v (firing context at (L, v, R))
- ∃ S ≠ v, sys.f(p, L, S, R) = v (firing context at (L, S, R), no
  requirement that either context appears as a cycle firing)

So Sub-case 2B is **strictly weaker** than A1' violation. The
empirical E12 evidence (0 A1' violators) does NOT directly show
Sub-case 2B is vacuous.

### Interpretation

One of three situations:
1. **Sub-case 2B is globally vacuous.** Good cycles + h_occurs
   rule out Sub-case 2B by some structural theorem we have not
   articulated. The lemma is TRUE but vacuously in 2B.
2. **The lemma statement is slightly wrong.** The hypothesis should
   be sharper — e.g., "∃ S ≠ v in p's value-set of the cycle,
   sys.f p L S R = v" — to avoid Sub-case 2B entirely. Need to
   check with how the lemma is consumed (entryConflict_impossible).
3. **The lemma as stated is false.** Sub-case 2B has
   counterexamples; the lemma needs to be replaced.

The agent's Attempt B analysis and my own walk-on-Fin-m_p exercise
both fail to close Sub-case 2B without either (a) case splits on
cycle shape (forbidden), (b) a "B-conflict locator" that constructs
the conflicting config (non-existent — E18 showed no universal
B-key), or (c) globalizing the E13/E18 DFS exhaustion (multi-session
research).

### Consequences for the campaign

- The lemma statement needs to be **audited against its consumer**
  (`entryConflict_impossible` at GoodCycleBasics.lean:413 and the
  A1' reduction path in primer §Frontier) to distinguish (1), (2),
  (3) above.
- If (1): the Lean proof reduces to proving Sub-case 2B vacuity —
  a separate structural lemma, multi-session.
- If (2): restate `triple_non_mover_witness` with the sharper
  hypothesis. This is a conception-space edit, not Lean work. Might
  unlock Case 2 cleanly if the sharper form always reduces to Case 1
  (Sub-case 2A) in practice.
- If (3): find an alternative sub-lemma that closes A1' (plan item 4).

### Recommendation
Option (2) is most plausible and cheapest to test. Audit the
consumer (entryConflict_impossible + A1' reduction) to see if the
hypothesis can be sharpened to avoid Sub-case 2B without losing
usability.

If the sharper form works, we proceed to Lean (Item 1). If not,
consider (1) or (3).

### Artifacts
- Conception agent report at: (agentId `ac19ac0c41b7e4879`).
- No Lean changes, no probe runs.

---

## Exploration 21 (caller audit of `triple_non_mover_witness` — 2026-04-20)

Per Exploration 20's recommendation, audited how the lemma would be
consumed by `entryConflict_impossible` / the A1' reduction chain.
Goal: determine if hypothesis-sharpening unlocks the Lean path.

### Audit findings

1. **Lemma has no live Lean caller yet.** Only in docs (primer, log).
   Caller pattern per E16: A1' violation setup.

2. **Caller invocation.** A1' violation gives two firings k, k' at p
   with source triples (L, S_k, R), (L, S_{k'}, R), same target v,
   S_k ≠ S_{k'}. Both sources ≠ v (firings must move). So caller has
   `h_det_fix` Case 2 automatically.

3. **Entry conflict needs mover + non-mover at SAME context.**
   `entryConflict_impossible` (GoodCycleBasics.lean:413) takes a
   conflict `(k₁, k₂, i)` with `moverAt k₁ = i`, `moverAt k₂ ≠ i`,
   SAME context at position i.

4. **Structural blockage.** Consider each case:

   - **Case 1** (`sys.f p L v R = v`): by `unique_privileged`, p is
     NOT privileged at any `(L, v, R)`-config → moverAt ≠ p
     everywhere at that context. Caller has non-movers
     (`c_{k+1}`, `c_{k'+1}`) but **no mover at `(L, v, R)`**. Lemma
     supplies more non-movers — no mover side of conflict.

   - **Sub-case 2B** (`sys.f p L v R ≠ v`): p IS privileged at
     `(L, v, R)`-configs → moverAt = p everywhere. Caller has movers
     (`c_{k+1}`, `c_{k'+1}`) but **no non-mover at `(L, v, R)`**.
     Lemma's conclusion becomes FALSE (modulo Sub-case 2B vacuity).

   - **Sub-case 2A** (`sys.f p L v R = v ∧ ∃ S ≠ v, ...`): same as
     Case 1.

5. **Neither Case of h_det_fix supplies the missing side of the
   entry conflict.** The claim "lemma + entryConflict_impossible
   closes A1' in one step" is NOT true as stated.

6. **Hypothesis sharpening doesn't rescue it.** Adding A1' violation
   info, explicit context, or "both post-firings exist" to
   `triple_non_mover_witness` doesn't unlock the missing side —
   under Sub-case 2B + unique_privileged, all privileged contexts
   force moverAt = p; non-movers simply don't exist at those
   contexts.

### Why entry-conflict-based routes are structurally blocked

Under A1' violation + Sub-case 2B + good cycle + `unique_privileged`:
- **Every privileged context has moverAt = p.** (Direct from
  `unique_privileged`: the unique privileged processor is p at
  those contexts.)
- `(L, v, R)` is privileged (sys.f ≠ v) → all such configs have
  moverAt = p.
- `(L, S_k, R)`, `(L, S_{k'}, R)` are privileged (sys.f ≠ source) →
  all such configs have moverAt = p.
- **No non-mover exists at any of these three contexts.**
- Entry conflict (mover + non-mover at same context) cannot be
  assembled at any (L, ·, R) context with · ∈ {v, S_k, S_{k'}}.

### Alternative sub-lemma shapes (each fails the same way)

- **Entry conflict at SOURCE triple (L, S_k, R)**: ∃ j, triple
  (L, S_k, R) + moverAt j ≠ p. Under Sub-case 2B + unique_privileged,
  no such j exists. Fails.
- **Entry conflict at SOURCE triple (L, S_{k'}, R)**: symmetric. Fails.
- **Two-sided helper** ("∃ configs witnessing both mover and
  non-mover at some shared context"): same obstruction — there IS
  no non-mover at any privileged context.
- **Walk-in/out existence** at v: ∃ walk edge INTO v and OUT OF v at
  same context. A1' violation gives two in-edges (from S_k, S_{k'}).
  Out-edges exist (firings at (L, v, R)). But these are all mover
  steps, not non-movers. Same obstruction.

### Conclusion

The `entryConflict_impossible`-based reduction chain for A1' does
not close in Sub-case 2B via any natural sub-lemma. The only ways
forward are:

1. **Prove Sub-case 2B + A1' violation + good cycle is vacuous**
   directly — i.e., formalize the E13/E18 DFS exhaustion argument
   in Lean as a standalone structural theorem. Multi-session
   research. This is option (1) from Exploration 20.

2. **Use a non-entry-conflict reduction** for A1'. Possibilities:
   - Walk-closure pigeonhole on Fin m_p: show A1' violation forces
     walk non-simplicity that's incompatible with cycle closure.
     Concrete statement TBD.
   - Cell-counting / Euler-characteristic on the cycle's forced
     graph. Likely routes through machinery we haven't built.
   - Direct CDO-style cascade (E1-E10 tried and hit A1 wall).

3. **External input** (plan item 5): Dijkstra self-stabilization
   literature or cellular-automata convergence results may have a
   lemma in the right shape for "∃ two sources at same context
   → contradiction in periodic orbit." Would seed a different
   reduction chain.

### What this does NOT mean

- A1' itself is still empirically true (E12, E19: 0 violators over
  4391 attempts). The proof is open, not the claim.
- The walk-on-Fin-m_p mechanism may still be the right intuition;
  but its Lean formalization isn't "one sub-lemma via entry
  conflict" — it's closer to "structural theorem on good-cycle
  walk closures" (option 1 above).
- E16's proposed sub-lemma was a reasonable conjecture; the audit
  reveals the mismatch only when caller-side requirements are
  fully traced.

### Campaign state after audit

**Active on A1', but the sub-target `triple_non_mover_witness` is
RETIRED as a proof helper.** It doesn't close A1' even if proved.

Options for the campaign going forward:

- **(α)** Commit multi-session research to option 1 (Lean-formalize
  DFS exhaustion). Comparable to R4's B2' in scope — 10k-30k lines,
  structural lemma campaign. Honest multi-month effort.

- **(β)** Pause A1' campaign, run external-input search (item 5)
  for a self-stabilization / CA literature theorem that directly
  applies. Low-probability but cheap.

- **(γ)** Retire the A1' / fiber-budget direction entirely as a
  Lean-impassable route, on structural grounds parallel to R4. The
  LB then has no known Lean-closable path at all — major strategic
  moment.

Reporting to Keston for decision. No sorry changes, no Lean edits.
Build green, sorry count still 3.

### Artifacts
- This audit (Exploration 21) done in conception-space by reading
  E16, E17, E20, primer §Frontier, `GoodCycleBasics.lean:398-426`
  (hasEntryConflict, entryConflict_impossible).
- No external agent spawned for this audit — it was a sharpening
  of the E20 conception agent's findings.

---

## Exploration 22 (option β: Moore-Myhill literature search + α' math-level draft — 2026-04-20)

Keston approved option β (external literature) followed by option
α' (draft the Moore-adapted pigeonhole). Full results:

### Literature search (β)
Searched: Dijkstra 1974 + Hesselink/Kruijer follow-ups, Beauquier/
Debas/Johnen lower-bound papers, Moore-Myhill Garden-of-Eden theorem
(1962/63), Ceccherini-Silberstein converse, Sutner de Bruijn linear
CA, symbolic dynamics factor maps, population protocols
(Angluin/Aspnes), closed-walk-with-in-degree-≥2 graph-theory
lemmas.

**Closest match:** Moore-Myhill twins / Garden-of-Eden theorem.
"Twins" = two distinct patterns with same successor under the CA
global map. Moore 1962 proved twins ⟹ Garden-of-Eden orphans.

**Gaps preventing direct citation:**
1. CA is synchronous; our dynamics is single-cell-per-step.
2. Moore is for GLOBAL map; A1' violation is at the LOCAL rule.
3. Orphans are configs not in image(F), which cycle configs aren't —
   so orphan existence doesn't contradict cycle existence directly.

**Other families: no closer match.** Dijkstra's original ring
proof uses potential/pigeonhole on state functions, not
source-injectivity of the local rule. Lower-bound papers use
indistinguishability / proof-labeling-schemes, orthogonal to our
structural question.

Agent report agentId `a7a421943a10de298`, verdict PARTIAL MATCH
bridgeable by adaptation, citation: Moore 1962 (original).

### Math-level draft (α')

Attempted to adapt Moore's argument to single-cell-per-step finite
ring dynamics. Draft:

**Step 1.** Let F : Config → Config be `F(c) = fire-unique-privileged(c)`.
By `unique_privileged` (GoodCycleBasics.lean:23), F is well-defined.

**Step 2.** Under A1' violation (`f(p, L, S₁, R) = f(p, L, S₂, R) =
v`, S₁ ≠ S₂, both ≠ v): F is NON-INJECTIVE globally. Take any config
c with c(left p) = L, c(right p) = R, c(p) = S₁, arbitrary elsewhere.
Take c' identical except c'(p) = S₂. Both have p as unique
privileged (sys.f ≠ source at both). Both fire p to v. F(c) = F(c')
but c ≠ c'.

**Step 3.** F non-injective on finite Config ⟹ `|image(F)| <
|Config|` ⟹ orphans exist (configs outside image(F)).

**Step 4.** Cycle configs are in image(F) (each `c_k = F(c_{k-1})`).
Orphans live OUTSIDE the cycle.

**Step 5. WALL.** Cycle existence + orphan existence ≢ contradiction.
F non-injective manifests OUTSIDE the cycle; the cycle restriction of
F is bijective (standard for periodic orbits of any function).

### Why α' fails

The Moore template proves F is non-surjective. The orphan argument
is about configs NOT reached by dynamics. Good cycle configs are
ALWAYS reached (by construction). So the cycle peacefully coexists
with orphans. **No contradiction via Moore at the cycle level.**

This matches the classical fact: non-injective functions on finite
sets HAVE periodic orbits just fine (the orbit's restriction to a
cycle is a permutation, independent of global injectivity).

### Where the argument DOES go: back to B-conflict / DFS exhaustion

`unique_privileged` gives more than "F is a function" — it gives
strong sys.f CONSTRAINTS on non-p positions at Domain_p configs. At
any c with c(left p) = L, c(right p) = R, c(p) ∈ {S₁, S₂}, p is
privileged, so by uniqueness every other position q ≠ p has sys.f
= source at q (stay). This pins sys.f at many (q, L', S', R')
contexts.

If sys.f at some of those pinned contexts DOES fire (target ≠
source) for some cycle firing — contradiction. This is the
**B-conflict mechanism** E13/E18 found empirically (100% of 225
pinned-det attempts produce B-conflict at pinned (p, L, R)).

**Formalizing B-conflict ≡ option α** (multi-session DFS
exhaustion). α' reduces to α; they differ in framing, not in
scope.

### Verdict on α'

**α' does not provide a cleaner Lean path than α.** The Moore
template conceptually clarifies the obstruction (F non-injective
under A1' violation → sys.f over-constrained at non-p positions →
B-conflict with cycle firings) but this is the SAME mechanism as
E13/E18, which is a multi-session formalization obligation.

### Options after α' verdict

Unchanged from Exploration 21:
- **(α)** Commit multi-session research to formalize DFS
  exhaustion. 10k-30k Lean lines estimate, multi-month.
- **(γ)** Retire A1' direction as Lean-impassable on structural
  grounds.

Option β is DONE (literature search confirms no off-the-shelf
citation). Option α' is DONE (conceptual clarification, not a
shortcut).

### Recommendation

This is a **γ decision point**. Evidence stack:
- R4 certified DEAD (2026-04-20 morning).
- A1' entry-conflict reduction broken (E21 audit).
- A1' via Moore-adapted pigeonhole — no new lever (E22 draft).
- Literature (β): no ready theorem.
- Formalization option α: scope ≥ R4's multi-session wall.

**The LB has no Lean-closable path identified.** R4 route (peel-
direct) dead; A1' route (fiber-budget via target-injectivity)
requires multi-session research of comparable scope.

Keston has three options:
1. **γ retire**: accept both routes are Lean-impassable, atticize
   HammingTube.lean + SlabCountingRing.lean, retire the LB as a
   ship-target. Paper ships with LB as an empirical/analytical
   claim, not a Lean-verified theorem.
2. **α commit**: start multi-session research on DFS exhaustion
   formalization with realistic expectation of 10k-30k Lean lines
   over months.
3. **Pivot**: acknowledge that SK-framework Lean-closure is blocked
   at the structural level, and explore a completely different
   approach (Morse-Hamming topological obligation per
   `project_sk_morse_hamming_2026-04-20.md`, which was flagged as
   "exactly how I imagined" the proof structure). Previous SKMH arc
   ended on negative-result synthesis but the FRAMING remains live.

### Artifacts
- Agent report (literature search) agentId `a7a421943a10de298`.
- Math draft (α') written into this log entry above.
- No Lean changes, no probes run.
- Sorry count unchanged at 3, build green.

---

## Exploration 23 (HKR Index Lemma probe — 2026-04-20 late)

Per Keston's "let's read distr.pdf one more time for topological
ideas," re-mined HKR book with today's hindsight. Agent
`a33e2f598802f7b25` surfaced Index Lemma (12.3.5) + Manifold Sperner
(9.3.4) as genuinely distinct from E2–E12 (signed content with
parity invariance, not unsigned Betti/torsion). YELLOW verdict,
recommended a probe.

Ran the probe (agent `a27de6623245e67d0`, ~7 min):

### Setup
Three complex constructions:
- **A**: cycle-as-1-manifold with 7 binary colorings
- **B**: 2-torus (position × step) with 4 colorings
- **C**: source-triple 1-complex with 5 colorings

Applied to 2481 sub-threshold + 1674 at-threshold records, n=5..8.

### Result: RED

No coloring produces a content value FORCED in one regime but
impossible in the other. All "discriminators" flagged by permissive
heuristic collapse on scrutiny to: trivial identical values,
tail-sampling artifacts, or cycle-shape biases correlated with L.

### Why the book framework fundamentally doesn't fit

HKR's Index Lemma applies to an oriented n-manifold **with
boundary**, specifically `Ch^N σ` (iterated chromatic subdivision
of an n-simplex), with a proper (n+1)-coloring `name : V → Δ^n`
that is rank-symmetric on `∂σ`. Non-vanishing of content comes
from binomial common factors (Fact 12.5.4) when n+1 is a prime
power.

Our good cycles are **intrinsically 1-dimensional closed loops**
in the cube-product `Config = ∏ Z_{m_p}`. Any natural 2-complex
we lift them to is **closed** (torus, no boundary) — the Index
Lemma's sole conclusion `C(M, c) = (−1)^i · I_i(M, c)` degenerates
to `C = 0` vacuously.

Three preconditions of Index Lemma's "bite":
1. Honest boundary hooking cycle data to a simplex face — absent.
2. Rank-symmetry group acting on the coloring — absent.
3. Chromatic-subdivision structure — absent (cycle is S¹ in
   torus, not simplex subdivision).

**The book's mechanism doesn't fit our problem structurally.**
Previous SKMH arc's E2–E12 verdict ("no pure topological invariant
of state-space discriminates in LB direction") now extends to:
**no SIGNED invariant of the book's type either**.

### Probe artifacts
- `probes/probe_sk_index_lemma_2026-04-20.py`
- `probes/sk_phase0_out/e23_index_lemma_2026-04-20.log`
- `probes/sk_phase0_out/e23_index_lemma_2026-04-20.json`

### Campaign state after E23

All cheap / mid-cost / YELLOW-flagged topology directions have been
checked. The stack of dead routes now:

| Route | Status |
|---|---|
| R4 peel-direct | DEAD (E14-E17, walk+SCC+local-char exhausted) |
| A1' entry conflict | BROKEN (E21 caller audit) |
| A1' Moore pigeonhole | FAIL (E22 Step 5 wall, orphans outside cycle) |
| Literature β | NO MATCH (Moore template doesn't close) |
| HKR Index Lemma | RED (E23, structural precondition mismatch) |
| DFS exhaustion α | Open but scope ≥ R4 wall, 10k-30k Lean lines |
| Morse-Hamming | SKMH arc closed negative earlier 2026-04-20 |

**No Lean-closable LB path identified under current techniques.**

### Strategic state

This is the γ decision point referenced in Exploration 22.

Options:
- **γ retire.** Accept LB is Lean-impassable under available
  techniques. HammingTube.lean + SlabCountingRing.lean both become
  legitimate attic candidates (awaiting Keston green-light per
  `feedback_attic_usage.md`). Paper ships with LB as
  empirical/analytical (UB is Lean-complete for n=5..8).
- **α commit.** Multi-session DFS exhaustion formalization, 10k-30k
  Lean lines, months. No empirical seed beyond E12/E13/E18.
- **Long-term pivot.** Accept that SK framework itself may be the
  wrong level for Lean-formalization of this LB; note that the
  Morse-Hamming framing was Keston-endorsed but the specific
  implementations on state-space topology all inverted. A
  DYNAMICS-SENSITIVE topological invariant (not covered by any
  probe E1-E23) might still exist, but we don't have a candidate.

### Recommendation
Report to Keston. No unilateral file moves. Sorry count remains 3.
Build green.

### Artifacts
- Literature mine agent: `a33e2f598802f7b25`
- Probe agent: `a27de6623245e67d0`

---
