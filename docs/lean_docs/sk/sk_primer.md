# SK Primer — Sink-Kernel Lower-Bound Program

**Audience:** fresh reader (mathematician or Codex) picking up the SK lower-bound
campaign cold. Synthesizes the 2026-04-14 through 2026-04-20 sessions.

**Purpose:** one document that explains (a) what SK is, (b) what separator it
gives, (c) how the proof was reorganized, (d) what's proved vs open, (e) which
directions are already dead, and (f) where to go next. Every claim is
cross-linked to its primary source in `lean/docs/sk/`.

> **⚠️ READ FIRST (2026-04-20 end of day): γ DECISION POINT.** No
> Lean-closable LB path currently identified. R4 peel-direct DEAD;
> A1' target-injectivity broken at audit; HKR Index Lemma RED. Awaiting
> Keston directional call (retire / multi-session commit / pivot).
> Full decision writeup: [sk_lb_decision_2026-04-20.md](sk_lb_decision_2026-04-20.md).
> Do NOT move files to attic, spawn probes, or open Lean attacks
> without explicit direction. Jump to **Current posture (2026-04-20,
> end of day)** below for today's evidence stack; skim the older
> routing paragraphs for context only.

**Routing for a next-agent attack (2026-04-19 late-late, SUPERSEDED):**
the primer describes two distinct workstreams — read both headers
before picking a target.

- **SK ship gate — AT REST.** Sorries #1 / #2 (`sk_nonempty_*` in
  `CloudsTheorem.lean`) and sorry #3 (`sourceTripleOfStep_injective`
  in `SlabCountingRing.lean`) are the three sorry-sites on the ship
  gate. Five RED routes (§0 "The wall"). Resumption criteria binding
  — do not open a sixth scoping cycle without the three gates
  clearing.
- **Twist-calculus package — OPEN, current frontier `DTNF_forward`.**
  Newly formalized in Lean (4 files under `LeanMn/LowerBound/SK/`);
  statements frozen; build green; *off* the ship gate. The next
  single-target attack is `DTNF_forward` in `DominantNormalForm.lean`:
  dominant-regime min closed threading admits a `DominantWitness`
  (4 R-twists + 2 L-twists + stretch balance `Σ k_R = Σ k_L`). Proof
  route is combinatorial on the tube digraph. Signature freeze:
  `sk_theorem_package_freeze_2026-04-19.md`. Slate:
  `sk_twist_calculus_slate_2026-04-19.md`. See the formalized-package
  addendum below and §11 file map ("Twist-calculus package" block).

**Current posture (2026-04-20, end of day): γ DECISION POINT —
no Lean-closable path identified.** See [sk_lb_decision_2026-04-20.md](sk_lb_decision_2026-04-20.md)
for the full decision writeup. Both routes attempted after the
2026-04-19 AT-REST state have now dead-ended:

1. **R4 peel-direct route**: certified DEAD.
   See [sk_r4_frontier_2026-04-20.md](sk_r4_frontier_2026-04-20.md).
   Phase A infrastructure shipped ([HammingTube.lean](../../../lean/LeanMn/LowerBound/SK/HammingTube.lean),
   211 lines, 1 sorry `peelTube_nonempty` at :175) but E14-E17 showed:
   - Walk-based constructions fail in 26% of records (E14, E15).
   - The unique non-trivial SCC per record (E16) is globally
     defined — best local predicate accuracy 46.7% min (E17).
   - Mathlib has no partial-function cycle-existence lemma at the
     needed shape.
   Realistic bounded-case-split port: 15k-40k Lean lines per Keston's
   10× correction. Violates `feedback_no_case_splits_in_lean.md`.

2. **A1' target-injectivity route**: broken at audit (E21) and
   pigeonhole (E22).
   - **E21 caller audit**: `triple_non_mover_witness` doesn't
     actually close A1' via `entryConflict_impossible`. Under
     `unique_privileged` (`∃!` at [GoodCycleBasics.lean:23](../../../lean/LeanMn/LowerBound/GoodCycleBasics.lean#L23)),
     every privileged context at p has moverAt = p. No non-mover
     exists at privileged contexts. Mover + non-mover at same
     context cannot be assembled from `(L, v, R)`, `(L, S_k, R)`,
     or `(L, S_{k'}, R)`.
   - **E22 Moore pigeonhole**: F non-injective under A1' violation
     ⟹ orphans exist, but orphans live OUTSIDE the cycle. No
     contradiction.
   - **E23 HKR Index Lemma probe**: RED. Structural preconditions
     (boundary, rank-symmetry, chromatic subdivision) absent in our
     cube-product configuration complex.

3. **Literature search (Moore-Myhill twins, Dijkstra K-state ring,
   Beauquier/Debas/Johnen, Angluin population protocols, etc.)**:
   no off-the-shelf theorem fits A1'.

**What remains on the table (decision for Keston, not autonomous
action):**

- **(γ) Retire LB as Lean ship-target.** Atticize HammingTube and
  SlabCountingRing's A1 block per explicit Keston green-light.
  Paper ships with LB as empirical/analytical (not Lean-verified).
  Sorry count drops from 3 to 1 (only UB side) on file retirement.
- **(α) Commit multi-session DFS-exhaustion formalization.** 10k-30k
  Lean lines, months; comparable to R4's wall in scope; no
  empirical seed narrower than the DFS itself.
- **Pivot.** No concrete candidate surfaced today.

**Empirical evidence stack (carry-over):**
- A1': 4391 exhaustive pinned-det attempts across n=5..9 + 1898
  observational = **6289 data points, 0 violators**. Budget-limited
  CLEAN at n=8 (271 attempts, 21% multiset coverage) and n=9 (230
  attempts, 7%). See Exploration 19 in
  [sk_a1_conception_log.md](sk_a1_conception_log.md).
- R4 peel: peel nonempty 100% across 1898 records; unique non-trivial
  SCC size ≥ 18/34/50/80 at n=5/6/7/8 (E16). Structurally striking
  but globally defined (E17).

**Sorry count 3, `lake build` green.** Commits since posture update:
`281d319`, `9c7683d`, `bd67f59`, `6c4e7cb`, `e5cb9d5`, `1a4a9ab`,
`f866f59`. No commits this session (2026-04-20 afternoon/evening) —
all artifacts are docs + probes + probe outputs. No file moves, no
sorry changes.

**Frontier is NOT `triple_non_mover_witness`.** The lemma is retired
as a proof helper per E21 audit — it doesn't close A1' even if
proved. Proposed reductions `triple_non_mover_witness → A1' via
entryConflict_impossible` and `A1' via Moore-pigeonhole` both
structurally blocked.

Hard constraint unchanged: nothing ships (no paper, no letter, no
preprint) until sorry count 0, per `feedback_no_ship_with_sorries.md`.

**For next-agent routing**: read [sk_lb_decision_2026-04-20.md](sk_lb_decision_2026-04-20.md)
FIRST. Do NOT spawn new probes or Lean attacks without Keston's
directional signal. Do NOT move any files to attic without
explicit green-light per `feedback_attic_usage.md`.

**Prior posture (2026-04-19, late-late session, superseded for A1'
target): CAMPAIGN AT REST.** Five structurally-distinct routes
attempted across the 2026-04-14 → 2026-04-19 arc, every one RED.
Consolidation memo: `sk_campaign_state_2026-04-19.md`. That memo's
directives (no sixth scoping cycle on the original five RED routes,
no named-conjecture ship path) remain binding; A1' is structurally
distinct from those five and is the only target on which the
campaign is active.

**Addendum (2026-04-19, transport-lift reopening — EXPLORATORY, not a
route resumption).** A probe arc run after the consolidation memo
reopened the board under a new lift object (`sk_board_reset_apr19.md`).
Dated verdicts from this arc, none shippable, all recorded as data:

- **R4a (edge–sink margin forest bound): REFUTED.** Peel nonempty in
  1898/1898 sampled records (n=5..8 sub-threshold), but
  `margin_inner < 0` in 73/1032 n=5 records — forest bound applies to
  undirected graphs, does not apply to a digraph. Probe:
  `probe_sk_edge_sink_margin_2026-04-19.py`.
- **R4b (directed cycle in D_tube): SURVIVES.** Tarjan + BFS girth
  confirms girth = L in 1895/1895 sampled records. Largest SCC ≈ 2L.
  Every base girth cycle has length equal to the canonical cycle L.
- **Tube index cocycle (vertex-valued phase): REFUTED.**
  (i) Σ(c) is multi-valued in 18–45% of tube vertices.
  (ii) Edge δ sets escape {0,1} on 39–83% of edges.
  (iii) No record has a threaded-all-δ=1 choice on its girth cycle.
  Conservation law Σδ ≡ 0 (mod L) on lex-min girth cycles holds in
  1898/1898 — but only as the shadow of a closed transport, not a
  local edge law. Probe: `probe_sk_cocycle_audit_2026-04-19.py`.
- **Transport-lift (both ends): both wrong, bracketing the answer.**
  T_strict (δ ∈ {0,1}) kills *all* lift cycles in 1898/1898.
  T_loose (all Σ-pairs) lifts the base girth cycle in 1898/1898, but
  trivially by inheritance. The correct transport is between them, and
  must be a physical move-semantics relation.
- **Strict anchored threading (Case A: p=q, Case B: p=M[i]):**
  0/1898 close. Failure is always `p ∉ {q, M[i]}` — Case C edges are
  load-bearing, not exceptional.
- **Anchored threading with same-defect slot re-anchoring:** 0/1898
  close. Slot-sliding on a fixed defect is not enough.
- **Min Case-C closed threading (primary empirical finding).** For
  every girth cycle in every sampled record, the closed T_loose
  threading with minimum Case-C count has exactly 6 Case-C edges for
  **n = 6, 7, 8** (647/669, 149/152, 45/45). n=5 spreads (4,5,6,7,8)
  due to L variation. The L − 6 remaining edges close under strict
  A/B. Probe: `probe_sk_min_caseC_threading_2026-04-19.py`.
- **Twist geometry — positional characterization.** Across
  841 records with min Case-C = 6:
  (a) Every Case-C edge simultaneously jumps q and i — `q_change`
  count per record = 6 and `i_change` count per record = 6 in
  **841/841**. "6 twists" = "6 defect-position jumps" = "6
  cycle-index jumps."
  (b) Σ_C Δq ≡ 0 (mod n) in **841/841** — defect position closes.
  (c) Σ_C Δi mod L concentrates on 6 (n=8: 45/45; n=7: 139/149; n=6:
  604/647), with small overflow to 7 / 8 — near-conservation on i.
  (d) C-edges fire from states with |Σ(c)| ≥ 2 at a higher rate than
  baseline (∼ 65 % vs. global ∼ 21 – 34 %); twists concentrate at
  genuine branch points.
  (e) Firing-position arity at twists skews binary (n=6 example:
  2821 binary / 629 ternary / 182 quaternary / 189 quintic / 57
  hex / 4 sept). Most twists happen at binary movers.
  (f) Δq transitions cluster on cyclic-neighbour shifts (±1 mod n)
  with a few longer jumps; defect migrates locally.
  Probe: `probe_sk_twist_geometry_2026-04-19.py`, output
  `sk_phase0_out/r4b_twist_geometry_2026-04-19.json`.

**Transport-lift board (not a ship route).** Main target unchanged:
construct a nonempty forced-closed S ⊆ NG(C). The transport-lift arc
settled on a decomposition of every min closed anchored threading
(n ≥ 6) as **(L − 6) strict A/B edges + 6 controlled twist edges**, a
twist being a simultaneous (q, i) defect-position jump at a branch
point. The resulting conjectural theorem shape ("any closed anchored
lift must contain exactly six defect-transposition edges, structurally
forced by a bounded geometric obligation independent of L") has since
been crystallized into the formalized twist-calculus package described
below. The pre-formalization language of "re-shaped targets" and
"sharpened conjectures" is superseded by that package.

**Twist-calculus package (2026-04-19 very late → formalized).**
*Frozen 2026-04-19 (late-late): the calculus package is now formalized
enough in Lean to support research on `DTNF_forward` and `CTCL_fold`
without changing interfaces.* Full statement slate:
`sk_twist_calculus_slate_2026-04-19.md`. Signature freeze:
`sk_theorem_package_freeze_2026-04-19.md`. Lean source:
`LeanMn/LowerBound/SK/{TwistCalculus, DominantNormalForm, CTCL,
FusionDefect}.lean`, `lake build` green, isolated from the SK ship gate.

Shape of the package:

- **Canonical generators:** `R_k = (-1, +(3+k))` (retreat),
  `L_k = (+2, -(3+k))` (leap), `F_k = (-2, -(3+k))` (fold).
  Per-generator charges `χ(R_k) = 1+k`, `χ(L_k) = 1-k`,
  `χ(F_k) = -7-k` (all proved in `TwistCalculus.lean`, no sorry).
- **Three regimes** by frequency at n = 6, 7, 8 (841 records):
  1. **Dominant** (4R + 2L, no exceptions) — **88.9 %**. Exact: no
     A-edges in backbone, stretch balance `Σ k_R = Σ k_L`.
  2. **Fold** (irreducible `F_k` primitives) — ≈ **4.0 %**.
     Unexpectedly satisfies CTCL (`Σ χ = 6`) exactly (34/34) despite
     `χ(F_k) = -7-k`. Compensation mechanism unexplained.
  3. **Fusion** (non-canonical, non-fold excess) — ≈ **7.0 %**. Four
     signatures; fusion defect `ε := Σ χ − 6 ∈ {0, 1, 2}`, deterministic
     from signature (linear additivity fit residual 0.0).
- **Theorem A = DTNF-forward** (dominant normal form). Formal shell
  in `DominantNormalForm.lean` via `DominantWitness` (4 R-twists, 2
  L-twists, stretch-balance `Σ k_R = Σ k_L`, explicit charge
  decomposition). One sorry.
- **Theorem B = CTCL** (Twist Charge Conservation Law: `Σ χ = 6` for
  every min closed anchored threading). `CTCL_from_witness` and
  `CTCL_dominant` proved in Lean modulo `DTNF_forward` (one-line
  algebra: `Σ χ = 4 + Σ k_R + 2 − Σ k_L = 6` by balance). `CTCL_fold`
  sorry-gated — open research target.
- **Theorem C = FDC** (Fusion Defect Classification: `ε ∈ {0, 1, 2}`,
  deterministic from fusion signature). Statements only in
  `FusionDefect.lean`; two sorries. Quarantined anomaly theory,
  explicitly NOT on the ship gate.
- **FRL (old Theorem B) archived as refuted.** CSP search returned
  0/59 fusion records globally balanceable; obstruction is algebraic,
  not a search-budget issue. See `sk_frl_csp_verdict_2026-04-19.md`.

**Current frontier: `DTNF_forward`.** Attention sink for the next
research push. Forward-only dominant normal form (Conjecture A′, the
converse realisability claim, is demoted and out of scope). Landing
it turns the package from "promising formal shell" into "one proved
regime plus two isolated open fronts" (`CTCL_fold`, FDC-Bound /
FDC-Additivity). Lean consumers (`CTCL_dominant`) already take
`DominantWitness` directly, so the proof surface does not need to
reshape interfaces. Proof route is combinatorial on the tube digraph.

This addendum describes a formalized stub package, not a ship route.
**Still no ship, still 4 SK ship-gate sorries, still AT REST** (the
new sorries in the twist-calculus files sit on the anomaly / open-
research side of the package, not the gate). Resumption criteria for
the SK ship gate at the top of the primer remain binding.

**The wall — where we're blocked.** Sorries #1 / #2 (`sk_nonempty_*`)
and sorry #3 (`sourceTripleOfStep_injective`, A1 wall) all reduce to
the same obstruction: **the det × cycle-structure interaction at a
Case B seed, with no slack.** Five disjoint attempts have all come back
to this same place:

| # | Route                         | Verdict | Why                                                              |
|---|-------------------------------|---------|------------------------------------------------------------------|
| 1 | R1 direct (sync-cascade)      | RED     | Reproduces A1 wall at step granularity — cascade-break shape guarantees non-matching triples. |
| 2 | §3 quotient                   | RED     | Every concrete quotient either needs case splits or collapses back to A1. |
| 3 | Fiber-budget port (§7.7)      | RED     | Closes `exists_unblocked_moveEntry` but the residual sorry #3 is the A1 wall relocalized (orbit-level step injectivity routes back through A1). |
| 4 | R4 Read-2 aggregate ansatz    | RED     | `E − T + sinks ≥ 1` fails on arithmetic at n ≥ 8 binary-dominated. See below. |
| 5 | CDO abstract attempts #1, #2  | RED     | #1 (closure-equation algebra) reduces to A1; #2 (det-level counterexample) rules out det-only proofs. Jointly: obstruction is neither structural-only nor algebraic-only; it lives in the interaction. |

**Route 4 quantitative wall (independent of A1).** At n=8 binary-dominated
(ms = (2,2,3,2,2,3,2,4), L=23, Σμ=12, T=181): `T = 181 > (n−3)/n · L · Σμ
= 172.5`. The `L·Σμ·((n−3)/n − ε − α)` term in the ansatz is **already
negative at n=8**, widening with n. α_worst grows linearly in n
(0.44 → 0.57 → 0.61 → 0.66 → 0.70 projected at n=9), and T/(L·Σμ)
spread at fixed (n, L, ms) is only 1.19× (T UB is cycle-shape-free on
that axis — so this is a genuine arithmetic wall, not a T1-regression
artifact). No single-term tightening saves the decomposition. Probe:
`probe_sk_T_upper_bound_2026-04-19.py`, output
`sk_phase0_out/r4_T_upper_bound_2026-04-19.json`.

**Why this is a convergent diagnosis, not five random failures.** Routes
1, 3, 5 reach A1 by direct algebra or reduction; route 2 reaches A1
after any quotient structure; route 4 fails on **independent**
quantitative grounds at the **same regime** (n ≥ 8, binary-dominated).
Four routes-to-A1 and one same-regime arithmetic wall is a stable
localization, not a repeated mistake. Attempts #1 + #2 jointly pin the
obstruction to the interaction: neither a purely-structural argument
(ignoring det) nor a purely-algebraic argument (ignoring (C, μ)) will
close it.

**Named conjecture (research artifact, DOES NOT SHIP).** Cleanest form
produced by the campaign:

> No closed simple single-priv cycle with seed-consistency at a Case B
> seed `(p, l, r, v, s_1, s_2)` satisfies `Move_q(C) ≠ ∅` for every
> `q ≠ p` — equivalently, for every such cycle there exists `q ≠ p`
> with `Move_q(C) = ∅`.

Single existence claim, uniform in (n, ms, p), clean algebraic
structure. Empirical floor: 16.9M terminals across 26 seeds, 0
violators (YELLOW-subset). Retained as a formal target if the problem
is attacked directly later. **Not a ship path** per
`feedback_no_ship_with_sorries.md`.

**Resumption criteria.** Do not open a sixth scoping cycle from inside
this arc. The next scoping session will not produce a route that has
not already been killed. Three gates must all clear before resuming:

1. A **genuinely new idea** has surfaced from outside the arc (reading,
   analogy, outside input) — not a rearrangement of known routes.
2. The idea attacks the **`(C, μ) × det` interaction directly**, not
   around it. Routes-around are known dead.
3. The idea has a **pre-commit tripwire structurally distinct** from
   routes 1–5. If the pre-commit shape matches the prior five, skip.

If any gate fails, stay at rest. The campaign's current state is the
correct state: sorry count 4, build green, diagnostic preserved,
nothing ships.

**Historical (reached during the arc, retained below):** Outcome A
audit (main theorem needs `.Nonempty`, not `|SK| ≥ 2^(n-1)`); fiber-
budget port to `exists_unblocked_moveEntry` at n ≥ 8; Sessions 2a/2b/2c
SlabCountingRing structure (`MoveEntry`, α/β, `stepMoveEntry`,
`Σα = L`, `Σβ ≤ n·L`, all zero-sorry); Session 4 bridge
`sk_nonempty_of_closed_forced_subset` in `SinkKernel.lean:156`. These
are load-bearing infra that survives the campaign pause — the sorry
count is 4, not higher, because of this work.

**HARD CONSTRAINT (2026-04-19, binding — read this carefully).** There
is **no out**. While **any** sorry remains in the Lean build — LB or
UB — **nothing external ships**. Not a paper. Not a preprint. Not an
arXiv upload. Not a DK letter. Not an email to Knuth or any other
mathematician claiming progress on the asymptotic question. Not a
Slack post, not a blog post, not a talk, not a named-conjecture
monograph, not a "results modulo one named hypothesis" writeup, not a
submitted abstract. **No ship, no letter, no nothing.**

The Phase III / DK-letter / named-conjecture artifact path is **not a
fallback**. It is not "a thing you can do if Lean doesn't close." It
is not on the table. Anything in this primer or the memo dir (§10.4,
§9, legacy scoping) that reads like a shippable backup option under
sorries is historical — read those sections as records of what was
considered and rejected, not as a menu.

**Ship gate: sorry count = 0, LB + UB, `lake build` green.** No other
threshold exists. No partial credit. No "publish the diagnostic."
Reframing decisions (R1 / R4 / Phase III / any future route) are
scored solely on whether they drive sorry count to 0. Producing a
publishable artifact short of that is not progress — it's a different
activity, and not the one the campaign is doing.

Source: `feedback_no_ship_with_sorries.md`, `feedback_deep_research_over_cheap.md`.

**What this means when the campaign is at rest (which it currently is,
see below).** The correct external surface is: **silence**. Sorry
count 4, build green, diagnostic preserved internally. Nothing goes
out. Stopping is not failing the constraint; shipping anyway would be.

---

## 0. Why this program matters (headline framing)

The program's threshold `M_n` is **piecewise**:

- `M_n = 32·3^(n-4)` for `n ∈ {5, 6, 7, 8}` (sharp small-n bound)
- `M_n = 4·3^(n-2)` for `n ≥ 9` (governs the asymptotic regime)

The small-n regime is strictly tighter (e.g. n=8: 32·3^4 = 2592 vs
4·3^6 = 2916). The asymptotic headline is driven by the n≥9 arm.

If the program lands, `liminf M_n^{1/n} ≥ 3` (from `4·3^(n-2) =
(4/9)·3^n` at n≥9). Combined with Dijkstra's classical `3^n` upper
bound, this forces `lim M_n^{1/n} = 3` — resolving **both** of Knuth's
1985 asymptotic questions on p2 of the original self-stabilizing rings
note (limsup is not < 3; liminf is > 2, in fact exactly 3).

So the headline is: **this program, if successful, resolves the Knuth
1985 open problem asymptotically** — not "tightens a lower bound."
Keep that in view when debugging forced-closure lemmas.

### Secondary headline: ARG's 1985 binary-count conjecture falls out

Clouds at n≥9 says any valid system has `stateProduct ≥ 4·3^(n-2)`.
Unpack at a ternary-dense multiset (`k` binary processors, the remaining
`n−k` all ternary):

```
2^k · 3^(n−k) ≥ 4·3^(n−2)
⟺ 2^k · 3^(2−k) ≥ 4
⟺ 9 · (2/3)^k ≥ 4
⟺ k ≤ 2
```

So **Clouds proves ARG's 1985 conjecture (constant number of binary
processors as n → ∞) as a corollary, with the constant being exactly 2**
at binary-plus-ternary multisets. (General multisets with `m_i ≥ 4`
need separate accounting; the clean statement is for the {2, 3} regime.)

This upgrades the external framing:

> **this program, if successful, resolves Knuth's 1985 asymptotic
> question and settles ARG's binary-count conjecture en route.**

It also suggests the n=9 phase transition (§5) may be **readable through
ARG/LCM machinery** rather than needing to be proved from scratch.
Three binaries survive at n ≤ 8 and fail at n = 9 — exactly the
territory where ARG's LCM constraint starts biting. Worth checking
whether the exhaustive failure of `{2³,3⁵,4}` at n=9 is ARG's constraint
in disguise. If so:

- The phase transition has a **principled name** rather than a
  computational witness.
- §5's exhaustive-sweep verification of `M_9 > 7776` becomes a
  **theorem** rather than a computation.
- The small-n-vs-large-n regime split (sorries #1 vs #2 in §7) may
  inherit structure from ARG, potentially informing the peel-witness
  construction.

Open: confirm or refute the ARG-LCM reading of `{2³,3⁵,4}` failure at
n=9. This is a literature check plus a direct algebraic comparison.

**Immediate action (2026-04-19, campaign at rest):** **none.** Five
routes RED, diagnostic preserved, resumption gated on a genuinely new
idea from outside the arc (see top block). Do not open a sixth
scoping-probe-verdict cycle from inside this arc. Per the hard
constraint above: **nothing ships while sorry count > 0**, and sorry
count is 4. No external artifact — paper, letter, preprint, email,
talk, blog — is a substitute for closing the sorries.

---

## 1. What is SK?

Let `ms = (m_0, …, m_{n-1})` be a state vector with each `m_i ≥ 2`, `n ≥ 5`.
Write `Config(ms) = ∏_i Fin(m_i)`, `M = ∏ m_i`. A **fair simple closed cycle**
`C` on `ms` is a cyclic sequence of distinct configs where every processor
fires at least once; each fire records a forced entry in the **det dict**

    det(C) : (p, c[(p−1) mod n], c[p], c[(p+1) mod n]) ↦ output.

The **non-good region** is `NG(C) = Config(ms) \ C`. The **forced graph** `G(C)`
has vertex set `NG(C)` with edges induced by `det(C)` restricted to `NG(C)`.
The **sink kernel** `SK(C)` is the fixpoint of "iteratively delete sinks". So
`|SK(C)| = 0` iff `G(C)` is a DAG.

**Why SK matters.** If a full transition table `T ⊇ det(C)` is valid
(self-stabilizing), then `G(T)` is a DAG on `NG(C)`, hence `SK(T) = ∅`. By
**monotonicity** (adding det entries can only add edges, never remove sinks
prematurely), `SK(det(C)) ⊆ SK(T)`. Thus `SK(det(C)) ≠ ∅` for *every*
candidate cycle at `ms` ⟹ no valid system exists at `ms`.

This replaces the 4-mechanism case split (Shadow / Palindromic EC / Universal
EC / Wiggle) with a single scalar probe on the determined bad graph. Source:
`sk_invariant_findings_2026-04-14.md`.

---

## 2. The separator that started it all (2026-04-14)

The breakthrough probe was `probe_witness_shadow_2026-04-14.py`: compute SK on
the *true* witness good cycle (extracted via the single-privileged walk from
stored rules) vs on every candidate from `find_short_cycles` on tails.

| n | witness |det| |NG| SK rounds | tail candidates all-nonempty? |
|---|---|---|---|---|
| 5 | L=18, \|SK\|=0, 20 rounds  | 240/240 nonempty |
| 6 | L=35, \|SK\|=0, 36 rounds  | 48/48 nonempty   |
| 7 | L=52, \|SK\|=0, 51 rounds  | (n=7 seeded enumerator) |
| 8 | L=55, \|SK\|=0, 79 rounds  | (n=8 seeded enumerator) |

**Why it was missed for months.** Prior probes used `enumerate_cycles`, whose
adjacency filter excludes the true witness cycles (lengths 18, 35, 52, 55 —
longer than typical search depth). Running on enumerator output made SK look
*anti*-separating at both sides. The fix: pull the witness directly from
`verify_witnesses.py`, then probe. Three structural blockers are documented in
`sk_invariant_findings_2026-04-14.md §"Historical context"`.

---

## 3. Structural rigidity and closed-form laws

Once SK separated witness from tail, the tail-side |SK| turned out to be
**strikingly rigid**:

- **|SK| is constant per (n, L)** across all multisets tested (5,548
  sub-`M_n` multisets at n=5..8, 0 empty-SK cases). At fixed n and L=2n
  length, |SK| does not depend on ms. Source:
  `sk_small_n_discovery_2026-04-15.md`.
- **Canonical 10-edge binary-cube skeleton**: reverse 6-cycle + 4 uniform
  attachments, identical at n=5 through n=8, edge multiplicities
  closed-form (`2^(n−3) − 1`, `2^(n−4)`, `2^(n−4) − 1`).
- **Per-processor edge count**, uniform-state count, and the full binary
  projection scale cleanly in `n`.

This rigidity is what enabled the "clouds" reformulation.

### Open structural conjecture (worth naming)

`|SK|` being ms-independent at fixed `(n, L)` — and the 10-edge binary-cube
skeleton appearing identically at n=5..8 with only multiplicities scaling
in closed form — **is not a counting coincidence**. It is evidence that
the forced graph on `NG(C)` factors through a combinatorial quotient that
only sees `(n, L)`, with fibers of predictable size.

If that quotient can be pinned down:

- The historical Lemma A / B / C dispatch becomes **post-hoc**. SK
  computation would be ms-insensitive *by construction*; the bound could
  be read off the skeleton instead of proved per regime. This is mostly
  academic now that the main theorem only needs nonemptiness, but it
  would give a clean analytical proof of the strong `|SK| ≥ 2^(n-1)`
  form that the empirical data supports.
- The obstruction triangle (§9) would become readable too. The three
  c*-program routes (Exp 20 / 21 / 23) plausibly close access to the
  **same skeletal object** from three directions — counting, orbital
  construction, and global potential are three ways to see the quotient,
  each obstructed for the same underlying structural reason.

This is not a session's work — it is a conjecture about where the
universality is coming from. Worth holding as a lens while any of the
remaining analytical routes are pursued. If a proof of Lemma C falls out
of skeletal reasoning rather than projection induction, that's a sign the
quotient has been identified.

---

## 4. The Clouds Theorem (unifying reformulation)

Originally posed as a single counting inequality:

> `|SK(C)| ≥ 2^(n−1)` for every fair simple closed cycle C on sub-`M_n` ms.

**This strong form is no longer the Lean target.** The 2026-04-18 audit
showed the main-theorem hook (`not_converges_of_closed_forced_set` at
`SinkKernel.lean:298` and its sibling `not_converges_of_SK_nonempty` at
`:281`) consumes only **nonemptiness** — `(SK gc).Nonempty` — plus
NG-membership and forced-successor closure. No cardinality bound is read
off. Both call sites (`SmallN/CloudsLB.lean:42`, `LargeN/CloudsLB.lean:34`)
route through the `.Nonempty` variant.

Accordingly, `CloudsTheorem.lean` was refactored. The current Lean target is:

> For `n ≥ 5` and sub-`M_n` `ms`, every `GoodCycle sys` satisfies
> `(SK gc).Nonempty`.

The Lemma A / B / C three-way split is gone from the file. The
three lemmas (`|SK| = 2^n − 2n − …` at L = 2n, the `+2^(n-3) − 1` step at
L = 2n+1, the `≥ 2^(n-1)` floor at L ≥ 2n+2) still hold
empirically at n = 5..10 across ~150K cycles with zero violations — they
are useful scaffolding and their sketches remain in the docs — but they
are not load-bearing.

The two remaining SK sorries (`sk_nonempty_small_n`, `sk_nonempty_large_n`)
are regime wrappers on the same structural obligation: produce a nonempty
Finset `S ⊆ NG(C)` that is closed under forced successors. Session 4's
bridge `sk_nonempty_of_closed_forced_subset` then converts that witness
into `(SK gc).Nonempty` with no further bookkeeping.

### Historical note (Lemma C scope)

At **all-binary** ms (`m_i = 2` for all i), det consistency forces **L = 2n**
— no longer cycles exist. So the historical Lemma C was only needed when
some `m_i ≥ 3`. Source: `sk_lemma_c_proof_path_2026-04-16.md §"Critical
Discovery"`. Under the nonemptiness-only target this observation is
downgraded from proof-critical to useful color.

---

## 5. UB witnesses — what realizes `M_n` (and the n=9 phase transition)

`M_n` is piecewise because the construction that realizes it changes at
n=9. Two distinct regimes, with a sharp transition. The LB program has to
match both.

### Regime 1: n ∈ {5, 6, 7, 8} — "3 binary + 1 quaternary + rest ternary"

Valid systems exist at product exactly `32·3^(n-4)` via the "3+1+rest"
multiset pattern:

| n | optimal ms                        | product  | = 32·3^(n-4) | stored witness cycle L |
|---|-----------------------------------|----------|--------------|-------|
| 5 | (2,2,2,3,4)                       | 96       | 32·3        | 18 |
| 6 | (2,2,2,3,3,4)                     | 288      | 32·9        | 35 |
| 7 | (2,2,2,3,3,3,4)                   | 864      | 32·27       | 52 |
| 8 | (2,2,2,3,3,3,3,4)                 | 2592     | 32·81       | 55 |

Cycle lengths from Probe 3 (`sk_invariant_findings_2026-04-14.md`). The
witness good cycles are **"other" type** — not pure sweep, not pure bounce
— a CLB-style bounce-with-ternary-detours structure. They are the cycles
on which Probe 3 first observed `SK = ∅` (see §2).

Proved: `M_n = 32·3^(n-4)` for n ∈ {5,6,7,8}, exact.

### The n=9 phase transition

The "3+1+rest" pattern **breaks at n=9**. A counting lemma + exhaustive
sweep forces the jump:

- **Counting**: at n=9, any product `≤ 7776 = 32·3^5` forces ≥ 3 binary
  positions (if ≤ 2 binary, product ≥ `4·3^7 = 8748 > 7776`).
- **Exhaustive sweep**: `M_9 > 7776`. All 56 orientations of `{2³,3⁵,4}`
  fail. `{2⁴,3⁴,6}` and `{2⁵,3³,9}` also fail (MEMORY.md).

So no valid system exists at product `32·3^5 = 7776` at n=9. The next
achievable product is **`4·3^7 = 8748`**, via a different construction —
not a scaling artifact but a genuine regime change. Ratio `M_9 / M_8 =
8748 / 2592 = 27/8 ≈ 3.375`, not the geometric `3`.

**Possible principled name (open, worth checking).** The exhaustive-sweep
failure of `{2³,3⁵,4}` at n=9 may be **ARG's 1985 LCM constraint in
disguise** rather than a brute computational fact. See §0 "Secondary
headline" for the corollary `k ≤ 2` that Clouds forces at ternary-dense
ms. Three binaries survive at n ≤ 8 and fail at n = 9 — exactly the
territory where ARG's constraint starts biting. If the reading holds,
this exhaustive sweep becomes a theorem and the phase transition gets a
principled name.

### Regime 2: n ≥ 9 — endpoint-binary CLB construction

Valid systems exist at product exactly `4·3^(n-2)` via:

- **Multiset**: `ms = (2, 3, 3, …, 3, 2)` — 2 binary at endpoints, all
  interior positions ternary.
- **Good cycle**: length `3n − 2`, `n² − 2n + 8` good configs, `n − 3`
  liveness fixes.
- **Worst-case convergence**: `⌊(3n² − 4n − 11)/4⌋ = Θ(n²)`.
- **n=9**: `ms = (2,3,3,3,3,3,3,3,2)`, product `4·3^7 = 8748`.

The construction is **universal** — it gives `M_n ≤ 4·3^(n-2)` for *all*
n ≥ 5 (it just isn't tight at small n). Scripts: `clb_inherent_cycles.py`,
`clb_verify_8748.py`, `clb_witness_8748.py`. Verified n=5..18, up to 172M
configs.

Proved: `M_n ≤ 4·3^(n-2)` for all n ≥ 5. At n ≥ 9 this is conjectured
tight. `M_9 = 8748` is proved exact.

### Implication for the LB program

The Clouds Theorem target is tight at both regimes:

- **n ∈ {5..8}**: must block every fair cycle with product `< 32·3^(n-4)`.
  Sorry #1 (`sk_nonempty_small_n` at `CloudsTheorem.lean:433`) covers this.
- **n ≥ 9**: must block every fair cycle with product `< 4·3^(n-2)`.
  Sorry #2 (`sk_nonempty_large_n` at `CloudsTheorem.lean:454`) covers this.

The Knuth-asymptotic headline (§0) lands at `lim M_n^{1/n} = 3` regardless
of the small-n regime; it is driven entirely by the n ≥ 9 arm. Small-n
tightness is a "quality" improvement, not a headline mover.

### Non-optimal but universal constructions (historical context)

For cross-reference, older constructions that are **universal but not
tight**:

- **Sol 3 v1**: `ms = (2, 3, …, 3)` — 1 binary at endpoint, rest ternary.
  Product `2·3^(n-1)`. Valid for all n ≥ 3. Not optimal; gives `M_n ≤
  2·3^(n-1)` which is weaker than `4·3^(n-2)`.
- **CUP-2 universal rules**: `ms = (2, 3, …, 3, 2)` — same multiset as
  Regime 2, with a specific rule table. Good configs `(n+2)(n+3)/2 − 5`,
  cycle length `3n − 2`. Fully analytical convergence via 6-tuple automaton.

The CLB endpoint-binary good-targeting construction (Regime 2) is the
tightest universal bound currently known.

---

## 6. What the Clouds Theorem replaces

| Prior theorem                              | Under clouds proof |
|--------------------------------------------|--------------------|
| Shadow Cycle Mirror (CIC Expl 11–12)       | NOT NEEDED (subsumed by Lemma A) |
| Palindromic Entry Conflict (CIC Expl 14)   | NOT NEEDED (subsumed by Lemma A/C) |
| Universal Entry Conflict (BinSCC Expl 10)  | NOT NEEDED (subsumed by Lemma C) |
| Wiggle Shadow Cycle (CIC Expl 12–13, 15)   | NOT NEEDED (subsumed by Lemma B/C) |
| ZeroWinding clustering lemma               | NOT NEEDED |
| BadCycleData → GlobalObstruction shadow trap | NOT NEEDED |
| `LowerBound/SK/...` prior architecture     | Replaced by 3 lemma files |

Thousands of Lean lines collapse to one dispatch and three lemma bodies. The
case-split gap finding (`sk_case_split_gap_2026-04-15.md`, 65% of sub-`M_n`
cycles fell outside the four mechanisms) is automatically closed because the
clouds bound is cycle-length-only.

---

## 7. Proof status (2026-04-19, late session)

### Active sorries

Source: `zerosorry_roadmap_2026-04-17.md` + §7.7 fiber-budget update.
**Four sorries outside `attic/`** — sorry #3 was relocalized during the
2026-04-19 late fiber-budget port from the compound
`exists_unblocked_moveEntry` (line 462) to the narrow step-level
injectivity `sourceTripleOfStep_injective` (line 479). Net count
unchanged; attack surface tightened.

| # | Location | Claim | Difficulty |
|---|---|---|---|
| 1 | `CloudsTheorem.lean:434` | `sk_nonempty_small_n` — produce nonempty forced-closed `S ⊆ NG` at n∈{5..8}, sub-`32·3^(n-4)` | Research (peel construction) |
| 2 | `CloudsTheorem.lean:455` | `sk_nonempty_large_n` — same shape at n≥9, sub-`4·3^(n-2)` | Research (peel construction) |
| 3 | `SlabCountingRing.lean:479` | `sourceTripleOfStep_injective` — `k ↦ sourceTripleOfStep gc k` injective on `Fin L` | Narrow (orbit-level); 0 counter-examples in 1190 cycles |
| 4 | `ConstLayerDAG.lean:10054` | CUP-2 P1 dispatch (UB-side) | Research-blocked, tripwires live |

Sorries #1, #2, #3 are all on the SK critical path. Closing #3
*conditionally* closed `exists_unblocked_moveEntry` at
`SlabCountingRing.lean:1068` for n ≥ 8 at sub-threshold product
(`stateProduct < 4·3^(n-2)`). Wiring #3's consumer into sorries #1 and
#2 is a follow-up session — see §7.7.

Both SK sorries are narrow existential obligations:
```
∃ S : Finset (Config sys.rs),
  S.Nonempty ∧ (∀ c ∈ S, NonGood gc c) ∧
  (∀ c ∈ S, ∃ c' ∈ S, c' ∈ forcedNeighbors (detOf gc) c)
```
They are *not* raw `(SK gc).Nonempty` obligations any more — the bridge
`sk_nonempty_of_closed_forced_subset` (SinkKernel.lean:156) handles the
conversion. Empirically the peel `peel(N_1(C) ∩ VC-NG)` is a valid choice
at n=5..8 (100%, 5548/5548 multisets) and on every Hamming-tractable
cycle at n ∈ {11, 12} that the Session 1 enumerator produced.

**No sorries** in `SlabCounting.lean`, `Forcing.lean`, `SinkKernel.lean`
(post Session 4 additions), `GoodCycleBasics.lean`, `FireCountNe.lean`,
`SmallN/*`, `LargeN/*`. `lake build LeanMn.LowerBound.Smal{l,arge}N.CloudsLB`
green.

### 7.5. SlabCountingRing status and the f-injectivity pinch point

> **Status (2026-04-19 late):** this section describes the *pre-reframe*
> pinch point. The fiber-budget route in §7.7 bypasses it (step-level
> counting absorbs collisions into `A_t` without needing `max_mult = 1`).
> Retained here for historical context and because the diagnosis is what
> motivated the reframe.

`SlabCountingRing.lean` is the paper-faithful port of §2 (move-entry
aggregation). Status after Sessions 2a/2b/2c:

| Piece | Status |
|---|---|
| `MoveEntry` structure (fields `i, l, s, r, v` with `in_det` and `is_move`) | **zero-sorry** |
| `alpha`, `beta`, `slabSize` | **zero-sorry** |
| `stepMoveEntry` builder (Step ↦ MoveEntry) | **zero-sorry** (~68 lines) |
| `sourceTriple_injective` (2b, MoveEntry-level) | **zero-sorry** |
| `cycleTriples` (source-indexed Finset) | **zero-sorry** |
| `sum_alpha_eq_L` | **zero-sorry** |
| `cycleTargetTriples` (target-indexed Finset via `Finset.image`) | **zero-sorry** |
| `sum_beta_target_le_n_mul_L` (target-indexed) | **zero-sorry** |
| `exists_unblocked_moveEntry` (line 1068, fiber-budget route) | **proved conditional on `sourceTripleOfStep_injective`** (2026-04-19 late) |
| `sourceTripleOfStep_injective` (line 479, load-bearing) | **sorry** — narrow step-level injectivity, 0 counter-examples in 1190 cycles |

**The pinch.** Paper step (b) is written over MoveEntries: `Σ β_k ≤ n·L`
summed over `MoveEntry`. Lean has `Σ_{target} β ≤ n·L` via
`Finset.card_image_le` at `SlabCountingRing.lean:392–394` — this bound
comes from "at most n positions can be the target at a given config." To
convert to MoveEntry-indexed form you multiply by `max_mult`, the maximum
number of cycle-active sources mapping to the same target at fixed `(l, r)`.

If **f-injectivity-on-cycles** holds, `max_mult = 1` and the conversion
is free. If it fails, the bound degrades by a factor of `max_mult ≤ m_p − 1`,
and at sub-threshold ms `m_p` is not bounded by a small constant
(pathological example: n=7, `ms = (2,2,2,2,2,2,15)`, product 960 < 972,
`max_mult ≤ 14`). So f-injectivity is not a convenience — it is
load-bearing for every counting-only closure route.

**f-injectivity-on-cycles (conjecture, `sk_f_injectivity_lemma_sketch_2026-04-18.md`).**
In any fair simple closed cycle `C`, at every position `p` and fixed
neighbors `(l, r)`, `s ↦ f(p, l, s, r)` is injective on cycle-active
middles.

**Empirical status.** Uniform across n=5..9, 1190/1190 cycles:
`L / L* = 1.00` exactly; max per-target sharing = 1 in every cycle; no
counterexamples. Source: `probe_sk_L_over_Lstar_2026-04-18.py`.

**Proof status.** Splits on `T(v) = f(p, l, v, r)` vs `v`:
- **Case A (`T(v) ≠ v`)**: closes in ~5 Lean lines via
  `unique_privileged` + `sourceTriple_injective`. Two distinct firing
  steps `j_A + 1, j_B + 1` inherit the same source triple `(p, l, v, r)` —
  direct 2b violation.
- **Case B (`T(v) = v`)**: open on paper. Structural obstruction:
  `(p, l, v, r)` is a stay, so the clean Case A collision doesn't
  reproduce. The cycle must exit the `(l, r)`-slab, change `v` via some
  other firing, and re-enter.

**Case B empirical vacuity.** `probe_sk_case_b_vacuity_2026-04-18.py`
constructively sweeps seed-forced det entries for the Case B
configuration (two sources → target v with `T(v) = v`). Result:
**0 Case B hits / 6,372 broad seeds** across n=5,6,7, 67.7s elapsed.
Strong evidence Case B is structurally vacuous in fair simple cycles,
but the obstruction is implicit — not a one-line consequence of
`sourceTriple_injective` + fixed-point.

**60-min scheduling-graph push (this session).** Built a concrete n=5
length-10 loop satisfying simplicity, 2b distinctness, det consistency,
and the Case B witness — failing only on fairness via a circular firing
dependency (pos 0 needs pos 4 or 1; pos 1 needs pos 0 or 2; pos 4 needs
pos 3 or 0). The construction exhibits a real obstruction at n=5 but the
dep-graph shape did not generalize uniformly in n, and closing it in
Lean would require case analysis over stay-triple commitments. Memo:
`sk_case_b_invariant_push_2026-04-18.md`.

**Critical-path consequence.** Sorries #1, #2, #3 all reduce to the same
research question: either prove f-injectivity (Case B closes on paper or
by a uniform structural argument), or find a counting route that
tolerates unbounded `max_mult`. No visible closure for n ≥ 7 as of this
session that doesn't route through one of these two. **The Case B
sub-program (§7.6) was the structured attempt to close the first horn;
it scoped the obstruction as formally equivalent to the original A1
problem.**

### 7.6. Case B sub-program — full scoping (2026-04-18 / 04-19)

This sub-program ran the structured push to either close Case B
vacuity or scope it precisely enough to ship as a named conjecture.
Three sequenced attempts, all binding pre-committed.

**(a) Stay-saturation invariant — RED (2026-04-18).** Goal: a local
descent function on the stay-graph (vertex `(q, t)`, MOVE/STAY
commitments) that proves Case B vacuity by potential argument.
Outcome: 60-min push exhausted candidate forms; no compact descent
function exists at the stay-graph level. This was the first
structurally-distinct global reframe of the original A1 problem.
Source: `sk_a1_stay_saturation_probe_2026-04-18.md`.

**(b) Closure-debt obstruction (CDO) — empirical probe.** Goal:
identify a single per-position invariant (closure-debt
`Δ_q = (c_terminal[q] - c_0[q]) mod m_q` plus MOVE-budget) that
characterizes Case B vacuity as `(U) ∨ (D)` — q either never fires (U)
or fires with blocked closure debt (D).

| Probe | Coverage | Verdict |
|---|---|---|
| Full sweep (`probe_sk_case_b_closure_debt`) | 726 / 726 seeds **all timed out** under tightened budget | INCONCLUSIVE (memo retracted; `sk_a1_closure_debt_probe_2026-04-19.md`) |
| Subset probe (`probe_sk_case_b_closure_debt_subset`) | 26 seeds, 16,908,958 terminals, 4 EXHAUSTIVE / 22 UNBOUNDABLE, **0 violators** | YELLOW-subset per binding pre-commit (`sk_a1_closure_debt_subset_probe_2026-04-19.md`) |

**Mechanical reading (binding):** YELLOW-subset → pivot to abstract
analysis. **Empirical signal:** 16.9 M terminals 0 violators across an
adversarially-chosen seed set (8 dense-ternary `n=6 ms=(2,3,3,3,3,3)`
seeds, the explicit failure mode that hung the full sweep, each
examined to 490 k–581 k terminals with 0 violators). Bayesian content
substantially stronger than mechanical YELLOW.

**(c) Abstract CDO proof attempts.** Pre-committed in
`sk_a1_cdo_abstract_attempt_precommit_2026-04-19.md`. Five outcome
categories: PASS / COUNTEREXAMPLE / FAIL / 3-cap-FAIL / REDUCTION.
The REDUCTION category was added 2026-04-19 after attempt #1 produced
an outcome the original §3 stop conditions hadn't anticipated.

**Attempt #1 — closure-equation algebra over `(C, μ, det)`.**
(`sk_a1_cdo_abstract_attempt1_2026-04-19.md`.) Verdict
**ABSTRACT-REDUCTION**. At a closed cycle, `Δ_q = 0` holds
automatically by the closure axiom, so CDO branch (D) is **vacuous at
the closed-cycle abstract level**. The unified scalar collapses to
`Ψ_q := MOVE_budget_q`, with `Ψ_q = 0 ⟺ Move_q(C) = ∅ ⟺ (U)`. The
abstract claim reduces to:

```
CDO at closed cycles  ⟺  ∃ q. Move_q(C) = ∅.
```

This is the **original A1 unfairness conjecture** in cleaner algebraic
clothing — the same hard problem the local-invariant push exhausted.
The closure-equation algebra at p (A/B-steps fire p, V-steps fire
non-p) gives concrete mover constraints but does not by itself force
any q ≠ p to have `Move_q = ∅`.

**Attempt #2 — det-centric pivot (object: `(det, seed)` not
`(C, μ, det)`).** (`sk_a1_cdo_abstract_attempt2_2026-04-19.md`.)
Verdict **ABSTRACT-COUNTEREXAMPLE at the det level**. All three
pre-committed sub-arguments (triple coverage, fixed-point propagation,
seed-reachability closure) fail to one explicit construction:
`det(q, (a, b, c)) := (b + 1) mod m_q` for every `q ≠ p`, leaving det
at p as the seed pins it. This det extends the seed; for every
`q ≠ p` and every triple, `det(q, t) ≠ b`, so `Move_q(det) = Triples_q`
and no q is det-uniform-STAY. Root cause: `det(p, ·)` and `det(q, ·)`
for `q ≠ p` are functions on **disjoint domains**, and the seed places
no constraint whatever on det at q ≠ p.

**Combined picture (attempts #1 + #2).** Two sharp boundary results:

- **With cycle structure** (attempt #1): obstruction reduces to original A1.
- **Without cycle structure** (attempt #2): obstruction does not exist.

Together: the proof obligation lives **exactly** in the det⨯cycle
structure interaction (unique-priv, simplicity, closure over `(C, μ)`),
with no slack on either side. Same hardness as original A1.

**Named conjecture (historical — see ship-gate note in §0).** The
DK-letter ship framing is superseded by the no-ship-with-sorries hard
constraint. The conjecture statement below is retained as a research
artifact (useful as a formal target if someone attacks Case B directly),
not as a ship candidate.

> **Conj. (Case B unfair-mover existence).** No closed simple
> single-priv cycle with seed-consistency at a Case B seed
> `(p, l, r, v, s_1, s_2)` satisfies `Move_q(C) ≠ ∅` for every `q ≠ p`.
> Equivalently: for every such cycle, there exists `q ≠ p` with
> `Move_q(C) = ∅` (i.e. q never fires).

A single existence claim, clean algebraic structure, uniform in
(n, ms, p), backed by 16.9 M-terminal empirical floor with 0
counterexamples and by the attempt-#1 reduction showing equivalence to
the original A1 problem.

**Pre-commit fit and Phase III escalation.** Per
`sk_portfolio_commitment_2026-04-18.md`, two structurally-distinct
global reframes failing → Phase III with Option A. Stay-saturation
(a) is the first formal RED. Attempt #1's REDUCTION is not a third
distinct angle — it is a *translation* of the same problem, which
informationally combines with attempt #2's COUNTEREXAMPLE to
**confirm** that no third distinct angle is reachable from this
direction. The escalation criterion is earned. See §10.4.

### Phase plan (post-audit)

- **Done**: audit (Outcome A), Session 1 de-risk (conditional A-pass),
  Session 4 bridge.
- **Next**: construct the peel Finset witness — port `peel_N1_nonempty`
  (empirical) or a SlabCounting-backed closed-forced-subset exists-claim
  (§6(a)-(d) of `SlabCounting.lean` are the four remaining obligations).
  Either route closes sorry #1 and #2 simultaneously (same obligation
  shape).
- **Deferred**: UB sorry #3 (`ConstLayerDAG.lean:10054`), separate
  critical-path, tripwires live per `project_constlayerdag_last_sorry_tripwires.md`.

Sessions 2 and 3 of the original `sk_audit_optiona.md` plan (Lemma A / B
structural ports) are **moot** — those sorries no longer exist in the
refactored file.

### 7.7. Fiber-budget reframe and Lean port (2026-04-19 late)

**Reframe.** Per `project_sk_reframe_2026-04-19.md`, the §7.6 finding
(Case B ≡ original A1) is evidence the bottleneck is **MoveEntry
parametrization**, not cycle-level math. Two alternative routes were
proposed, both attacking `SlabCountingRing.lean:462` directly without
routing through f-injectivity:

1. **Fiber-budget (primary).** Work at step-level granularity. For each
   cycle step `k ∈ Fin L`, index by `stepMoveEntry gc k`. Prove
   `α(stepMoveEntry k) = 1` (source-level injectivity of the step map;
   becomes sorry #3). Prove `Σ_k β(targetTripleOfStep k) ≤ L · Σ_p (m_p − 1)`
   via per-position double count: for each `(c, p)` configuration/position
   pair, the β-contribution is bounded by `m_p − 1` via
   `c_k(p) ∈ Fin(m_p) \ {c(p)}`. Collisions absorb into `A_t`;
   `max_mult = 1` is never needed; Case B is irrelevant.
2. **Peel-ranking (secondary).** Prove `peel(N_1(C) ∩ VC-NG) ≠ ∅` directly
   by contradiction (empty peel ⟹ every vertex has a peel time ⟹ a
   ranking where every forced successor is earlier ⟹ local obstruction
   on Hamming-1 slabs). Not yet scoped; secondary fallback.

**Scoping memo.** `sk_fiber_budget_scope_2026-04-19.md` — YELLOW-toward-PASS
verdict. Closes sorry #3 at n ≥ 8 at sub-threshold product
(`stateProduct < 4·3^(n-2)`). Residual at n ∈ {5, 6, 7} not addressed
by this route; small-n arm needs a separate argument (peel port or a
sharper arithmetic lemma).

**Lean port outcome.** `SlabCountingRing.lean` grew 464 → 1178 lines.
Structure (9-step proof):

1. `sourceTripleOfStep_injective` (line 479) — **SORRY, load-bearing**.
   Empirically tight: 0 counter-examples in 1190 cycles at n=5..9
   (`probe_sk_L_over_Lstar_2026-04-18.py`). Natural proof path:
   orbit-level argument on cycle structure.
2. `alpha_stepMoveEntry_eq_one` (line 505) — follows from (1) + cycle
   `Nodup`.
3. `matching_steps_card_le` (target-fiber injection into Fin m_p \ {c(p)}).
4. `sum_beta_target_stepMoveEntry_le` — `Σ_k β(target_k) ≤ L · Σ_p (m_p − 1)`.
5. `slabSize_ge_pow` — `slabSize(stepMoveEntry k) ≥ 2^(n-3)` for n ≥ 4.
6. `two_mul_prod_ge` — `∏(2 + d_i) ≥ 2^n + 2^(n-1) · σ`.
7. `key_pow_ineq` — `2^(n-3) + n − 1 ≤ 2^n + 2^(n-1) · σ` at n ≥ 8.
8. `sigma_m_lt_of_subMn` — `Σm < 2^(n-3) + n − 1` under `∏m < 4·3^(n-2)`
   and n ≥ 8.
9. `exists_unblocked_moveEntry` (line 1068) — main theorem, tightened
   signature:

   ```
   theorem exists_unblocked_moveEntry
       (gc : GoodCycle sys) (hn : 8 ≤ sys.rs.n)
       (hsub : stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)) :
       ∃ e : MoveEntry sys gc, e.blocked < e.slabSize
   ```

   Contradiction: assume all blocked ⟹ `L + L · Σ(m−1) ≥ L · 2^(n-3)` ⟹
   `Σm ≥ 2^(n-3) + n − 1`, contra (8).

`lake build LeanMn.LowerBound.SK.SlabCountingRing` green. Net sorry count
in file: 1 → 1 (relocalized, not reduced).

**Wall moved, not down.** The old wall was `exists_unblocked_moveEntry`
with natural proof path ≡ A1. The new wall is `sourceTripleOfStep_injective` —
a *step-level* (single-cycle) claim, not a *MoveEntry-level* (universal)
claim. It doesn't require f-injectivity; forced outputs don't enter.
Whether the new wall falls is the next open question. Pre-commits from
§10.4 are not retriggered by this move (sorry count unchanged), but the
Phase III carve-out scoping §10.1 requested has now been done and
produced a tractable-looking residual. Recommendation is to attempt the
step-level injectivity lemma before sealing Phase III.

**Not yet wired.** `exists_unblocked_moveEntry` currently has no
consumers — sorries #1 and #2 in `CloudsTheorem.lean` produce Finset S
directly via the `sk_nonempty_of_closed_forced_subset` bridge. Closing
#3 alone does not automatically close #1/#2; a follow-up session needs
the `(c) unblocked entry → VC-NG edge` obligation wired through. This
is a Lean-plumbing task, not a research task.

### 7.8. Route diagnostics: R1 direct proof and R4 peel-direct (2026-04-19, late-late)

Post-§7.7 the active question is whether `sourceTripleOfStep_injective`
falls directly (R1) or whether a disjoint route (R4: peel-direct,
orphaning sorry #3) is preferable. Both scoped this session.

#### R1 — direct proof of sorry #3 via sync-cascade

Memo: `sk_step_injectivity_scope_2026-04-19.md` (§6b).

Setup: two `Fin L` indices k ≠ k' mapping to the same source triple
`(p, (c_k(L p), c_k(p), c_k(R p)))`. Paired trajectory starting at
aligned seeds, diff set `Δ = {q : c_k(q) ≠ c_{k'}(q)}`, sync predicate
`SS_t` ≡ matching moverAt and matching full triples.

Invariant under `SS_t`: `Δ` stays constant and `{L q_t, q_t, R q_t} ∩ Δ = ∅`
(mover stays clean).

First break at step T: by fairness + `next_mover_is_local`, T ≤ t*
(first step at which mover ∈ Δ), and strictly T < t*. Break anatomy:
- **B1** same mover, triples differ via a *farther-neighbor* coordinate
  in Δ (not L/mid/R);
- **B2** movers differ, WLOG in `{L q, R q}`.

**Wall.** `entryConflict_impossible` requires mover + non-mover at the
same position with the **same** `(L, S, R)` triple. The break gives
either mover + mover, or mover + non-mover with **different** triples
(farther-neighbor differs). `sys.f` absorbs the collision; no
contradiction lands. Closing would need a secondary Δ-growth invariant,
global counting across the cascade, or a later-step entry-conflict
trigger — none visible.

**Verdict — RED.** Cascade wall is the A1 wall at step granularity.
R1 does not bypass the obstruction that §7.6 identified as A1-equivalent.

#### R4 — peel-direct (orphan sorry #3)

Memo: `sk_peel_direct_scope_2026-04-19.md`.

Premise: close sorries #1 and #2 via direct peel-nonemptiness in
`CloudsTheorem.lean`, bypassing the fiber-budget route entirely. The
existing bridge `sk_nonempty_of_closed_forced_subset`
(`SinkKernel.lean:156`) consumes any nonempty forced-closed `S ⊆ NonGood`;
peel of a suitable subset produces this directly.

Three candidate constructions:
- **A.** Explicit Hamming-1 shadow (requires generalizing the Shadow
  Cycle Mirror Theorem beyond the proved 3-binary + ternary case; open
  and killed by the zig-zag structure — 15% of peel steps are non-lockstep
  anchor-re-indexing). Dead.
- **B.** `peel(N_1(C) ∩ VC-NG)` via `iterateRemove`. Empirical target
  (656/656 records nonempty at n=5..8).
- **C.** Abstract slab-counting. Routes back to `exists_unblocked_moveEntry`
  and thence sorry #3. Not a bypass.

Phase structure for (B):
- **Phase A.** Infrastructure: `hammingDist`, `N_1`, Finset definitions.
  Mechanical, ~1–2 sessions.
- **Phase B1.** `N_1(C) ∩ VC-NG ≠ ∅`. Cheap state-count argument.
- **Phase B2.** `peel(...) ≠ ∅`. Core research obligation.

#### R4 post-scope diagnostic (handoff-doc read)

Sources: `sk_scc_tube_findings_2026-04-16.md`,
`project_sk_peel_n1_2026-04-16.md`.

- **peel nonempty 656/656 records** at n=5..8 across sampled sub-`M_n`
  multisets. Not a marginal empirical signal.
- **Edge-sink margin ≥ 6 uniformly** across all records:
  `|E_N1| − (|T_N1| − |sinks_N1|) ≥ 6`. If analytical margin ≥ 1, peel
  nonempty by graph pigeonhole (more edges than a forest admits on the
  non-sink subset ⟹ cycle ⟹ peel ≠ ∅).
- **Disjoint from sorry #3.** Margin is a graph-counting claim on the
  N_1 tube, not a triple-algebra claim. No `sourceTripleOfStep_injective`
  appears in the chain.
- **Zig-zag / dom_pair / GOOD-BAD split are strong-form phenomena**
  (|peel| = 2^(n-1)), not nonemptiness phenomena. For R4's nonemptiness
  target they don't appear.

R4's research obligation reduces to:

> **B2'.** `|E_N1| − (|T_N1| − |sinks_N1|) ≥ 1` uniformly in `(n, L, C, ms)`.

Single counting inequality. Uniform. Empirically overshot 6×.

#### R1 vs R4 ledger (updated)

| Axis | R1 (direct sorry #3) | R4 (peel-direct) |
|---|---|---|
| Scope | 1 sorry (#3) | 2 sorries (#1, #2) |
| Lean infra status | Exists | N_1 / hamming / edge-counting new |
| A1-wall routing | **Yes** — cascade break ≡ farther-neighbor collision absorbed by `sys.f` | **No** — graph counting on N_1 tube |
| Research obligation | Secondary Δ-invariant or global counting — none visible | Edge-sink margin ≥ 1 — single uniform counting inequality |
| Empirical coverage | 0 c-ex in 1190 cycles (sorry #3 true) | 656/656 records, margin ≥ 6 |
| Verdict this session | **RED** — cascade wall = A1 wall | **YELLOW** — uniform counting obligation |

#### Tripwire for R4 (from scope memo §9)

If the B2' closure routes through per-triple det invariants or requires
`sourceTripleOfStep_injective`, **STOP** — R4 hits its own version of
the A1 wall. Current read: graph counting on N_1 is structurally
distinct from triple algebra on the cycle, so this tripwire looks
unlikely to fire, but it must be checked before Phase A commitment.

#### Proposed next step

Before Phase A Lean infrastructure, run a Python probe to derive a
**closed-form lower bound** on the edge-sink margin — express
`|T_N1|`, `|E_N1|`, `|sinks_N1|` as functions of `(n, L, C, ms)`; test
whether margin ≥ 1 is analytically uniform. Cheap and discriminating.

- Probe PASS: commit Phase A, port B1 + B2' in Lean. R4 ships both SK sorries.
- Probe FAIL (margin becomes cycle-structure-dependent): R4 hits its own
  wall; escalate to §10.4 Phase III (DK letter).

Awaiting green-light before committing Lean sessions.

---

## 8. Peel-witness attack surface (what sorries #1 and #2 reduce to)

Target (both regimes): produce a Finset `S ⊆ NG(C)` that is nonempty and
closed under forced successors. Regime-specific only in the sub-threshold
hypothesis (`< 32·3^(n-4)` at n∈{5..8}, `< 4·3^(n-2)` at n≥9).

### Primary route — Hamming-1 peel

Let `N_1(C) ∩ VC-NG` be the Hamming-1 neighborhood of `C` intersected with
value-consistent non-good configs. `peel(N_1(C) ∩ VC-NG)` is the fixpoint
of "delete configs without a forced successor inside the set."

**Empirical status:**

- n=5..8, 5548 sub-`M_n` multisets, 100% nonempty; contains the `L`-cycle
  exactly. Source: `project_sk_hamming1_discovery_2026-04-16.md`.
- At n=7, `|peel(N_1(C) ∩ VC-NG)| = 2^(n-1)` **exactly** for all 373
  records — a surprising equality, not needed for the current target but
  documents the object's rigidity.
- Session 1 (2026-04-18) de-risk: all 6 cycles the DFS enumerator
  produced at n ∈ {8, 9, 11, 12} had nonempty peel. The cycle enumerator
  TLE'd on most ternary-dense n ≥ 11 multisets — a probe-scaling limit,
  not a refutation. Source: `session1_derisk_log_2026-04-18.md`.

**Structural claim (open).** The peel is nonempty at every n, every fair
cycle `C`, every sub-`M_n` ms, because:
- Hamming-1 neighbors of `C` inherit forced-successor structure from det
  (edge-counting in SlabCounting).
- Forced-successor closure is monotone, so the peel is a fixed point
  reachable in ≤ `|N_1(C)|` steps.
- Emptiness would require every Hamming-1 neighbor to have its forced
  successor off `N_1(C)` — rules out via SlabCounting's slab unblocking
  obligations §6(a)-(d).

### Alternative route — SlabCounting-backed

`SlabCounting.lean` already proves the sorry-free abstract core
(`slab_gt_budget`, `exists_underfunded`, `exists_closed_nonempty_subset`,
`slab_unblocked`). The remaining four obligations (§6 (a)-(d), token-ring
connection) would directly produce a nonempty closed-forced-subset of
NG(C) from slab counting. Either route suffices; the team picks whichever
ports cleanly.

### Dead directions (ruled out across 2026-04-16 / 2026-04-17 sessions,
retained here in case a future re-scoping tempts a re-visit)

Originally aimed at the strong `|SK| ≥ 2^(n-1)` target. With that target
now dropped they are less relevant, but the historical findings stand:

1. **Universal binary-cube lift** (`{0,1}^n ⊆ SK ∪ C`): fails at n=6 (0/6).
2. **σ-charging singleton sinks into C**: 100% dead-end before reaching C.
3. **Coordinate-slice peeling** (`peel({c : c[p]=v})`): slice survivors
   are zero — slicing destroys forced-edge structure.
4. **Auxiliary potentials over |π_p|**: every candidate collapses to
   `|π_p|` or `|S|`.
5. **Hamming-1 universal kernel as a floor** (`peel(N_1(C)) ≥ 2^(n-1)`):
   tight at n=7, fails at n=8 (0.70) and n=9 (0.44) — but the set is
   still **nonempty**, which is all the current target needs.

Sources: `sk_peel_induction_2026-04-17.md`, `exploration_log_sk_2026-04-17.md`.

---

## 9. Witness-category pivot (2026-04-17 / 2026-04-18) — historical

This section is retained for reference. It was live while the strong
`|SK| ≥ 2^(n-1)` target was in force and the survivor theorem was load-
bearing; the audit (§10) later dropped both, rendering the pivot
unnecessary for the current target.

If Lemma C large-n were not closable directly, could a *different* Finset
witness replace SK in the main obstruction plumbing? Six categories were
scoped:

| Category | Status |
|---|---|
| B-1 peel(N_k(gc) ∩ VC-NG) | **No-go** (R-A and R-B share anchor-formula core with survivor theorem) |
| B-2 detOf algebraic invariants | **No-go** (counting / orbital / semigroup trichotomy, all collapse) |
| B-3 graph-theoretic SCC | **No-go** (folded into B-1 R-B) |
| B-4 topological winding | **Open-on-different-axis** (blocked by 3CB at n≥9 + `nonZeroWinding_obstruction` sorry; non-Finset shape) |
| B-5 ergodic/measure | Unscoped |
| B-6 pure combinatorial identity | Unscoped |

**Obstruction triangle** (`sk_witness_pivot_handoff_2026-04-18.md`): every
Finset-shaped witness category maps through one of {counting, orbital
construction, global potential}, and those three routes are closed by c*-program
Exp 21 / 20 / 23 respectively. B-4 is the only category outside the triangle,
but it doesn't produce a Finset.

**Survivor theorem is irreducible** across all scoped Finset categories. The
pivot did not relieve the analytical core.

### Post-audit: B-1 verdict is moot

The 2026-04-18 audit resolved to Outcome A. The main-theorem interface
consumes only `(SK gc).Nonempty`, not the `|SK| ≥ 2^(n-1)` floor. That
drops the survivor-theorem requirement, and with it the need for a
Finset-witness pivot *around* the survivor theorem. The Hamming-1 peel
result produces nonemptiness directly, so B-1's pessimism no longer
applies to the current target.

B-4 (winding) remains blocked by 3CB at n≥9 and the
`nonZeroWinding_obstruction` sorry; it was never Finset-shaped anyway.
B-2 / B-3 were declared no-go. B-5 / B-6 were deprioritized under
Outcome A — scoping them was only load-bearing conditional on Outcome B.

---

## 10. Strategic decision points

### 10.0. Audit resolved (2026-04-18): Outcome A

The critical-path audit has been performed and resolved. Details:

- `not_converges_of_closed_forced_set` (`SinkKernel.lean:298`) consumes
  `hS : S.Nonempty`, NG-membership, and forced-successor closure — **no
  cardinality bound**.
- `not_converges_of_SK_nonempty` (line 281) consumes `(SK gc).Nonempty`.
- Both real call sites (`SmallN/CloudsLB.lean:42`,
  `LargeN/CloudsLB.lean:34`) route through the `.Nonempty` variant.

Consequences actually realized:

- `CloudsTheorem.lean` refactored: the 9-sorry Lemma A/B/C decomposition
  is gone; only two nonemptiness obligations remain (#1, #2 in §7).
- Session 4 landed the bridge `sk_nonempty_of_closed_forced_subset` in
  `SinkKernel.lean:156`, reducing the two theorems' bodies to a single
  existential sorry each (produce the nonempty forced-closed NG subset).
- B-1 pessimism moot; B-5 / B-6 scoping optional; survivor theorem not
  load-bearing at the main-theorem interface.

Memo: `project_sk_audit_outcomea_2026-04-18.md`.

### 10.1. Current live question (updated 2026-04-19 late-late): NONE — campaign at rest

All three route-scoping sessions from 2026-04-19 have closed RED:

- **R1 (direct sync-cascade, §7.8):** RED. Cascade-break shape
  reproduces A1 wall at step granularity.
- **R4 Read-2 aggregate ansatz (§7.9):** RED. `E − T + sinks ≥ 1`
  ansatz already fails arithmetically at n=8 binary-dominated
  (`T > (n−3)/n · L · Σμ`), independent of A1. T UB tightening
  (option (ii)) fires the α > 0.7 tripwire at projected n=9.
- **CDO abstract attempts #1 + #2:** RED. Together with R1, §3
  quotient, and fiber-budget, this is the fifth convergent RED. See
  the top-block wall table.

Combined with the two earlier RED verdicts (§3 quotient, fiber-budget
≡ A1 via step injectivity), that is five structurally-distinct
attempts, all closed. There is no scoping question currently live that
has not already been killed in the arc.

**Correct action:** **stop.** Write the consolidation memo
(`sk_campaign_state_2026-04-19.md`, done), put the campaign down.
Resume only on a genuinely new idea from outside this arc that passes
the three gates in the top block (§ "Current posture"). Sorry count
stays at 4; `lake build` stays green; nothing ships per the §0 Hard
Constraint.

All prior "updated options" (R4 probe-then-port; R1 secondary
invariant; Phase III / DK letter; `native_decide` carve-out) are
either now executed-and-RED (R4, R1) or explicitly dead as ship paths
(Phase III, `native_decide`). They are not a menu.

### 10.2. After SK zerosorry

- **UB sorry #3** (`ConstLayerDAG.lean:10054`) — research-blocked;
  tripwires in `project_constlayerdag_last_sorry_tripwires.md`. Do not
  touch without green-light (`feedback_lb_sk_scope.md`).
- **Paper writeup** — the campaign resolves Knuth's 1985 asymptotic
  question and (modulo unpacking at ternary-dense multisets) ARG's
  binary-count conjecture (§0).

### 10.3. Legacy strategic options (retained for reference)

The four options from `sk_witness_pivot_handoff_2026-04-18.md` (B-5/B-6
scoping, accept irreducibility, weaken threshold, accept as open
research) were **conditional on Outcome B**. With Outcome A confirmed
they are not on the active path. Retained here only so a future re-scope
doesn't have to rediscover them.

### 10.4. Phase III decision matrix (2026-04-19) — SUPERSEDED

> **Superseded by the §0 ship-gate note** (`feedback_no_ship_with_sorries.md`,
> 2026-04-19): no ship, no DK letter while any sorry remains. Anything
> below that routes toward "ship with named conjecture" is not a live
> option. The matrix and scoping work are retained as a record of what
> was considered, not as a recommendation.

Two structural pre-commits bear on the next move:

- **Portfolio commit** (`sk_portfolio_commitment_2026-04-18.md`):
  second structurally-distinct global reframe failing → Phase III with
  Option A (DK letter + named conjecture).
- **Attempt-precommit** (`sk_a1_cdo_abstract_attempt_precommit_2026-04-19.md`,
  §4 as updated 2026-04-19): two ABSTRACT-FAIL or ABSTRACT-REDUCTION
  verdicts within the 3-attempt cap → Phase III.

**State of the ledger.**

| # | Reframe | Verdict | Source memo |
|---|---|---|---|
| 1 | Stay-saturation invariant | RED | `sk_a1_stay_saturation_probe_2026-04-18.md` |
| 2 | CDO closed-cycle algebra (attempt #1) | ABSTRACT-REDUCTION | `sk_a1_cdo_abstract_attempt1_2026-04-19.md` |
| 3 | CDO det-centric (attempt #2) | ABSTRACT-COUNTEREXAMPLE (det-level) | `sk_a1_cdo_abstract_attempt2_2026-04-19.md` |

**Strict pre-commit reading.** ABSTRACT-COUNTEREXAMPLE does not
mechanically trigger Phase III (only FAIL or REDUCTION do). A third
abstract object could be attempted within the 3-cap. *But there is no
third natural object*: `(C, μ, det)` was attempt #1, `det` alone was
attempt #2, and any "third" object is either a refinement of these
or a re-clothing.

**Spirit reading.** Attempt #2's det-level COUNTEREXAMPLE is
**confirmatory** of attempt #1's REDUCTION — both point at the same
location of the proof obligation (the det⨯cycle interaction).
Together they establish a sharp boundary: with cycle structure ≡ A1,
without cycle structure no obstruction exists. This functions as
the second non-PASS outcome and earns Phase III escalation.

**Recommendation (historical, superseded).** Under the pre-2026-04-19
framing, spirit reading + portfolio binding + no third distinct angle
in sight pointed at Phase III with Option A. Under the §0 ship-gate
note this recommendation is **dead** — the DK letter is not a ship
path while sorries remain. The bullets below list what a DK letter
*would have contained* had that path been viable, retained as a record
of the scoping work only.

1. Headline: program resolves Knuth 1985 (`lim M_n^{1/n} = 3`)
   conditional on the named conjecture.
2. Named conjecture: Case B unfair-mover existence (§7.6 statement).
3. Empirical floor: 16.9 M terminals, 0 violators across 26 seeds
   including 8 dense-ternary `n=6` adversarial cases.
4. Reduction-to-A1 equivalence: closed-cycle CDO ≡ original A1
   unfairness conjecture (attempt #1 result).
5. Sharp boundary on where the obstruction can live (attempt #2
   det-level COUNTEREXAMPLE).
6. ARG corollary: `k ≤ 2` binary processors at ternary-dense ms (§0).

**Single carve-out before commit.** Scope SlabCountingRing.lean:462
directly for ~30 min before sealing Phase III, in case a counting
route exists that doesn't go through f-injectivity. Diagnosed as
unlikely (portfolio retired this) but worth confirming before the
binding move. See §10.1 orthogonal route note.

---

## 11. Where to look (file map)

Foundational discovery (read first, in order):
1. `sk_invariant_findings_2026-04-14.md` — the invariant, the separator, how it was missed.
2. `sk_small_n_discovery_2026-04-15.md` — |SK| per-n invariance, 5,548-multiset probe.
3. `sk_unified_clouds_statement_2026-04-15.md` — the single-inequality reformulation.

Proof architecture:
4. `sk_lemma_a_generalized_2026-04-15.md` — Lemma A with analytical sketch.
5. `sk_lemma_a_part1_sketch_2026-04-17.md` — Sorry #1 proof plan (ready for port).
6. `sk_lemma_c_clouds_floor_2026-04-15.md` — Lemma C conjecture, proof candidates.
7. `sk_lemma_c_proof_path_2026-04-16.md` — all-binary L=2n forcing, revised architecture.

Open-problem and dead-direction maps:
8. `sk_peel_induction_2026-04-17.md` — Strategy (A), what's open, what's dead.
9. `exploration_log_sk_2026-04-17.md` — Strategy Register (eliminated
   approaches, obstructions, building blocks).
10. `sk_scc_tube_findings_2026-04-16.md` — Hamming-1 peel route.
11. `sk_slab_counting_theorem_2026-04-16.md` — slab route (edges, not cycles).
12. `sk_edge_cycle_gap_handoff_2026-04-16.md` — why VC approaches are stuck.

Witness-category pivot (2026-04-17/18):
13. `sk_witness_category_pivot_handoff_2026-04-17.md` — parent handoff (B-1..B-6).
14. `sk_witness_pivot_findings_log_2026-04-17.md` — session log F-01..F-08.
15. `sk_witness_b{1,2,4}_scoping_2026-04-17.md` — per-category verdicts.
16. `sk_witness_pivot_handoff_2026-04-18.md` — current state, strategic options.

Operational:
17. `zerosorry_roadmap_2026-04-17.md` — sorry inventory. Read the top
    memos (`SESSION_4_VERDICT_2026-04-18`, `SESSION_1_VERDICT_2026-04-18`,
    `AUDIT_VERDICT_2026-04-18`) before the stale 9-sorry table below them.
18. `session1_derisk_log_2026-04-18.md` — Session 1 probe log, coverage
    gap discussion, de-risk verdict.
19. `phase2_3_codex_brief_2026-04-17.md` — Codex brief for the old
    Phases 2–3. **Stale post-refactor** — sorries it targets no longer exist.
20. `sk_phase0_verdict_2026-04-18.md` — Phase 0 paper-check for compact
    structural witness (short cycles / uniform shadow / closed-form peel).
    NO-GO. Two addenda:
    - Shortest cycle in forced graph on NG(C) has length `k = L(C)`
      uniformly (5/5 dumps, n∈{5,6,7,8,9}).
    - Shadow-cloud: forced graph on NG(C) is dense in length-`L(C)`
      cycles — 123 at n=5, ≥5000 at n≥6 (enumeration cap). Firing
      sequences are **unrelated** to `C.movers` (not shift/reverse).
      No individual shadow is canonical; the *set* of all length-`L(C)`
      cycles might be, but that's not a compact Lean witness.
    Upshot for Phase 2: SlabCounting only needs ≥1 closed-forced-subset.
    Given ≥5000 length-`L(C)` cycles per dump at n≥6, `∑ blocked ≤
    (n+1)·L` should have **orders-of-magnitude slack**. If the double-
    counting margin is tight/O(1), that's a red flag — revisit the
    statement. Shadow-cloud count is also a useful empirical sanity-check
    for any auxiliary lemma of the form "NG has many forced-neighbor-in-NG
    configs."

Lean entry points:
- `lean/LeanMn/LowerBound/SK/CloudsTheorem.lean` — 2 SK sorries
  (`sk_nonempty_small_n` at :434, `sk_nonempty_large_n` at :455).
- `lean/LeanMn/LowerBound/SK/SlabCountingRing.lean` — paper-faithful
  §2 port + fiber-budget route. Sessions 2a/2b/2c: MoveEntry, α, β,
  stepMoveEntry, `sum_alpha_eq_L`, `sum_beta_target_le_n_mul_L` all
  zero-sorry. 2026-04-19 late fiber-budget port (§7.7): file grew
  464 → 1178 lines; `exists_unblocked_moveEntry` at :1068 proved
  conditional on `sourceTripleOfStep_injective` (:479). **1 sorry** at
  :479 — narrow step-level injectivity, 0 counter-examples in 1190
  cycles at n=5..9.
- `lean/LeanMn/LowerBound/SK/SinkKernel.lean` — SK definition,
  bridge `sk_nonempty_of_closed_forced_subset` at :156,
  main-theorem hooks `not_converges_of_SK_nonempty` at :281 and
  `not_converges_of_closed_forced_set` at :298.
- `lean/LeanMn/LowerBound/SK/Forcing.lean` — detOf, forcedNeighbors,
  NonGood, hasForcedNeighborIn. `forcedNeighbors` operates on Config,
  never references MoveEntry — so the MoveEntry aggregation is a
  paper-faithful accounting device, not a Lean-machinery artifact.
- `lean/LeanMn/LowerBound/SK/SlabCounting.lean` — abstract sorry-free
  core (`slab_gt_budget`, `exists_underfunded`,
  `exists_closed_nonempty_subset`, `slab_unblocked`). §6(a)-(d)
  token-ring obligations are discharged by SlabCountingRing plus the
  remaining f-injectivity-dependent bridge.
- `lean/LeanMn/LowerBound/SK/GoodCycleBasics.lean` — cycle primitives.
- `lean/LeanMn/LowerBound/SmallN/CloudsLB.lean:42`,
  `lean/LeanMn/LowerBound/LargeN/CloudsLB.lean:34` — the two main-theorem
  call sites; both consume `.Nonempty`.

Twist-calculus package (2026-04-19 late-late, off the ship gate):
- `lean/LeanMn/LowerBound/SK/TwistCalculus.lean` — core algebraic
  layer. `TwistEdge`, `twistCharge := Δi + 2·Δq`, `Generator {R, L, F}`,
  per-generator charge lemmas `twistCharge_R/L/F` (all proved, 0
  sorry), `TwistData`, regime predicates (`isDominant`, `isFold`,
  `isFusion`).
- `lean/LeanMn/LowerBound/SK/DominantNormalForm.lean` —
  `DominantWitness` structure (`kR : Fin 4 → ℕ`, `kL : Fin 2 → ℕ`,
  `balance`, `charge_decomp`) and `DTNF_forward` (sorry — **current
  frontier**). Empirical basis: 748/748 dominant-regime records at
  n = 6, 7, 8.
- `lean/LeanMn/LowerBound/SK/CTCL.lean` — `CTCL_from_witness` +
  `CTCL_dominant` proved (one-line algebra through
  `DominantWitness`); `CTCL_fold` sorry-gated (open research target —
  compensation mechanism for `Σ_F χ = -X` unexplained).
- `lean/LeanMn/LowerBound/SK/FusionDefect.lean` — `fusionDefect`,
  `fusionSignature` (noncomputable, `open Classical`),
  `FusionDefectBound` + `FusionDefectAdditivity` (both sorry,
  quarantined anomaly theory, **NOT on the ship gate**).
- Signature freeze (read before touching Lean):
  `sk_theorem_package_freeze_2026-04-19.md`.
- Slate (theorem-by-theorem statements + empirical bases):
  `sk_twist_calculus_slate_2026-04-19.md`.
- DTNF ⇒ CTCL-dominant one-page derivation:
  `sk_ctcl_from_dtnf_2026-04-19.md`.
- Twist-geometry probe record: `sk_twist_geometry_2026-04-19.md`.
- Board-reset rationale (CTCL promotion, FRL archival):
  `sk_board_reset_apr19.md`, `sk_frl_csp_verdict_2026-04-19.md`.
- Projection-lemma note (cross-cutting design obligation, not yet
  Lean'd): `sk_projection_lemma_note_2026-04-19.md`.

Session-2 and Phase-2.1 docs:
- `sk_phase2_1_papercheck_2026-04-18.md` — Tier 1/2/3 paper check.
  Tier 3 (`Σ(α+β) ≤ (n+1)·L`) survives; max empirical `Σ(α+β)/L = 3.16`
  at n=5..9. Tier 1 (per-config ≤ 2) fails (max match = 3).
- `sk_f_injectivity_lemma_sketch_2026-04-18.md` — f-injectivity
  conjecture, Case A proof, Case B obstruction analysis.
- `sk_case_b_invariant_push_2026-04-18.md` — 60-min scheduling-graph
  push; n=5 circular-dep construction; O1–O6 observations; A1–A5
  invariant attempts.
- `sk_plan_a18.md` — ship plan (8 steps); §2.3 small-n arm options.

Session-2 probes:
- `probe_sk_L_over_Lstar_2026-04-18.py` — L/L* ratio sweep
  (1190/1190 cycles, L/L* = 1.00 uniform at n=5..9).
- `probe_sk_case_b_vacuity_2026-04-18.py` — Case B constructive sweep
  (0/6,372 hits across n=5,6,7).

Case B sub-program (2026-04-18 / 04-19):
- `sk_a1_stuck_closure_observation_2026-04-18.md` — CDO spec; Δ_q,
  fire_count, MOVE-budget data; (U) ∨ (D) candidate invariant; §6
  verdict thresholds.
- `sk_a1_stay_graph_definition_2026-04-18.md` — formal stay-graph
  vertex/edge structure; realization assumption.
- `sk_a1_stay_saturation_probe_2026-04-18.md` — RED: no compact
  descent function at the stay-graph level. First global reframe.
- `sk_a1_closure_debt_probe_2026-04-19.md` — full-sweep CDO probe;
  INCONCLUSIVE (726/726 timed out), memo retracted.
- `sk_a1_closure_debt_subset_probe_2026-04-19.md` — 26-seed subset
  probe; YELLOW-subset (16,908,958 terminals, 0 violators, 4 EXH /
  22 UNB); §4 Bayesian tension; §6 Phase III pre-commit.
- `sk_a1_cdo_abstract_attempt_precommit_2026-04-19.md` — pre-commit
  for abstract attempts; §3 stop conditions (5 outcomes incl. REDUCTION
  added 04-19); §4 verdict table.
- `sk_a1_cdo_abstract_attempt1_2026-04-19.md` — attempt #1 (closure-
  equation algebra). Verdict: ABSTRACT-REDUCTION (closed-cycle CDO ≡
  original A1).
- `sk_a1_cdo_abstract_attempt2_precommit_2026-04-19.md` — attempt #2
  pre-commit; det-centric pivot; three sub-arguments; named conjecture
  for DK letter.
- `sk_a1_cdo_abstract_attempt2_2026-04-19.md` — attempt #2 (det-
  centric). Verdict: ABSTRACT-COUNTEREXAMPLE at det level (`det(q,t):=b+1`
  construction).
- `sk_case_b_invariant_push_2026-04-18.md` — earlier 60-min
  scheduling-graph push; n=5 circular-dep construction; O1–O6.
- `sk_f_injectivity_lemma_sketch_2026-04-18.md` — f-injectivity
  conjecture, Case A 5-line proof, Case B obstruction.
- `probe_sk_case_b_closure_debt_subset_2026-04-19.py` — subset
  probe script.
- `sk_phase0_out/case_b_closure_debt_subset.json` — subset probe output.
- `sk_phase0_out/case_b_closure_debt.json` — full-sweep probe output
  (all timed out).

Fiber-budget reframe + port (2026-04-19 late):
- `sk_fiber_budget_scope_2026-04-19.md` — scoping memo, YELLOW-toward-PASS
  verdict; per-step double count; arithmetic lemma
  `Σm < 2^(n-3) + n − 1`; tightened signature for `exists_unblocked_moveEntry`.
- `project_sk_reframe_2026-04-19.md` (memory) — binding reframe:
  drop `|SK|≥2^(n-1)` / Case B / f-injectivity; two live routes on
  `SlabCountingRing:462` (fiber-budget primary, peel-nonemptiness
  secondary).

---

## 12. Hard constraints in force

From feedback memory (do not violate without Keston green-light):

- **No case splits in Lean proof body** (`feedback_no_case_splits_in_lean.md`).
  B-4's attic route violates this — flagged as a reason B-4 is functionally
  a no-go even though mathematically open.
- **No `native_decide`** (`feedback_no_native_decide.md`). Small-n peel
  construction will tempt it; resist.
- **No axioms without cited publication** (`feedback_no_axioms.md`).
- **No regime dispatch** (wrapper instantiations OK; proof-body branching not).
- **No imports from `attic/`** (`feedback_attic_usage.md`).
- **Sorry count is the only metric** (`feedback_lean_no_infra_loops.md`) —
  each session must produce a measurable sorry drop before any infra work.
- **No ship, no letter, no anything external while sorries remain**
  (`feedback_no_ship_with_sorries.md`). Ship gate = **sorry count 0,
  LB and UB, `lake build` green**. No other threshold. This rules out
  — not just a formal paper — also: DK letters, arXiv preprints,
  emails to outside mathematicians claiming progress, talks/abstracts,
  Slack or blog posts, named-conjecture monographs, "results modulo
  one hypothesis" writeups, or any other external artifact that
  presents the work as closed or closable. There is **no out** via
  reframing the artifact. Named-conjecture ship paths (historical
  §10.4 Phase III Option A / DK letter) are not a fallback and never
  were — they are dead unless Keston issues an **explicit written
  override** overriding this feedback file by name. The correct
  external state while sorries remain is silence.
- **No scratch-file route-switching** (`feedback_combinatorial_quagmire.md`).
- **Push through codex agent stops** (`feedback_codex_push.md`) — RLHF-
  conditioned premature stopping is a known failure mode.

---

## 13. One-paragraph summary for a cold reader (updated 2026-04-19 late-late — campaign at rest)

**Short version for a cold reader.** The SK lower-bound program reduces
to two sorries (`sk_nonempty_small_n`, `sk_nonempty_large_n`) plus a
load-bearing step-injectivity sorry (`sourceTripleOfStep_injective`,
the "A1 wall"). Across five days (2026-04-14 → 2026-04-19), five
structurally-distinct routes were attempted: R1 direct, §3 quotient,
fiber-budget, R4 Read-2 aggregate ansatz, and two CDO abstract
attempts. Every route closed RED. Four of them reduce to or reproduce
the A1 wall; the fifth (R4 Read-2) fails on independent arithmetic
at n ≥ 8 binary-dominated (`T > (n−3)/n · L · Σμ` already observed).
The obstruction is sharply localized to the det × cycle-structure
interaction at a Case B seed, with no slack. Campaign is now at rest:
sorry count **4**, `lake build` green, diagnostic preserved in
`sk_campaign_state_2026-04-19.md`. **Under the §0 Hard Constraint,
nothing external ships — no paper, letter, preprint, DK letter, talk,
or named-conjecture artifact — until sorry count hits 0.** The correct
external state is silence. Resumption is gated on a genuinely new idea
from outside this arc, attacking the `(C, μ) × det` interaction
directly, with a pre-commit shape distinct from routes 1–5. Absent
that, stay at rest.

---

## 13a. Historical technical summary (retained for context)


The sink-kernel `SK(C)` of the determined bad graph on `NG(C) = Config \ C`
is a scalar probe that replaces a dozen prior obstruction mechanisms:
`SK(C) ≠ ∅` for every fair cycle at sub-`M_n` `ms` ⟹ no valid system
exists. The 2026-04-18 audit of `SinkKernel.lean` confirmed the
main-theorem hooks consume only `(SK gc).Nonempty`, not any cardinality
floor — so the strong `|SK| ≥ 2^(n-1)` conjecture (empirically true across
~150K cycles at n=5..10) is not load-bearing. `CloudsTheorem.lean` was
refactored to target nonemptiness directly, collapsing the prior 9-sorry
Lemma A/B/C decomposition to 2 sorries. Session 4 landed the bridge
`sk_nonempty_of_closed_forced_subset`; Sessions 2a/2b/2c ported the
paper-faithful `SlabCountingRing` (MoveEntry, α, β, `sum_alpha_eq_L`,
`sum_beta_target_le_n_mul_L`) all zero-sorry. The **Case B sub-program**
(2026-04-18/19, §7.6) ran the structured push to close the old
obstruction `exists_unblocked_moveEntry` via MoveEntry-indexed
f-injectivity: stay-saturation invariant exhausted RED; CDO subset probe
YELLOW (16.9 M terminals, 0 violators); attempt #1 → ABSTRACT-REDUCTION
(closed-cycle CDO ≡ original A1); attempt #2 → ABSTRACT-COUNTEREXAMPLE at
det level. Combined: f-injectivity Case B lives *exactly* in the det⨯cycle
interaction with no slack, formally equivalent in hardness to A1. The
**2026-04-19 late fiber-budget reframe** (§7.7, `project_sk_reframe_2026-04-19.md`)
read this as evidence the bottleneck was MoveEntry parametrization, not
cycle-level math, and attacked `SlabCountingRing.lean:462` at a different
granularity: per-step, not per-MoveEntry. Per-position double count gives
`Σ_k β(target_k) ≤ L · Σ_p (m_p − 1)`, which with `α(step_k) = 1` and
`slabSize ≥ 2^(n-3)` reduces to the arithmetic lemma
`Σm < 2^(n-3) + n − 1` (proved from `∏(2+d_i) ≥ 2^n + 2^(n-1)·σ`).
`exists_unblocked_moveEntry` at `SlabCountingRing.lean:1068` is now
proved conditional on a single narrow step-level injectivity claim
`sourceTripleOfStep_injective` at `:479` (empirically tight: 0
counter-examples in 1190 cycles at n=5..9). The wall **moved** from the
compound MoveEntry-level obstruction (≡ A1) to a single-cycle step-level
claim. **Late-late 2026-04-19 scoping of both R1 and R4 routes** (§7.8):
R1 (direct proof of sorry #3 via sync-cascade invariant) verdict
**RED** — the cascade-break shape reproduces the A1 wall at step
granularity (`entryConflict_impossible` needs matching triples, break
guarantees non-matching via farther-neighbor coordinate in Δ, `sys.f`
absorbs the collision). R4 (peel-direct, orphan sorry #3) verdict
**YELLOW** — obligation reduces to a single uniform counting inequality
(edge-sink margin ≥ 1 on the N_1 tube) empirically overshot 6× across
656/656 records and disjoint from A1 / sorry #3. Net sorry count
unchanged (still **4** outside `attic/`: 2 SK nonemptiness + 1
SlabCountingRing injectivity + 1 UB). `lake build` green. Binding next
move: cheap Python probe to test whether B2' (edge-sink margin) has a
uniform analytical lower bound; PASS ⟹ commit Phase A Lean infra
(`hammingDist`, `N_1`, edge-counting) and port R4, which closes sorries
#1 and #2 simultaneously (sorry #3 becomes orphaned — under the §0
ship-gate note it must then either close via the orbit-level argument
or `SlabCountingRing.lean` moves to `attic/`, since no sorry may remain
in the main build at ship); FAIL ⟹ find a third structurally-distinct
route. Phase III / DK-letter is **not** a viable fallback — ship gate is
sorry count 0, not a publishable named-conjecture artifact. If the
program lands, it resolves Knuth 1985 (`lim M_n^{1/n} = 3`) and settles
ARG's binary-count conjecture as a corollary (§0).
