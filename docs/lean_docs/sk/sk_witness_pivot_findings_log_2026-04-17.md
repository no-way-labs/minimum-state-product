# SK Witness Category Pivot — Session Findings Log

**Session window:** 2026-04-17 → 2026-04-18
**Frame:** Continuation after the Hamming-≤2 c\*-witness program closed
by 6 no-gos (Exp 20–25, `sk_2n2_residue_2026-04-17.md`). Parent
handoff: `sk_witness_category_pivot_handoff_2026-04-17.md`.

This is a running log of findings across the witness-category pivot
session. Each entry is dated, scoped to a single discovery/decision,
and cross-references the doc and memory entry where the analytical
content lives.

---

## F-01 (2026-04-17) — B-1 viable architecturally; d_n does not transfer

**Object scoped:** `S_k(gc) := peel(N_k(gc) ∩ VC-NG)` for k=3 uniform.

**Finding:** B-1 is a viable Clouds-routable category. Routes via
`not_converges_of_closed_forced_set` (SinkKernel.lean:219) — does
**not** need `(SK gc).Nonempty`; the two CloudsTheorem.lean sorries
(421, 431) can be replaced by `S_3(gc).Nonempty` directly.

**Why d_n doesn't transfer:** d_n at depth 15 from c\*, outside
N_3(gc). Quotient/potential obstructions require sink/chain shape;
T_3 has cycles (empirical L-cycle in 641/641 records).

**Why B-1 substrate is interesting:** ~2^n vs poly(n) for T(c\*),
empirical fringe is small minority, margin ≥ 6 across all records vs
≤1 for c\*-cascade.

**Sub-obligations:** (1) Hamming predicate, (2) peel wrapper,
(3) routing, (4) cycle-in-T_3 theorem. (1)–(3) mechanical (~130
lines); (4) is real analytical work.

**Doc:** `sk_witness_b1_scoping_2026-04-17.md`
**Memory:** `project_sk_witness_b1_2026-04-17.md`

---

## F-02 (2026-04-17) — B-1 sub-obligation 4 splits into R-A and R-B; both open

**Decomposition of cycle-in-T_3:**
- **R-A** (constructive L-cycle): build the L-step companion with
  anchor map `i ↦ (q_i, v_i)`, dominant-pair characterization at n=7.
- **R-B** (existential via fringe upper bound): show
  `|D(T_k)| < |T_k|` analytically; existence of cycle by counting.

**Finding:** Both routes open. R-A re-creates the σ_w reorder
obstruction from Exp 20 in a different substrate (anchor-map
formula instead of word permutation). R-B is structurally cleaner
for Lean but premise unverified, no prior probes.

**Recommendation issued:** Do NOT start Lean port yet —
sub-obligations 1–3 are infra-loop trap without sub-obligation 4
(per `feedback_lean_no_infra_loops.md`). Spawn paper-style R-B
counting effort first.

**Doc:** `sk_witness_b1_anchor_map_2026-04-17.md`

---

## F-03 (2026-04-17) — R-B fringe bound reduces to R-A's anchor formula

**Sharpening of F-02:** Worked through R-B sketch on T_1(gc) substrate
(strongest case). Easy case (mover outside anchor window) replicates
cycle move; hard case (mover in {q-1, q, q+1}) may exit T_1.

**Finding:** Bounding `|D(T_1)|` from above requires showing the
"good companion sub-cycle" (mover-outside-anchor for L consecutive
steps) always exists. **This is exactly the L-cycle anchor map of R-A.**

**Consequence:** R-A and R-B share the same combinatorial core; they
differ only in whether the cycle is exhibited explicitly. Neither
buys analytical relief over the survivor theorem.

**Doc:** `sk_witness_b1_verdict_2026-04-17.md` §1.4

---

## F-04 (2026-04-17) — B-1 closed: theorem-shaped no-go

**Verdict statement:**

> The B-1 category — `peel(N_k(gc) ∩ VC-NG)` for any fixed `k`
> uniform in `n` — admits a uniform-in-`n` Lean-portable proof of
> Sub-obligation 4 (cycle existence in `T_k`) only if either
> (i) a uniform-in-`n` formula for the L-cycle companion anchor
> map `i ↦ (q_i, v_i)` is established, or
> (ii) an analytical fringe upper bound `|D(T_k)| < |T_k|` is
> established. Both reduce to the same combinatorial core (R-A's
> anchor formula); the substrate change `T_1 → T_3` widens the
> margin but does not eliminate the obligation.

**B-3 (graph-theoretic SCC) folded in:** SCC route shares same
analytical core as R-B; not separately scoped.

**Doc:** `sk_witness_b1_verdict_2026-04-17.md`

---

## F-05 (2026-04-17) — Winding invariants live in main tree, but no Clouds plug

**Audit of attic winding files:**
- `attic/.../Obstruction/NonZeroWinding.lean:34`: central sorry
  `nonZeroWinding_obstruction` — Phase 4 TODO, never closed.
- `attic/.../Proof/OddWinding.lean:184`: by_cases on
  `threeConsecutiveBinary` — explicit case split, forbidden by
  `feedback_no_case_splits_in_lean.md`.
- `attic/.../Proof/Sweep.lean:6-7`: dispatches D1/D2 on
  consecutive/non-consecutive binary.

**Live winding infrastructure:** `lean/LeanMn/LowerBound/CycleTypes.lean`
has `gc.zeroWinding`, `gc.isOddWinding`, `gc.isSweep`,
`gc.uniformDirection`, `totalDisplacement`, `edgeNetFlow` and basic
edge-flow lemmas (lines 310, 339, 349, 772–933, 1034–1066). Only live
consumer is `EntryConflict/PairedCrossing.lean` — SK directory uses
**none** of it.

**Finding:** Winding infrastructure survived the SK pivot at the
data level but plugs nothing. The closing analytical work is the
central sorry, which has never been done.

**Doc:** `sk_witness_b4_scoping_2026-04-17.md` §1, §4

---

## F-06 (2026-04-17) — B-4 doesn't fit witness-category frame

**Theorem shape of winding obstruction:**
`(converges sys gc) ∧ (¬gc.zeroWinding) → False`

**Finding:** Produces no Finset. Short-circuits `¬converges` upstream
of CloudsTheorem.lean:421/431; does NOT discharge those sorries.

**Consequence:** B-4 is a parallel non-SK obstruction track, not a
witness category in parent handoff's sense
(handoff §"What 'witness object category' means" requires a Finset
recipe).

**Doc:** `sk_witness_b4_scoping_2026-04-17.md` §3

---

## F-07 (2026-04-17) — B-4 has best obstruction profile but hits independent open problems

**Obstruction transfer table for B-4:**
| Obstruction | Transfers? | Why |
|---|---|---|
| d_n sink (Exp 23) | No | Winding is global, not per-config |
| σ_w reorder (Exp 20) | Partially | Only via Sweep sub-case construction |
| Survivor theorem (Exp 21) | No | Different shape (no counting) |
| Quotient bound (Exp 22) | Untested | No prior analysis |
| Predecessor fork (Exp 24) | No | No backward-orbit dependence |
| Hamming-2 collapse (Exp 25) | No | Different witness frame |

**Finding:** Cleanest profile of any category scoped (1.5/6
transfer). But blocked by **two independent open problems**:
(i) `nonZeroWinding_obstruction` central sorry (never closed),
(ii) 3CB open problem at n≥9 (`project_3cb_open_problem.md`).

**Verdict:** B-4 is **open-on-different-axis** — not a no-go like
B-1, but not a viable drop-in either. If either independent open
problem closes, B-4 becomes immediately viable.

**Doc:** `sk_witness_b4_scoping_2026-04-17.md` §5, §6
**Memory:** `project_sk_witness_b4_2026-04-17.md`

---

## F-08 (2026-04-18) — B-2 (detOf algebraic invariants) closed by trichotomy

**Trichotomy claim:** Any algebraic-invariant route producing a
forced-closed NonGood Finset falls into one of three sub-categories,
each hitting a known obstruction:

> (i) **Counting / cardinality** — already realized as
> `SlabCounting.lean`; Step 4 edge→cycle gap (Exp 21).
>
> (ii) **Constructive orbit identification** — per-position dynamics
> lifted to configuration cycles requires anchor map; reduces to
> R-A core, recreates σ_w reorder (Exp 20).
>
> (iii) **Semigroup / global action** — equivalent to forced-graph
> action = survivor theorem; d_n sink obstruction (Exp 23) lives
> natively.

**Sketch of exhaustiveness:** `detOf gc` is a finite partial function
`Fin n × Fin m³ ⇀ Fin m`; its only mathematical structure is data
(counting), orbital action (construction), or generated semigroup
(global invariants). No fourth route.

**SK is the maximal Finset (sharpening):** By SinkKernel.lean:75-78,
`SK gc` is **already** the largest NonGood Finset closed under
`forcedNeighbors (detOf gc)`. Any B-2 witness ⊆ SK gc, so producing
one is **equivalent to** proving `(SK gc).Nonempty` — exactly the
two CloudsTheorem.lean sorries.

**Obstruction profile:** All three of (Exp 20, 21, 23) transfer.
**Worst profile of any category scoped** — abstraction is shallow.

**Doc:** `sk_witness_b2_scoping_2026-04-17.md`
**Memory:** `project_sk_witness_b2_2026-04-17.md`

---

## Net status table after this session

| Category | Status | Date | Doc |
|---|---|---|---|
| B-1: peel(N_k ∩ VC-NG) | No-go (R-A/R-B share core) | 2026-04-17 | `sk_witness_b1_*.md` |
| B-2: detOf algebraic invariants | No-go (trichotomy) | 2026-04-18 | `sk_witness_b2_scoping_2026-04-17.md` |
| B-3: graph-theoretic SCC | No-go (folded into B-1) | 2026-04-17 | (in B-1 verdict §1.4) |
| B-4: topological winding | Open-on-different-axis | 2026-04-17 | `sk_witness_b4_scoping_2026-04-17.md` |
| B-5: ergodic / measure | Unscoped | — | (none) |
| B-6: pure combinatorial identity | Unscoped | — | (none) |

**3/4 scoped → no-go. 1/4 scoped → open on independent axis.
2/6 unscoped (lowest priority per parent handoff).**

## Strategic options after F-01..F-08

Per parent handoff §"What a success looks like", a full no-go for
B-1..B-6 triggers project verdict:

> the survivor theorem is irreducible across all reasonable witness
> categories, and the strategy pivots to (A) accept as open research
> or (C) weaken the numeric threshold.

**Two more scoping passes** (B-5, B-6) would formalize this verdict.
Both are flagged "lowest priority"/"speculative" with no prior
footprint. The trichotomy structure of B-2 suggests B-5/B-6 will
also yield trichotomy-style closures cheaply.

**Decision pending Keston:**
- **Option 1**: Complete B-5, B-6 scoping (~one doc each).
- **Option 2**: Accept the verdict on B-1, B-2, B-3 strength + B-4
  reduction to independent open problems.
- **Option 3**: Pivot to (C) weaken the numeric threshold.
- **Option 4**: Pivot to (A) accept as open research, freeze the
  campaign.

## Files created this session

In `lean/docs/sk/`:
- `sk_witness_b1_scoping_2026-04-17.md`
- `sk_witness_b1_anchor_map_2026-04-17.md`
- `sk_witness_b1_verdict_2026-04-17.md`
- `sk_witness_b4_scoping_2026-04-17.md`
- `sk_witness_b2_scoping_2026-04-17.md`
- `sk_witness_pivot_findings_log_2026-04-17.md` (this doc)

In memory:
- `project_sk_witness_b1_2026-04-17.md`
- `project_sk_witness_b4_2026-04-17.md`
- `project_sk_witness_b2_2026-04-17.md`
- updates to `MEMORY.md` index

## Discipline notes

Throughout the session:
- No empirical probes spawned (per parent handoff constraint).
- No Lean code written (per `feedback_lean_no_infra_loops.md`,
  sub-obligations 1–3 of B-1 explicitly deferred).
- No attic imports (per `feedback_attic_usage.md`); all attic
  references are read-only with paths and line numbers.
- No case-split proofs proposed (per `feedback_no_case_splits_in_lean.md`);
  flagged the attic OddWinding case-split as a B-4 obstruction.
- No `native_decide` use (per `feedback_no_native_decide.md`).
- All deliverables in the form requested by parent handoff:
  candidate uniform theorem statement OR theorem-shaped no-go.
