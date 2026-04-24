# Paper 2 Lower Bound — All Paths Tried

**Scope.** Complete survey of every LB route this project has attempted, from
the pre-SK four-mechanism case-split architecture through the SK Clouds
program, the five-route A1 campaign, the transport-lift / twist-calculus
arc, the R4 peel-direct revival, and the SK Morse–Hamming topological arc.
Plus: where the two open frontiers currently live.

**Headline claim (the target).** `M_n ≥ 4·3^(n-2)` for `n ≥ 9` (and
`32·3^(n-4)` for `n ∈ {5..8}`). Combined with Dijkstra's classical `3^n` UB,
this resolves **both** of Knuth's 1985 asymptotic questions from
STAN-CS-85-1055 (`limsup M_n^{1/n} < 3`? `liminf M_n^{1/n} > 2`?) — it forces
`lim M_n^{1/n} = 3`. It also implies ARG's 1985 binary-count conjecture as a
corollary (at `{2,3}` multisets, `k ≤ 2` binary processors).

**Current Lean state (as of 2026-05-17 end of day).** Sorry count = 4 LB +
1 UB (off-scope). `lake build` green. LB campaign is **at paper-writing
trigger**: Wave 5 terminal queue (§10.7) closed without a proof-shaped
result; the Wave 5 addendum (2026-05-17) closed the two remaining
gaps (proper P7 Čech H¹ and P1.5 analytical attempt) — both RED — and
Wave 6 (2026-05-17, §10.8) ran four addendum-identified leads:
T1 V_tube-refinement RED, T2 T+sided-only-circulation empirical
GREEN / analytical RED-budget, T3 Conley-index RED (scale-normalized),
T4 non-standard-sheaf three-candidates RED. Paper-writing trigger
remains active. Per Wave 6 §5.3 genuine-exhaustion and addendum §4.1
anti-drift discipline, paper writing begins as conjecture + evidence
+ comprehensive catalog. The Wave 2
threshold fix (2026-04-21, §10.2) split the unprovable
`peelTube_nonempty` into two piecewise obligations `peelTube_nonempty_small_n`
(n ∈ {5..8} at sharp `32·3^(n-4)`) and `peelTube_nonempty_large_n`
(n ≥ 9 at sharp `4·3^(n-2)`), net +1 sorry. The topological revival arc
(Waves 1–5 + addendum + Wave 6, §10) retired 2026-05-17 with the
circulation route validated-as-detector but dead-as-LB-mechanism, and
T2's stronger restricted-theorem empirical observation paper-integrated
with a specific named structural obstruction (q-tube forward-walk
hole at position-q firing steps).

This document is intended to be self-contained with
`docs/p2.md` (problem statement, Dijkstra's three
solutions, Knuth's open problem, 1985-seminar partial results, post-1985
literature) **and** `docs/witness_primer.md` (the
record-holding constructions: small-n `M_n = 32·3^(n-4)` witnesses, the
CLB ternary-strip witness at `n ≥ 9` with `ms = (2,3,…,3,2)` and product
`4·3^(n-2)`, the phase transition at `n = 9`, ARG's binary-count
corollary). A reader with p2 + WP has the *problem* and the *target*.
This doc gives the Lean-level *obligation*, the dead routes, and the
live frontiers.

Section §0 gives the Lean glossary, worked example, and sharp forms of
the two open frontiers; §1–§7 catalog the dead routes; §8 re-states the
two frontiers; §9 gives current posture and binding constraints; §10
catalogs the Waves 1–5 + addendum topological revival arc (2026-04-21
→ 2026-05-17), retired as detector-only with terminal probe queue
closed at Wave 5 and the two remaining gaps (proper P7, P1.5 proof
attempt) addressed in the 2026-05-17 addendum.

---

## 0. Preliminaries — objects, the UB side, a worked record, and the sharp frontier statements

### 0.1 Core objects (glossary)

All definitions from `LeanMn/LowerBound/{GoodCycleBasics, SK/Forcing,
SK/SinkKernel, SK/HammingTube, SK/SlabCountingRing}.lean`. Notation:
`n` = ring size, `m : Fin n → ℕ≥2` = state counts per processor,
`Config = (i : Fin n) → Fin (m i)`, `left i = i-1`, `right i = i+1`
(mod n), state product `∏ m = ∏_i m(i)`.

**System and rule.** A `System` is a ring spec `(n, m)` plus a
transition function `sys.f : (i, l, s, r) → Fin (m i)`. Processor `i` is
**privileged** at config `c` iff `sys.f i c(i-1) c(i) c(i+1) ≠ c(i)`. A
**good cycle** `gc` is a list `configs = [c_0, c_1, …, c_{L-1}]` of
distinct configs with:
- `unique_privileged`: at every `c_k` exactly one processor is privileged
  (call it `moverAt k`),
- `closed`: `c_{k+1}` = apply-move of `c_k` at `moverAt k` (mod L),
- `distinct`: all `c_k` pairwise distinct,
- `fair`: every processor fires at least once across the cycle.

`L := gc.configs.length` is the cycle length. `NonGood gc c` means `c ∉ gc.configs`.

**The determined dictionary `detOf gc`.** Reading the cycle's firings as
a partial rule: for each key `(i, l, s, r)`, find the first step `k`
where `(c_k(left i), c_k(i), c_k(right i)) = (l, s, r)`; output
`c_{k+1}(i)`. If `i = moverAt k` this is a **move** (different from `s`);
if `i ≠ moverAt k` it's a **stay** (equal to `s`). The determined
dictionary forces every valid transition function extending the cycle.

**Forced graph.** `forcedNeighbors D c` = the list of configs reachable
from `c` by firing exactly one processor whose `(i, l, s, r)` has a
**move** entry in `D`. The **forced graph on `S`** has vertices `S` and
edges `c → c'` whenever `c' ∈ forcedNeighbors (detOf gc) c ∩ S`.

**Sink-kernel `SK(gc)`.** Start with the Finset of all non-good configs;
iteratively `removeOnce` = discard every config with **no** forced
neighbor in the remaining set (a *sink*). Iterate to fixpoint. The
fixpoint is `SK(gc)`. Two properties:
- `SK_subset_nonGood`: `SK ⊆ {c : NonGood c}`.
- `SK_closed`: every `c ∈ SK` has some forced neighbor `c' ∈ SK`.

**T1 soundness (`SinkKernel.not_converges_of_SK_nonempty`).**
`SK(gc).Nonempty ⟹ ¬ converges sys`. One non-good config with a
forced successor chain that stays non-good suffices to refute
convergence.

**Hamming-1 tube.** `hammingDist c c' = #{i : c(i) ≠ c'(i)}`. `N_1Of c`
= Hamming-1 ball around `c`. `N_1Tube gc` = ⋃ over cycle configs.
`valueSetTube gc p` = {values `c_k(p)` for `k ∈ Fin L`}. `VC gc c` = `∀ p,
c(p) ∈ valueSetTube gc p` (value-consistent). `VC_NG = VC ∩ NonGood`.
`T_N1 := N_1VC_NG = N_1Tube ∩ VC_NG`. `peelTube` = `iterateRemove (detOf
gc) T_N1 ∞` — same sink-peeling operation as `SK`, but starting from
`T_N1` instead of all non-good.

**Step triples.** For `k ∈ Fin L`:
- `configTripleAt c i = (c(left i), c(i), c(right i))`,
- `sourceTripleOfStep gc k = ⟨moverAt k, configTripleAt c_k (moverAt k)⟩`
  — the dependent-pair `(i, (l, s, r))`, of type
  `Σ i, Fin (m (left i)) × Fin (m i) × Fin (m (right i))`,
- `targetTripleOfStep gc k` — same position, but middle coord replaced
  by the forced output `sys.f i l s r`.

**Move entries and slab counts.** A `MoveEntry` is a record
`(i, l, s, r, v)` with `detOf gc i l s r = some v` and `v ≠ s` (it's a
move). For each entry:
- `α(entry) := #{c ∈ gc.configs : configTripleAt c i = (l, s, r)}`
  (cycle configs matching the **source** triple),
- `β(entry) := #{c ∈ gc.configs : configTripleAt c i = (l, v, r)}`
  (cycle configs matching the **target** triple),
- `slabSize(entry) := ∏_{j ∉ {i-1, i, i+1}} m(j) ≥ 2^(n-3)` (products
  of moduli at positions outside the entry's 3-local neighborhood),
- `blocked(entry) := α + β`; the entry is **blocked** iff
  `blocked ≥ slabSize`.

**Two aggregate budgets** (SlabCountingRing, Sessions 2a/2b/2c, all
sorry-free):
- `Σ α = L` (each cycle config uniquely realizes one source triple,
  namely its own firing step),
- `Σ β ≤ n · L` (each cycle config can be the target triple at most at
  each of `n` positions).

**Case B seed.** In the CDO / A1' analysis a *seed* is a tuple
`(p, l, r, v, s_1, s_2)` where `p` is a position, `(l, s, r)` is a
source triple firing to `v`, and `s_1 ≠ s_2` are two distinct values of
`p`'s state set. A **Case B** seed is one where
`targetTripleOfStep_injective` could fail: two steps `k ≠ k'` with
`moverAt k = moverAt k' = p`, shared outer `(l, r)`, and post-move
middles `v = sys.f p l s_1 r = sys.f p l s_2 r` — i.e. two distinct
source middles collapse to the same target triple under `sys.f`. A
Case-B seed is *consistent* iff both candidate firings satisfy all
single-priv / closure / distinctness constraints a good cycle imposes
locally.

**`Move_q(C)` and the MOVE budget.** For a closed single-priv cycle
`C`, `Move_q(C) := {k : moverAt k = q}` (the steps where `q` fires). In
CDO language, `Ψ_q := Move_budget_q` is the structural count such that
`Ψ_q = 0 ⟺ Move_q(C) = ∅ ⟺ q never fires in `C`` (violating fairness
unless `q` is a valid silent processor).

### 0.2 Sub-threshold in the Lean proof

WP §3–§5 gives the full UB story; for this doc we only need the
**sub-threshold hypothesis** in the two SK theorems:

- **Small-n arm (`5 ≤ n ≤ 8`).** `sk_nonempty_small_n` takes
  `stateProduct sys.rs < 32 * 3 ^ (sys.rs.n - 4)` — the sharp small-n
  threshold from WP §3.1. Internally widens to
  `< 4 * 3 ^ (n - 2)` via `32 ≤ 4·3^2`.
- **Large-n arm (`n ≥ 9`).** `sk_nonempty_large_n` takes
  `stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)` — the CLB threshold
  from WP §5.
- **The LB obligation** (from WP §6.1) is: every `(ms, f_0, …, f_{n-1})`
  with sub-threshold `∏ m_i` fails one of Dijkstra's five properties.
  Our route: show `converges sys = False` via
  `SK(gc).Nonempty → ¬ converges sys`.

The LB in Lean thus comes down to: **assume a `GoodCycle gc` exists at
sub-threshold; derive `(SK gc).Nonempty`**; the rest (T1 soundness →
`¬ converges`) is already proved.

### 0.3 Worked example at n = 5, ms = (2, 2, 2, 2, 3)

Product = 48 < 96 = `32·3^(5-4)`, so this is sub-threshold. Pick a
fair simple cycle `C` of length `L = 10` (one of three exist per probe
`probe_sk_hamming1_empty_discriminator_2026-04-17.py`). We observe:

| Quantity | Value | Source |
|---|---|---|
| `|Config|` (state space) | `48` | `2^4 · 3 = 48` |
| `L` (cycle length) | `10` | cycle is `GoodCycle` shape |
| `|NonGood|` | `38` | `48 − 10` |
| `|SK|` | ≥ `20` | probe `sk_phase0_out/`, agrees with `|SK|` `(n, L)`-invariance |
| `|T_N1|` | ~30 | `N_1Tube ∩ VC_NG`, empirical |
| `|peelTube|` | ≥ 1 (nonempty) | E13 + E16: peel 100%, min SCC size 18 |
| # source triples in the cycle | `10` (all distinct) | A1' empirically 0 violators |

The **forced graph on `T_N1`** has one non-trivial SCC of size ≥ 18
(unique per record). The LB ship reduces to:

> There exists `c ∈ T_N1` with a forced successor `c' ∈ T_N1` (and
> by iteration, a cycle) — i.e. `peelTube` is nonempty.

Or equivalently via slab counting:

> Not every `MoveEntry` is blocked; some source triple's `α + β < 2^(n-3)`.

Under **T1 soundness** (`not_converges_of_SK_nonempty`), either closed
form refutes `converges sys`.

The empirical signature at this record:
- `sourceTripleOfStep : Fin 10 → SourceTriple` is injective (10 distinct
  triples — checked directly).
- Every non-cycle config at Hamming distance 1 is value-consistent
  (since `(2,2,2,2,3)` has few values, VC ≈ all-of-N_1 at n=5).
- The forced graph on `T_N1` has ~30 vertices, ~40 edges, one SCC of
  size 18 (BIG-SCC), and the peel equals the BIG-SCC ∪ its 1-hop
  feeders.

This is the structure every sub-threshold record shares. Any brainstormed
route must exploit either the A1-injectivity pattern **or** the
peel/SCC structure — ideally both.

### 0.4 Sharp frontier statements (fully unfolded)

#### Frontier 1 — `peelTube_nonempty_{small,large}_n`

**Lean file.** `LeanMn/LowerBound/SK/HammingTube.lean:169, 190`.

```
theorem peelTube_nonempty_small_n (gc : GoodCycle sys)
    (hn_lo : 5 ≤ sys.rs.n) (hn_hi : sys.rs.n ≤ 8)
    (hsub : stateProduct sys.rs < 32 * 3 ^ (sys.rs.n - 4)) :
    (peelTube gc).Nonempty

theorem peelTube_nonempty_large_n (gc : GoodCycle sys)
    (hn : 9 ≤ sys.rs.n)
    (hsub : stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)) :
    (peelTube gc).Nonempty
```

**Shape fix history.** Before Wave 2 (2026-04-21, §10), this was stated
as a single unified theorem with hypothesis `stateProduct sys.rs <
4 * 3 ^ (sys.rs.n - 2)`. That form was **refuted by the small-n witnesses
`witness_n5..8`** at products `{96, 288, 864, 2592}` — each valid, so
`SK(C) = ∅` and `peelTube(C) = ∅`, contradicting the claim. The old
form survived only because `sk_nonempty_small_n` internally widened
its hypothesis from `< 32·3^(n-4)` to `< 4·3^(n-2)` — an illegal
move (widening the hypothesis of a target lemma, not the
conclusion). Wave 2 Priority 0 landed the split above. Sorry delta:
+1 in `HammingTube.lean`.

Unfolded (same content for both arms): **there exists a config
`c₀ : Config sys.rs` such that**

1. `c₀ ∉ gc.configs` (non-good),
2. `∃ c ∈ gc.configs` with `hammingDist c c₀ = 1` (inside the 1-tube),
3. `∀ p : Fin n, c₀(p) ∈ valueSetTube gc p` (value-consistent),
4. and `c₀` survives **every** iteration of sink-removal on
   `N_1Tube ∩ VC_NG`. Equivalently: there is an infinite forward
   trajectory in `N_1Tube ∩ VC_NG` under `forcedNeighbors (detOf gc)`,
   i.e. a **directed cycle in the forced graph on `T_N1`**.

**Empirical form (E13).**
`|E_{N_1}| − (|T_{N_1}| − |sinks_{N_1}|) ≥ 1` uniformly — the forced
graph has more edges than vertices minus sinks, so pigeonhole forces a
cycle. The margin overshoots 8× in 164 probed records. Rigorously this
is not enough (DAGs can have `|E| ≥ |V|` without cycles, e.g. via
degree-2 forks), which is why the Lean route has to be structural,
not arithmetic.

**Consumer wiring.** Closes `sk_nonempty_small_n` (CloudsTheorem.lean:418)
via `sk_nonempty_via_tube_small_n` and `sk_nonempty_large_n` (:445) via
`sk_nonempty_via_tube_large_n`:

```
sk_nonempty_via_tube_{small,large}_n :
  peelTube_nonempty_{small,large}_n hypotheses → (SK gc).Nonempty
```

And `SK gc .Nonempty → ¬ converges sys` via T1.

#### Frontier 2 — `sourceTripleOfStep_injective` / `targetTripleOfStep_injective`

**Lean file.** `LeanMn/LowerBound/SK/SlabCountingRing.lean:490–501`.

```
private theorem targetTripleOfStep_injective (gc : GoodCycle sys) :
    Function.Injective (targetTripleOfStep gc)

private theorem sourceTripleOfStep_injective (gc : GoodCycle sys) :
    Function.Injective (sourceTripleOfStep gc)
  -- already proved FROM targetTripleOfStep_injective via sys.f congruence.
```

Unfolded: **for every pair of distinct steps `k ≠ k'` in `Fin L`,**

```
targetTripleOfStep gc k ≠ targetTripleOfStep gc k'
```

i.e. the post-move dependent triple `⟨moverAt k, (l_k, v_k, r_k)⟩`
— where `v_k = sys.f (moverAt k) l_k s_k r_k` — differs from the
corresponding triple at step `k'`.

**Equivalent (named-conjecture) form.** No closed simple single-priv
cycle with seed-consistency at a Case B seed `(p, l, r, v, s_1, s_2)`
satisfies `Move_q(C) ≠ ∅` for every `q ≠ p`. I.e. in every such cycle,
some `q ≠ p` never fires — violating fairness. A1' failure would
manifest as two cycle steps `k, k'` with the same mover `p = moverAt k
= moverAt k'`, the same outer `(l, r)`, distinct middles `s_1 = s_k, s_2
= s_{k'}`, but equal post-move middle `v_k = v_{k'} = v`. That degenerate
double-fire is ruled out structurally by fairness — the conjecture
claims.

**Consumer wiring.** Load-bearing for the **fiber-budget** closure of
the SlabCounting ring port: with A1' in hand, the double-count
`Σ β ≤ n·L` combines with `Σ α = L` and `slabSize ≥ 2^(n-3)` to force
`Σ m_p ≥ 2^(n-3) + n − 1`, which contradicts sub-threshold at `n ≥ 8`.

### 0.5 Why the two routes are independent in Lean but both converge empirically

Peel-direct operates on the **forced graph on the Hamming-1 tube**: it
ignores the algebraic structure of `sys.f` at Case-B seeds and just
asks whether any single perturbation of a cycle config enters an
absorbing subgraph of non-good forced successors.

A1' operates on the **map `Fin L → SourceTriple`** (equivalently, on
the det dictionary's structure around double-fires): it ignores the
Hamming-1 geometry and asks whether the cycle's own firing steps can
collapse in the triple space.

Both routes end at `(SK gc).Nonempty` (Frontier 1 via
`sk_nonempty_of_peelTube`; Frontier 2 via the fiber-budget → not-all-
blocked → forced-non-good-successor chain). Both are true empirically
(6289 and 1898 records respectively, 0 violators). Each is
structurally orthogonal to the other's obstruction mode: peel-direct
fails because *walks can't simulate teleological cycle-selection*; A1'
fails because *the obstruction lives in the `(C, μ) × det`
interaction, not in either side alone*.

### 0.6 Coverage inversion (one load-bearing diagnostic for topological routes)

For any dynamics-complex invariant `I(forced-graph-on-NG)`, the signal
has been **inverted** across all ms-sensitive probes because
`|det(C)| / T_total ≈ L / (n · ∏ m)` decreases as product grows. So
sub-threshold records (small ∏ m) get *dense* forced graphs (many
edges per vertex, few sinks), at-threshold records get *sparse*
forced graphs — pushing any monotone-in-coverage invariant in the
**opposite** direction a LB needs. Future topological attempts must
first handle coverage scaling (subtract it, quotient it, or attack an
invariant that is provably coverage-insensitive).

---

## 1. Pre-SK era — the four-mechanism case-split architecture

**Lean location.** Atticized to
`lean/attic/pre_sk_2026-04-14/` on 2026-04-14 (see
[lb_sk_restart_plan_2026-04-14.md](lb_sk_restart_plan_2026-04-14.md)).
`git mv` preserved, files do not build. Includes:
`lower_bound/{ArcConfinement, IntervalDisplacement, MNU, Theorem}.lean`,
`lower_bound/EntryConflict/` (8 files), `lower_bound/Obstruction/` (5),
`lower_bound/Proof/` (9), `lower_bound/Shadow/` (2).

### 1.1 The proof plan (per [lb_complete_proof.md](lb_complete_proof.md))

Case split on the good cycle's type given `≥3` binary and sub-threshold
product:

| Case | Mechanism | Status at peak |
|---|---|---|
| Safe processor exists | flip → ShadowTrap | sorry-free |
| ZW, cw = 0 | single fire → shadow trap | sorry-free |
| ZW, cw > 0 | fc=2 palindromic + EC | sorrys in provider existence |
| Sweep consecutive | phase dispatch + `allNormalFormFalse2` | sorrys in counting |
| Sweep non-consecutive | forced-entry ShadowTrap via H-1 | sorrys in H-1 sub-lemmas |
| Odd winding | PhaseExtractionClean + NormalFormBridge | sorry-free through bridge |

Supporting pieces proved analytically (still valid math):
- **Shadow Cycle Mirror Theorem** (all five properties: closure, movers,
  distinctness, disjointness, Universal Escape via MNU).
- **Palindromic Entry Conflict** (3 consec binary, analytical, all n).
- **Wiggle Shadow Cycle** (80 closure identities, symbolic).
- **Universal Entry Conflict non-consecutive binary** (4 mechanisms:
  BothEvenReturn, ToggleFR-Corner, ZeroSide-EC, Traversal Return; plus two
  ring-level lemmas — Parity Obstruction + Ring Alternation).
- **`allNormalFormFalse2`** (cross-phase EC from long one-sided phase).
- **H-1 Uniqueness** (Value Coverage + Arc Return + GCD Obstruction).

### 1.2 Why it failed as a Lean ship gate

Three converging problems:

1. **Mutual recursion in the proof logic** (see
   [lb_architecture_fix_roadmap.md](lb_architecture_fix_roadmap.md)). Each
   case proof delegates its "isolated firings" sub-case to the global
   dispatch; global dispatch case-splits and calls back. Termination is
   semantic, not structural — Lean cannot see it. Stubs in
   `CaseObstructionsCore` were a workaround; deleting them just moved
   sorrys.
2. **`feedback_no_case_splits_in_lean.md`**. The architecture is
   fundamentally case-split. Keston verdict:
   > Case-split proofs in Lean on this project = land war in Asia.
3. **The 3CB open problem** at `n ≥ 9` (three consecutive binary,
   [3cb_open_problem.md](sk/3cb_open_problem.md)). No known analytical
   mechanism. Blocks `Sweep:312` and `OddWinding:153`.

After months of work the architecture stalled at 2–4 sorrys with no path
to closure, triggering the 2026-04-14 reboot.

### 1.3 The Apr 11–15 rewrite (sessions 1–7)

Partial renovation preserving the math but rebuilding wiring per
[lb_renovation_spec.md](lb_renovation_spec.md) and the session audits
(`lb_rewrite_session[1-7]_audit.md`). Outcomes:

- **Proof/ZeroWinding.lean**: 3,668 → 165 lines; architecture matches math.
- **Branch A of Sorry #1 — PROVED** (Two-Site Complementary-Tail theorem,
  both Lemma A and Lemma B, Phases 0h–0m). See
  [lb_campaign_2026-04-12/](lb_campaign_2026-04-12/) — `zw_provider_lemma_a_proof_attempt_2026-04-12.md`,
  `zw_provider_lemma_b_proof_attempt_2026-04-13.md`. Math-complete; only a
  Lean port remains.
- **Branch B (session 7)**: reclassified — the residual 3% EC-free family
  at n=9 `(2,3,3,2,3,3,2,3,3)` is `isSweep` per Lean's definition
  (`|Δ| = 18 = 2n`), **not** odd-winding. Closable via
  `BadCycleData → GlobalObstruction.shadowTrap` using a structural
  characterization (period-3, low-stay, no-runs-of-3).
- **Ended at 2 sorrys**: `provider_interval_exists_zw` (clustering lemma,
  still open analytically for non-all-binary minCL cases) and a residual
  sweep-no-pivot non-3CB obligation.

**None of this survived the SK pivot in Lean — but the math is preserved**
in the attic and in [lb_campaign_2026-04-12/](lb_campaign_2026-04-12/).

### 1.4 Dead-end analyses from the pre-SK / rewrite arc

Recorded in [lb_campaign_2026-04-12/README.md](lb_campaign_2026-04-12/README.md):

- Sharp enclosing **four-site oscillation theorem** — falsified outside
  all-odd-gap (`zw_provider_four_site_spoiler_phase0_2026-04-12.md`).
- **Two-inside-sites local route** — broader global form subsumed it; local
  form killed (`zw_provider_two_inside_sites_pa_attempt_2026-04-12.md`).
- **Naïve prev-fire / next-fire two-site sharpening** — falsified
  (`zw_provider_two_site_prev_next_obstruction_2026-04-12.md`).
- **Run-local minimal-counterexample descent** — falsified
  (`zw_provider_min_counterexample_pa_attempt_2026-04-12.md`).
- **4-site boundary-pivot stencil** — empirically superseded by the 2-site
  form (`zw_provider_boundary_pivot_phase0_2026-04-12.md`).
- **Universal non-consecutive EC (UEC)** — UNSAFE: the all-odd-gap family
  is a counterexample ([feedback_uec_scope.md](../../probes/.. "memory")).
  Replaced with pivoted theorem + local mechanisms.

---

## 2. The SK pivot (2026-04-14)

**Motivation.** The Sink-Kernel invariant, discovered 2026-04-14
([sk/sk_invariant_findings_2026-04-14.md](sk/sk_invariant_findings_2026-04-14.md)),
unifies all four mechanisms of the old case split into one structural
object. The idea: for every sub-threshold good cycle, the binary-cube
projection of `SK(C)` contains a canonical 10-edge skeleton. If true,
collapse the case split into one theorem.

**Lean location.** `LeanMn/LowerBound/SK/`. The ship gate is wired through
[CloudsTheorem.lean](../../lean/LeanMn/LowerBound/SK/CloudsTheorem.lean):
`sk_nonempty_small_n` (:418) and `sk_nonempty_large_n` (:445), which
route through `peelTube_nonempty_small_n` / `peelTube_nonempty_large_n`
in [HammingTube.lean](../../lean/LeanMn/LowerBound/SK/HammingTube.lean):169, 190
(piecewise after Wave 2 threshold fix, §10.2) and/or
`sourceTripleOfStep_injective` in
[SlabCountingRing.lean](../../lean/LeanMn/LowerBound/SK/SlabCountingRing.lean):492.

### 2.1 First SK architecture — the 10-edge skeleton (atticized)

**Lean attic**: `LeanMn/LowerBound/SK/Attic/`:
- `Skeleton.lean` — canonical 10-edge skeleton on the 3-cube (reverse
  6-cycle + 4 pole attachments), `decide` permitted.
- `BinaryCubeProj.lean` — 3-binary projection `Config → CubeVertex`.
- `TailTheorem.lean` — T2, the structural heart ("projection of `SK` at
  sub-threshold `n ≥ 9` contains all 4 pole-attachment edges").
- `Witness.lean` — T4, witness regime at `k=2` binary (CLB witness
  `ms = (2,3,…,3,2)`) handled analytically.
- `PhaseChange.lean` — T5, regime split recording `k=2` for the witness.

**Why moved to Attic.**
1. **10-edge form failed empirically** at maximally-spread binary
   placements (e.g. n=7 with binary at {0,3,6}); see
   [sk_witness_template_findings_2026-04-15.md](sk/sk_witness_template_findings_2026-04-15.md).
   Replaced by the 4-pole form, which is uniform across all tested
   placements.
2. **Outcome A audit (2026-04-18)** retired the quantitative
   `|SK| ≥ 2^(n-1)` target entirely: the main theorem only needs
   `(SK gc).Nonempty` via `SinkKernel.not_converges_of_SK_nonempty`. One
   sink suffices. See [sk/sk_audit_outcomea_2026-04-18.md](sk/sk_audit_outcomea_2026-04-18.md).
3. With `|SK| ≥ 2^(n-1)` gone, the skeleton+projection machinery (≥800
   lines Lean estimate, with a 400–700 line girth-2k lemma) is no longer
   load-bearing.

---

## 3. The five-route SK arc (2026-04-14 → 2026-04-19) — all RED

After Outcome A reshaped the target to `.Nonempty`, five structurally
distinct routes were attempted. Consolidation memo:
[sk/sk_campaign_state_2026-04-19.md](sk/sk_campaign_state_2026-04-19.md).

| # | Route | Verdict | Why |
|---|---|---|---|
| R1 | Direct (sync-cascade, step-granularity) | RED | Cascade-break shape reproduces A1 wall at step level: non-matching triples **is** A1. |
| R2 | §3 orbit-level quotient | RED | Every concrete quotient either needs case splits or collapses back to A1. |
| R3 | Fiber-budget / fiber-counting | RED | Closes `exists_unblocked_moveEntry`; residual sorry is `sourceTripleOfStep_injective` = A1 wall relocalized. |
| R4 | Read-2 aggregate ansatz `E − T + sinks ≥ 1` | RED | **Independent** quantitative wall at n ≥ 8 binary-dominated. At ms=(2,2,3,2,2,3,2,4), L=23, Σμ=12: `T=181 > (n−3)/n·L·Σμ=172.5`. α_worst grows 0.44→0.57→0.61→0.66→0.70 linearly in n. No single-term tightening saves the decomposition. |
| R5 | CDO abstract attempts #1, #2 | RED | #1 (closure-equation algebra on `Ψ_q = Move_budget_q`) reduces to A1. #2 (det-only counterexample) rules out det-only proofs. Jointly: obstruction lives in the **(C, μ) × det interaction**, not in either component alone. |

**The wall (sharp localization).** Four routes-to-A1 plus one same-regime
arithmetic wall = stable localization, not a repeated mistake. Neither
pure structure nor pure algebra suffices.

**Named conjecture** (research artifact, does **not** ship per
`feedback_no_ship_with_sorries.md`):

> No closed simple single-priv cycle with seed-consistency at a Case B
> seed `(p, l, r, v, s_1, s_2)` satisfies `Move_q(C) ≠ ∅` for every
> `q ≠ p`.

**Empirical floor.** 16,908,958 terminals across 26 Case B seeds; 0
violators. YELLOW-subset verdict. Full-sweep 726-seed probe: every seed
timed out, 0 violators within budget.

---

## 4. Transport-lift / twist-calculus arc (2026-04-19 late)

Probe arc run after the five-route consolidation memo, framed by
[sk/sk_board_reset_apr19.md](sk/sk_board_reset_apr19.md).

### 4.1 Probe-level verdicts (all non-shipping data)

- **R4a** (edge–sink margin forest bound): **REFUTED**. Peel nonempty
  1898/1898; but `margin_inner < 0` in 73/1032 n=5 records — forest bound
  applies to undirected graphs, not digraphs.
- **R4b** (directed cycle in D_tube): **SURVIVES.** Tarjan + BFS girth
  confirms girth = L in 1895/1895 sampled records. Largest SCC ≈ 2L.
- **Tube index cocycle** (vertex-valued phase): **REFUTED.** Σ(c) is
  multi-valued in 18–45% of tube vertices; edge δ escapes {0,1} on
  39–83% of edges; no threaded-all-δ=1 choice on any girth cycle.
- **Transport-lift both ends wrong**: T_strict kills all lifts 1898/1898;
  T_loose trivially lifts by inheritance.
- **Strict anchored threading** (Case A: p=q, Case B: p=M[i]): **0/1898
  close.** Case C edges are load-bearing, not exceptional.
- **Same-defect slot re-anchoring**: 0/1898 close.
- **Min Case-C closed threading (structural finding, non-shipping).**
  Every girth cycle has exactly **6 Case-C edges** at n=6,7,8 (647/669,
  149/152, 45/45). Σ_C Δq ≡ 0 (mod n) in 841/841. "6 twists" = "6
  defect-position jumps" = "6 cycle-index jumps."

### 4.2 Twist-calculus package (formalized, then atticized)

Lean source at one point: `LeanMn/LowerBound/SK/{TwistCalculus,
DominantNormalForm, CTCL, FusionDefect}.lean`. Build green, isolated from
ship gate. Three regimes identified (n=6,7,8 combined):

1. **Dominant (4R + 2L, no exceptions)** — 88.9%. Stretch balance
   `Σ k_R = Σ k_L`.
2. **Fold** (irreducible `F_k`) — ≈4.0%. CTCL `Σ χ = 6` exactly 34/34
   despite `χ(F_k) = −7−k`. Unexplained compensation.
3. **Fusion** — ≈7.0%. Fusion defect `ε := Σ χ − 6 ∈ {0, 1, 2}`,
   deterministic from signature.

Theorems stated: DTNF_forward, CTCL, FDC. Lean built `CTCL_from_witness`
and `CTCL_dominant` modulo `DTNF_forward`.

**Verdict: DEAD.** Forced-closure probe FAIL outcome 3 on 2026-04-20:
escape rate grows 0.36 → 0.43 linearly in n. Gate §7.2 RED. All four
twist files moved to `attic/twist_calculus_2026-04-20/`. Campaign AT REST
reinstated.

**FRL (Fusion Rate Law, old Theorem B)** archived as refuted: CSP search
returned 0/59 fusion records globally balanceable; obstruction is
algebraic, not a search-budget issue
([sk/sk_frl_csp_verdict_2026-04-19.md](sk/sk_frl_csp_verdict_2026-04-19.md)).

---

## 5. R4 peel-direct revival (2026-04-19 late → 2026-04-20) — CERTIFIED DEAD

**Lean artifact (live but orphaned).**
[HammingTube.lean](../../lean/LeanMn/LowerBound/SK/HammingTube.lean) — 2 sorries
after Wave 2 threshold fix (2026-04-21, §10.2):
`peelTube_nonempty_small_n` at :169 and `peelTube_nonempty_large_n` at
:190. Target (same for both arms):

> For every good cycle `C` at sub-threshold product,
> `peel(N_1(C) ∩ VC-NG)` is nonempty — equivalently, the forced-NG
> subgraph on `T_N1` contains a directed cycle.

**Empirical floor (excellent).**

| Fact | Value |
|---|---|
| peel nonempty | 100% of 1898 records |
| margin_total = `|E| − (|T| − |sinks|)` | ≥ 4 uniformly |
| # non-trivial SCCs per record | **exactly 1** |
| non-trivial SCC min size | 18/34/50/80 at n=5/6/7/8 |
| peel ⊇ non-trivial SCC | 100% |

### 5.1 The probe chain E13–E17 and Mathlib gap

Full writeup: [sk/sk_r4_frontier_2026-04-20.md](sk/sk_r4_frontier_2026-04-20.md).

| Probe | Target | Result |
|---|---|---|
| E13 | `margin_total ≥ 1` pigeonhole | Margin empirically OK — but DAGs can have `|E| ≥ |V|`, so not rigorous. |
| E14 | Canonical lex-first walk closes in T_N1 | **FAIL**: walk exits T_N1 in 41% of records. |
| E15 | Any of 5 smart-walk rules (degree, 2-hop reach, 2-hop sink-avoid, max-firing-pos) | **FAIL**: 26% residue on best-of-5. |
| E16 | ∃ non-trivial SCC of uniform minimum size | **STRUCTURAL FACT** — exactly one SCC per record, but framing ≡ cycle existence, no reduction. |
| E17 | Local predicate P(c) for SCC membership | **FAIL** — best combination (`in_deg ≥ 1 ∧ has_nonsink_successor`) min accuracy 46.7%. SCC is genuinely global. |
| Mathlib | Partial `f` on finite α + non-sinks ⟹ cycle | **GAP** — no such theorem. Fallback lifts collide with E15 residue. |

**The analytical wall.** Peel existence is a **global** property; every
uniform local rule we can define fails on a cycle-shape residue, and the
local feature space doesn't separate cycle-shape families cleanly enough
to close the gap. Any deterministic cycle-independent successor-choice
rule can be led astray toward sinks before the cycle-closing edge is
reached — greedy can't simulate teleological.

**Realistic bounded case-split port:** 15k–40k Lean lines per Keston's
10× correction — violates `feedback_no_case_splits_in_lean.md`.

---

## 6. A1' target-injectivity revival (2026-04-20) — BROKEN

**Lean artifact (live).**
[SlabCountingRing.lean](../../lean/LeanMn/LowerBound/SK/SlabCountingRing.lean)
at :492 — `sourceTripleOfStep_injective` (A1'). The `sourceTripleOfStep`
version is already proved from `targetTripleOfStep_injective` via
`sys.f` congruence; A1' **is** target-injectivity.

**Empirical floor (excellent).** 4391 exhaustive pinned-det attempts
across n=5..9 + 1898 observational = **6289 data points, 0 A1'
violators.** Budget-limited CLEAN at n=8 (271 attempts, 21% multiset
coverage) and n=9 (230 attempts, 7%).

### 6.1 Why Lean routes don't close it

Conception log: [sk/sk_a1_conception_log.md](sk/sk_a1_conception_log.md)
(Explorations 1–23).

- **E21 caller audit — BROKEN.** `triple_non_mover_witness` cannot close
  A1' via `entryConflict_impossible`. Under `unique_privileged` (`∃!` at
  [GoodCycleBasics.lean:23](../../lean/LeanMn/LowerBound/GoodCycleBasics.lean#L23)),
  every privileged context at p has `moverAt = p`. No non-mover exists at
  privileged contexts. Mover + non-mover at same context cannot be
  assembled from `(L, v, R)`, `(L, S_k, R)`, or `(L, S_{k'}, R)`.
- **E22 Moore pigeonhole — FAIL.** F non-injective under A1' violation
  ⟹ orphans exist, but orphans live **outside** the cycle. Cycle configs
  are always in `image(F)`. No contradiction via Moore's finite-space
  orphan argument.
- **E23 HKR Index Lemma — RED.** 2481 sub + 1674 at-threshold records,
  16 coloring/complex combinations across three constructions (cycle as
  1-manifold, 2-torus position × step, source-triple 1-complex). All
  signed contents collapse to `C = 0` trivially (closed cycles ⟹ ∂M = ∅
  ⟹ Index Lemma degenerates). Structural preconditions absent: oriented
  manifold with boundary, rank-symmetry group action on coloring,
  chromatic subdivision.
- **Literature search.** Moore–Myhill twins, Dijkstra K-state ring,
  Hesselink, Beauquier/Debas/Johnen, Angluin population protocols,
  chromatic simplicial methods: no off-the-shelf theorem fits A1'.
  (Agent `a7a421943a10de298`.)

**Eliminated approach classes (Strategy Register).**

1. Sync-cascade step-granularity (R1) — reproduces A1.
2. Orbit-level quotient (R2) — collapses to A1 or case splits.
3. Fiber-counting / fiber-budget (R3) — routes through A1.
4. Read-2 aggregate quantitative (R4) — arithmetic wall at n ≥ 8
   binary-dominated.
5. Det-only / closure-equation abstract (R5) — #1 reduces to A1; #2
   admits construction-level counterexamples.
6. Transport-lift / tube-index cocycle — multi-valued signatures, δ
   escapes {0,1}.
7. Projection lemma via twist-geometry — forced-closure FAIL outcome 3.
8. Cycle-structure-only (C, μ) arguments — Gate-2 explicit failure.
9. Det-only arguments not using (C, μ) — Gate-2 explicit failure.

---

## 7. SK Morse–Hamming (SKMH) topological arc (2026-04-20)

**Framing (Keston-endorsed).** Prove via a *topological invariant* of
`X(ms) \ C` that forbids any valid transition function from existing.
Keston: "exactly how I imagined this proof working."
See [feedback_topological_invariant_proof_shape.md](..).
Log: [skmh/exploration_log_skmh.md](skmh/exploration_log_skmh.md).

**Conjecture (Morse–Hamming).** `f ⊇ det(C)` is self-stabilizing iff `f`
induces a complete discrete Morse vector field on `X(ms) \ C` with all
critical cells in `G(C)`. Corollary (if conjecture holds):
`β_k(X(ms) \ C) > 0` for some `k ≥ 1` ⟹ no self-stab at that `(ms, C)`.
LB reformulation: `∀ sub-threshold ms, ∀ fair simple cycle C, ∃ k ≥ 1`
with `β_k(NG(C)) > 0`.

### 7.1 Ten probes, ten failures

| # | Invariant | Object | Result |
|---|---|---|---|
| E2 | β_1 | ∏Δ^{m_i-1}, induced NG | Always 0 (m_p≥3 "one-3" 2-cells fill 1-holes) |
| E3 | ∃k β_k>0 | ∏Δ, induced NG | 50% sub-threshold rate; ambient-dim driven |
| E4 | f-vector linears (χ, Hilbert poly, c_0/M) | ∏Δ, induced NG | Monotone with ambient dim; no discrimination |
| E5 | Herlihy content under processor coloring | ∏Δ, induced NG | Probe **broken** — Hamming-paths aren't simplices of ∏Δ |
| E6 | Z/n equivariant Euler | ∏Δ, induced NG | Probe **broken** — Z/n doesn't act on NG(C) unless C is Z/n-invariant |
| E7 | Integer torsion H_*(NG; ℤ) mod p=2,3,5,7 | ∏Δ, induced NG | 0 torsion anywhere (H_* free abelian) |
| E8 | Flow β_0 on forced-graph cube | Dynamics complex | **Signal but INVERTED** — coverage scaling `L/(n·∏m_i)` |
| E9/E18 | Normalized β_0 / closed-SCC count | Dynamics | Same inversion |
| E11 | Triple complex β_0, β_1 | Rule-constraint graph | Inverted |
| E12 | Direct SK via sink-iteration | Forced graph | Correct direction — but **combinatorial, not topological** |

### 7.2 The meta-diagnosis

1. **Homotopy type of `NG(C) ⊆ ∏Δ^{m_i-1}` is `(n, L)`-parametrized.**
   `ms` enters via ambient dim (cell counts), not through rank data. So
   Betti numbers scale **with** product — wrong direction for a LB.
2. **Coverage inversion.** Any dynamics-complex invariant that reduces to
   "how well det(C) covers NG triples" is coverage-driven, not
   self-stab-driven. `|det|/T_total = L/(n·∏m_i)` decreases as product
   grows.
3. **SK is the cleanest threshold discriminator available and it's
   combinatorial**, not a homotopy invariant.

Honest verdict (skmh §Synthesis after E12):
> The LB has a **combinatorial core** (sink-kernel count, or equivalently:
> does det(C) extend to an acyclic flow on NG). Any topological invariant
> of the ambient / complement spaces is either (i) driven by `(n, L)` via
> homotopy, (ii) driven by coverage ratio (wrong direction), or (iii)
> reducible to SK via sink-iteration (combinatorial, not topological).
> The Keston-endorsed shape did not match the problem in any natural
> model category tested.

**What survives:** coverage inversion as a load-bearing diagnostic for
any future topological attempt; `|SK|` constant per `(n, L)` as evidence
the LB factors as `(n, L)` constraints + arithmetic bound on `L`;
reusable Python infrastructure for chain complexes, flow graphs, SCC,
mod-p rank, SK computation.

---

## 8. Two open frontiers

After all the above, four LB sorries remain in Lean; they collapse to
**two open frontiers**. (The fifth sorry is UB #9, off-scope.)

The Wave 2 threshold fix (2026-04-21, §10.2) split Frontier 1 into two
piecewise obligations `peelTube_nonempty_small_n` and
`peelTube_nonempty_large_n` — the previously-unified form was refuted
by the small-n witnesses. Both piecewise forms are research-open.

### Frontier 1 — `peelTube_nonempty_{small,large}_n` (the R4 peel-direct route)

- **Lean sites.** [HammingTube.lean:169](../../lean/LeanMn/LowerBound/SK/HammingTube.lean#L169) (small_n),
  [HammingTube.lean:190](../../lean/LeanMn/LowerBound/SK/HammingTube.lean#L190) (large_n).
- **Consumers.** [CloudsTheorem.lean](../../lean/LeanMn/LowerBound/SK/CloudsTheorem.lean)
  `sk_nonempty_small_n` (:418) via `sk_nonempty_via_tube_small_n` and
  `sk_nonempty_large_n` (:445) via `sk_nonempty_via_tube_large_n`.
  Closing both zeroes LB sorries #1 and #2.
- **Statement.** For every good cycle `C` at sub-threshold product,
  `peel(N_1(C) ∩ VC-NG)` is nonempty. Equivalently: the forced-NG
  subgraph on `T_N1` contains a directed cycle.
- **Empirical status.** Peel nonempty 100% across 1898 records; exactly
  **one** non-trivial SCC per record; minimum SCC size grows as n
  (18/34/50/80 at n=5/6/7/8); peel ⊇ SCC always.
- **Analytical wall.** Global property; no uniform deterministic walk
  rule simulates it (26% residue on best-of-5); no local predicate
  characterizes SCC membership (min accuracy 46.7%); Mathlib has no
  partial-function cycle-existence lemma at this shape.
- **Math-level status.** **Certified dead for Lean** under
  `feedback_no_case_splits_in_lean.md`. Would require 15k–40k Lean lines
  of bounded case splits.

### Frontier 2 — `sourceTripleOfStep_injective` (the A1 wall)

- **Lean site.** [SlabCountingRing.lean:492](../../lean/LeanMn/LowerBound/SK/SlabCountingRing.lean#L492),
  sometimes written `targetTripleOfStep_injective` (equivalent via
  `sys.f` congruence).
- **Consumer.** Load-bearing for fiber-budget closure.
- **Statement (named conjecture form).** No closed simple single-priv
  cycle with seed-consistency at a Case B seed `(p, l, r, v, s_1, s_2)`
  satisfies `Move_q(C) ≠ ∅` for every `q ≠ p` — equivalently, some
  `q ≠ p` has `Move_q(C) = ∅`.
- **Empirical status.** 6289 data points (4391 exhaustive pinned-det +
  1898 observational), **0 violators**. 16.9M terminals across 26 seeds,
  **0 violators** (YELLOW-subset, budget-limited CLEAN at n=8/n=9).
- **Analytical wall.** Obstruction lives in the **`(C, μ) × det`
  interaction**. Five disjoint routes converge here (R1 direct, R2
  quotient, R3 fiber-budget, R4 quantitative, R5 CDO). Two joint
  diagnostics:
  - Purely-structural arguments (ignoring det) are dead — Gate-2 failure
    class.
  - Purely-algebraic arguments (ignoring `(C, μ)`) are dead — CDO #2
    counterexample.
- **Moore / HKR / literature routes exhausted.** E21 audit: unique
  privilege + context assembly blocks mover/non-mover at same context.
  E22: Moore orphans live outside the cycle. E23: HKR Index Lemma's
  boundary/rank-symmetry/subdivision preconditions all absent.

---

## 9. Current campaign posture (2026-05-10 end of day)

Per [sk/sk_lb_decision_2026-04-20.md](sk/sk_lb_decision_2026-04-20.md),
the topological revival arc (§10) closed 2026-05-10 at the Wave 5
terminal queue. Paper-writing trigger fires per Wave 5 plan §9:
**write the paper as conjecture + evidence + comprehensive catalog**.

γ decision point remains open for the proof side — no Lean LB proof
ships (sorry count 4 LB). Awaiting Keston directional call between:

| Option | What |
|---|---|
| **(γ) Retire** | Atticize HammingTube + SlabCountingRing A1 block. Paper ships LB as empirical/analytical, not Lean-verified. Sorry count drops to 1 (UB only). |
| **(α) Multi-session DFS-exhaustion formalization** | 10k–30k Lean lines, months. No empirical seed narrower than DFS itself. Tension with no-case-splits feedback. |
| **Pivot** | No concrete candidate surfaced. Speculative angles: arithmetic divisibility on per-position walk-lengths α_p; re-read EWD391 / Hesselink K-state directly; algebraic obstructions on det via monoid/group actions; entropy / information-theoretic arguments on cycle-preserved info. |

**Binding constraints (do not violate).**

- `feedback_no_ship_with_sorries.md` — no paper, no DK letter, no
  preprint, no talk, no named-conjecture writeup while any sorry remains.
  Ship gate = sorry count 0.
- `feedback_no_case_splits_in_lean.md` — case-split proofs in Lean on
  this project = land war in Asia.
- `feedback_no_time_gates.md` / `feedback_no_time_caps_on_research.md` —
  stop conditions are math-level (structural collapse, probe verdict),
  not clock-level.
- `feedback_attic_usage.md` — do not atticize any file without explicit
  Keston green-light.

**Resumption gates (all three must clear before reopening the campaign).**

1. Genuinely new idea from outside the 2026-04-14 → 2026-04-20 arc.
2. Attacks the `(C, μ) × det` interaction directly, not around it.
3. Pre-commit tripwire structurally distinct from R1–R5 / peel-direct /
   SKMH routes.

If any gate fails, stay at rest. The campaign's current state (sorry
count 4 LB, build green, diagnostic preserved, empirical detector
available as probe tool, paper-writing in progress) is the correct
state. The Wave 2 threshold fix accounts for the +1 sorry delta vs
2026-04-20; the topological revival arc itself (Waves 1–5, §10) did
not change sorry count further — its signal is empirical, not
shippable as a proof.

### 9.1 Paper-writing posture (added 2026-05-10)

Wave 5 plan §9 trigger fired. Paper target structure per Wave 5
consolidation §9.1:

1. Problem statement (adapt `p2.md`).
2. Exact `M_n` values and UB constructions at n ≤ 9.
3. Phase transition at n = 9.
4. Upper bound witnesses (adapt `witness_primer.md`).
5. Lower bound conjecture + structural evidence: circulation detector
   (100% accuracy on 29 records at n ∈ {5..10}); direction-covariant
   balance; P1.5 subclass observation; sharpness at boundary.
6. Negative-results catalog: dead routes from §§1–7 plus Waves 1–5.
7. Open questions: analytical closure of direction-covariant balance
   on `longest_ter_run ≤ 1` subclass; weighted tropical; proper
   2-skeleton Forman–Ricci; Conley index (unattempted).

Single ship-candidate analytical follow-up, if Keston green-lights:
**prove the direction-covariant balance identity on the
`longest_ter_run ≤ 1` subclass** (Wave 5 §9.2). Would be a restricted
`peelTube_nonempty` theorem on that subclass. Prior ~30% for clean
case-split-free proof.

---

## 10. Topological revival arc (2026-04-21 → 2026-05-17) — RETIRED AS DETECTOR-ONLY

Responding to Keston's topological-invariant preference
(`feedback_topological_invariant_proof_shape.md`). Probed 4 waves,
8 distinct probes. Summary: Lean threshold bug fixed (permanent),
circulation LP validated as 100%-accurate detector, no LB mechanism
extracted. All primary artifacts under
`lean/docs/topo_revival/`.

### 10.1 Wave 1 — ambient topological invariants (2026-04-21) — 4/4 RED

Plan: [`wave1/probe_plan_topological_revival_2026-04-21.md`](topo_revival/wave1/probe_plan_topological_revival_2026-04-21.md).
Memo: [`wave1/probe_wave1_consolidation_2026-04-26.md`](topo_revival/wave1/probe_wave1_consolidation_2026-04-26.md).

Eight ambient-topological invariants specified, four ran in Phase A:

- **P1 π_1 / H_1 of NG(C):** RED. Tietze reduction to `(0 gens, 0 rels)`
  on 6/6 in-budget records. β_1 = 0 universally. No commutator-based
  obstruction in 2-cell fillings.
- **P2 linking matrix of mover-class subcycles:** RED. Proxy matrix is
  antisymmetric + rotation-covariant, forcing `det Λ = 0` and
  rank(Λ) determined by (n, L) alone.
- **P3 Lefschetz / ζ_f orbit multiset:** RED. Orbit signal driven by
  multiset composition (pure-binary vs mixed), not threshold status.
- **P6 Cheeger / spectral-gap of forced-NG:** RED. λ_2 = 0 on 10/10
  records — graph disconnected in both classes. §0.6 coverage-inversion
  confirmed directly.

P5 (Forman–Ricci) was the one unresolved Phase A probe; skipped when
Waves 2–4 made it moot. Phase B/C/D (Fourier, sheaf H¹, Conley index)
never ran; all were contingent on a Phase A YELLOW that never
materialized.

### 10.2 Wave 2 — lifted-defect circulation route (2026-04-21) — YELLOW-with-caveats

Plan: [`wave2/probe_plan_wave2_circulation_2026-04-21.md`](topo_revival/wave2/probe_plan_wave2_circulation_2026-04-21.md).
Memo: [`wave2/probe_wave2_consolidation_2026-04-26.md`](topo_revival/wave2/probe_wave2_consolidation_2026-04-26.md).

Three priorities landed:

- **Priority 0 threshold bug fix — SHIPPED.** The old unified
  `peelTube_nonempty` at `< 4·3^(n-2)` was refuted by
  `witness_n5..8`. Split into piecewise `peelTube_nonempty_small_n`
  (n ∈ {5..8}) and `peelTube_nonempty_large_n` (n ≥ 9) per §0.4.
  Consumer rewiring in `CloudsTheorem.lean:418, 445`. `lake build`
  green. **Net +1 sorry** (was 1 unprovable; now 2 research-open).
  This fix survives Wave 4 retirement — it's correct regardless of
  what the LP probe does next.
- **Priority 0.5 verified at-threshold corpus — PARTIAL.** 1/20+
  records (n=9 CLB via imported `clb_witness_8748.build_system`). In-file
  generalization `build_clb_witness` failed on n ≠ 9 due to
  edge-cost shortcut — fixed in Wave 3 Priority 0.
- **Priority 1 C1 lifted-circulation LP — YELLOW.** 18/18 sub-threshold
  feasible, 0/1 verified at-threshold feasible, O(4) edge types
  (transport, c_self, c_left, c_right), trivial cycle-time-shift
  stabilizer on every feasible record. Coverage correlation 0.297
  (borderline). All seven pre-commit kill criteria not fired.

Notable bug history: first-pass C1 implementation had a one-edge-per-
vertex bug producing false 11/18 sub-infeasibility. Fix emitted all
forced moves per lifted vertex; corrected run gave the YELLOW above.

### 10.3 Wave 3 — C1 hardening + C2 balance identity (2026-04-26) — C2 RED

Plan: [`wave3/probe_plan_wave3_c1_hardening_2026-04-26.md`](topo_revival/wave3/probe_plan_wave3_c1_hardening_2026-04-26.md).
Memo: [`wave3/probe_wave3_consolidation_2026-05-03.md`](topo_revival/wave3/probe_wave3_consolidation_2026-05-03.md).
P4 prose: [`wave3/stab1_structural_argument_2026-04-26.md`](topo_revival/wave3/stab1_structural_argument_2026-04-26.md).

Seven priorities, three material:

- **P0 CLB generalization fix — DONE.** `build_clb_witness_v2` with
  full edge_costs sweep. 6/6 records at n=5..10 pass `verify_system`.
- **P1 corpus expansion — SURVIVES.** Sub 19/19 feas, at 0/6 feas at
  n=5..10 verified CLB. Discrimination confirmed beyond Wave 2's
  N=1 at-threshold.
- **P2 balance identity — RED.** Per-vertex decomposition `T + W_right
  + W_self + W_left = 0` (LP constraint), but leading-order residual
  `|T + W_right| / |T|` averages 4.9% (plan required <1%).
  `c_self + c_left` carry 10.7% of flow weight despite only 2.9% of
  edge count — they are leading-order contributions with few
  carriers, not subleading corrections. The plan's posited
  "transport-absorbed-by-c_right" balance identity does not hold.
- **P3 c_right asymmetry — structural.** Reverse-cycle test: c_right
  and c_left swap support weights. Orientation-dependent, tracks
  bounce direction — not a classify_type convention.
- **P5 scalar-feature regression — R²=0.809, threshold acc=1.0.**
  6-feature linear classifier perfectly separates feasibility on the
  25-record Wave 3 corpus. Surface reading: scenario (b) — LB
  factors through arithmetic. Pushback: corpus is structurally
  stratified (all sub records have ≥3 binaries; all at records have
  exactly 2 binaries). The 100% accuracy is consistent with
  `n_bin ≥ 3` being the only separator, which is a sampling artifact
  of the sub-threshold structural constraint, not a real arithmetic
  separator.
- **P6 coverage correlation CI, P7 perturbation — background checks
  with no flip.**

Gate decision (plan §9.1): P1 SURVIVES × P2 RED row → "Stop at
YELLOW. C1 is real but there's no balance identity to prove."
Recommendation: arithmetic pivot. Pushback: the arithmetic pivot
was tested on a corpus where the arithmetic signal was
structurally predetermined, so Wave 4 must dispositively test
whether 3-binary at-threshold records (which do exist but weren't
in the Wave 3 at-corpus) are also infeasible before pivoting.

### 10.4 Wave 4 — dispositive test + arithmetic pivot (2026-05-03) — DETECTOR-ONLY

Plan: [`wave4/probe_plan_wave4_2026-05-03.md`](topo_revival/wave4/probe_plan_wave4_2026-05-03.md).
Memo: [`wave4/probe_wave4_consolidation_2026-05-10.md`](topo_revival/wave4/probe_wave4_consolidation_2026-05-10.md).

- **P0 small-n witness dispositive test — Case A PASSES.** All 4
  small-n witnesses (w5–w8 from `docs/verify_witnesses.py`, 3-binary
  at sharp `32·3^(n-4)`, class 4) are INFEASIBLE in C1. Binary count
  alone is **not** the separator. The Wave 3 scenario-(b) reading
  via `n_bin ≥ 3` is falsified — on the expanded 29-record corpus
  the classifier's accuracy drops to 86.2%. Circulation captures
  something real that is not reducible to binary count.
- **P0.5 classify_type audit — CLEAN.** 0/4795 forward-direction
  edges in `other_*` buckets. The 4-type partition is complete in
  forward direction. Wave 3's reverse-cycle "other" edges were
  reversal-only artifacts.
- **P1 direction-covariant decomposition — still RED.** Merging
  `c_right + c_left` gives mean leading residual 2.72%. |W_self|
  is 52.6% of |T + W_sided| — c_self is not subleading. Factor
  ~1.8× improvement over Wave 3 but still 2.7× the threshold.
- **P2 arithmetic extraction (expanded corpus) — Case B-ish.**
  10-feature richer regression: R²=0.789, in-sample acc=0.966, LOO
  acc=0.931. Best approximation is `log(M_n(n)) − log(prod)` — the
  threshold condition itself. No separator better than tautological.
- **P4 ARG comparison — skipped.** Gated on P2 Case A, didn't fire.

Gate decision (plan §7.1): P0=A × P1=C × P2=B/C → "Arithmetic
pivot fails. Return to §9."

### 10.5 Net result for the history

- **Permanent positive:** the Wave 2 Lean threshold fix (§0.4). This
  removes an unprovable statement and is correct regardless of the
  subsequent arc's verdict. The two resulting sorries are
  research-open and represent the true frontier obligation.
- **Permanent tool:** the C1 lifted-circulation LP is a 100%-accurate
  feasibility detector for valid-vs-sub-threshold on 29 records at
  n ∈ {5..10}. Useful for search (pruning candidate witnesses at
  n ≥ 11) even though not ship-ready as a proof. Preserved in
  `wave3/probe_wave3_combined_2026-04-26.py` and
  `wave4/probe_wave4_combined_2026-05-03.py`.
- **Negative structural results:** neither the original 4-type
  decomposition, nor the direction-covariant 3-type decomposition,
  nor the 10-feature scalar-arithmetic regression produces a
  ship-ready LB mechanism. These three specific extraction families
  are now known-dead on this corpus; a future attempt would need a
  distinct structural family.
- **Route status:** validated-as-detector, dead-as-LB-mechanism.
  Returns to §9 γ decision. No new Lean targets. Scripts parked in
  `topo_revival/wave{1,2,3,4}/` per `feedback_attic_usage.md`.

### 10.6 Calibration note

Wave 3 posterior on arithmetic-pivot success was 70/30; Wave 4
collapsed this to 0/100 on that specific pivot. That is a ~70pp
miss driven by an inadequate corpus-structural analysis at Wave 3
end. The specific failure mode — "scenario (b) is the threshold
condition itself, not an independent arithmetic invariant" — was
not in Wave 2 or Wave 3's option space and was only surfaced by
Keston's pushback on the Wave 3 consolidation. Filed for future
phase-transition hunts.

### 10.7 Wave 5 — terminal probe queue (2026-05-10) — PAPER TRIGGER

Plan: [`wave5/probe_plan_wave5_2026-05-10.md`](topo_revival/wave5/probe_plan_wave5_2026-05-10.md).
Memo: [`wave5/probe_wave5_consolidation_2026-05-17.md`](topo_revival/wave5/probe_wave5_consolidation_2026-05-17.md).

Seven-probe bounded queue with explicit stop conditions: "any probe
produces a proof-shaped result → integrate into paper" or "queue
exhausted → paper as conjecture + evidence + catalog." Six probes
ran; P8 Conley deferred per queue exhaustion + §11.1 anti-drift
discipline.

- **P7 sheaf H¹ (simplified extension-consistency proxy):**
  AMBIGUOUS-leaning-RED. 10/19 sub records pass a "stay"-completion
  `verify_system` — counter to expectation (should be 0/19 if
  `M_n` is sharp); likely a probe-interpretation subtlety (cycle
  extractor + property check may not be comparing like-for-like).
  Flagged for audit if P7 ever reopened, but the kill criterion
  (H¹ ≠ 0 at every sub) clearly does not fire regardless of
  interpretation.
- **P1.5 zero-residual subclass characterization:** YELLOW. The
  direction-covariant balance residual is exactly zero on 15/19
  sub records; `longest_ter_run ≥ 2` predicts the 4 nonzero cases
  with 18/19 accuracy (one 5-proc anomaly: `ms = (2,2,5,2,2)`).
  Restricted-theorem candidate: prove analytically that the
  balance identity holds on the `longest_ter_run ≤ 1` subclass.
  Not attempted in Wave 5. This is the single ship-candidate
  follow-up from the topological arc.
- **Sharpness probe:** SURVIVES. Sub always feasible just below
  CLB at-threshold, at always infeasible. Tested at n ∈ {5, 6};
  n=7 sub timed out in cycle enumeration.
- **Random-multiset robustness:** SURVIVES. 100% feasibility on
  12 random sub multisets across n=5..7 where cycle construction
  succeeded. Detector-claim generalizes beyond strided enumeration.
- **P5 Forman–Ricci (simplified 1-skeleton):** AMBIGUOUS/RED. Mean
  `Ric_F` is higher at at (21.84) than at sub (9.91), but the
  gap correlates with graph size (ambient dim) — replicates E4's
  f-vector failure mode. Simplified to 1-skeleton; proper
  2-skeleton on the full ∏Δ complex not attempted.
- **Tropical LP:** RED. Uniform-weighted min-cycle-mean is 1.0
  on every feasible sub record and undefined on at. Tropical
  eigenvalue collapses to "cycle exists: 1.0 / no cycle: undef"
  — tautological. Weighted version (using Φ-optima from the LP
  as edge weights) not attempted.
- **P8 Conley index:** DEFERRED. Not run. If revisited, Wave 1 §8
  has implementation scope.

**Decision matrix row (Wave 5 plan §8.1):**

| P7 | P1.5 | Sharp+Random | Others | Verdict |
|---|---|---|---|---|
| RED (AMBIG) | YELLOW | SURVIVES | P5 AMBIG, Tropical RED | Paper as conjecture + evidence + catalog, with P1.5 YELLOW noted as partial restricted result. |

**Paper-writing trigger fires.** §9.1 above restates the paper
target structure and the single ship-candidate analytical follow-up.

**Wave 5 addendum (2026-05-17).** Plan:
[`wave5/probe_plan_wave5_addendum_2026-05-17.md`](topo_revival/wave5/probe_plan_wave5_addendum_2026-05-17.md).
Memo: [`wave5/probe_wave5_addendum_consolidation_2026-05-17.md`](topo_revival/wave5/probe_wave5_addendum_consolidation_2026-05-17.md).

Closed two Wave 5 gaps before paper writing:

- **Item 1 — proper P7 Čech H¹:** implemented the sheaf on 3-cells
  with configuration-star cover and computed nerve β₁ over ℤ/2 on
  20/28 corpus records (8 n ≥ 7 records skipped — nerve too large).
  Result: type-2 RED per plan §1.3 — at-threshold records have
  nerve β₁ ∈ [27, 11179], not zero. The sheaf-cohomology framing as
  specified does not isolate self-stabilizability; it measures
  nerve-cover topology. Upgrades the Wave 5 stay-completion proxy's
  AMBIGUOUS-RED to a concrete numerical RED-type-2.

- **Item 2 — P1.5 analytical proof attempt:** three directions
  attempted (cycle-return c_self chains, defect-potential coboundary,
  T+sided-only circulation existence). Each identifies a specific
  obstruction to a uniform-in-n case-split-free proof. Verdict:
  RED-budget at 1-session. Two follow-up leads documented
  (`max_q |V_tube[q]| ≤ 2` refined subclass; direct T+sided-only
  circulation existence), both plausible but unverified. Paper
  records as open problem, not theorem.

Addendum §0.4 typical-case branch fires: paper ships at current
scope. **[Revised 2026-05-17 — Wave 6 subsequently ran per §10.8.]**

### 10.8 Wave 6 — live leads from addendum (2026-05-17)

Plan:
[`wave6/probe_plan_wave6_2026-05-17.md`](topo_revival/wave6/probe_plan_wave6_2026-05-17.md).
Memo:
[`wave6/probe_wave6_consolidation_2026-05-17.md`](topo_revival/wave6/probe_wave6_consolidation_2026-05-17.md).

The addendum's "no Wave 6" exit was reversed when the consolidation
§2.5 leads were recognized as specifically-named structural targets
rather than vague gestures. Four targets, ordered by cost × EV:

- **T1 — V_tube refinement (`max_q |V_tube[q]| ≤ 2`):** RED
  false-negative. Predicate achieves 8/19 accuracy on the
  reconstructed Wave 5 sub corpus, strictly worse than the
  baseline `longest_ter_run ≤ 1` at 18/19. The addendum
  consolidation §2.5 lead 1 claim ("empirically matches 19/19")
  was unchecked and wrong; correct that claim in the consolidation.

- **T2 — T+sided-only circulation existence:** empirical GREEN,
  stronger than pre-commit. 19/19 records (not just 16/16
  subclass) carry a T+sided-only nonneg circulation; LP witness
  support size with and without c_self is identical on every
  record. c_right dominates c_left 213:2 in default orientation
  (symmetry-breaking is a cycle-start artifact). Analytical proof
  attempt via q-tube forward walk stalls at the same case-split
  boundary as addendum Item 2: walk closes uniformly on
  non-adjacent-mover steps and sided-mover steps, but hits a
  position-q firing "hole" that needs per-step cross-q case
  analysis. Verdict: empirical GREEN, analytical RED-budget.

- **T3 — Conley index of good cycle:** RED no discrimination.
  Raw (β₀, β₁) pairs of N/L (N = C ∪ N_1(C), L = exit set)
  are set-disjoint between sub and at, but the scale-normalized
  β₁/|N| is [1.087, 1.500] at sub-threshold and [1.080, 1.500]
  at at-threshold — fully overlapping. Replicates the Wave 1 P1
  (n, L)-parametrized failure mode; β₁ is a size statistic, not
  a topological discriminator.

- **T4 — Non-standard sheaves (three candidates):** RED all.
  (a) single-priv-propagation sheaf: H¹ = 0 uniformly across sub
  and at. (b) path / cycle-space sheaf on lifted forced-NG
  1-skeleton: normalized β₁/|V| ∈ [0.02, 0.48], ranges overlap.
  (c) convergence-depth-parameterized sheaf: more defects at
  at-threshold than sub-threshold (inverted signal; +
  stay-completion bug errored 18/19 sub records). None
  discriminates.

**Aggregate verdict.** Genuine exhaustion per plan §5.3:
T1/T3/T4 RED, T2 empirical GREEN but analytical hits the
addendum's same wall, no new specifically-named forward direction
surfaced. Paper-writing trigger fires. Upgrades:

- Section 5 (structural evidence) P1.5 subsection: **upgrade**
  Wave 5's "T(v) + W_sided(v) = 0 at 15/19" to **T2's stronger
  "T+sided-only circulation exists at 19/19; c_self structurally
  unnecessary"** with the q-tube-walk obstruction documented.
- Section 6 (negative catalog): **delete** the unverified
  `max_q |V_tube[q]| ≤ 2` claim; **add** T3 Conley and T4
  non-standard-sheaf entries as additional dead routes.
- Section 7 (open questions): T+sided-only circulation
  existence is the central open structural conjecture, now
  with 19/19 empirical support and a specific named obstruction
  (mov_k = q position-firing holes).

Lean state unchanged (4 LB + 1 UB sorries). Do NOT start Wave 7.

### 10.9 What any future topological revival must clear

Beyond §9's three gates:

4. **Corpus-structural diagnostic up front.** Any arithmetic
   separator claim on a stratified corpus must first check whether
   the signal is a structural artifact of the stratification.
   Specifically: sub-threshold corpora on this problem are
   structurally `n_bin ≥ 3`; at-threshold corpora include 2-binary
   CLB **and** 3-binary small-n absorbers. Test against both
   families before claiming arithmetic separation.
5. **Decomposition beyond mover-defect edge-type geometry.** The
   4-type (transport, c_self, c_left, c_right) and 3-type
   (transport, c_sided, c_self) decompositions both fail the <1%
   balance-residual threshold. A future decomposition must argue
   structurally why a different axis should produce a cleaner
   identity.
6. **Address the `∏m < M_n` tautology.** Any claimed arithmetic
   separator must be shown to not reduce to the threshold condition
   via algebraic manipulation. The Wave 4 P2 regression rediscovered
   the threshold approximately and called it a new inequality;
   future attempts must pre-commit a Newness check against the
   problem's own definition.

These are in addition to §9's existing gates (1) genuinely new idea,
(2) attacks `(C, μ) × det` directly, (3) tripwire distinct from
R1–R5 / peel-direct / SKMH. The topological revival satisfied gates
(1)–(3) at Wave 2 start; gates (4)–(6) are the Wave 2–4 learnings.
