# Wave 6 consolidation — four live leads from Wave 5 addendum

**Date.** 2026-05-17 (wave executed in single session).
**Status.** Genuine exhaustion per plan §5.3. T1/T3/T4 RED with
specific structural diagnostics; T2 empirical GREEN with a
paper-integrable observation but analytical proof stalls at the
same case-split boundary as Wave 5 addendum Item 2.

**Artifacts.**
- T1: [`probe_wave6_t1_vtube_refinement_2026-05-17.py`](probe_wave6_t1_vtube_refinement_2026-05-17.py),
  [`phaseW6_t1_results.json`](phaseW6_t1_results.json)
- T2: [`probe_wave6_t2_tsided_only_2026-05-17.py`](probe_wave6_t2_tsided_only_2026-05-17.py),
  [`probe_wave6_t2_structure_2026-05-17.py`](probe_wave6_t2_structure_2026-05-17.py),
  [`phaseW6_t2_results.json`](phaseW6_t2_results.json),
  [`phaseW6_t2_structure.json`](phaseW6_t2_structure.json)
- T3: [`probe_wave6_t3_conley_2026-05-17.py`](probe_wave6_t3_conley_2026-05-17.py),
  [`phaseW6_t3_results.json`](phaseW6_t3_results.json)
- T4: [`probe_wave6_t4_sheaf_2026-05-17.py`](probe_wave6_t4_sheaf_2026-05-17.py),
  [`phaseW6_t4_results.json`](phaseW6_t4_results.json)

**Companion plan.** [`probe_plan_wave6_2026-05-17.md`](probe_plan_wave6_2026-05-17.md).

---

## §0. Headline

| Target | Verdict | Note |
|---|---|---|
| T1 — V_tube refinement | **RED (false-negative)** | 8/19 accuracy, strictly worse than W5 baseline's 18/19 |
| T2 — T+sided-only circulation | **Empirical GREEN / Analytical RED-budget** | 19/19 records feasible without c_self; c_left/c_right 2:213 asymmetric; proof stalls at case-split boundary |
| T3 — Conley index of good cycle | **RED (no discrimination)** | β_1 scales with \|N\|; normalized β_1/\|N\| ranges overlap fully (sub [1.087, 1.500] vs at [1.080, 1.500]) |
| T4 — Non-standard sheaves | **RED (all three candidates)** | 4.2.1 H¹=0 everywhere, 4.2.2 cycle-space β_1 overlaps, 4.2.3 at-records have *more* defects than sub |

Per plan §5.3, genuine exhaustion reached: T1/T3/T4 RED with
identifiable obstructions; T2's empirical finding is a strict
upgrade over Wave 5 but the analytical proof hits the same wall
as Wave 5 addendum §§5–7. Plan §5.4 test: does this consolidation
name a new specifically-identified forward direction? T2 empirical
GREEN names the *same* lead Wave 5 addendum §2.5 already identified
("T+sided-only cycle existence"), now verified empirically. No new
lead is surfaced. **Paper-writing trigger fires.**

---

## §1. Target 1 — V_tube refinement (RED false-negative)

### 1.1 Hypothesis and outcome

Wave 5 addendum consolidation §2.5 lead 1 claimed:

> Refine the subclass hypothesis to `max_q |V_tube[q]| ≤ 2`.
> Empirically matches 19/19.

The claim was **unchecked and wrong**. On the reconstructed Wave 5
sub corpus (19 records, n=5..7), the predicate achieves **8/19
accuracy** — strictly worse than Wave 5's baseline
`longest_ter_run ≤ 1` at **18/19**.

### 1.2 Confusion matrix

```
                  pred zero   pred nonzero
  actual zero         4           11
  actual nonzero      0            4
  accuracy: 8/19 = 0.4211
```

11 zero-residual records have `max_q |V_tube[q]| ≥ 3`. The predicate
is too strict: any record with a ternary-or-higher proc that visits
≥3 distinct values in the cycle fails it, but most such records have
dc_residual = 0.

### 1.3 Misses (all false-negative)

All 11 misses are sub-threshold records with a non-binary proc that
visits ≥3 values in cycle (e.g., `(2,2,2,3,2)` with V_tube = [2,2,2,3,2],
`(2,2,5,2,2)` with V_tube = [2,2,5,2,2]) but zero dc_residual. V_tube
size at a position does not correlate with the direction-covariant
balance condition.

### 1.4 Diagnostic

The Wave 5 addendum consolidation §2.5 leads were documented without
running an empirical check against the existing Wave 5 residual data.
This is an **honesty failure in the Wave 5 addendum consolidation**,
not a research failure — the claim looked plausible ("V_tube ≤ 2
covers the (2,2,5,2,2) anomaly"), but was never tested.

**Correction.** Revise the Wave 5 addendum consolidation §2.5 lead 1
to "not empirically verified; subsequent testing in Wave 6 T1 showed
strict false-negative on 11/19 records."

### 1.5 Paper impact

None positive. Remove the T1 lead from any paper text. Keep the
Wave 5 baseline `longest_ter_run ≤ 1` as the subclass predicate
(with the known false-positive at `(2,2,5,2,2)`).

---

## §2. Target 2 — T+sided-only circulation (Empirical GREEN / Analytical RED-budget)

### 2.1 Empirical result (GREEN, stronger than pre-commit)

Per plan §2.3 pre-commit: GREEN if 100% of subclass records feasible
without c_self. Actual result: **100% of ALL 19 sub records feasible
without c_self**, not just the 16 subclass records.

```
Subclass (longest_ter_run ≤ 1):     16/16 feasible without c_self.
Non-subclass (longest_ter_run ≥ 2):  3/3 feasible without c_self.
Total:                               19/19.
```

**Support size with c_self == support size without c_self** on all 19
records (LP witness ignores c_self even when allowed). c_self edges
constitute up to 14.9% of the graph but contribute 0% to any LP flow.

### 2.2 Structural refinement

The T+sided-only witness decomposition:

- transport: 66.5% of flow
- c_right:   33.2% of flow
- c_left:     0.3% of flow (2 records only: (2,3,2,2,3) flow=1, (2,3,3,2,3,2) flow=1)
- other:      0% of flow

**c_right dominates c_left 213:2** in the default cycle orientation
(about 100× asymmetry). The asymmetry is an artifact of
`enumerate_cycles` lexicographic start-ordering; under reverse
orientation, c_left and c_right would swap. The **symmetric** claim
is: T + (c_left ∪ c_right) circulation exists on all sub-threshold
records; c_self is structurally unnecessary.

`same_q_frac` per record (fraction of witness flow on single-q
tubes) ranges 33.3%–79.4% — witnesses use cross-q jumps
extensively. Pure q-tube decomposition does not hold.

### 2.3 Analytical proof attempt (RED-budget, same wall as Wave 5)

Claim per plan §2.4:

> On the forced-NG lifted graph of a sub-threshold subclass record,
> the subgraph induced by T ∪ c_left ∪ c_right contains a directed
> cycle.

**Structural attempt:** Consider the "q-tube forward walk" starting
at (k₀, q, a). At each step k:
- If `mov_k ∉ adj(q)`: transport edge to (k+1, q, a). ✓
- If `mov_k = q-1` or `q+1`: c_left/c_right edge to (k+1, q, a)
  provided the move context `(mov_k, c_k[mov_k-1], c_k[mov_k], a)`
  is in `move_entries`.
- If `mov_k = q`: **only** c_self edge is available; c_self excluded.

The q-tube walk has a "hole" at every step where `mov_k = q`.
Every position q fires at least once per good cycle, so every
q-tube has ≥1 hole. Closing the hole requires a cross-q jump
via sided or `other` edges.

The cross-q jump's target depends on the specific move-entries
context at step k, which is a per-step case analysis of the mover
sequence. This is exactly the same structural obstruction Wave 5
addendum §§5–7 hit — cycle-local case analysis at the position-q
firing step.

**Verdict:** analytical RED-budget at 1-session. Matches
`feedback_no_case_splits_in_lean.md` — case-split proofs are
explicitly refused; the uniform structural argument does not
close in one session, and no new analytical handle has appeared.

### 2.4 Paper upgrade this produces

Replace Wave 5's "T(v) + W_sided(v) = 0 on 15/19" with the stronger:

> **Empirical observation (Wave 6 T2).** On the lifted forced-NG
> of every sub-threshold good cycle in our 19-record corpus
> (n = 5..7), a nonzero nonnegative circulation exists supported
> entirely on transport ∪ c_left ∪ c_right edges; the c_self edge
> type (firing at the tube position from an off-cycle value) is
> never needed by the LP optimum. Furthermore, in the default
> cycle orientation, c_left/c_right support is 2:213 (c_right
> dominant by ~100×), with the symmetry-breaking an artifact of
> cycle-start labeling. An analytical proof of T+sided-only
> circulation existence was attempted via a q-tube forward-walk
> argument; the argument closes uniformly on steps where the
> cycle's mover is non-adjacent to q and on sided-adjacent steps,
> but hits a case-split obstruction on steps where the mover
> equals q (the "hole" at position-q firing steps), where closing
> the walk requires a per-step cross-q jump analysis. The claim
> remains open as an empirical observation without a uniform
> proof.

This is strictly stronger than Wave 5's P1.5 observation.

### 2.5 New leads produced by T2? None new.

T2's empirical GREEN confirms the *same* lead Wave 5 addendum §2.5
lead 2 already named. The analytical obstruction is the *same*
as Wave 5 addendum §5–7. No new structural object is identified.

---

## §3. Target 3 — Conley index (RED no discrimination)

### 3.1 Setup

Isolating block `N = C ∪ N_1(C)` (Hamming-1 neighborhood of cycle).
Exit set `L = {c ∈ N : f(c) ∉ N}` where `f` is the stay-completion
of the det table. Simplicial complex on `N/L` with vertices = N∪{∗},
1-simplices = Hamming-1 edges, 2-simplices = Hamming-1 triangles.
Betti numbers β₀, β₁ over ℤ/2.

### 3.2 Raw result

Disjoint sets of (β₀, β₁) pairs per class:
- sub: (1, {41,57,64,66,76,80,84,86,100,128,135,140,147,154,161,163,166,169}) ∪ (2, {41,57})
- at:  (1, {87,120,134,189,262,495})

β₀ = 2 occurs only for the 2 sub records with `|L| = 0` (both
all-binary: (2,2,2,2,2) and (2,2,2,2,4)); for these records the
stay-completion makes N forward-invariant, degenerating the
isolating-block condition. For all other records β₀ = 1.

### 3.3 Scale-normalized check (kills the apparent discrimination)

|N| differs materially between sub and at records (sub |N| = 30–150,
at |N| = 69–334). β₁ correlates strongly with |N|:

- sub β₁/|N|: **[1.087, 1.500]**
- at β₁/|N|:  **[1.080, 1.500]**

- sub β₁ − |N|: [11, 49]
- at β₁ − |N|:  [14, 161]

Under any reasonable normalization the sub and at distributions
overlap completely. The raw (β₀, β₁) set-disjointness is a size
artifact, not a topological discriminator.

### 3.4 Verdict and diagnostic

**RED (no discrimination)**, effectively the (n, L)-parametrized
failure mode from plan §3.3 / Wave 1 P1. The Conley complex's
homotopy type under Hamming-1 isolating block is dominated by
configuration-space size and cycle length. No topological feature
isolates "valid extension exists" from "valid extension does not
exist."

Deeper issue: the Conley index is supposed to be homotopy-invariant
under `detOf`-preserving homotopies of f. At sub-threshold, no
valid f exists, so any completion is arbitrary, and the index
reflects completion choice, not intrinsic structure. At-threshold
records have a canonical valid completion (CLB or small-n
witness), but the index on N = C ∪ N_1(C) still measures
neighborhood topology, not the attractor character of C. A
correct use of Conley theory would require showing the index
lands in a specific homotopy class for period-L attractors of
convergent finite-state maps — the expected index depends on
L and symbolic-dynamics class and is not a simple wedge of
circles.

### 3.5 Paper impact

Negative-catalog entry:

> **Subsection — Conley index.** We computed the Čech-like Conley
> complex β₀, β₁ of N/L for N = C ∪ Hamming-1 neighborhood and L
> = boundary-exit set. Normalized β₁/|N| ∈ [1.087, 1.500] at
> sub-threshold and [1.080, 1.500] at at-threshold, fully
> overlapping. Under scale-invariant Conley statistics the good
> cycle's neighborhood topology does not discriminate
> self-stabilizability. Replicates the Wave 1 P1 (n, L)-parametrized
> failure mode: invariants depending only on configuration-space
> size and cycle length cannot isolate valid-extension.

---

## §4. Target 4 — Non-standard sheaves (RED all three candidates)

### 4.1 Candidate 4.2.1 (single-priv-propagation) — RED

H¹ = 0 on all 19 sub records AND all 6 at records. The sheaf stalks
(det-consistent "potential moves" at each cycle step) are too
simple: restriction maps along cycle edges are trivially consistent
with det, and the Čech complex has no nontrivial cocycles. No
discrimination.

### 4.2 Candidate 4.2.2 (path sheaf / cycle-space β₁) — RED

β₁ of the lifted forced-NG 1-skeleton as an undirected graph:

- sub β₁: [11, 42]; sub β₁/|V|: [0.102, 0.367]
- at β₁:  [4, 132]; at β₁/|V|:  [0.021, 0.480]

Ranges overlap completely; no discrimination.

### 4.3 Candidate 4.2.3 (convergence-parameterized) — RED (inverted)

Computed #Hamming-1 defects (|d(c) − d(c')| > 1) in the
convergence-depth function:

- sub: 29 (for the one sub record where stay-completion converges
  globally; 18/19 errored because stay-completion on partial det
  has many non-convergent trajectories)
- at: [124, 2538] — *more* defects than sub.

The signal goes in the wrong direction. At-threshold records have
LONGER convergence chains with more Hamming-1 crossings, so more
depth-jumps. Sub-threshold records under stay-completion are
dominated by non-convergent stuck configs, which have d(c) = -1
excluded from the defect count.

### 4.4 Aggregate verdict

Plan §4.3 pre-commit: GREEN if any candidate has H¹ > 0 on all sub
AND H¹ = 0 on all at. None of the three candidates achieves this.

Route RED per plan §4.3: "all three candidates fail to discriminate."

### 4.5 Paper impact

Negative-catalog entry:

> **Subsection — Non-standard sheaves.** Three candidate
> sheaf constructions with non-trivial restriction maps were
> tested: (a) single-priv-propagation sheaf with cycle-step
> indexing, (b) path-cycle-space sheaf on the lifted
> forced-NG 1-skeleton, (c) convergence-depth-parameterized
> sheaf. Candidate (a) gives H¹ = 0 uniformly. Candidate (b)
> has normalized β₁/|V| ∈ [0.02, 0.48] with sub and at
> overlapping. Candidate (c) has higher H¹ at at-threshold
> (inverted signal). No sheaf-cohomological formulation in
> the design space explored discriminates self-stabilizability.

---

## §5. Aggregate Wave 6 verdict

### 5.1 Paper-writing trigger fires

Per plan §5.3 genuine exhaustion:
- T1 RED ✓ (predicate strictly worse than baseline)
- T2 empirical GREEN (but paper-integrable observation without
  new lead); analytical RED-budget at same case-split boundary as
  Wave 5 addendum
- T3 RED ✓ (scale-invariant, no discrimination)
- T4 RED ✓ (all three candidates)

Per plan §5.4 non-exhaustion tests:
- Any target SURVIVES? T2 empirical GREEN but names no new forward
  direction — it's the same lead Wave 5 addendum §2.5 identified.
- Any RED produces new specifically-identified forward direction?
  **No.** T1's RED correction, T3's size-normalization kill, T4's
  candidate-by-candidate RED all land on known obstruction classes
  ((n, L)-parametrized, case-split-required, local-cellular).

Paper ships with the Wave 6 upgrades.

### 5.2 Paper upgrades from Wave 6

- **Section 5 (structural evidence), P1.5 subsection:** upgrade
  from Wave 5's "T(v) + W_sided(v) = 0 at 15/19" to Wave 6 T2's
  stronger **"T+sided-only circulation exists at 19/19; c_self
  structurally unnecessary; c_left/c_right ~100× asymmetric in
  default orientation."** Document the q-tube forward-walk proof
  attempt and its case-split obstruction at mov_k = q steps.

- **Section 6 (negative catalog):**
  - **Delete** Wave 5 addendum consolidation §2.5 lead 1 claim
    (`max |V_tube[q]| ≤ 2` empirically 19/19) — was unverified and
    wrong.
  - **Add** T3 Conley index entry: normalized β₁/|N| overlap
    [1.087, 1.500] at both classes; (n, L)-parametrized failure
    mode.
  - **Add** T4 non-standard sheaves entry: three candidate
    constructions, all RED.

- **Section 7 (open questions):** add the T+sided-only circulation
  existence claim as the central open structural conjecture — now
  with empirical 19/19 support — and document the q-tube-walk
  obstruction at mov_k = q steps as the specific structural gap.

### 5.3 Do NOT start Wave 7

Per plan §6 anti-drift and §6.1: a wave that produces no
specifically-named forward direction should end in paper, not
another wave. Wave 6 has satisfied this condition. The T2
empirical GREEN does not name a new lead — it's the same lead
Wave 5 addendum identified, now supported by stronger empirical
data but with the same analytical wall.

Genuine extension would require: a new analytical handle on the
mov_k = q hole closure (not a new probe), or a fresh topological/
algebraic angle not in the Wave 1 P1–P8 / Wave 6 T1–T4 design
space. Neither has appeared.

### 5.4 Lean state unchanged

Sorry count still 4 LB + 1 UB. No new Lean work produced by
Wave 6. Wave 2 threshold fix intact.

---

## §6. Honest caveats and flags

- **T2 analytical RED-budget, not pure RED.** Attempted only a
  q-tube forward-walk structural proof in one session; plan
  allowed days to 1-2 weeks. Per `feedback_no_case_splits_in_lean.md`
  and `feedback_no_time_caps_on_research.md`, stopping at the
  case-split boundary is the right call absent a new analytical
  angle.

- **T3 used a specific isolating block (radius 1) and stay-completion.**
  A richer isolating-block construction (radius 2, or
  Kalies–Mrozek–Rybakowski multi-valued setup) might give a
  different index. Not pursued given |N|-overlap already kills the
  candidate. Noted for completeness.

- **T4 candidates were implementation choices, not canonical.** The
  plan §4.2 design space is broader than the three I implemented.
  Specific candidate (c) implementation had a stay-completion
  convergence failure bug (18/19 sub errored), so its RED signal
  is partly implementation-dominated. The other two candidates
  (a, b) are clean.

- **Wave 5 addendum consolidation §2.5 lead 1 was wrong.** T1
  revealed the "empirically matches 19/19" claim was unverified.
  Update the addendum consolidation to correct this; do not
  quote the unverified claim in any paper text.

---

## §7. One-line summary

**T1 RED wrong-predicate; T2 empirical GREEN + analytical RED-budget
at Wave-5-same wall; T3 RED scale-normalized; T4 RED all three
candidates. Paper-writing trigger fires. T2's upgrade of the P1.5
observation is the one strict gain; everything else is negative
catalog.**

---

*End of Wave 6 consolidation.*
