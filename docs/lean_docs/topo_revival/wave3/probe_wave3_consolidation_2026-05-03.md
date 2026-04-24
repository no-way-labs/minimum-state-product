# Wave 3 consolidation — C1 hardening outcomes

**Date.** 2026-04-26 (within Week-1 Wave-3 window; stopping on verdict
per `feedback_no_time_gates.md`).
**Artifacts.**
- [`probe_wave3_combined_2026-04-26.py`](probe_wave3_combined_2026-04-26.py)
- [`phaseW3_results.json`](phaseW3_results.json)
- [`stab1_structural_argument_2026-04-26.md`](stab1_structural_argument_2026-04-26.md) (P4)

**Companion plans.** [`probe_plan_wave3_c1_hardening_2026-04-26.md`](probe_plan_wave3_c1_hardening_2026-04-26.md).

---

## §0. Headline

**C2 balance-identity test fails (§3.3 SURVIVES condition not met).
Scenario (b) pivot-to-arithmetic is the most consistent read.**

Per plan §9.1 decision matrix:

| Priority | Outcome |
|---|---|
| P1 | SURVIVES (sub 19/19 feas, at 0/6 feas across n=5..10 verified CLB) |
| P2 | **RED** (mean leading residual / T = 4.9%; plan SURVIVES requires < 1%) |
| P5 | **R² = 0.809, threshold acc = 1.0** — in the "mixed" band but threshold classifier is perfect (scenario-(b)-leaning) |
| P6 | Inconclusive (coverage cor 0.496, 95% CI [0.243, 0.710] straddles 0.3) |

P1 × P2(RED) row in §9.1 matrix →
**"Stop at YELLOW. C1 is real but there's no balance identity to
prove; C3 is unreachable. Route ships as empirical observation only."**

P5's 100% threshold-accuracy adds weight for an **arithmetic pivot**:
a linear classifier on `(n, L, log prod, #binary, #ternary, #≥4)`
perfectly separates feasibility, consistent with scenario-(b).

**Recommendation.** Do NOT proceed to C3. Investigate arithmetic LB
inequality from P5's regression coefficients, and if that closes,
ship the arithmetic route rather than C3.

---

## §1. P0 — CLB generalization fix (DONE)

`build_clb_witness_v2` restores the full `O(non_good × free_entry)`
edge-cost sweep. All six generated records pass `verify_system`
(liveness, mutex, closure, convergence, fairness):

| n | ms | product | L |
|---|---|---|---|
| 5 | (2,3,3,3,2) | 108 | 13 |
| 6 | (2,3,3,3,3,2) | 324 | 16 |
| 7 | (2,3,3,3,3,3,2) | 972 | 19 |
| 8 | (2,3,3,3,3,3,3,2) | 2916 | 22 |
| 9 | (2,3,3,3,3,3,3,3,2) | 8748 | 25 |
| 10 | (2,3,3,3,3,3,3,3,3,2) | 26244 | 28 |

All six are composition class 3 (endpoint-binary ternary-strip).
Products are 4·3^(n-2) — **at-sharp** for n=9 (matches M_9) and
**above-small-n-sharp** for n ∈ {5..8} (where sharp is 32·3^(n-4)).

---

## §2. P1 — Corpus expansion

### 2.1 Sub-threshold

19 records at n ∈ {5, 6, 7}, classes 1 and 2 only.

**Classes 3, 4, 5 are structurally empty at strict sub-threshold**
for n ∈ {5..8}:

- **Class 3** `(2, 3, …, 3, 2)` product = 4·3^(n-2) = sharp-large-n,
  above small-n sharp at 32·3^(n-4) — not in `enumerate_multisets(n, M_n)`.
- **Class 4** `{2^3, 4, 3^(n-4)}` product = 32·3^(n-4) = small-n sharp,
  also not strictly below.
- **Class 5** `<3 binaries`: any such multiset has product ≥ 2·2·3·3·3^(n-4)
  = 4·3^(n-2) (n=5 ≥ 324) > M_n, so excluded.

This is a **structural property of the sharp-threshold, not a sampling
failure**. The Wave 2 addendum's ask for ≥ 10 records per class cannot
be met for classes 3, 4, 5 at strict sub-threshold. Confirmation of
composition-confound can only use classes 1 (3 records) + 2 (16
records); both are uniformly feasible, so the **pure-binary-only
confound does NOT fire**.

### 2.2 At-threshold

6 verified records from fixed CLB v2. All infeasible in C1.

### 2.3 Feasibility breakdown

- sub class 1 (pure binary): 3/3 feasible
- sub class 2 (binary-dominated): 16/16 feasible
- at class 3: 0/6 feasible
- (classes 4, 5 absent)

**P1 SURVIVES** per §2.5 bullet 1: feasibility discriminates sub vs at,
non-pure-binary classes are all feasible at sub.

---

## §3. P2 — Balance identity test (RED)

### 3.1 Results on 19 feasible sub records

Per-vertex T(v), W_right(v), W_self(v), W_left(v) computed from the LP
optimal Φ. Incidence-zero `B^T Φ = 0` holds exactly (max per-vertex
total = 0 to numerical precision).

| record | ms | lead_residual/T | sub/T |
|---|---|---|---|
| (2,2,2,2,2) n=5 | pure binary | 0.000 | 0.000 |
| (2,2,2,2,4) n=5 | | 0.000 | 0.000 |
| (2,2,2,3,2) n=5 | | 0.000 | 0.000 |
| (2,2,2,4,2) n=5 | | 0.000 | 0.000 |
| (2,2,3,2,2) n=5 | | 0.250 | 0.500 |
| (2,2,3,3,2) n=5 | | 0.167 | 0.333 |
| (2,2,5,2,2) n=5 | | 0.167 | 0.333 |
| (2,3,2,2,3) n=5 | | 0.167 | 0.333 |
| (2,2,2,2,2,2) n=6 | pure binary | 0.000 | 0.000 |
| (2,2,2,2,6,2) n=6 | | 0.000 | 0.000 |
| … | … | … | … |

- Mean leading residual / T = **0.049** (4.9%).
- Mean subleading / T = **0.107** (10.7%).

### 3.2 Why this is RED

Plan §3.3 SURVIVES condition: `|T(v) + Σ c_right(v)| / |T(v)| < 0.01`
on average. Observed 4.9%, 5× the threshold.

Plan §3.4 KILL (first bullet): "if T(v) and Σ c_right balance(v) do
not cancel at leading order — i.e., c_self and c_left carry Ω(1)
weight in the balance despite being < 1% of support count."

Specifically: c_self + c_left are 1.8% + 1.1% = 2.9% of **edge count**
(support-occupancy), but carry 10.7% of **flow weight** at the
balance. Per-edge they are ~3× heavier than transport + c_right on
average. **They are not subleading corrections; they are leading-order
contributions that happen to have few carriers.**

This kills the plan's posited "transport-absorbed-by-c_right" balance.
A different coordinate system may produce a cleaner identity, but
**no such identity was found in this pass**, and the specific one the
plan posited is empirically wrong.

### 3.3 What this does NOT kill

- C1's central discrimination claim (sub feasible, at infeasible)
  survives. P2's failure says the *mechanism* posited for C3 is wrong,
  not that circulation itself is the wrong invariant.
- A different balance decomposition (e.g., along cycle-mover-orbit
  classes rather than edge-type classes) might survive. Exploring
  alternative decompositions is out of Wave 3 scope per §3.4 plan.

### 3.4 Impact on C3

Per plan §3.5: "If Priority 2 fails its SURVIVES condition, C3 is
structurally unreachable — there is no uniform balance identity to
prove." **C3 is unreachable on the `(T, c_right, c_self, c_left)`
decomposition.** A hypothetical C3 on a different decomposition would
need its own empirical validation before being attempted.

---

## §4. P3 — c_right asymmetry (STRUCTURAL)

Reverse-cycle test on 3 records, n=6:

| ms | forward types (c_right, transport) | reverse types (c_left, transport) |
|---|---|---|
| (2,2,2,2,2,2) | 21, 15 | 15, 21 |
| (2,2,2,2,6,2) | 9, 31 | 12, 28 |
| (2,2,2,5,2,2) | 13, 27 | 12 + 2 other, 26 |

c_right support exactly swaps with c_left under cycle reversal in the
pure-binary case and approximately so in mixed cases. **Asymmetry is
orientation-dependent.** This is consistent with plan §4.4 outcome (a):
"structural — document with one paragraph of explanation."

The bounce direction of the cycle induces a preferred "downstream"
side for twist edges at the defect boundary. The forced-NG dynamics
inherit this direction: defect configurations `c_k[q:=a]` with
`moverAt(k) = q + 1` ("right neighbor of defect fires") produce
**coherent** successors that stay in `T_N1`; `moverAt(k) = q - 1`
("left neighbor fires") more often produces Hamming-2-from-cycle
successors that leave `T_N1` and contribute no edge. The result is a
disproportionate population of c_right edges in the edge set and an
even more disproportionate population in the LP support.

Under `gc_rev`, the bounce direction flips, so "right neighbor fires"
becomes "left neighbor fires" and c_right ↔ c_left swap.

**Implication for C2/C3.** The edge-type taxonomy is
orientation-aware. Any balance identity that distinguishes c_right
from c_left privileges the cycle's bounce direction. A balance
identity in a **cycle-direction-covariant** coordinate system (e.g.,
merging c_right and c_left into a single "c_sided" class) might be
cleaner. This is a concrete direction for a future P2 retry.

---

## §5. P4 — stab = 1 argument

Separate prose memo: [stab1_structural_argument_2026-04-26.md](stab1_structural_argument_2026-04-26.md).

Short version: stab = L (full invariance) is ruled out structurally by
the time-fiber truncation argument (any lifted fiber `F_{q,a}` with
truncated length forces invariant `Φ` to zero on that fiber). stab = 1
uniform on all 19 records is **empirical, not structurally justified**.
The Wave 2 addendum §3.3 guard (`stab < L`) is satisfied; the stronger
promise (`stab = 1`) should not be promoted to a pre-commit.

---

## §6. P5 — Scalar-feature regression

Features: `(n, L, log(prod), n_binary, n_ternary, n_≥4)`. Target:
feasibility indicator.

| metric | value |
|---|---|
| R² (linear) | **0.809** |
| threshold accuracy (pred ≥ 0.5 → feasible) | **1.0** |
| n records | 25 |

### 6.1 Interpretation

R² in [0.8, 0.95] = "mixed" per plan §6.3. **BUT** threshold accuracy
= 1.0: the linear classifier correctly separates every record. That's
stronger than R² suggests because linear regression optimizes MSE not
classification loss; a logistic regression would likely give pseudo-R²
> 0.95 on the same data.

The **effective** read: scalar features linearly separate feasibility
outcomes at this corpus. This is a characteristic of scenario (b):
"the LB factors through arithmetic, not through topology."

### 6.2 Decision branch

Plan §6.3 says 0.8 ≤ R² < 0.95 → "Green-light C3 with flag. Run C3
and arithmetic route in parallel." But with P2 RED (no C3 balance
identity available) and threshold acc = 1.0 (arithmetic separation
is perfect at this corpus), the sensible pivot is:

**Scenario (b) is the dominant explanation.** The arithmetic route
becomes primary; circulation becomes the discovery mechanism.

### 6.3 What the coefficients say

`beta = [bias, n, L, log(prod), n_bin, n_ter, n_≥4]`
(values: see `phaseW3_results.json`; large-magnitude features
dominate). A manual inspection of which features carry the separation
would identify the candidate arithmetic inequality — out of Wave 3
scope. Recommended as Wave 4 Priority 1.

---

## §7. P6 — Coverage correlation CI

- Point estimate: `cor(feasible, coverage) = 0.496`
- 95% bootstrap CI (1000 resamples): `[0.243, 0.710]`
- n = 25

CI straddles 0.3. Per plan §7.3: "escalate corpus to ≥ 100 records."

**But** the correlation is driven by class structure: all 6
at-threshold records have low coverage (ternary-strip, lots of
configs per cycle step), all are infeasible; sub-threshold records
have high coverage, all feasible. So the correlation reflects
class separation, which is exactly what P5 captured directly.

**Residualization (plan §0.4 protocol).** After regressing feasibility
on coverage and taking residuals, the discrimination sub-vs-at is
*still* perfect (because P5's linear model on scalar features without
coverage also gives acc = 1.0 — coverage is redundant with the
composition features). So coverage-inversion risk is present but
doesn't flip any decision: the arithmetic signal survives.

---

## §8. P7 — Probe perturbation (PASS)

Three edge-definition variants (v2a drain-to-good, v2b value-
inconsistent, v2c Hamming≥2) re-run on 5 sub + 6 at records.

**0/11 records flipped feasibility across all variants.** Route is
robust to this class of edge-definition perturbation.

### 8.1 What this clears

The meta-concern from Wave 2 — that the one-edge-per-vertex bug
flipping 11/18 records indicated probe sensitivity — is addressed.
v2a/v2b/v2c differ from v2 by deliberate semantic expansions, and
none flip. The remaining risk is in **which edges v2 excludes**, not
in **which edges v2 includes**.

### 8.2 What this does not clear

A pathological edge definition tailored to flip results could exist.
The three tested variants are "natural" expansions that any careful
reader would consider; they are not adversarial.

---

## §9. Aggregate Wave 3 verdict and recommendation

### 9.1 Gate matrix row

| P1 | P2 | P5 | P7 | Row in plan §9.1 |
|---|---|---|---|---|
| SURVIVES | **RED** | 0.8 ≤ R² < 0.95, acc=1 | PASS | "Stop at YELLOW. C1 is real but there's no balance identity to prove; C3 is unreachable. Route ships as empirical observation only." |

### 9.2 Nuanced verdict

- **C1 as an empirical LB-candidate discriminator**: SURVIVES at
  n=5..10, 19 sub + 6 at records. Infeasibility at at-threshold is
  robust across edge-definition variants.
- **C3 as an analytical target**: BLOCKED. The plan's posited
  `(T, c_right, c_self, c_left)` decomposition does not produce a
  leading-order balance (P2 RED). A different decomposition might,
  but none was found in Wave 3.
- **Scenario (b) arithmetic pivot**: STRONGLY INDICATED. R²=0.809
  with 100% threshold accuracy on 6-feature scalar regression.

### 9.3 Recommended Wave 4 structure

**Priority 1.** Extract the arithmetic inequality from P5's regression
coefficients. Specifically: solve for a closed-form inequality
`f(n, L, prod, #binaries, #ternaries, #≥4) ≤ 0` that is satisfied
exactly by the feasibility pattern. If such an inequality is
Lean-tractable, it becomes the candidate arithmetic LB.

**Priority 2.** Attempt alternative P2 decompositions on the existing
corpus — in particular cycle-direction-covariant versions that merge
c_right and c_left (the P3 finding suggests these are mirror images).
If a cleaner balance identity emerges on the new decomposition, the
C3 route reopens. Budget: 1 day.

**Priority 3.** Expand corpus to n=11..14 at at-threshold via v2 CLB
builder, and verify P1 discrimination continues. Budget: 1 day.

### 9.4 What should NOT happen next

- No C3 attempt on the `(T, c_right, c_self, c_left)` decomposition.
  The plan's balance identity does not hold.
- No A1' dichotomy Lean work. Per Wave 2 §3.6, gated on C2 YELLOW
  which is now firmly RED.
- No 1898-record expansion yet. The decision that matters (pivot
  to arithmetic vs retry C2 on different decomposition) is
  determined by Wave 4 Priority 1 + 2 at the current corpus size.

### 9.5 Revised risk estimate

Prior (Wave 3 start): 60/40 circulation-correct vs C3-eats-campaign.

Posterior (Wave 3 end):
- **C3 on plan's decomposition**: ~0/100. RED by empirical test.
- **C3 on alternative decomposition**: ~25/75 (unknown; Priority 2 tests).
- **Arithmetic pivot**: ~70/30 probability of closing a Lean-tractable LB,
  contingent on Wave 4 Priority 1 succeeding.

The circulation program has **succeeded as a discovery mechanism**:
it surfaced a scalar-arithmetic separation that probably IS the
mechanism. The analytical C3 target dies, but the research direction
it opened survives as an arithmetic inequality hunt.

---

## §10. Honest caveats

- **Sub-threshold corpus is classes 1 and 2 only.** Classes 3, 4, 5 are
  structurally empty at strict sub-threshold. The composition-confound
  check is therefore partial: pure-binary-only confound does not fire
  (both classes 1 and 2 are uniformly feasible), but more complex
  composition dependencies are untested.

- **Corpus size 25 is thin for regression CI.** R² = 0.809 at n=25
  has wide confidence intervals. A corpus doubling would tighten the
  bound. Recommended as Wave 4 cheap check.

- **P3 reverse-cycle test: 2 of 3 records show `other` edges appearing
  under reversal.** These are not accounted for in the original
  (forward) edge classification. Suggests the classify_type function
  may be missing cases; a follow-up audit of classify_type is
  warranted before promoting the c_right/c_left merge as a clean
  direction-covariant coordinate.

- **P4 stab=1 argument is partial.** Stab < L is structurally argued;
  stab = 1 uniform is empirical only.

- **P7 tests 3 variants, not exhaustive.** A v2d "include diagonal
  Hamming-1 lifts" or v2e "include multi-fire edges" could give
  different answers. The specific three tested are the natural
  deliberate expansions; not a full robustness proof.

---

*End of Wave 3 consolidation.*
