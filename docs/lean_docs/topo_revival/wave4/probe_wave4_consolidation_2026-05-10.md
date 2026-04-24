# Wave 4 consolidation — dispositive test + arithmetic pivot

**Date.** 2026-05-03 (stopping on verdict, well inside the Week-1 budget).
**Artifacts.**
- [`probe_wave4_combined_2026-05-03.py`](probe_wave4_combined_2026-05-03.py)
- [`phaseW4_results.json`](phaseW4_results.json)

**Companion plans.** [`probe_plan_wave4_2026-05-03.md`](probe_plan_wave4_2026-05-03.md).

---

## §0. Headline

**P0 dispositive PASSES: circulation discrimination survives at 3-binary
at-threshold.** Binary count alone is not the separator.

**But:**
- **P1 (direction-covariant decomposition): RED.** Residual 2.7% > 1% target.
- **P2 (arithmetic regression on expanded corpus): Case B-ish.**
  Best scalar separator is `∏m ≥ M_n` itself — tautological.
- **P0.5 (classify_type audit): CLEAN.** 0/4795 forward-direction edges
  fall in `other_*` buckets. Wave 3 numerics stand.

Per plan §7.1 decision matrix: row `P0=A, P1=C, P2=B/C` →
**"Arithmetic pivot fails. Return to §9."**

The circulation captures a real signal (confirmed by P0) but neither
the balance-identity route (P1) nor the arithmetic-inequality route
(P2) extracts it into a ship-ready form on this corpus with these
tools. The route ends at **validated-as-detector, unshipped-as-LB-mechanism**.

---

## §1. P0 — Small-n witness dispositive test (PASSES)

### 1.1 The 4 witnesses

All loaded from `docs/verify_witnesses.py`, all pass `verify_system`:

| n | ms | product | L | n_bin | n_ter | n_≥4 |
|---|---|---|---|---|---|---|
| 5 | (2,2,2,3,4) | 96 | 18 | 3 | 1 | 1 |
| 6 | (2,2,2,4,3,3) | 288 | 35 | 3 | 2 | 1 |
| 7 | (3,2,2,2,3,4,3) | 864 | 52 | 3 | 3 | 1 |
| 8 | (2,2,3,4,3,3,2,3) | 2592 | 55 | 3 | 4 | 1 |

All are at the **sharp small-n threshold** `32·3^(n-4)` = M_n. All
have exactly **3 binaries + 1 quaternary** + ternary fill (class 4).

### 1.2 Result

**4/4 INFEASIBLE** in the Wave 2 v2 C1 probe. All zero support, all
zero feasibility objective. Case A of plan §1.3 fires.

### 1.3 What this rules out

The scenario (b) interpretation from Wave 3: "the separator is
`# binaries ≥ 3`, which perfectly tracks feasibility on that corpus."

Wave 4 corpus now has **3-binary records in both the feasible and
infeasible classes**:
- Sub-threshold 3-binary multisets: feasible (many records in
  original 19).
- Small-n witnesses (3-binary at-threshold): **infeasible**.

`# binaries` alone cannot distinguish these. On the 29-record Wave 4
corpus, the `n_bin ≥ 3` classifier achieves 86.2% accuracy (4 errors),
not 100%. The Wave 3 regression's apparent 100% was a **sampling
artifact**: the 3-binary class was populated only from the feasible
(sub-threshold) side.

### 1.4 What this confirms

C1 captures an obstruction that is **not reducible to `n_bin`**.
Circulation infeasibility distinguishes valid self-stabilizing systems
from sub-threshold cycles even when binary count is held fixed at 3.
This is a real structural signal.

---

## §2. P0.5 — classify_type audit (CLEAN)

Instrumented classifier with `other[rel_mov, rel_fire]` logging across
all 29 records (sub + CLB at + small-n at).

**Result: 0 out of 4795 edges in `other_*` buckets.** The 4-type
partition `(transport, c_self, c_left, c_right)` is complete in
forward direction for every record tested.

The Wave 3 consolidation §10 caveat 3 ("2/3 reverse-cycle records
show `other` edges") is confirmed as a **reverse-cycle-only
phenomenon**, not a forward-direction classifier bug. The reversed
dynamics produce edges not present in the forward direction; the
classifier's silence on those edges reflects the reversed cycle's
different forced-NG structure, not a misclassification.

Wave 3 P2, P3, P5 numerics stand. No re-run needed.

---

## §3. P1 — Direction-covariant decomposition (RED)

Merging `W_sided = W_left + W_right`, testing `|T(v) + W_sided(v)| / |T(v)| < 0.01`.

### 3.1 Per-record residuals on 19 feasible sub records

| ms | L | |T+W_sided|/|T| | |W_self|/|T+W_sided| |
|---|---|---|---|
| (2,2,2,2,2) | 10 | 0.000 | 0.000 |
| (2,2,2,2,4) | 10 | 0.000 | 0.000 |
| (2,2,2,3,2) | 14 | 0.000 | 0.000 |
| (2,2,2,4,2) | 14 | 0.000 | 0.000 |
| (2,2,3,2,2) | 14 | 0.000 | 0.000 |
| (2,2,3,3,2) | 16 | **0.167** | 2.000 |
| (2,2,5,2,2) | 18 | **0.167** | 2.000 |
| (2,3,2,2,3) | 14 | 0.000 | 0.000 |
| (2,2,2,2,2,2) | 12 | 0.000 | 0.000 |
| (2,2,2,2,6,2) | 20 | 0.000 | 0.000 |
| (2,2,2,5,2,2) | 20 | 0.000 | 0.000 |
| (2,2,3,3,3,2) | 22 | **0.100** | 2.000 |
| (2,3,3,2,3,2) | 22 | **0.083** | 4.000 |
| (2,5,2,3,2,2) | 21 | 0.000 | 0.000 |
| (3,2,2,4,2,2) | 17 | 0.000 | 0.000 |
| (2,2,2,2,2,2,2) | 14 | 0.000 | 0.000 |
| (2,3,2,2,5,2,3) | 17 | 0.000 | 0.000 |
| (2,4,2,3,2,2,3) | 17 | 0.000 | 0.000 |
| (3,2,2,2,2,3,4) | 16 | 0.000 | 0.000 |

- **Mean `|T + W_sided| / |T| = 0.0272`** (2.72%). Plan §3.3 threshold is <0.01 → **FAIL**.
- **Mean `|W_self| / |T + W_sided| = 0.5263`** (52.6%). `c_self` is more than half of the sided balance — NOT a subleading correction.

### 3.2 What this kills

Plan §3.3 Case A/B (clean 2-way or 3-way balance) does NOT fire.
Plan §3.3 Case C fires: "residual > 1% even in direction-covariant
coordinates → no clean balance identity exists on this corpus."

The residual is concentrated on records with ms structure `(…, 3, 3, …)`
— consecutive ternaries produce nontrivial `c_self` weight that
doesn't cancel via direction merging.

### 3.3 Improvement over Wave 3 original

Wave 3 P2 (original 4-type decomposition): 4.9% mean leading residual.
Wave 4 P1 (direction-covariant 3-type): 2.72%.

**Factor of ~1.8 improvement**, but still 2.7× the plan threshold.
Merging c_left + c_right accounts for about half the residual; the
other half is c_self, which is structurally distinct from transport
and cannot be absorbed into a 2-type decomposition.

### 3.4 Implication for C3

C3 on **both** the original 4-type and the direction-covariant 3-type
decompositions is structurally unreachable — neither admits a clean
leading-order balance on this corpus. A 3-way identity `T + W_sided +
W_self = 0` holds trivially (LP feasibility), but is not "leading-
order-plus-subleading" — all three terms are comparable.

A future attempt would need a **4-way or higher** decomposition that
privileges a different axis than the mover-defect-position geometry.
None is currently proposed.

---

## §4. P2+P3 — Arithmetic extraction on expanded corpus

### 4.1 Corpus

29 records:
- Sub-threshold: 19 (all feasible)
- At-threshold CLB ternary-strip: 6 (all infeasible)
- At-threshold small-n witnesses (class 4): 4 (all infeasible)

### 4.2 Tautology check: `n_bin ≥ 3` classifier

**Accuracy on 29 records: 86.2%** (4 errors). Not a tautology on the
expanded corpus (it was on Wave 3's 25-record). The 4 errors are the
4 small-n witnesses: `n_bin = 3`, infeasible, misclassified by the
`n_bin ≥ 3 → feasible` rule.

This is the dispositive fact P0 was designed to surface. Confirmed.

### 4.3 Richer 10-feature linear regression

Features: `(n, L, log(prod), n_bin, n_ter, n_≥4, longest_bin_run,
lcm_non_bin_seg, mover_var, longest_mov_run)`.

| metric | value |
|---|---|
| R² (linear) | 0.789 |
| in-sample threshold acc | 0.966 (1 err) |
| leave-one-out acc | 0.931 (2 err) |

Top features by |β|:

| feature | β | interpretation |
|---|---|---|
| bias | +0.905 | |
| log_prod | +0.830 | paradoxical sign; reflects interaction with n |
| n_≥4 | -0.562 | quaternary → infeasible (small-n witnesses) |
| n | -0.561 | larger n → infeasible (CLB) |
| n_bin | +0.451 | more binaries → feasible (sub records) |
| n_ter | -0.449 | more ternaries → infeasible |
| longest_bin_run | -0.393 | longer binary block → infeasible |

### 4.4 Which case fires?

Plan §4.4:
- Case A: simple closed form, 100% acc, not tautological → **NO** (acc 96.6% in-sample, 93.1% LOO, not 100%).
- Case B: closed form IS `∏m ≥ M_n` → **effectively YES**. The linear
  regression is approximating `log(M_n(n)) - log(prod)`, which is the
  threshold condition. The nonlinear M_n(n) (piecewise: `32·3^(n-4)`
  for n ≤ 8 vs `4·3^(n-2)` for n ≥ 9) cannot be represented exactly
  by linear in (n, log_prod), explaining the 6.9% LOO error.
- Case C: no simple closed form separates with 100% → **also YES in
  spirit.** No feature combination tested achieves 100%.

### 4.5 The consequence

The "arithmetic inequality" the circulation route empirically
discovers is **the threshold condition itself**. Extracting it as a
"new LB" would be circular — we'd be proving `∏m < M_n → ¬converges`
by an argument that assumes knowledge of M_n.

This matches Wave 2 addendum §4.2 scenario (b)'s failure mode:
"the LB factors through arithmetic" but the arithmetic IS the
threshold, not an independent mechanism.

### 4.6 The 1 in-sample error

One record is misclassified by the richer regression even in-sample.
Which one? The model gives `yhat < 0.5` for one sub-threshold record
or `yhat ≥ 0.5` for one at-threshold record. Likely candidates (by
distance-from-threshold): a sub-threshold record with very high
log(prod) close to M_n, or a small-n witness with low n and n_≥4=1
that the model's coefficients don't cleanly handle. Not investigated
further — not decision-relevant.

---

## §5. P4 — ARG relationship check (SKIPPED)

Plan §6: P4 is gated on P2 Case A (clean closed-form not tautological).
P2 fired Case B/C (tautological / no clean form). **P4 is moot.**

The circulation route did not produce a candidate inequality to compare
to ARG 1985. If it had, and the inequality had been `∏m < M_n`, that
IS ARG's conjecture at the quantitative level — so the comparison
would have been Case (b) "equivalent to ARG, empirical validation
only." Given we never got a candidate inequality, we can't even claim
empirical validation.

---

## §6. Aggregate Wave 4 verdict

### 6.1 Decision matrix row (plan §7.1)

| P0 | P1 | P2 | P4 | Row verdict |
|---|---|---|---|---|
| A | C | B/C | — | **Arithmetic pivot fails.** Return to §9. |

### 6.2 What the route accomplished

The circulation program produced three real outcomes over Waves 2–4:

1. **Lean threshold bug fix** (Wave 2 Priority 0). The overbroad
   `peelTube_nonempty` statement was refuted by small-n witnesses and
   is now split into the correct piecewise form. Build green.

2. **Empirical detector** (Waves 2–4). The lifted-defect circulation LP
   is a 100% accurate feasibility/infeasibility detector for the
   self-stabilizing property on the 29-record corpus (19 sub feasible,
   10 at infeasible). This is a concrete discovery.

3. **Negative result on the structural proof routes**. Neither the
   original decomposition (Wave 3 P2), nor the direction-covariant
   decomposition (Wave 4 P1), nor the scalar-arithmetic separator
   (Wave 3 P5 → Wave 4 P2) produce a ship-ready LB mechanism. This
   is a negative but non-trivial result: it says the circulation
   detector's signal lives in a more complex object than any of the
   tested forms.

### 6.3 What the route did not accomplish

- No new LB proof.
- No Lean-tractable analytical target.
- No strengthening of ARG's 1985 conjecture.
- No discovery of a novel feature that separates self-stabilizing
  systems from sub-threshold non-systems other than the threshold
  condition itself.

### 6.4 Status of the program per Keston's priorities

Per `feedback_topological_invariant_proof_shape.md`: Keston's imagined
proof shape is "a topological invariant forbids it." The circulation
route was the closest Wave 1–4 candidate to that shape (it is a
flow-theoretic invariant of forced-NG). **The flow-theoretic signal
IS a topological-flavored invariant, but the route to turn it into a
proof fails.**

Per `feedback_no_ship_with_sorries.md`: nothing ships. Consistent with
Wave 4 outcome.

Per `feedback_no_case_splits_in_lean.md`: no case-split Lean work
proposed. Consistent.

---

## §7. Recommended next moves

### 7.1 Immediate (Wave 5 or campaign retirement)

Per plan §7.1 "Return to §9" and `lb_all_paths_history.md §9`:

- **Option γ (campaign retire):** Formalize the circulation route's
  negative result in a named memo, file the probe scripts, update
  `lb_all_paths_history.md` §9 with the Wave 2–4 summary. The route
  retires as a detector-without-mechanism, alongside SKMH and twist-
  calculus.
- **Option δ (parking):** Keep the scripts and corpus around; revisit
  if a new structural idea surfaces that could turn the LP support
  structure into a proof. Specifically: a **tropical / idempotent**
  decomposition of the LP (working over `(ℝ, max, +)` instead of
  `(ℝ, +, ·)`) might expose the separator that linear regression
  cannot see. Not in current scope.

### 7.2 What to SHIP as byproducts

- **The threshold bug fix in Lean** (already shipped in Wave 2; survives).
- **The 29-record empirical detector** (can appear in a supplementary
  results section of any future M_n paper: "we observe a 100%-accurate
  LP-based detector on n ∈ {5..10}; the mechanism is unknown").
- **Wave 3 + Wave 4 negative results** — document which specific
  decompositions and feature families fail. Saves a future researcher
  from retrying identical moves.

### 7.3 What NOT to do

- **Do not claim an LB proof** based on circulation. The tested
  extraction routes all fail.
- **Do not attempt C3 analytical work.** Plan §7.1 says arithmetic
  pivot fails; the C3 analytical target was conditional on one of
  P1 or P2 surviving.
- **Do not pursue Wave 1 P7 (sheaf H¹) or P8 (Conley)** as immediate
  follow-ups. They are independent tracks and their priors have not
  been updated by Wave 4. Revisit only if a genuinely new idea
  surfaces.
- **Do not continue expanding corpus.** 29 records is sufficient for
  the negative verdict; 1898-record expansion would consume budget
  without changing the verdict (it would tighten CIs on the negative
  result but not produce a new positive).

---

## §8. Honest caveats

- **Wave 3 posterior was 70/30 arithmetic-pivot-works. Wave 4
  posterior is 0/100 on that pivot.** That's a big swing driven by
  P0 dispositive + P2 tautology-bound failure. Calibrating: my prior
  underestimated the "scenario (b) is the threshold itself" outcome
  by ~70 percentage points.

- **"Validated as detector" is not trivial.** The circulation LP
  achieves 100% accuracy separating valid from sub-threshold. This
  is a detector we did not have before. It could be useful for
  **search** (finding or ruling out candidate witnesses at n=11+)
  even though it does not ship as a proof.

- **The 2.7% residual on P1 direction-covariant could be reduced by
  a 4-way+ decomposition.** Not attempted. If a future session
  finds a geometrically-motivated 4-type refinement where c_self
  splits into sub-types that cancel against specific transport
  classes, the residual might drop to <1%. Low prior.

- **R² = 0.789 on richer regression could be lifted by interactions.**
  Adding `n × n_bin`, `log_prod × n_ter`, etc. might push R² above
  0.95 without needing the threshold formula explicitly. Not
  attempted in this pass. If it worked, we'd still be in Case B
  (the closed form would still be equivalent to `∏m < M_n` after
  algebraic manipulation), just obfuscated.

- **29 records is modest.** A 100-record corpus might surface a
  feasibility-class exception (sub-threshold infeasible or at-threshold
  feasible), which would change P0's verdict. Low prior given the
  theoretical argument that the LP is measuring a threshold-sensitive
  property.

---

## §9. One-line summary

**Circulation route status: validated-as-detector, dead-as-LB-mechanism.**
The probe stops here. The Lean threshold fix stays in place, the
empirical detector is worth keeping as a probe tool, and Wave 5 (if any)
should explore a different structural family — not further
decompositions or arithmetic features on this corpus.

---

*End of Wave 4 consolidation.*
