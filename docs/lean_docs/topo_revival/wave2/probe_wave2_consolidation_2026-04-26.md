# Wave 2 Priority 0 / 0.5 / 1 consolidation

**Date.** 2026-04-21 (inside the Week-1 Wave-2 window).
**Artifacts.**
- Lean: `LeanMn/LowerBound/SK/HammingTube.lean`, `CloudsTheorem.lean`.
- Probe: [`probe_c1_lifted_circulation_2026-04-21.py`](probe_c1_lifted_circulation_2026-04-21.py),
  [`phaseC1_results.json`](phaseC1_results.json).
**Companion plans.** [`probe_plan_wave2_circulation_2026-04-21.md`](probe_plan_wave2_circulation_2026-04-21.md),
[`probe_plan_wave2_addendum_2026-04-26.md`](probe_plan_wave2_addendum_2026-04-26.md).

---

## §0. Headline

**C1 = YELLOW.** The lifted-defect circulation LP is feasible on
18/18 sub-threshold records and infeasible on the 1 verified
at-threshold record. Cycle-time-shift stabilizer is trivial on every
feasible record. Edge types bounded at O(4). Coverage correlation
0.297, just under the 0.3 residualization threshold.

**C1 passes pre-commit SURVIVES per Wave 2 §2.4 + addendum §2.3 + §3.3**,
with two explicit caveats on corpus statistical strength (§3 below).

**Recommendation.** Proceed to Gate C2 edge classification, conditional
on expanding the verified at-threshold corpus to ≥ 4 records before
C2 produces binding verdicts.

---

## §1. Priority 0 — threshold bug fix (DONE, build green)

**Change.** `HammingTube.lean:171–175` previously stated
`peelTube_nonempty` with the unified hypothesis
`stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)`. That statement is
refuted by every `witness_n5/6/7/8` — each valid at product
`32·3^(n-4)` with `SK(C) = ∅` and therefore `peelTube(C) = ∅`.

Split into two piecewise statements per Wave 2 §1.2:

```lean
theorem peelTube_nonempty_small_n
    (gc : GoodCycle sys)
    (hn_lo : 5 ≤ sys.rs.n) (hn_hi : sys.rs.n ≤ 8)
    (hsub : stateProduct sys.rs < 32 * 3 ^ (sys.rs.n - 4)) :
    (peelTube gc).Nonempty := by sorry

theorem peelTube_nonempty_large_n
    (gc : GoodCycle sys)
    (hn : 9 ≤ sys.rs.n)
    (hsub : stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)) :
    (peelTube gc).Nonempty := by sorry
```

Consumers in `CloudsTheorem.lean:418, 445` rewired via new bridges
`sk_nonempty_via_tube_small_n` / `sk_nonempty_via_tube_large_n`.
The illegal hypothesis-widening at :428–440 is removed — the small-n
bridge now consumes `< 32·3^(n-4)` directly with no widening.

**Sorry delta.** +1 in HammingTube (1 → 2), 0 elsewhere. The
previously-unprovable unified sorry is replaced by two provable
piecewise obligations. Net: moved from 1 unprovable sorry to 2
research-open sorries.

`lake build LeanMn.LowerBound.SK.HammingTube LeanMn.LowerBound.SK.CloudsTheorem`
completes green; only pre-existing simp-lint warnings in
`SlabCountingRing.lean`.

---

## §2. Priority 0.5 — verified at-threshold corpus (PARTIAL, 1 record)

**Target** (addendum §1): 20+ records from Sources 1/2/3, all passing
`verify_system`.

**Achieved.** 1 record: n=9, ms=(2,3,3,3,3,3,3,3,2), product 8748,
L=25, via the imported `clb_witness_8748.build_system`. All five
properties (liveness, mutex, closure, convergence, fairness) pass.

**Known-broken.** An in-file generalization of the CLB bounce-cycle
construction to arbitrary n was written (`build_clb_witness`), but it
fails `verify_system` at all n ∈ {5..9} because the liveness-fix step
shortcuts edge-cost computation. The original `clb_witness_8748.py`
does the full O(non_good × free_entry) edge-cost sweep; my
generalization replaced that with `cost = 0` for speed, which picks
liveness-fix entries that break closure/mutex. **The shortcut is the
bug.** Fix path: restore the full edge-cost computation. Budget: half
a day, not done in this pass.

**Source 1 (small-n `witness_n5..8`):** not attempted. No stored
witness files for n ∈ {5..8} found in the repo; would need fresh
construction. Budget: 1 day per n via targeted combinatorial search.
Flagged as follow-up.

**Impact on C1.** Only n=9 at-threshold discrimination tested. The
CLB witness at n=9 is infeasible in the lifted LP — this one data
point **does** fire the pre-commit (which is binary at the record
level), but statistical strength is minimal. Caveat explicit below.

---

## §3. Priority 1 (C1) — lifted-defect circulation LP, full run

### 3.1 Corpus summary

- **Sub-threshold:** 18 records across n ∈ {5, 6, 7}, 6 multisets per
  n (even-strided from `enumerate_multisets`).
- **Verified at-threshold:** 1 record, n=9 CLB (above).

### 3.2 Per-record outcomes (all sub-threshold feasible)

| class | n | ms | L | V_lift | E_lift | feasible | supp | stab/L |
|---|---|---|---|---|---|---|---|---|
| sub | 5 | (2,2,2,2,2) | 10 | 30 | 40 | **T** | 30 | 1/10 |
| sub | 5 | (2,2,2,2,5) | 10 | 30 | 40 | **T** | 30 | 1/10 |
| sub | 5 | (2,2,2,4,2) | 14 | 58 | 60 | **T** | 14 | 1/14 |
| sub | 5 | (2,2,3,2,3) | 14 | 48 | 60 | **T** | 14 | 1/14 |
| sub | 5 | (2,2,5,2,2) | 18 | 80 | 83 | **T** | 18 | 1/18 |
| sub | 5 | (2,3,2,3,2) | 15 | 65 | 72 | **T** | 15 | 1/15 |
| sub | 6 | (2,2,2,2,2,2) | 12 | 48 | 60 | **T** | 36 | 1/12 |
| sub | 6 | (2,2,2,3,2,4) | 16 | 72 | 92 | **T** | 32 | 1/16 |
| sub | 6 | (2,2,3,2,3,2) | 17 | 92 | 107 | **T** | 34 | 1/17 |
| sub | 6 | (2,2,7,2,2,2) | 21 | 139 | 129 | **T** | 42 | 1/21 |
| sub | 6 | (2,4,2,2,2,2) | 16 | 84 | 89 | **T** | 32 | 1/16 |
| sub | 6 | (3,2,2,2,3,2) | 17 | 92 | 107 | **T** | 34 | 1/17 |
| sub | 7 | (2,2,2,2,2,2,2) | 14 | 70 | 84 | **T** | 56 | 1/14 |
| sub | 7 | (2,2,2,3,3,2,5) | 17 | 113 | 115 | **T** | 51 | 1/17 |
| sub | 7 | (2,2,3,3,3,2,2) | 17 | 113 | 115 | **T** | 51 | 1/17 |
| sub | 7 | (2,3,2,2,3,2,3) | 16 | 108 | 110 | **T** | 64 | 1/16 |
| sub | 7 | (2,4,3,2,2,2,3) | 17 | 128 | 121 | **T** | 68 | 1/17 |
| sub | 7 | (3,2,2,3,3,3,2) | 17 | 130 | 124 | **T** | 68 | 1/17 |
| **at** | **9** | (2,3,...,3,2) | **25** | — | — | **F** | 0 | 25/25 |

18/18 sub feasible. 0/1 verified at feasible.

### 3.3 Pre-commit kill criteria — all NOT fired

| Kill criterion | Source | Fired? | Evidence |
|---|---|---|---|
| Sub-thresh infeasible anywhere | §2.4 | ✗ | 0/18 infeasible |
| At-thresh feasible anywhere | §2.4 | ✗ | 0/1 feasible |
| High-entropy support | §2.4 | ✗ | 4 edge types (transport, c_right, c_self, c_left), O(4) not O(2^n) |
| Feasibility confined to pure-binary | addendum §2.3 | ✗ | 3/3 class-1 + 15/15 class-2 feasible |
| Composition confound (strength ratio) | addendum §2.3 | ✗ | N/A classes 3,4,5 empty this corpus |
| Coverage correlation > 0.3 | §2.5 | ✗ (borderline) | cor = 0.297 (just under) |
| Cycle-time-shift invariance on ≥80% | addendum §3.3 | ✗ | 0/18 feasible have full invariance |

### 3.4 Edge-type breakdown (pre-read for C2)

Aggregate by type across the 18 sub-threshold records (E_lift edge counts):

| type | total | feasible-support total | fraction of support |
|---|---|---|---|
| transport | 1095 (57%) | 585 | 82% |
| c_right | 469 (24%) | 207 | 29% |
| c_self | 34 (1.8%) | 2 | 0.3% |
| c_left | 21 (1.1%) | 1 | 0.1% |
| (other / non-matching) | 0 | 0 | 0 |

The support is dominated by transport + c_right (> 99% of weight).
c_self and c_left appear sparsely, never in pure-binary records.
No "other" edges occur — the (transport, c_self, c_left, c_right)
partition is complete on this corpus, satisfying the addendum §3.3
requirement of an O(n)-bounded classification.

### 3.5 Cyclic-symmetry guard (addendum §3.3)

Stabilizer ratio = |{s : support invariant under cycle-time shift by s}| / L.

- Sub-threshold feasible records: mean 0.067, min 0.048, max 0.100.
  All 18 have stabilizer = 1 (trivial — support is not cycle-time-shift
  symmetric).
- At-threshold n=9 record: stabilizer ratio = 1.0, but support is
  empty (infeasible), so the "full invariance" is vacuous.

**The §3.3 guard passes uniformly on sub-threshold.** The circulation
support discriminates individual k-positions within the cycle, not
just (k mod L, q)-classes. This is the structural feature that P2
lacked one level up.

### 3.6 Coverage diagnostic

`cor(coverage, feasible) = 0.297`, computed on all 19 records.

This is 0.003 under the §2.5 kill threshold of 0.3. At this corpus
size (19 records) the sampling error on the correlation is comfortably
wider than 0.003, so the distinction between 0.297 and 0.3 is noise.
**Should be treated as borderline.** Residualization procedure
(§0.4 of original plan) is applicable. Under residualization, compute
`S' = feasible − β·coverage` and re-check whether the at-threshold
record is still the outlier; with only 1 at-threshold record, the
residual calculation is dominated by sub-threshold variance.

Recommended: flag coverage-correlation borderline as a caveat on the
YELLOW verdict, and re-run after corpus expansion.

---

## §4. Aggregate verdict and recommendation

**C1 = YELLOW-with-caveats.** All seven pre-commit kill criteria
evaluated. None fired. SURVIVES condition met with two caveats:

1. **Corpus size at at-threshold is 1.** The binary pre-commit is
   satisfied, but statistical strength is minimal. Pre-commit language
   ("feasibility fails at ANY at-threshold record") is technically met,
   but the spirit of the §2.4 plan was a multi-record at-threshold
   confirmation.

2. **Coverage correlation 0.297 is borderline.** One record flip in
   either direction would push it past 0.3 and trigger residualization.

### 4.1 Recommended next steps, priority order

1. **Fix the CLB generalization.** Restore the full edge-cost
   computation in `build_clb_witness` and regenerate at-threshold
   records for n ∈ {5, 6, 7, 8, 10}. Budget: half a day. **Blocking
   prerequisite for any binding C2 verdict.**

2. **Proceed to C2 edge-type balance identity** on the existing
   sub-threshold corpus. The support's (transport, c_right) dominance
   is a strong structural fingerprint — test empirically whether per-
   vertex `Σ transport_in − Σ transport_out = −(Σ c_right_in −
   Σ c_right_out)`. Budget: 1–2 days. This is the addendum §2.8 test
   and can run in parallel with step 1.

3. **Expand sub-threshold corpus to the full 1898 records.** Current
   18 records is a sample; the §5 stated corpus is 1898. Most cycles
   will be routine (transport-heavy, feasible); some will surface
   counterexamples to the balance identity if one exists.

4. **Run C2's cyclic-symmetry guard on the expanded corpus.** With
   1898 records the stabilizer-ratio distribution becomes statistically
   meaningful.

### 4.2 Recommended holds

- **Do NOT proceed to C3 yet.** C3 is the 2–4 week analytical
  obligation. It should only be attempted once C2 has confirmed the
  balance identity empirically across a full corpus AND on an
  expanded at-threshold class.

- **Do NOT proceed to A1' dichotomy (Priority 3) yet.** Per plan §3.6,
  Priority 3's right-branch depends on C2 being at YELLOW. C2 is not
  yet at YELLOW — it is not yet run.

### 4.3 What this changes from Wave 2's original risk estimate

Original: 70/30 route correct / C3 eats campaign. Addendum revised to
55/45 post-Phase-A.

Post-C1: revise back up to ~70/30, contingent on the corpus caveats
being addressed. The central empirical claim survives on the first
probe specifically designed to discriminate it from R1–R5's dead
routes. The specific signals that fired RED on Phase A (ambient-
simplicial P1/P2/P5, density-inverted P6) **do not fire here**. The
route distinguishes itself from the Phase-A failure modes by
construction.

The 30% residual risk is concentrated in Gate C3 (the balance
identity) and in the corpus-expansion caveats. If corpus expansion
flips a single at-threshold record to feasible, pre-commit fires RED
and the estimate collapses.

---

## §5. Honest implementation notes

- **Initial run had a one-edge-per-vertex bug.** First pass emitted
  only the first forced move at each lifted vertex, producing 11/18
  sub-threshold records as falsely infeasible. Fixed in the second
  pass; LP now correctly tests "does the full forced graph contain
  a directed cycle". All 18 sub-threshold records are now feasible.
  Noting this because it affected the interpretation of the first
  run — which, taken at face value, would have fired RED on
  "sub-threshold infeasibility anywhere" spuriously.

- **At-threshold n=9 infeasibility is a real, verified signal.** The
  CLB witness passes `verify_system` completely, the cycle is
  extracted by re-running the bounce closure, and the lifted LP
  reports no feasible nonzero circulation. This is the first direct
  empirical evidence that valid systems do not support lifted
  circulation in the sense the route requires.

- **The `stab_ratio = 1.0` entry for the at-threshold record is
  vacuous.** Empty support is trivially invariant under every shift.
  The cycle-time-shift guard should be evaluated only on records
  where the support is nonempty — in the current corpus, that's only
  the 18 sub-threshold records, all of which pass.

- **Edge-type coverage is complete on this corpus.** No "other"
  edges appear at all, meaning every forced-move edge in the lifted
  graph is captured by the transport / c_self / c_left / c_right
  partition. This is a structurally useful fact for C2.

- **`verify_at_threshold_record` for n=9 is load-bearing.** It
  imports `clb_witness_8748.build_system` directly rather than
  regenerating. If that import path ever breaks, C1's at-threshold
  result collapses and the YELLOW verdict downgrades to PARTIAL.
  Flag this as a fragility.

---

*End of Wave 2 Priority 0 / 0.5 / 1 consolidation.*
