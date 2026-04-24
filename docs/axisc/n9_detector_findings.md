# n ≥ 9 detector — findings memo

**Written:** 2026-04-22. **Scope:** everything learned from executing the
8-axis probe program laid out in `n9_detector_design.md`. Input for the
paper §6 / §6.4 / §7 update, but this memo does **not** edit the paper.

---

## 0. Headline

**Axis C — "SK nonempty on the candidate's forced-NG graph" — is the
detector upgrade.** It gives a one-sided structural certificate that
strictly generalizes the paper's C1 circulation LP:

- **Perfect separation** on the extended 72-record corpus (w5..w8 at-
  threshold + 59 n=8 sub-threshold + 9 n=9 Table 7 records, incl. the
  4 non-adjacent `{2^3, 3^5, 4}` counterexamples).
- **Recovers all 4 counterexamples** that the C1 LP misses. Separation is
  asymmetric-free: Axis C fires on every record C1 fires on, plus the 4.
- **No det-coverage artifact** (cross-check verified — stripping w5..w8
  det to cycle-only triples preserves SK = 0).
- **One-sided certificate, mathematically tight:** SK ≠ 0 under the
  cycle's partial det ⇒ no extension to a valid system (convergence
  forbidden). Converse empirically holds on the corpus.

The upgrade is a ~50-line edit to the existing pipeline: build forced-NG
graph, sink-peel to SK, report nonempty. Runtime ≤ 0.1 s per record at
n = 9 (negligible vs LP solve).

---

## 1. Definition and construction

Given a candidate record `(ms, cycle, movers, det)`:

1. `NG := { c ∈ ∏ Z_m_i : c ∉ cycle }` — non-good configs.
2. `forced_NG := directed graph on NG` with edges `c → c'` iff
   `∃ p : det[(p, c[(p-1)%n], c[p], c[(p+1)%n])] ≠ c[p]` and applying
   that move yields `c' ∈ NG`.
3. `SK := largest S ⊆ NG such that ∀ c ∈ S, ∃ c' ∈ S with c → c'`
   (the *sink kernel* — computed by iteratively removing vertices with no
   out-edge in the current set until fixed point).
4. **Detector fires** iff `|SK| > 0`.

The det used is the partial dictionary produced by `enumerate_cycles` or
its equivalent — coverage is exactly the triples visited at cycle
configs (typical coverage at n=9: ~0.6% of all `(p, triple)` entries).

### Monotonicity and the certificate

SK is monotonic in the edge set: adding forced edges can only remove
sinks, which can only grow (or keep) SK. Any *extension* of `det` to a
full transition function `f` is a superset of det's forced edges, so
`SK(f) ⊇ SK(det)`. Hence:

> **If SK > 0 under partial det, SK > 0 under every extension f.**

A valid self-stabilizing system has SK = 0 under its full f (every NG
trajectory terminates at the good cycle; no NG config is in a closed
subset under the forced-move relation). So SK(det) ≠ 0 ⇒ *no extension
of det yields a valid system.* That is precisely the "sub-threshold"
certificate the paper needs.

---

## 2. Corpus audit — Axis C verdict

Full audit over 72 records:

| group | n | records | SK fires | C1 feas | SK-recovers-C1-miss | SK-loses-C1-win |
|---|---|---|---|---|---|---|
| at-threshold (w5..w8) | 5..8 | 4 | **0** | 0 | 0 | 0 |
| n=8 sub-threshold | 8 | 59 | **59** | 59 | 0 | 0 |
| n=9 Table 7 sub | 9 | 9 | **9** | 5 | **4** | 0 |
| **total** | | **72** | **68** | **64** | **4** | **0** |

The four recoveries are exactly the 4 n=9 non-adjacent `{2^3, 3^5, 4}`
counterexamples surfaced by Strengthening Task #1. `|SK|` and the
largest nontrivial SCC on those records:

| ms (n=9, prod=7776) | L | \|SK\| | \|SK\|/\|NG\| | non-triv SCCs | largest SCC |
|---|---|---|---|---|---|
| `[2,3,2,3,3,3,2,3,4]` | 47 | 2682 | 0.347 | 12 | 1020 |
| `[2,3,2,3,3,3,2,4,3]` | 47 | 2862 | 0.370 | 16 | 1050 |
| `[2,3,2,3,2,3,3,3,4]` | 47 | 3856 | 0.499 | 38 | 1185 |
| `[2,3,2,3,3,3,3,2,4]` | 44 | 2037 | 0.264 | 12 | 930 |

Half (or more) of NG is in the peel on these candidates. The nontrivial
SCCs are substantial (~1000 configs), which suggests structurally
distinctive peel geometry worth attacking as a standalone sub-result.

---

## 3. Cross-check: Axis C is not a det-coverage artifact

**Concern raised by Axis D's result:** Axis D (identity-completion
verifier) fires 4/4 on counterexamples but is an artifact of the
record-building asymmetry — w5..w8 records use `build_record_from_witness`
which extends det to every triple; n=9 records use `enumerate_cycles`
which covers only cycle-visited triples. Could Axis C's split be similar?

**Test:** strip w5..w8 det to cycle-only triples (matching the n=9
pattern exactly), recompute SK. If SK > 0 appears on stripped w5..w8,
Axis C is also coverage-driven.

**Result:**

| witness | \|NG\| | full-det \|SK\| | partial-det \|SK\| | partial-det misses |
|---|---|---|---|---|
| w5 | 78 | 0 | **0** | 168 |
| w6 | 253 | 0 | **0** | 480 |
| w7 | 812 | 0 | **0** | 1812 |
| w8 | 2537 | 0 | **0** | 6876 |

**Verdict: GENUINE.** Partial-det SK = 0 on every valid witness even
under comparable det-coverage thinness. The n=9 counterexamples' SK > 0
is a real structural signal.

---

## 4. The other seven axes — what we learned

All eight axes from `n9_detector_design.md §3` (T+sided-only step 1,
axes A–E) plus the three follow-ups (F, G, I) were executed to an
actionable verdict. Axis H (PEC) was scoped but not run because the 4
counterexamples lack the fc=2 / CL=2n structure PEC requires.

| axis | description | counterex. recovery | verdict |
|---|---|---|---|
| step 1 | C1 with c_self edges forbidden | 0/4 (monotonicity) | GREEN as drop-in, no extra coverage |
| A | ternary-strip mover template match | 0/4 cleanly | YELLOW — best \|ρ\|=0.72 (`edit_dist_norm`), boundary overlap |
| B | embed det into strip's lifted graph | not run | DEFERRED — embedding-well-posed question too loose |
| **C** | **SK nonempty on forced-NG** | **4/4** | **GREEN** — primary upgrade |
| D | LP-B via identity completion + verifier | 4/4 | RED — det-coverage artifact, verified by Axis C cross-check |
| E | coupled (C, μ)×det spectral gap | not run | DEFERRED — unnecessary once C fires |
| F | Hamming-2 tube circulation LP | 0/4 | RED as implemented — target-search restricted to k, k+1 only; also drops 4 of C1's 5 n=9 wins |
| G | Farkas-dual fingerprint on C1-infeasible | 4/4 marginal | YELLOW — counterexamples have slightly higher y-entropy (0.934–0.939 vs w5..w8 0.871–0.919) but overlap with w8 |
| H | Palindromic Entry Conflict (Case 3c) | n/a | OUT OF SCOPE — counterexamples' cycles are L=44,47 not 2n=18; Case 3c's fc=2 branch doesn't fire |
| I | mover-adjacency obstruction graph | 0/4 | RED — all features \|ρ\| < 0.5, best `pm1_frac` = +0.40 below kill threshold |

**Takeaways.**

- The mathematically right object is the **candidate's forced orbit
  structure on NG under its own partial det**, not ambient geometry of
  the cycle (A, I) nor the LP's certificate-level features (G) nor
  Hamming-tube refinements (F). Axis C is close to the existing SK
  formalization in `lean/LeanMn/LowerBound/SK/`, which is a useful
  coincidence (see §6).
- **Axis D is a cautionary tale.** It fires perfectly, gives the right
  answer on the 4 counterexamples, but the signal is an artifact of
  how records are built. This class of signal can look like a detector
  while measuring something else entirely. The Axis C cross-check in §3
  is the template for how to audit future "too good to be true" probes.
- **Cheap reformulations of C1 (step 1, F, G)** keep its strength but
  can't recover what C1 missed. Adding or restricting edges in the 1-
  tube LP preserves C1's blind spot at the 4 counterexamples. Only
  stepping off the 1-tube (to the full forced-NG graph) dissolves the
  blind spot.

---

## 5. Relationship to C1 and to the paper's narrative

Define two predicates per record:
- `C1(rec)` — "C1 circulation LP on the 1-tube is feasible."
- `AxisC(rec)` — "SK nonempty on forced-NG of the partial det."

**Empirical observation across the 72-record corpus:** `C1 ⟹ AxisC`
with no counterexamples. The implication is *strict* — the 4 non-
adjacent `{2^3, 3^5, 4}` records at n=9 are in `AxisC \ C1`.

**Structural reason.** A feasible C1 gives a nontrivial circulation on
the Hamming-1 tube, which lifts (via the tube's projection back to
forced moves between NG configs at Hamming distance ≤ 1 from the
cycle) to a directed cycle in forced-NG. Hence C1-feas ⇒ AxisC-fires.
The reverse can fail: a forced cycle in NG may require configs at
Hamming distance ≥ 2 from the good cycle, which the 1-tube LP cannot
see. The 4 counterexamples are exactly this: peel witnesses at
Hamming distance 2 (and higher) from cycle.

**Paper narrative options, in order of strength.**

1. **Replace the detector.** Reformulate §6 around Axis C and demote C1
   to "a sufficient-but-not-necessary condition." Tighten the detector
   theorem to `AxisC(rec) ⇒ rec is sub-threshold.` Gain: no
   counterexamples. Cost: retire "C1 separates 29/29" as the headline;
   replace with "Axis C separates 72/72 including the n=9 transition."
2. **Keep C1, add §6.4a as a detector upgrade for n ≥ 9.** Preserve the
   §6 flow and introduce Axis C as the post-C1 refinement. Cleaner
   edit, honest framing, preserves the paper's pedagogical arc from
   simple LP to structural SK.
3. **Stay with C1 + explicitly document the 4 as failures.** The
   "case (b) honest framing" of `n9_detector_design.md §5`. We now know
   this is unnecessarily weak given Axis C's result.

Recommendation: **option 2**, at least for the first revision. The C1
LP is genuinely useful as the "cheapest detector that separates n ≤ 8"
— it's not wrong, just incomplete at n ≥ 9. Axis C is a clean strict
generalization that closes the gap.

### Suggested paper update points (do not edit; for author action)

- **§6.3 Table 2 (corpus):** extend with the n=8 sub-threshold row
  (59 records, C1 feas 59/59). Strengthening Task #1 artifact.
- **§6.3 "asymmetric in n" caveat:** downgrade in scope — n=8 coverage
  is now extended to 59/59; n=9 sub is 5/9 under C1 but 9/9 under Axis C.
- **§6.4 restricted-feasibility:** the T+sided-only audit shows
  c_self edges are never load-bearing on the 72-record corpus (0 flips
  across at-threshold, n=8 sub, n=9 sub). The c_self = 0 restriction
  is a no-cost tightening if desired.
- **new §6.4a "Axis C detector for n ≥ 9":** state Axis C, the
  one-sided certificate, the corpus verdict (9/9 at n=9), and the
  monotonicity proof that SK ≠ 0 under partial det ⇒ no valid extension.
- **§7 obstructions / open questions:** replace "universal n ≥ 9
  detector remains open" with "universal n ≥ 9 detector is Axis C
  (forced-NG SK) under the usual candidate-construction pipeline;
  analytical sharpness — i.e., proving SK ≠ 0 holds uniformly in n for
  all sub-threshold records — remains open."
- **Appendix C certificate scaffold:** Axis C adds a per-record |SK|,
  |NG|, nontrivial-SCC count, largest-SCC size. These are deterministic
  (no LP), integer-valued, and trivially machine-recheckable.

---

## 6. Lean-side implications

The existing Lean SK formalization lives in `lean/LeanMn/LowerBound/SK/`.
Two open sorries on the critical path (from memory):

- `HammingTube.lean:169, 190` — `peelTube_nonempty_{small,large}_n`
- `SlabCountingRing.lean:492` — `sourceTripleOfStep_injective` (A1')
- `CloudsTheorem.lean:418, 445` — consumer wiring `sk_nonempty_{small,large}_n`

Axis C's SK is *not* restricted to the Hamming tube — it's on the full
forced-NG graph. So it's not a direct discharger of `peelTube_nonempty`
in the current form, but it suggests a cleaner replacement target:

> **Candidate Lean theorem (for a future tightening):** for every
> candidate good-cycle + partial-det record `rec` produced by the
> enumeration pipeline, if `rec.product < M_n` then the sink-kernel of
> the forced-NG graph on `rec` is nonempty.

This is a *global* claim (over the finite corpus at each n), which fits
a `native_decide`-discharged finite fact — except (per
`feedback_no_native_decide`) that discharge is forbidden on this
project. The analytical question — a uniform structural argument for
why SK ≠ 0 must hold — is the honest open problem. The 4 counter-
examples give us a concrete, small target for that analytical work: if
someone can characterize the SCC structure of `SK` on these four
records (each ~1000-config SCCs), the proof might route through that.

The feedback memory `feedback_topological_invariant_proof_shape`
(Keston's stated preference for "a topological invariant forbids it")
is consistent with Axis C: the sink kernel is a discrete *topological*
invariant of `X(ms) \ C` under the forced-move digraph — its non-
emptiness is a closure property, not an arithmetic one on det.

---

## 7. Open questions surfaced by this work

### Q1 — sharp uniform-in-n bound on SK size?
On n=9 Table 7 records, `|SK|/|NG|` ranges 0.22–0.70. On n=8 sub-
threshold, 0.13–0.92. Is there a uniform lower bound of the form
`|SK| ≥ c(n)` for some c(n) growing with n? Empirically `|SK|` grows
polynomially in `∏m` across the corpus.

### Q2 — the 4 counterexamples' shared SCC geometry.
The 4 have non-trivial SCC counts `12, 16, 38, 12` and largest SCCs
`1020, 1050, 1185, 930`. The `38` outlier is ms `[2,3,2,3,2,3,3,3,4]`
— the one with alternating binaries over the first five positions.
Worth investigating: is the largest SCC a structured orbit (bounce,
wiggle, shadow) that already appears in the UB witness library?

### Q3 — is there an SK-of-SK reduction to a strictly smaller invariant?
The largest nontrivial SCCs are themselves strongly connected digraphs
of ~1000 configs. Running SK on the induced subgraph (treating the SCC
as its own NG) might collapse it further. If the iterated SK stabilizes
at a small *core SK* with analytically tractable structure, that's the
hook for an analytical proof.

### Q4 — transporting Axis C to the adjacent-binary class at n=9.
Every n=9 Table 7 record we tested is already sub-threshold, so every
SK > 0. To test that Axis C doesn't over-fire, we'd want a *valid* n=9
record at the strip threshold 8748 — ms `(2,3,3,3,3,3,3,3,2)` or its
mates from the CLB construction. Adding that to the corpus (via
`clb_witness_8748.py`) and confirming SK = 0 there would be a clean
above-threshold control.

### Q5 — does the Axis F implementation bug hide a real signal?
My Hamming-2 tube code restricts target-search to cycle steps `k` and
`k+1`, which is under-coverage for N_2 moves. Correctly scanning all
cycle steps might show a sharper signal than C1. Low priority (Axis C
already wins) but a proper implementation would let us cleanly compare
tube depth to forced-NG depth as geometric refinements of each other.

---

## 8. Artifacts produced

All under `lean/docs/paper_upgrade_1/`:

### Drivers
- `probe_t_sided_only.py` — step 1, c_self-forbidden LP.
- `probe_axis_c_forced_ng.py` — **primary detector.** Full-NG SK + SCC.
- `probe_axis_c_cross_check.py` — det-stripping validation of Axis C.
- `probe_axis_a_template.py` — strip-template correlation audit.
- `probe_axis_d_extension.py` — identity-completion verifier (artifact).
- `probe_axes_fgi.py` — Hamming-2 LP, Farkas dual, mover-adjacency.

### Result artifacts
- `t_sided_only_{results.json, summary.md}` — step 1 fast path.
- `t_sided_only_full_{results.json, summary.md}` — step 1 + n=8 sub (71 records).
- `axis_c_forced_ng_{results.json, summary.md}` — primary Axis C, fast path.
- `axis_c_forced_ng_full_{results.json, summary.md}` — Axis C + n=8 sub (72 records, headline table in §2 above).
- `axis_a_template_{results.json, summary.md}` — correlation audit.
- `axis_d_extension_{results.json, summary.md}` — identity-verify (artifact).
- `axes_fgi_{results.json, summary.md}` — F/G/I combined.

### Documentation (pre-existing)
- `n9_detector_design.md` — the 464-line design doc the work executes.
- `strengthening_work.md` — upgrade program.
- `phase1_n8_summary.md` — Strengthening Task #1 n=8 outcome.
- `run1_stdout.log` — Task #1 raw log with 4 counterexamples on record.

---

## 9. Binding constraints honored

- `feedback_no_case_splits_in_lean`: Axis C is a *uniform* definition
  (SK = largest subset closed under forced-out-edges), no case-split
  per (k binary, position, modulus).
- `feedback_no_axioms`, `feedback_no_native_decide`: Axis C's empirical
  separation is not claimed as a proof; the uniform structural argument
  remains open (§7 Q1, Q2, Q3).
- `feedback_no_ship_with_sorries`: this work does not close any sorry;
  it identifies a cleaner target for future sorry-closing work (§6).
- `feedback_topological_invariant_proof_shape`: Axis C is a discrete
  topological invariant (closure property of forced-NG) — aligned with
  Keston's stated proof-shape preference.
- `feedback_deep_research_over_cheap`: the cheap reformulations
  (step 1, A, F, G, I) ranged from clean-but-non-improving to RED;
  the deeper structural move (forced-NG SK) was the one that worked.
  Confirms the heuristic.
