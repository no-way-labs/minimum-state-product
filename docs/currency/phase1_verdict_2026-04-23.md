# Currency Reframing — Phase 1 Verdict (2026-04-23)

**Program:** `currency_reframing_program.md` (this directory).
**Phase 1 question:** Does any candidate currency Q ∈ {L, κ_mover, κ_total,
H_pos, H_mover, H_joint, ratios} separate the 97-record corpus more cleanly
than ∏mᵢ does, and saturate on a clean q(n) curve on the valid side?

**Verdict:** **Outcome 3 from the program §Phase 1 expected outcomes.** No
candidate Q separates more cleanly than ∏mᵢ, and ∏mᵢ (specifically log₂∏mᵢ)
saturates the valid side tightly. The reframing hypothesis fails its first
contact with the corpus. ∏mᵢ is, on the empirical evidence available, the
right currency — or, more precisely, the right ambient currency in whose
units the dynamical obstruction is to be measured.

This is a clean null. It strengthens the case that the §7 obstruction is
genuinely in the joint (C, µ) × detOf interaction as previously diagnosed,
not in the currency of the question.

---

## Method

Rebuilt the 97-record corpus (4 absorbers + 6 CLB ternary-strip + 19 small-n
sub + 59 n=8 sub + 9 n=9 Table 7 sub) via the canonical phase1 + wave4
builders at the same budgets that produced
`paper_upgrade_3/corpus_canonical.json` (overall hash `f4b017b1f57687cc`).
For each record computed:

- **L** = good cycle length
- **κ_mov** = #{(p, c[p−1], c[p], c[p+1]) at step k where movers[k] = p}
  (program memo §Candidate 2 definition)
- **κ_tot** = same set summed over *all* p, not only movers
- **H_pos_sum** = Σᵢ Hᵢ where Hᵢ is the empirical entropy of position-i values
  along C
- **H_mover** = entropy of mover-position distribution
- **H_joint** = entropy of (i−1, i, i+1) value triples across (k, i)
- Six ratio variants (L/n, L/n², κ/L, κ/(n·L), Hpos/log₂prod, Hpos/(n·log₂3))
- coverage = L / ∏mᵢ

For each Q the **per-n separation** test asked: at each n, can Q strictly
separate the 2 valid (at-threshold) records from the sub-threshold records?
Margin = signed gap (positive = strict separation). AUC = pairwise
concordance. Valid-side saturation = coefficient of variation of mean(Q)/n^k
across the 5 n-values, minimised over k ∈ {0, 1, 2}.

Implementation: `compute_currencies.py` (rebuild + L/κ/H) →
`currencies_97.csv`. Analysis: `phase1_separation.py` →
`phase1_separation_report.txt`, `phase1_separation_summary.json`. All
artifacts live in `lean/LeanMn/LowerBound/SK/` (sandbox-writable).

Cross-check: 96 of 97 (n, sorted_ms, L) keys match `corpus_canonical.json`
exactly. One record (n=8, sorted_ms=(2,2,2,2,2,3,3,5)) found an alternative
cycle (L=22 vs canonical L=46) — same sub-threshold multiset, different
fair good cycle. Both are valid sub-threshold representatives; the verdict
is unaffected.

---

## Headline ranking

| currency             | AUC   | strict_n / 5 | rel_margin | sat_CV |
|----------------------|-------|--------------|------------|--------|
| **product (∏mᵢ)**    | 1.000 | 5            | 0.113      | 1.048  |
| **log₂(product)**    | 1.000 | 5            | 0.022      | 0.030  |
| H_pos_sum            | 0.882 | 3            | 0.084      | 0.026  |
| H_pos_avg            | 0.882 | 3            | 0.084      | 0.026  |
| Hpos_over_nlog23     | 0.882 | 3            | 0.070      | 0.026  |
| H_joint              | 0.866 | 2            | 0.032      | 0.029  |
| L                    | 0.784 | 2            | 0.151      | 0.228  |
| L_over_n             | 0.784 | 2            | 0.151      | 0.228  |
| L_over_n2            | 0.784 | 2            | 0.106      | 0.253  |
| κ_total              | 0.782 | 2            | 0.151      | 0.114  |
| coverage             | 0.763 | 1            | 0.002      | 0.930  |
| κ_mov_over_L         | 0.723 | 0            | 0.000      | 0.077  |
| κ_mov_over_nL        | 0.723 | 0            | 0.000      | 0.255  |
| κ_mover              | 0.697 | 2            | 0.177      | 0.128  |
| Hpos_over_log2prod   | 0.639 | 0            | 0.000      | 0.034  |
| H_mover              | 0.610 | 1            | 0.002      | 0.095  |

Only ∏mᵢ and log₂∏mᵢ achieve perfect AUC = 1.000 with strict separation at
every n. Every dynamical candidate fails on one or both axes.

---

## The n=9 anti-separation kill

The most informative finding is at n=9. The corpus has 1 valid record (the
CLB ternary-strip on `(2,3,3,3,3,3,3,3,2)`, prod = 8748, L = 25, κ_mov = 25,
H_pos_sum = 12.08) and 9 sub-threshold records (all Table 7 multisets at
prod = 7776, L ∈ {39, …, 53}, κ_mov ∈ {39, …, 47}, H_pos_sum ∈ {10.08, …,
12.53}).

| Q             | valid n=9   | sub n=9 range | margin    |
|---------------|-------------|---------------|-----------|
| product       | 8748        | 7776          | **+972**  |
| L             | 25          | 39 – 53       | **−14** (anti) |
| κ_mover       | 25          | 39 – 47       | **−14** (anti) |
| κ_total       | 75          | 107 – 133     | **−32** (anti) |
| H_pos_sum     | 12.08       | 10.08 – 12.53 | **−0.45** (overlap) |
| H_joint       | 5.56        | 5.71 – 6.17   | **−0.15** (anti) |

At the regime where the M_n phase transition actually lives (n=9, where
M_n = 4·3^(n−2) replaces 32·3^(n−4)), the dynamical currencies are not just
*looser* than ∏mᵢ — they *flip direction*. Sub-threshold Table 7 cycles are
strictly *longer* and *more entropic* than the valid CLB cycle.

This is not noise. It is the structural fact that the n=9 sub-threshold
multisets {2³3⁵4, 2⁴3⁴6, 2⁵3³9} are *near-threshold* with rich, unconstrained
cycle structure but happen to have product = 7776 < 8748. Their cycles look
"valid-like" on every dynamical axis we measured, and only ∏mᵢ sees that
they are sub-threshold. The reframing hypothesis predicted the opposite — it
predicted these would look obviously broken on the dynamical axis. They do
not.

---

## What the program memo predicted, and what we found

The §Why-the-product-is-suspicious section gave three priors:

1. **Representation-dependent inflation.** ∏mᵢ can be inflated arbitrarily by
   adding unused states. → Unfalsified. Real, but the corpus is not built
   from inflated representations, so the prior does not bite empirically.
2. **Insensitive to reachability.** Coverage L/∏mᵢ supposedly ignores how
   much of Config(m) the cycle visits. → **Falsified for our purpose:**
   coverage is the worst separator in the table (sat_CV = 0.93, and it
   actively *anti-separates* — valid records have *lower* coverage than sub).
3. **Insensitive to rule-table content.** κ supposedly captures rule-table
   information that ∏mᵢ misses. → **Falsified:** κ_mov is the *worst* of
   the three core candidates (AUC = 0.697), and κ_tot ties with L. Rule-
   table information content as captured by the program memo's κ definition
   does not separate.

The §candidate ordering in the program memo was L > κ > H. Empirically the
order is reversed: H > κ_tot ≈ L > κ_mov, and all three are dominated by
log₂∏m. The three-way tie of H_pos_sum, H_pos_avg, and Hpos_over_nlog23 at
sat_CV = 0.026 is interesting but irrelevant — they all fail strict
separation at n = 8 and n = 9.

---

## Why log₂∏mᵢ saturates so tightly (sat_CV = 0.030)

The valid-side data:

| n  | record         | log₂ product |
|----|----------------|--------------|
| 5  | absorber       | 6.585        |
| 5  | CLB strip      | 6.755        |
| 6  | absorber       | 8.170        |
| 6  | CLB strip      | 8.340        |
| 7  | absorber       | 9.755        |
| 7  | CLB strip      | 9.925        |
| 8  | absorber       | 11.340       |
| 8  | CLB strip      | 11.510       |
| 9  | CLB strip      | 13.095       |
| 10 | CLB strip      | 14.680 (extrap; corpus has the record) |

Both witness families track log₂∏m linearly in n with the same slope (≈ log₂ 3
per step), differing by a small additive constant. Mean (log₂∏m)/n = 1.41
across all 10 valid records, with CV = 0.030. This *is* the §Conjecture 9
asymptotic M_n = 4·3^(n−2) restated in log space, recovered cleanly from
the valid-side data with no fitting.

No dynamical Q matches this. L on the valid side: absorber L grows ≈
n²/2, CLB L grows = 3n−2, and the two families *diverge*; sat_CV(L_over_n) =
0.228 ≫ 0.030. Entropy H_pos_sum ≈ 0.83·n·log₂3 across both families — close
in CV but it is essentially "log₂∏m × constant" in disguise (since at-
threshold ∏m = 4·3^(n−2) and the cycle visits configurations with high
per-position diversity), so the CV match is downstream of the product
saturation, not independent of it.

---

## Reading this against the §7 catalog

The program memo argued each §7 invariant family fails for a reason that
"would be a feature, not a bug, if the program were attacking the correct
currency." The Phase 1 evidence does not bear that out. If a dynamical
currency were the right axis, we would expect at least one of L, κ, H to
*beat* ∏m on the corpus. Instead all of them fail at n = 9, where they
anti-separate.

The §7 obstruction diagnosis ("the obstruction lives in the joint (C, µ) ×
detOf interaction") is consistent with this finding. (C, µ) × detOf is a
high-dimensional structured object; ∏m is the right *aggregate* coordinate
on it; the obstruction is some non-aggregable structural property that
∏m happens to control via the validity-property cascade. The §7 invariants
fail not because they look at ∏m, but because they try to extract that
non-aggregable structure from cellular / sheaf / map-level invariants that
do not see joint structure.

This also aligns with Keston's stated proof-shape preference (memory:
`feedback_topological_invariant_proof_shape.md`) — a topological invariant of
X(ms) \\ C that *uses* ∏m as the ambient coordinate is not refuted by this
result. The reframing program targeted a different shape (drop ∏m as the
quantity, measure on the cycle directly) and that shape is the one that
fails.

---

## Implication for the program

Per the §Risks-and-failure-modes section: *"None of L, κ, H separates the
corpus more cleanly than ∏mᵢ. The hypothesis fails. This is a legitimate
empirical outcome and would be publishable as a null result if carefully
done."*

We are at that point. Recommended next moves, in order:

1. **Stop the program at Phase 1.** Phases 2–5 are conditional on Phase 1
   identifying a clean Q*; we did not. There is nothing to formalize, prove,
   or transport.
2. **Catch a residual question** before stopping: program §Phase 1
   "what else might Q be" brainstorm. Three candidates we did *not* test
   that are still on the menu:
   - **Spectral quantity of the forced-NG graph** (eigenvalue gap; Cheeger
     constant). The Axis-C SCC structure has been computed for every record
     already; using its eigenstructure as Q is one query away.
   - **Möbius / order-poset invariants** of the cycle's order ideals on the
     value lattice ⊗ᵢ Z/mᵢ.
   - **Forman discrete-Morse Betti numbers of X(ms) \\ C** (the
     Morse-Hamming attack from `project_sk_morse_hamming_2026-04-20.md`).
     This was a fresh LB direction, fits Keston's topological-invariant
     preference, and is operationally a different Q. If Phase 1' tests this
     against the corpus and it *also* fails to beat ∏m, the null is
     stronger and the catalog is complete enough to publish.
3. **Update the §7 framing in the paper.** The paper should acknowledge that
   "is the currency wrong?" was tested empirically and the answer is no.
   This *strengthens* the §7 obstruction diagnosis — it is no longer "we
   couldn't find an invariant" but "we tested whether the search space was
   wrong, and it is not". That is a publishable refinement.

If Keston wants to push the program further before stopping, the
brainstorm-extension Phase 1' (test β₁ of X(ms)\\C and forced-NG spectrum)
is the highest-yield next test — it operationally fits the topological-
invariant proof shape and answers the residual "what else might Q be"
question with the same corpus.

---

## Files

- `compute_currencies.py` — corpus rebuild + L/κ/H computation
- `phase1_separation.py` — per-n separation + ranking
- Outputs (in `lean/LeanMn/LowerBound/SK/`):
  - `cycles_97_cache.json` — rebuilt corpus with cycle/movers/det (~3 MB)
  - `currencies_97.csv` — one row per record, all currencies
  - `phase1_separation_report.txt` — per-Q per-n table + ranking
  - `phase1_separation_summary.json` — machine-readable verdict per Q

Total wall time: 28 min for the rebuild (one-shot; cache enables instant
re-runs). Separation analysis: < 1 s.
