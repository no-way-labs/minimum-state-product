# Strengthening task #1 — n=8 sub-threshold corpus extension

**Status.** Complete. Separation holds at n = 8 across the full sub-threshold
corpus (59/59). At the n = 9 Table 7 stretch, the detector surfaces the
strengthening doc's case (b) outcome: 4 LP-infeasible sub-threshold
counterexamples, all at the same structurally-named sub-family
(non-adjacent 3-binary orientations of `{2^3, 3^5, 4}`, product 7776).

**Data:** `phase1_n8_sub_corpus.json` (49 KB), `run1_stdout.log`,
`phase1_counterexample_analysis.json`.

## Headline numbers

| class                             | coverage                              | LP-feasible          |
|-----------------------------------|---------------------------------------|----------------------|
| at-threshold small-n (w5..w8)     | n ∈ {5,6,7,8}, prod ∈ {96,288,864,2592} | **0/4** (expected 0) |
| n = 8 sub-threshold               | 59 unordered multisets, prod < 2592   | **59/59** (expected all) |
| n = 9 Table 7 sub-threshold       | 9 (multiset, ordering) pairs at prod 7776 | **5/9** (expected all) |

4 n = 9 counterexamples (sub-threshold, LP-infeasible):

| ms                                    | L   | n_bin | bin_adj_pairs | min_bin_gap |
|---------------------------------------|-----|-------|---------------|-------------|
| `[2, 3, 2, 3, 3, 3, 2, 3, 4]`         | 47  | 3     | 0             | 2           |
| `[2, 3, 2, 3, 3, 3, 2, 4, 3]`         | 47  | 3     | 0             | 2           |
| `[2, 3, 2, 3, 2, 3, 3, 3, 4]`         | 47  | 3     | 0             | 2           |
| `[2, 3, 2, 3, 3, 3, 3, 2, 4]`         | 44  | 3     | 0             | 2           |

All 4 have LP objective `0.0` and support size `0` — the circulation LP
cleanly certifies that no nonneg circulation exists on the lifted 1-tube
graph of these cycles. Not a numerical artifact.

## Finer structure — adjacency signature split

**`{2^3, 3^5, 4}`** (5 orderings with cycles found):

| `bin_adj_pairs` | `min_bin_gap` | LP verdict | count |
|---|---|---|---|
| 0 | 2 | infeasible | 4 |
| 1 | 1 | feasible   | 1 |

Non-adjacent 3-binary orientations of this multiset are 4/4 LP-infeasible;
adjacent orientations are 1/1 LP-feasible.

**`{2^4, 3^4, 6}`** (4 orderings with cycles found, all LP-feasible):

| `bin_adj_pairs` | `min_bin_gap` | LP verdict | count |
|---|---|---|---|
| 0 | 2 | feasible | 1 |
| 1 | 1 | feasible | 2 |
| 2 | 1 | feasible | 1 |

Note `(2, 3, 2, 3, 2, 3, 2, 3, 6)` has `bin_adj_pairs = 0` **and** is
feasible. So the LP's failure locus is not "non-adjacent binaries in
general" but specifically "non-adjacent, k = 3 binaries, at product 7776."
Matches ARG's hypothesis zone (the sub-family ARG's 1985 LCM bound is
silent on; see `docs/arg_lcm/paper.md`).

**`{2^5, 3^3, 9}`** — no candidate cycle found in any of the 28
canonical orderings within the 15s-per-ordering budget. Either the
budget is too tight or these orderings structurally admit no fair
single-priv cycle at L ≤ 54. Flagged as a coverage gap, not as
LP-separation data.

## Restricted-LP variants on the 4 counterexamples

Ran `probe_strengthening1_counterexample_analysis.py` with three LP variants:

| variant          | edges allowed | 4 counterexamples feasible |
|------------------|----------------------|---------------------------|
| C1 (current)     | transport + c_self + c_left + c_right | 0/4 |
| T+sided-only     | transport + c_left + c_right (c_self forbidden) | **0/4** |
| transport-only   | transport | 0/4 (trivially) |

**T+sided-only does not recover the counterexamples.** This rules out
axis 1 (one-line "forbid c_self") of `n9_detector_design.md`. The n ≥ 9
detector cannot be built by restricting the existing C1 edge set.

On the 5 feasible records, T+sided-only preserves feasibility exactly
(5/5) with identical support size to C1 — consistent with the Wave 6 T2
restricted-feasibility observation the paper already reports in §6.4.

## Implications for the paper

### §6.3 Table 2 (`tab:corpus`)

Add a new row for the n = 8 sub-threshold sweep:

| class | n values | count | LP status |
|---|---|---|---|
| ... existing ... | | | |
| n = 8 sub-threshold (full multiset sweep) | n = 8 | **59** | feasible (59/59) |

Soften the "asymmetric in n" caveat: sub-threshold coverage is now full
at n = 8, and partial (5/9 orderings across the 3 multisets) at n = 9
sub-threshold.

### New subsection: n = 9 counterexamples (first counterexample class)

**Honest headline:** "The C1 circulation LP separates across the full
n = 8 sub-threshold corpus (59/59 sub-threshold LP-feasible, 4/4
at-threshold LP-infeasible). At n = 9, the sub-threshold side fractures
on the non-adjacent 3-binary orientations of `{2^3, 3^5, 4}`
(product 7776): 4 such orderings are LP-infeasible despite being
sub-threshold. The failure sub-family coincides with ARG's 1985 LCM
bound's silence class (see §5.3 / `docs/arg_lcm/paper.md`); the C1 LP
therefore inherits ARG's blind spot on this specific orientation
class."

### §6.4 restricted-feasibility observation

No change needed. Wave 6 T2's observation (c_self edges are structurally
unnecessary on the sub corpus) is not disturbed by the counterexample
finding: on the 5 feasible n = 9 records and the 59 n = 8 records, the
T+sided-only LP preserves feasibility; on the 4 counterexamples, both
C1 and T+sided-only are infeasible, so the restricted statement is
consistent.

### §7 (open questions) — add one

> Construct a detector that correctly flags non-extension on the
> non-adjacent 3-binary orientations of `{2^3, 3^5, 4}` at n = 9
> (and, conjecturally, the analogous orientations at n ≥ 9 for any
> multiset with `k = 3` binary processors and product < `4 · 3^(n-2)`).
> The design space is catalogued in
> `paper_upgrade_1/n9_detector_design.md`.

## Reproducibility

```
python3 -u probe_strengthening1_n8_subthreshold.py \
  --n8-budget 8.0 --n8-max-orderings 30 \
  --n9-budget 15.0 --n9-max-orderings 150 \
  --output /path/to/phase1_n8_sub_corpus.json

python3 -u probe_strengthening1_counterexample_analysis.py
```

Run 1 wall-clock: 1655.9 s. Deterministic (no randomness).
