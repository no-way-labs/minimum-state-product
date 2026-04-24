# §1.1 Full-NG Axis C at n = 10, 11 — findings

**Status (2026-04-24, updated).** Full two-tool (DFS + SMT)
sub-threshold sweeps complete at **both n = 10 and n = 11**.

## 0. Headline

**Axis-C fires on every cycle the two-tool pipeline surfaces at
n = 10 and n = 11.**

- n = 10: **320 / 320** (multiset, ordering) probes fire Axis-C
  across all 291 sub-threshold multisets (77 DFS + 214 SMT-closed),
  **zero silent, zero UNKNOWN**.
- n = 11: **585 / 585** probes fire Axis-C across 563 of 564
  sub-threshold multisets (90 DFS + 473 SMT-closed), **zero silent,
  one SMT-budget UNKNOWN** at multiset `[2^8, 4, 4, 6]`.

Sink-kernel geometry: |SK|/|NG| ∈ [0.026, 0.999], mean 0.110 at
n = 11 (similar range at n = 10). Cycle lengths L ∈ [22, 65] at
n = 11.

Conjecture 20 is consistent with both sub-threshold levels at the
tested pipeline depth.

## 1. Scope

- Scale-up target family at labelled n ∈ {10, 11}
  (`axis_c_scale_up_results.json`, 3 orderings each).
- **Full sub-threshold sweep at n = 10**: 291 / 291 multisets,
  `MAX_ORD=2`, `budget_per_ord=30 s`, runtime 13,282 s ≈ 3.7 h
  (`axc_n10_sweep_results.json`).
- n = 11 sub-threshold sweep: started 2026-04-23, 564 multisets,
  same parameters (`axc_n11_sweep_results.json`).

## 2. Per-record verdicts

### 2.1 Scale-up target family {2³, 3^(n-4), 4}

**Labelled n = 10** (10-element ms).

| ms | L | \|NG\| | SK_1 | SK_2 | SK_inf | min_r | girth |
|---|---|---|---|---|---|---|---|
| [3, 3, 2, 4, 2, 3, 3, 2, 3, 3] | 44 | 23284 | 229 | 1641 | 5693 | 1 | None |
| [2, 3, 3, 3, 2, 3, 2, 4, 3, 3] | 53 | 23275 | 90 | 1580 | 12039 | 1 | 4 |
| [3, 3, 4, 3, 2, 3, 2, 3, 2, 3] | 52 | 23276 | 181 | 1173 | 4623 | 1 | None |

Axis-C fire: **3** / 3; silent: **0** / 3.

**Labelled n = 11** (11-element ms).

| ms | L | \|NG\| | SK_1 | SK_2 | SK_inf | min_r | girth |
|---|---|---|---|---|---|---|---|
| [3, 3, 3, 3, 3, 2, 3, 2, 3, 2, 4] | 53 | 69931 | 0 | 973 | 13715 | 2 | None |
| [3, 3, 3, 2, 3, 2, 3, 4, 3, 2, 3] | 52 | 69932 | 170 | 2442 | 13894 | 1 | None |
| [3, 3, 2, 3, 2, 3, 3, 3, 2, 4, 3] | 53 | 69931 | 0 | 849 | 26464 | 2 | 8 |

Axis-C fire: **3** / 3; silent: **0** / 3.

### 2.2 Full sub-threshold sweep at n = 10

Parameters: `max_multisets=0` (all 291), `max_orderings=2`,
`budget_per_ord=30 s`, runtime 13,282 s ≈ 3.7 h.

| outcome | multisets | notes |
|---|---:|---|
| Cycles found, Axis-C evaluated | **77** | — |
| No cycle in budget (`dt_enum_s = 30.0`) | **214** | cycle enumerator timed out, Axis C not evaluated |

Across the 77 probed multisets, 106 (multiset, ordering) pairs
successfully found a cycle and were evaluated by Axis C:

- Axis-C fire: **106 / 106**
- Axis-C silent: **0 / 106**

**No silent records at tested depth.**

#### 2.2.1 Enumeration-budget pattern

The 214 no-cycle multisets are **enumeration-budget timeouts**, not
"no cycle exists". The cycle-enumerator runtime blows up as max(m_i)
grows (more branches per processor, larger effective search space):

| max(m) | total | cycles found | fire-rate |
|-------:|------:|-------------:|----------:|
| ≤ 5 | 49 | 42 | 86 % |
| 6 | 25 | 14 | 56 % |
| 7 | 23 | 8 | 35 % |
| 8 | 22 | 3 | 14 % |
| ≥ 9 | 172 | 10 | 6 % |

This is an **enumeration-tractability artifact**, not Axis C
evidence. Closing the gap requires a longer per-ordering budget
(e.g.\ 300 s or 600 s) on the 214 budget-limited multisets, or a
smarter cycle enumerator targeted at high-max(m) cases.

#### 2.2.2 Detector richness on the 106 evaluated records

- Cycle length L ∈ [20, 59]; bulk of mass at L ∈ [32, 59].
- SK fraction |SK| / |NG|: min 0.046, max 1.000, **mean 0.397**.
  SK is structurally substantial on every firing record.
- Smallest SK: all-binary {2^10}, L=20, SK = full NG (1004/1004).
- Largest NG probed: {2^7, 3, 4, 17}, |NG| = 26,076, SK-frac 0.087
  (still positive; SK has 2268 configs).
- Cycle-coverage on evaluated multisets: 37 / 77 fire on all
  tested orderings (both orderings); 8 / 77 are single-ordering-
  only because the other ordering's cycle enumeration timed out.

### 2.3 Sub-threshold sweep at n = 11

**Complete.** Two-tool pipeline:

- **DFS pass** (`probe_axisc_n10_sweep.py --n 11`, 564 multisets,
  30 s/ordering, 2 orderings each): 90 multisets yielded a cycle
  across 112 (multiset, ordering) probes. **112 / 112 fire Axis-C**.
- **SMT gap-closer** (`sweep_smt_n10_uncovered.py` reused with
  `--in axc_n11_sweep_results.json --out axc_n11_smt_sweep_results.json
  --L-max 30 --timeout 90`, targeting the 474 DFS-budget-limited
  multisets): 473 FOUND, 1 UNKNOWN (`[2^8, 4, 4, 6]`, prod=1536).
  **473 / 473 fire Axis-C**.

Combined: 585 (multiset, ordering) probes across 563 / 564
sub-threshold multisets at n = 11, all firing Axis-C. Wall-clock
total ≈ 10 h (DFS + SMT).

## 3. Det-coverage audit for any SK = ∅ cases

N/A this pass (no silent records in the 106 evaluated).

## 4. Verdict against Conjecture 20

**GREEN on all probed records at both n = 10 and n = 11.**

- n = 10: 320 / 320 probes fire across all 291 sub-threshold
  multisets (two-tool pipeline closed).
- n = 11: 585 / 585 probes fire across 563 / 564 sub-threshold
  multisets (one SMT-budget UNKNOWN, not an obstruction).

**Scope caveat.** Per-probe firing ≠ per-multiset completeness.
The DFS half uses a fixed 30 s budget and two canonical orderings;
the SMT half finds *a* good cycle per multiset, not all. The
verdict is "GREEN on every probe the pipeline surfaced", not
"GREEN on every candidate good cycle on every multiset". See
§6.5 scope caveat in `papers/draft1/src/main.tex`.

## 5. Open items

1. **Close the one remaining n = 11 UNKNOWN** (`[2^8, 4, 4, 6]`)
   with a longer SMT timeout or stronger cycle-existence encoding
   (e.g. symmetry break on mover sequence).
2. **n = 12 sweep** as the next layer (1000+ sub-threshold
   multisets; budget ~24 h DFS + ~6 h SMT under the current
   parameters).
3. **Integration into `corpus_canonical.json`** — add an
   "axc_n10_full" and "axc_n11_full" class with one record per
   (multiset, ordering) pair closed by the pipeline.

## 6. Artifacts

- `probe_axisc_n10_sweep.py` — driver with verbose progress,
  checkpoints, `--n`, `--max-multisets`, `--max-orderings`,
  `--budget-per-ord`.
- `axc_n10_sweep_results.json` — 291-multiset full sweep
  (overnight, 2026-04-23).
- `axc_n11_sweep_results.json` — 564-multiset DFS sweep (complete).
- `axc_n11_smt_sweep_results.json` — 474-multiset SMT gap-closer
  (473 FOUND, 1 UNKNOWN).
- `sweep_smt_n10_uncovered.py` — SMT-batch driver, reused at n = 11.
- `probe_cycle_smt.py` — z3 cycle-existence encoder.
- `run_overnight_n10_n11.sh` — wrapper.
- `analyze_r_star_n10_n11.py` + `r_star_analysis.md` — r* extraction.
