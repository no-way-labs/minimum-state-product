# §1.7 Corpus-count reconciliation — findings and paper-edit proposal

**Status.** Closed. Canonical 97-record corpus assembled at
`lean/docs/paper_upgrade_3/corpus_canonical.json`, overall hash
`f4b017b1f57687cc`.

## 0. Headline

The paper's `"Axis C separates all 97 records"` abstract claim is
**mathematically sound and now cleanly backed by a single shipped
artifact**, but was not backed that way prior to this audit. The
corpus data was splinted across two files that between them covered
only 72 of 97 records under the Axis-C detector:

- `phase1_n8_sub_corpus.json` / `axis_c_forced_ng_full_results.json`:
  72 records = 4 small-n absorbers (at_smallN) + 59 n=8 sub-threshold
  + 9 n=9 Table-7 sub-threshold.
- `phaseW4_results.json` (wave4 probe): the 29-record LP-detailed
  corpus = 19 sub n∈{5,6,7} + 4 at_smallN + 6 ternary-strip (at_clb
  n∈{5..10}), with **only LP/C1 verdicts, no Axis-C**.
- Overlap: 4 at_smallN records appear in both. Union: 72 + 29 − 4 = 97.

So the 97 claim was a union-of-slices claim without a single shipped
file holding the union. Axis-C had never been run on the 19 + 6 = 25
records unique to `phaseW4_results.json`.

## 1. What was done

A consolidation pass (`lean/docs/paper_upgrade_3/consolidate_corpus.py`
+ `close_na.py`):

1. Re-loaded the 72 phase1 records (LP + Axis-C verdicts shipped).
2. Re-built the 29 wave4 records from `build_sub_corpus(per_n=8)`
   (re-enumeration), `load_smalln_witnesses()` (verify_witnesses
   tables), and `build_at_corpus()` (CLB constructor for n∈{5..10}),
   obtaining raw `(cycle, movers, det)` for each.
3. Ran `probe_axis_c_forced_ng.analyze_record` on each wave4 record
   to produce the previously-missing Axis-C verdicts.
4. Merged on canonical key `(n, ms, L, class)` with absorber records
   unified across the two sources (phase1 wins on fields present in
   both).
5. Patched one residual edge case: the n=8 multiset `{2⁵, 3², 5}`
   appears in `phase1_n8_sub_corpus.json` as ordering
   `[2,2,2,2,2,3,3,5]` with L=46, but in `axis_c_forced_ng_full`
   as ordering `[2,2,2,2,3,3,2,5]` with L=22 — the two sweeps hit
   different good-cycle enumerations on the same multiset. The L=46
   ordering's Axis-C verdict was filled in by re-running
   `enumerate_cycles` + `analyze_record` for that specific ordering
   (`sk_nonempty=True`, `sk_size=811`, `sk_frac=0.582`, largest SCC
   of size 362).

The resulting `corpus_canonical.json` has 97 records with every
per-record column (LP feasibility, restricted-LP feasibility where
applicable, Axis-C sink-kernel size, SCC stats, per-record 8-char
hash, source provenance), and an overall 16-char corpus hash
`f4b017b1f57687cc` computed over `(id, per-record hash,
Axis-C verdict)` triples.

## 2. Per-class separation verdict

| class | total | LP feas | LP infeas | Axis-C fire | Axis-C silent |
|---|---:|---:|---:|---:|---:|
| at_clb (ternary-strip, valid) | 6 | 0 | 6 | 0 | 6 |
| at_smallN (absorber, valid) | 4 | 0 | 4 | 0 | 4 |
| sub (sub-threshold n∈{5..8}) | 78 | 78 | 0 | 78 | 0 |
| sub_n9table7 (sub-threshold n=9 Table 7) | 9 | 5 | 4 | 9 | 0 |
| **total** | **97** | **83** | **14** | **87** | **10** |

**Axis C:** fires on all 87 sub-threshold records, silent on all 10
valid records → **separates 97 of 97**.

**C1 LP:** feasible on 83 sub-threshold, infeasible on all 10 valid,
infeasible on 4 sub-threshold (the n=9 non-adjacent `{2³, 3⁵, 4}`
counterexamples) → separates 93 of 97 (the 4 misses are the known
sub_n9table7 counterexamples).

The relationship `C1-feasible ⇒ Axis-C-fires` holds on the entire
corpus (0 counterexamples) and `Axis-C ∖ C1 = {4 n=9 counterexamples}`,
matching the paper's §6.5 claim.

## 3. The other "68"s

The numbers 68 and 72 appear in several project memos; for future
readers, these are the distinct slices:

- **68 in `partial_dynamical_invariants_status.md` §0 headline.**
  = 4 n=9 Table-7 counterexamples + 59 n=8 sub-threshold + 5 n=10/11
  sub-threshold sampling. This is the β_1 ≥ 178 evidence slice used
  for Conjecture B''; includes n≥10 sampling not otherwise in this
  97-record corpus. Rename suggestion for memos:
  **"68-record β_1 evidence slice"**, to avoid implying a third
  corpus.
- **68 in `longest_ter_run_audit.json` / `app:lndsc-topo` item 5.**
  = 59 n=8 sub-threshold + 9 n=9 Table-7 sub-threshold. The
  longest_ter_run ≤ 1 subclass probe's total; `in_subclass = 58` of
  these; `in_subclass_restricted_feas = 58` confirms the 58/58 figure
  in `main.tex`. Rename suggestion:
  **"68-record longest_ter_run audit corpus"**.
- **72 in `axis_c_forced_ng_full_results.json`.** = 4 at_smallN + 59
  n=8 sub + 9 n=9 Table-7 sub. This is the Axis-C slice that was
  shipped prior to §1.7; superseded by the canonical 97-record file.
- **72-record "n ≤ 9 corpus" in `main.tex` §6.5.** Same as above.
  Paper edit: keep the 72-record cite when specifically discussing
  what Axis-C had been computed on at paper-draft time, OR update
  to "97-record corpus" and cite `corpus_canonical.json` (preferred,
  §4 below).

## 4. Proposed paper edits

### 4.1 Appendix D (`tab:corpus-full`)

Options, in preference order:

**Option A (preferred): replace `tab:corpus-full` with a split of
two smaller tables.**

- `tab:corpus-lp-detailed`: the 29 LP-detailed rows from
  `phaseW4_results.json`, as currently shipped — no change to
  columns, same hash `98faf429b06e5f92`. Caption amended to
  **"LP-detailed sub-corpus of the 97-record canonical corpus of
  §6.3 (29 rows);** full Axis-C-extended 97-row data in
  `corpus_canonical.json`, hash `f4b017b1f57687cc`."
- `tab:corpus-axc-summary`: a 4-row table (one per class) showing
  LP / Axis-C verdicts counted as in §2 above. This is the single
  table that substantiates the abstract's "separates all 97" claim.

**Option B (larger): fully populate `tab:corpus-full` with 97 rows.**
Requires restructuring columns to fit the Axis-C fields
(`sk_nonempty`, `sk_size`, `sk_frac`, `largest_scc`); shipment cost
is page count. Only worth it if a referee specifically demands
per-record visibility of every Axis-C number.

**Option C (thinnest): leave `tab:corpus-full` as-is, point the
caption at `corpus_canonical.json` as the authoritative full-97
record.** Minimal rewrite; still honest about the split.

Recommend Option A.

### 4.2 Abstract + §6.3 + §10 Conclusion language

The current abstract sentence reads:

> "The circulation-LP detector separates 93 of 97 records, with the
> four failures concentrated at the n = 9 non-adjacent {2³, 3⁵, 4}
> orientations; a strict upgrade, the sink-kernel on the candidate's
> forced-NG digraph (Axis C), separates all 97 ..."

This is now **accurately** backed by `corpus_canonical.json`. No
text change required, only a new citation to the canonical file
and hash. Suggested insertion after "(Axis C)":

> "(Axis C, §6.5; per-record data in `corpus_canonical.json`,
> overall hash `f4b017b1f57687cc`)"

Analogous citations in §6.3 footnote and §10.

### 4.3 §6.5 (`sec:detector-axis-c`)

Current: "The upgrade is machine-rechecked on the full 72-record
n ≤ 9 corpus in `axis_c_forced_ng_full_results.json`."

Update: "The upgrade is machine-rechecked on the full **97-record**
corpus in `corpus_canonical.json` (overall hash
`f4b017b1f57687cc`); the subset covered in
`axis_c_forced_ng_full_results.json` accounts for 72 of 97 (the 4
at_smallN + 59 n=8 sub + 9 n=9 Table-7 sub records), with the
remaining 25 (19 sub n∈{5,6,7} + 6 at_clb n∈{5,...,10}) filled in by
the §1.7 reconciliation pass."

Current "fires on all 68 sub-threshold records ... silent on all 4
stored small-n absorber witnesses" — this 68 is the 59+9 slice; keep
as-is but add a parenthetical: "(plus the 19 n∈{5,6,7}
sub-threshold and 6 at_clb records recovered in the §1.7
reconciliation: SK fires on all 19, silent on all 6)".

### 4.4 Status doc (`partial_dynamical_invariants_status.md`)

Rename the "68 records" headline slice to
**"68-record β_1 ≥ 178 evidence slice (4 n=9 counterex + 59 n=8 sub
+ 5 n=10/11 sub)"** on its first mention, to distinguish from the
other 68. No content change; this is a nomenclature fix only.

## 5. What's preserved from §1.7 scope

- Abstract / §6.3 / §10 corpus-count claims: consistent and now
  backed.
- Appendix D's 29-record corpus: preserved, re-contextualized as
  an LP-detailed sub-corpus.
- The `relaxed_search_n5_n6.json` 5.5M-sample search result (zero
  hits) is untouched by §1.7; it remains the status doc's claim.
- The paper's `"all 97"` is now backed by 97 individual Axis-C
  records. No aspiration left in that sentence.

## 6. Open items (not §1.7 scope)

- §1.8 (SMT-based relaxed-convention exhaustive search at n=5,6)
  still upgrades the transport evidence in §8.7.
- §1.1 (Axis-C at n=10, 11 without Hamming restriction) is
  separate — the corpus there is sub-threshold candidates at
  **n=10, 11** which are NOT in the current 97-record corpus
  (which stops at n=10 and only covers 1 ternary-strip record there).
- `corpus_canonical.json` is a v1.0 snapshot. When §1.1 lands
  additional n=10, 11 rows, the canonical file is updated and the
  overall hash refreshes; readers should always cite the hash, not
  just the filename.

## 7. Pre-commit checks for the reconciliation

- [x] All 97 records have an LP feasibility verdict.
- [x] All 97 records have an Axis-C verdict (0 NA after patch).
- [x] C1-feasible ⇒ Axis-C-fires on every record (0 counterexamples).
- [x] The 4 n=9 Table-7 LP-infeasible records all have Axis-C fire
      (i.e., Axis C recovers them — matches `paper §6.4`).
- [x] All 10 valid-system records have Axis-C silent (matches
      monotonicity certificate: convergence forbids SK-nonempty).
- [x] The 1-NA multiset `{2⁵, 3², 5}` ordering discrepancy is
      documented and patched.
- [x] Overall hash `f4b017b1f57687cc` computed over a deterministic
      function of per-record hashes + Axis-C verdicts.

## 8. Artifacts

- `lean/docs/paper_upgrade_3/corpus_canonical.json` — 97-row
  consolidated corpus.
- `lean/docs/paper_upgrade_3/consolidate_corpus.py` — rebuild
  driver (re-runs wave4 builders + Axis-C).
- `lean/docs/paper_upgrade_3/close_na.py` — 1-record patch driver
  for the `{2⁵, 3², 5}` ordering mismatch.
- This memo.
