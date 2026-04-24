# App C exhaustive-search driver

This is the driver bundle described at `\cref{app:exhaust-repro}` of
`papers/draft1/src/main.tex`. It enumerates every
sub-threshold multiset `m` on `n` positive integers `≥ 2` with
`∏ m_i < M_n` (connected convention), every orientation modulo the
dihedral group `D_n` (rotation + reflection), and feeds each orbit
representative to the lower-bound certificate pipeline.

## Scripts

| Script | Role |
|---|---|
| `multiset_enum.py` | Deterministic C1 + C2 records (state-count coverage + orientation coverage), runnable standalone. |
| `generate_manifest.py` | Writes `coverage_manifest.json` aggregating C1 + C2 across `n ∈ {3, ..., 9}`. |
| `driver.py` | Top-level entry point per App C.9; prints C1 + C2 summary, runs the Python C3+C4+C5 pipeline (`--n N`), and runs referee replay (`--replay PATH`). |
| `exhaustive.c` | Optional C worker for the C3+C4+C5 inner loop (same semantics, faster). Build with `make`; invoked per `(n, ms, orientation)` as `./exhaustive --n N --ms m0,... --orient m0,...`. |

## Quick start

```bash
# Deterministic C1 + C2 summary (matches Table 9's left columns)
python3 driver.py

# Regenerate the machine-readable coverage manifest
python3 generate_manifest.py

# Per-n detail
python3 multiset_enum.py 9
```

## What's shipping today vs at DOI mint

**Ship today (deterministic, reproducible bit-for-bit):**
- C1 state-count coverage (the 147 sub-target multisets at `n = 9`,
  etc. — matches Table 9 left-hand columns exactly: `0, 1, 5, 12, 27,
  59, 147` multisets and `0, 1, 6, 22, 77, 343, 2085` dihedral orbit
  representatives).
- C2 processor-orientation coverage, per-multiset orbit reps.
- `coverage_manifest.json` consumable by referees without running the
  search.

**Ship at DOI mint (artifact archive):**
- C3 candidate good-cycle counts per orientation.
- C4 partial rule-table counts per candidate good cycle.
- Rejection-certificate stream per orbit representative.
- Driver hash and independent-verifier hash (App C.4).

## Related scripts in the project

- `docs/lean_docs/paper_upgrade_1/probe_strengthening1_n8_subthreshold.py`
  runs the cycle-enumeration + LP-detector subpipeline against the
  same corpus (n = 8 sub-threshold, 59 records; n = 9 Table 7, 9
  records) and emits `phase1_n8_sub_corpus.json` as downstream input
  for the rejection stream.
- `docs/lean_docs/paper_upgrade_1/farkas_certificates.py`
  emits per-infeasible-record Farkas topological-sort witnesses that
  serve as the machine-checkable form of the LP-infeasibility portion
  of the rejection certificates.
- `probes/verifier.py` is the connected-convention
  final verifier (App C.1); `relaxed_verifier.py` (in
  `paper_upgrade_1/`) is the Knuth-relaxed variant, used only for
  §8.7 cross-convention probes.

## Coverage manifest schema

```
{
  "schema_version": 1,
  "totals": {
    "n_values": [3, ..., 9],
    "M_n_connected": [...],
    "multisets_below": [...],
    "D_n_orbit_reps": [...]
  },
  "per_n": { "n": { "multiset_count", "orientations_count",
                     "per_multiset": [...orbit reps...] } },
  "c3_candidate_good_cycles": "pending_full_search",
  "c4_partial_rule_tables":   "pending_full_search",
  "rej_by_pruning":           "pending_full_search",
  "rej_by_verifier":          "pending_full_search",
  "driver_hash":              "pending_full_search",
  "independent_verifier_hash": "pending_full_search",
  "manifest_hash": "<sha256/16>"
}
```
