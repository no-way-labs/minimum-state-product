# Python–Lean parity runner (strengthening task #3)

**Target audit gap.** Appendix A.1 of the paper describes three layers
against Lean `IsValid`-encoding bugs (clause-by-clause docstring
transcription, dual-path Python re-verification, negative-control
checks). All three exist in the sources, but the audit trail was
implicit. This runner ships the dual-path check as an executable
artifact so a referee can **run the script** rather than trust the
authors.

## What it checks

For each small-n witness with both a Python and a Lean encoding
(w4, w5, w6, w7, w8):

1. **lean_parse.** Parses `lean/LeanMn/SmallN/Defs.lean` for the
   witness's `ms` (via `wNM`) and per-processor rule tables (via
   `wNP0 .. wNP(n-1)` match arms).
2. **py_load.** Loads `(ms, rules)` from
   `docs/verify_witnesses.py::witness_nN()`.
3. **parity.** Compares rule tables entry-by-entry under the ms
   bounds; asserts 0 diffs.
4. **verify_lean_encoding.** Runs
   `claude/verifier.py::verify_system()` on the Lean-parsed table;
   asserts `valid = True`.
5. **verify_py_encoding.** Runs `verify_system()` on the Python
   table; asserts `valid = True`.
6. **negative_control.** Copies the Lean-parsed table, flips a
   single move-entry to `S` (i.e. neutralizes one privileged
   transition); runs `verify_system()` on the mutant; asserts
   `valid = False`.
7. **(optional) lake build.** With `--lake`, runs
   `lake build LeanMn.SmallN.Defs`, which succeeds iff every Lean
   `wN_valid : valid wNSystem` theorem compiles. This is the
   Lean-side verification that the paper's Appendix A.1 claims.

Exit code = number of failed steps across all witnesses and the
optional lake build.

## Running

```
cd docs/parity/
python3 -u parity_runner.py             # 6 witnesses + CUP-2 tables + per-n verify
python3 -u parity_runner.py --lake      # also run `lake build LeanMn.SmallN.Defs`
python3 -u parity_runner.py --skip-cup2 # witness-only (faster, n=4..8 sharp)
python3 -u parity_runner.py --cup2-n-max 10 --lake   # full A+ audit
```

Output artifact: `parity_report.json` (per-witness steps with
pass/fail, rule-table hashes, verify_system details, negative-control
targets).

## Scope and known gaps

**In scope (extended 2026-04-22, task #3 round 2).**
- n ∈ {4, 5, 6, 7, 8} witnesses (`w4..w8` in Lean,
  `witness_n4..n8` in Python).
- **n=4 optimal witness** `w4opt` (ms=(2,2,2,3), product 24 = M_4 sharp).
  Python encoding `witness_n4opt()` added to
  `docs/verify_witnesses.py` under this task; parity is now
  round-trip against Lean `w4optSystem`.
- **CUP-2 universal tables** (n-independent): `T_bot, T_low, T_mid,
  T_high, T_top` from Python `claude/cup2_theorem.py` vs Lean
  `TBotVal, TLowVal, TMidVal, THighVal, TTopVal` in
  `lean/LeanMn/Tables.lean`. All 5 tables parity-checked
  entry-by-entry.
- **CUP-2 per-n verification** for n ∈ {4, 5, ..., 10}: build the
  CUP-2 system via `cup2_theorem.build_system(n)`, run Python
  `verify_system`; assert valid. Cycle length matches `3n − 2`
  formula at every n in range.
- **`lake build`** (with `--lake` flag): compiles
  `LeanMn.SmallN.Defs`, which requires every `wN_valid` theorem
  to hold under the project's Lean+Mathlib stack. Expected:
  `Build completed successfully (8029 jobs)`, rc=0.

**Known gap** (flagged for a follow-up extension, not blocking):

- **n ≥ 11 CUP-2 parity.** Python `cup2_theorem.build_system(n)`
  is defined uniformly for all `n ≥ 4` via the 5 universal tables,
  but the Lean `cup2System` + convergence certificates
  (`cup2Converges4..cup2Converges10`) are currently proved only for
  n ∈ {4..10}. Extending Lean-side coverage is a separate Lean-
  formalization task; the Python side already covers
  `verify_system` for n ∈ {5..18} per the paper's §6.
- **CLB vs CUP-2.** The CLB construction
  (`claude/clb_witness_8748.build_system` and its generalization
  `build_clb_witness_v2`) is a distinct witness family that agrees
  with CUP-2 on product = `4·3^(n-2)` but uses a different
  constructional algorithm (good-targeting free-entry completion).
  A full CLB-vs-CUP-2 constructional-equivalence check is out of
  scope for this runner but would be a natural follow-up.

## Why Python is the verifier-of-record

Both sides verify the witness against Dijkstra's five properties,
but the runner uses the Python `verify_system` for both encodings
because:

1. It is the project's gold-standard verifier (`feedback_no_axioms.md`
   — no `native_decide` shortcuts are treated as proof).
2. The Lean validity proofs use
   `native_decide +revert` for the bad-rank-decrease invariant; on
   existing small-n witnesses this is already compiled in the Lean
   sources. `lake build` (optional in this runner) is the symmetric
   Lean check.
3. The point of this runner is **encoding parity**, not verifier
   parity — confirming the two sides describe the same state counts
   and rule tables. Once parity holds, the two sides' validity
   judgments necessarily agree on the same system.

## Expected behavior for a referee

Routine pass: 5/5 witnesses pass every step, exit 0, stdout ends in
`SUCCESS`. The rule-table hashes are deterministic (SHA-256 truncated
to 16 chars) and should match across runs on any machine, fixed per
the witness tables committed to the repo.

If the Python or Lean table is edited, the corresponding hash shifts
and the `parity` step fails with specific per-entry diffs
(first 20 shown in the JSON report).

## Integration with paper §A.1

The paper's Appendix A.1 mentions "three audit layers": clause-by-clause
docstring transcription (the Lean source), dual-path Python
re-verification (the `verifier.py` on each witness), and
negative-control checks (flipped rule entries in dev logs). This
runner ships the second and third as an automated, exit-code-returning
artifact. The first is the Lean source review and is out of scope for
a script.
