# Minimum state product for self-stabilizing token rings

[![DOI](https://zenodo.org/badge/1178892429.svg)](https://doi.org/10.5281/zenodo.19744462)

Companion artifact for the paper
**"Minimum State Products on Dijkstra's Token Ring: Exact Values for
n = 3 through 9 and a large-n conjecture supported through n = 10."**

Zenodo archive DOI: [10.5281/zenodo.19744463](https://doi.org/10.5281/zenodo.19744463)

## What's here

- `paper/` — the paper source (`main.tex`, `references.bib`) and built
  PDF (`main.pdf`).
- `lean/` — the Lean 4 / Mathlib formalization. `lake build` in this
  directory should succeed on the pinned toolchain.
- `probes/` — the full set of Python research probes (~2,100 files,
  ~633k LoC). These back every empirical claim in the paper, including
  the landscape-detail appendix. The top level collects the primary
  Claude-agent probe lineage (2,050 scripts); `probes/gpt/` collects a
  parallel GPT-agent lineage (80 probes + 14 pytest regression tests) —
  the dual-agent methodology used to cross-check results is described
  in `docs/ra_le_workflow.md`.
- `docs/` — the independent Python verifier, research memos, and the
  RA / PA / LE workflow documentation.
- `docs/lean_docs/` — Lean-program findings memos, post-mortems, plans,
  roadmaps, and the per-session audit trail.
- `exploration_logs/` — 30 chronological narrative research logs
  spanning the Python-probe and Lean-formalization sides of the program.
- `corpus.json`, `corpus_canonical.json`, `coverage_manifest.json`, and
  other top-level data artifacts — paper-cited datasets. See the paper's
  Appendix L for the full manifest.
- `REVIEWER.md` — theorem ↔ single-reproduction-command map; the
  contract between the paper and this artifact.
- `requirements.txt` — pinned Python dependencies (numpy, scipy,
  z3-solver, more-itertools). Only required for the exploratory probes
  that use z3 / scipy; the dispositive checks are stdlib-only.

The volume is deliberate. A reader should see that the paper's
surviving results are the ridge of a much larger exploratory program.

## Start here

1. Read `paper/main.pdf`.
2. Open `REVIEWER.md` — each theorem, observation, and conjecture in
   the paper is paired with a single reproduction command.
3. Skim `docs/ra_le_workflow.md` for the research-workflow methodology.
4. See [Reproducing the results](#reproducing-the-results) below for
   build, verify, and re-run instructions.
5. `docs/lean_docs/lb_all_paths_history.md` is the master ledger of
   attempted lower-bound routes. `exploration_logs/` collects 30
   chronological narrative logs from both agent lineages — Python probe
   side (`exploration_log_clb.md`, `exploration_log_cup2.md`,
   `exploration_log_3cb_*.md`, `exploration_log_allkiller.md`,
   `exploration_log_glb.md`, `exploration_log_m9_lb.md`, etc.) and Lean
   formalization side (`exploration_log_lean.md`, `exploration_log_lb.md`,
   `exploration_log_ax.md`, etc.) — the day-to-day research record.

## Scope

The Lean formalization is split into two targets so that *proved
claims* and *open research obligations* are distinguished in the build
verdict itself:

- `lake build` (default target `LeanMn`) — verifies every paper-cited
  theorem. Compiles **sorry-free** with zero `declaration uses sorry`
  warnings.
- `lake build LeanMn.Research` — compiles the sink-kernel lower-bound
  program for general `n`. Builds successfully but surfaces 5
  `declaration uses sorry` warnings corresponding to the
  stated-but-not-yet-proved obligations the paper discusses in §7 and
  Appendix K.

A reader running `lake build` on a fresh clone should see a clean green
verdict for the proved results.

The independent Python verifier re-checks every stored witness and every
rejection certificate. The exhaustive-search coverage manifest
reproduces bit-for-bit (overall `manifest_hash` = `f684ed53216a0d7f`,
the truncated SHA-256 over the manifest payload computed by
`generate_manifest.py`; the file's own SHA-256 depends on JSON
whitespace and is not the stability check).

Not every probe under `probes/` is runnable standalone — some reference
intermediate data produced by sibling probes, and a small number
originally imported from external research projects. Affected files
carry an in-file note. The full set is shipped as a research record,
not as a product.

## Reproducing the results

### Python version

Python 3.11 or newer (tested on 3.13.2). The dispositive checks
(`docs/verifier.py`, `docs/verify_witnesses.py`, and
`probes/exhaustive_search/`) are standard-library only — no `pip
install` required to reproduce the paper-cited verdicts.

The exploratory probes under `probes/`, the SMT-based certificates
under `docs/axisc/` + `docs/m5rel/`, the circulation-LP detector under
`docs/topo_revival/`, and `exact_check.py` (the rationalising LP post-
check) import `numpy`, `scipy`, `z3-solver`, or `more-itertools`. Pin
them all at once with:

```bash
python3 -m venv .venv && . .venv/bin/activate
pip install -r requirements.txt
```

The pins in `requirements.txt` are exact; loosening them breaks the
bit-for-bit reproducibility claim.


### Rebuild the paper

Requires a TeX Live (or equivalent) distribution with `pdflatex` and
`bibtex`. Takes ~1–2 minutes.

```bash
cd paper
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

### Build the Lean formalization

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).
The toolchain is pinned to `leanprover/lean4:v4.28.0` by
`lean/lean-toolchain`; `elan` will download it on first use.

```bash
cd lean
lake exe cache get    # download prebuilt Mathlib .olean cache (~5 GB)
lake build            # compile this project on top
```

**Do not skip `lake exe cache get`** unless you actually want to
recompile all of Mathlib from source. With the cache, first-time build
takes roughly **25–55 minutes end-to-end** (cache download ~10–20 min,
project build ~10–30 min, the latter dominated by 120 `native_decide`
invocations that each fork a C compile + run). Without the cache,
Mathlib rebuilds from source and the total is 1.5–4 hours depending
on your CPU.

Subsequent builds reuse `.lake/build/` and take seconds to a few
minutes unless you touch a heavily-imported file.

**Dependencies** are pinned by `lake-manifest.json`: Mathlib v4.28.0,
plus batteries, aesop, Qq, proofwidgets, plausible, importGraph, Cli,
LeanSearchClient. No manual dep management required.

This command builds `lean_lib LeanMn`, the **proved tree**. It verifies
every paper-cited theorem and compiles **sorry-free**. Specifically, the
proved tree covers:

- The `M_4 = 24` exact-value theorem (`SmallN/Theorem.lean`,
  `LowerBound/SmallN/LB2222.lean`).
- Upper-bound constructions for all `n >= 4`, including the CUP-2
  certificate chain (`UpperBound/`, `SmallN/Cup2Convergence.lean`,
  `Cycle.lean`, `Tables.lean`).
- Proved lower-bound infrastructure (`LowerBound/CycleTypes.lean`,
  `FireCountNe.lean`, `GoodCycleBasics.lean`, the `EntryConflict/`
  tree, and the sorry-free SK primitives `Forcing`, `SinkKernel`,
  `PartialDet`, `SlabCounting`).

#### Building the research tree (open obligations)

The sink-kernel lower-bound program for general `n` is research in
progress. These modules are collected under `LeanMn.Research`:

```bash
cd lean
lake build LeanMn.Research   # after lake exe cache get + lake build
```

Incremental on top of the proved-tree build; adds a few minutes.
Compiles successfully but surfaces **5 `declaration uses sorry`
warnings** — the stated-but-not-yet-proved obligations described in
the paper's §7 and Appendix K:

- `LowerBound/SK/HammingTube.lean` — 2 obligations
- `LowerBound/SK/EdgeMajorityB2.lean` — 2 obligations
- `LowerBound/SK/SlabCountingRing.lean` — 1 obligation

These files compile, meaning their *statements* are well-typed and
usable by downstream modules (`CloudsTheorem`, `SmallN/CloudsLB`,
`LargeN/CloudsLB`). Their *proofs* remain to be filled in.

### Re-run the independent verifier

Pure Python, stdlib-only — no external package installs required.
Spot-checks every stored witness and rejection certificate. Runs in
under a minute.

```bash
python3 docs/verifier.py
python3 docs/verify_witnesses.py
```

### Reproduce the exhaustive lower-bound coverage manifest

Stdlib-only. Deterministic; the `manifest_hash` field inside
`coverage_manifest.json` reproduces bit-for-bit to
`f684ed53216a0d7f` (truncated SHA-256 over the C1 + C2 payload).
The C1 + C2 portions populate in seconds from a clean clone.

```bash
python3 probes/exhaustive_search/driver.py           # C1+C2 summary
python3 probes/exhaustive_search/generate_manifest.py  # writes coverage_manifest.json
```

The per-certificate rejection stream (C3 + C4 + C5) ships in full
for `n ∈ {3, 4}` and the all-binary orientation at `n = 5`;
aggregate counts for the remaining `n = 5` orientations are in
`artifacts/rejections/summary.json`. Regenerating a full
per-orientation stream for `n ∈ {5, ..., 9}` is done via the
compiled C worker (seconds to hours per orientation on a single
core):

```bash
cd probes/exhaustive_search && make
./exhaustive --n N --ms <sorted> --orient <orient> > out.jsonl
python3 driver.py --replay out.jsonl
```

See `probes/exhaustive_search/REJECTION_STREAM.md` for the full
ship-state rules.

### Re-run a probe

Every `.py` under `probes/` is a research probe. Most reference
repo-relative paths (e.g. `./probes/...`) and expect to be run from the
repository root:

```bash
python3 probes/<probe-name>.py
```

See the per-probe exploration-log memos under `probes/*.md` for
interpretation. Probes under `probes/branch_b_bypass/` and
`probes/sk_*_out/` are session-specific research artifacts — some are
self-contained, others depend on intermediate data generated by sibling
probes. The paper's Appendix §K (landscape-detail) indicates the
provenance for each reported result.

#### GPT-agent probe lineage

`probes/gpt/` collects a parallel GPT-agent probe lineage (~90 scripts
plus 14 pytest regression tests under `probes/gpt/tests/`). These were
produced by a second agent running against the same problem statement;
the dual-agent methodology is documented in `docs/ra_le_workflow.md`.

```bash
python3 probes/gpt/<probe-name>.py
python3 -m unittest probes.gpt.tests.test_<probe-name>
```

The pytest suite is the only regression-test coverage in this artifact
— the Claude-agent lineage was validated against paper-cited witnesses
via `docs/verifier.py` rather than unit tests. A handful of GPT-lineage
tests invoke an external `src_comp_ver/` verifier that is not shipped
in this artifact.

### Note on runtime scope

Not every probe in this repository is runnable standalone. Some
originally depended on data or tools outside this artifact (e.g.
`probes/brainstorm_parity.py` references an external `paper3_dev_010`
generator that is not included). Affected files carry an in-file note.
The full set is shipped for research-record transparency, not because
every probe is reproducible in isolation.

## Contact

Keston Aquino-Michaels — <kestonamichaels@gmail.com>.

The single best form of referee feedback is a reproducibility issue
on any row of `REVIEWER.md` — please quote the command you ran, the
expected output per that file, and the actual output.

## License

See `LICENSE` (MIT, code). The paper text (`paper/main.tex`,
`paper/main.pdf`) is provided under its own licensing terms — see the
paper itself.

## Citation

See `CITATION.cff`. (Zenodo DOI is assigned at archive-mint time.)
