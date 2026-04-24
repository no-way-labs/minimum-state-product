# LLM-Assisted Methodology — Draft Section Notes

Source for a future methods section / appendix in
`paper/main.tex`. Placement deferred until the
in-flight major revision lands; this file captures findings + proposed
structure so the draft can be lifted straight into .tex when the time comes.

Counts computed 2026-04-24 against this shipped artifact (STAGE tree),
excluding `.lake/`, `attic/`/`Attic/`, and `__pycache__/`. The commit-count
row is measured against the full private research tree the artifact was
curated from.

---

## The two protocols

### Residue prompt (`docs/residue_prompt_v2.md`)

Persistent, grepable record of every substantive attempt, maintained in
`exploration_log.md` files scattered through the project tree. Each entry
carries a fixed schema:

- Strategy (one sentence)
- Outcome (SUCCEEDED / FAILED / ABANDONED / STALLED)
- Failure Constraint (specific structural reason, not narrative)
- What This Rules Out (the class, not just the instance)
- Surviving Structure (partial results that outlived the strategy)
- Reformulations (with load-bearing assessment)
- Concrete Artifacts (computed examples, structural results, tools,
  representations)
- What Would Unblock This, Key Parameters, Open Questions

Each log carries a running **Strategy Register** at the top: eliminated
approach classes, obstructions, building blocks, known reformulations —
updated after every exploration. Explicit rules cover session continuity,
periodic synthesis, "when stuck," "when stalled (conceptual vs
computational)," and "when to escalate."

### RA / PA / LE workflow (`docs/ra_le_workflow.md`)

Three specialist roles plus a human orchestrator:

- **RA (Research Agent)** — investigates computationally. Writes Python,
  enumerates examples, verifies conjectures across parameter sizes,
  characterizes failure modes. Delivers verdicts, not proofs.
- **PA (Proof Agent)** — takes RA-verified claims and constructs analytical
  arguments a mathematician would accept. Delivers proof arguments with
  lemmas and justifications; does not write Lean.
- **LE (Lean Engineer)** — writes Lean from PA specs. Fills sorrys, wires
  theorems, verifies builds. Does not investigate whether claims are true.
- **Orchestrator (human)** — decides what to investigate, writes prompts,
  maintains the sorry scoreboard, catches "stinky" work.

Two operating modes:

- **Mode 1** — orchestrator spawns disposable sub-agents (parallelism,
  clean separation, but synthesis burden on the orchestrator).
- **Mode 2** — single agent with deliberate hat-switching (tight feedback,
  full context preserved, but requires discipline to avoid hybrid drift).

The sorry scoreboard is the sole progress metric; anti-patterns catalogued
include sorry fission, duct-tape architecture, RA-without-validation,
LE-without-spec, grinding past diminishing returns.

---

## Magnitude of LLM-assisted work

| Artifact | Count |
|---|---|
| Logged explorations (`## Exploration` entries) | **721** across **30** `exploration_log*.md` files |
| Research `.md` artifacts (all tracked markdown in this artifact) | **117** files / **71,590** lines |
| Lean-side docs (`docs/lean_docs/`) | **42** files / **18,467** lines |
| SK-specific docs (`docs/lean_docs/sk/`) | **15** files |
| Live Lean code (excl `.lake`/`attic`) | **28,728** lines / **50** files |
| Active Lean `sorry`s remaining | **5** (in the research tree `LeanMn.Research`; proved tree is sorry-free) |
| Lean attic (failed routes preserved) | **78,845** lines / **102** files |
| Python under `probes/` (Claude-agent lineage, excl `probes/gpt/`) | **612,665** lines / **2,050** files |
| Python under `probes/gpt/` (GPT-5.4/Codex lineage, + 14 pytest regression tests) | **20,530** lines / **80** files |
| Git commits touching the source research tree | **489** over 2026-03-07 → 2026-04-24 (~7 weeks) |

The 30 logs partition into a Claude-agent lineage (24 logs — `lean`,
`lb`, `lb_endgame`, `ax`, `clb`, `cup2`, `cic`, `3cb_*`, `constlayerdag`,
`sk_*`, `skmh`, `wiggle`, `binscc`, `noncons_terminal`, etc.) and a
GPT-agent lineage (6 logs — `allkiller`, `gec`, `glb`, `m10`, `m5_m9`,
`m9_lb`). The largest are `exploration_log_lean.md` (112 entries),
`exploration_log_lb_endgame.md` (108), `exploration_log_glb.md` (100),
`exploration_log_m5_m9.md` (80), and `exploration_log_m4_lower.md`
(73).

---

## Tooling

- **GPT-5.4 (Xhigh)** via Codex CLI — used for marginal RA/PA probes under
  the RA/LE workflow. Subject to a known "stop reflex" that the
  orchestrator must push through (see
  `feedback_codex_push.md`, `feedback_codex_management_lessons.md`).
- **Claude Opus** (Anthropic) sub-agents — primary LE sorry-closure agent
  and Mode-2 deep-session agent (see `feedback_prefer_subagents_over_codex.md`).
- **Human orchestrator** — one person, Keston Aquino-Michaels, holding the
  sorry scoreboard, the mathematical big picture, and all cross-session
  corrections.

---

## Epistemic guardrails

- No axioms unless backed by a cited published paper; computational-only
  verification is not a proof (`feedback_no_axioms.md`).
- No `native_decide` — find the analytical WHY instead
  (`feedback_no_native_decide.md`).
- Sorry count is the only metric for formalization progress. Not infra
  changes, not line counts, not "files touched" (`feedback_lean_no_infra_loops.md`).
- RA verdicts feed PA arguments which feed LE code; no speculative Lean
  until an RA has verified the underlying claim.
- `attic/` / `Attic/` directories preserve every failed route rather than
  deleting it, so the failure landscape is visible and grepable
  (`feedback_attic_usage.md`).
- Every Lean lemma has a classical proof that does not rely on LLM
  assistance for its truth value; Lean sorries are tracked, not hidden.

---

## What the LLMs did NOT do

- The obstruction catalog in §6 was human-adjudicated, not LLM-asserted.
- No novel mathematical claim was accepted without computational
  verification + human review.
- Detector numbers, LP feasibility verdicts, and exhaustive-search
  certificates are replayable independently of any LLM.
- Sorries remaining in the Lean formalization are tracked in
  `MEMORY.md` + handoff docs; nothing is hidden behind axioms or
  `native_decide`.

---

## Proposed section structure (for when the revision lands)

Placement options to revisit:

- **(A)** New body section `\section{LLM-assisted methodology}` inserted
  between §8 Related work and §9 Conclusion (~1 page).
- **(B)** New appendix `\section{LLM-assisted methodology and artifact
  inventory}` after `app:landscape-detail` (~2 pages, with full table).
- **(C)** Short Conclusion subsection + fuller appendix. Mirrors how
  detectors are treated (main text + formal appendix).

Current default recommendation: **(C)**.

Subsections in any placement:

1. Framing paragraph — detectors, failed-approach catalog, Lean
   formalization, exhaustive-verification pipeline all produced under two
   named protocols; this section states protocols + volume for provenance.
2. The residue-prompt protocol — one paragraph citing
   `docs/residue_prompt_v2.md`.
3. The RA/PA/LE workflow — one paragraph citing `docs/ra_le_workflow.md`.
4. Quantitative table (as above).
5. Epistemic guardrails (bullets).
6. What the LLMs did not do (bullets).
7. Models used (one paragraph).

## Open calls before .tex drafting

1. Placement: (A), (B), or (C)?
2. Python LOC: broken out by agent lineage (Claude / GPT) or a single
   "≈633K lines of Python probes/verifiers" headline?
3. Model disclosure: specific names (GPT-5.4, Claude Opus) or generic
   ("two frontier LLM families from OpenAI and Anthropic")?

---

## Reproducibility — how the counts were computed

Run from the repository root.

```bash
# Explorations
grep -c '^## Exploration' exploration_logs/*.md | awk -F: '{t+=$2} END{print t}'

# Research .md artifacts (count + lines, tracked only)
git ls-files | grep '\.md$' | wc -l
git ls-files | grep '\.md$' | xargs wc -l | tail -1

# Live Lean code (excl .lake and attic)
find lean -name '*.lean' -type f \
  -not -path '*/.lake/*' -not -path '*/attic/*' -not -path '*/Attic/*' \
  | xargs wc -l | tail -1

# Active sorrys (comment-suppressed lines excluded)
find lean -name '*.lean' -type f \
  -not -path '*/.lake/*' -not -path '*/attic/*' -not -path '*/Attic/*' \
  | xargs grep -nE '^[^-]*\bsorry\b' | grep -v -- '--.*sorry' | wc -l

# Lean attic (failed routes preserved)
find lean -name '*.lean' \( -path '*/attic/*' -o -path '*/Attic/*' \) \
  | xargs wc -l | tail -1

# Python by lineage
find probes -name '*.py' -type f -not -path '*/gpt/*' \
  -not -path '*/__pycache__/*' | xargs wc -l | tail -1
find probes/gpt -name '*.py' -type f \
  -not -path '*/__pycache__/*' | xargs wc -l | tail -1

# Commits (run against the source research tree, not this artifact)
git log --pretty=format:'%ad' --date=short --  | wc -l
```
