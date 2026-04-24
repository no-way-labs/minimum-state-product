# UB Convergence Post-Mortem

## What happened

The Lean formalization of CUP-2 convergence diverged from the best known
proof, resulting in ~14,855 lines of dead-end infrastructure that had to be
excised and replaced with ~400 lines following the correct approach.

## Timeline

### Before March 12 — AP development phase (Python exploration)

During development of the analytical proof (`verification_claims_v2.md`,
`verification_claims_v4.pdf`), the Python exploration scripts generated
extensive computational verification. The AP was written with the B1-B4
table-chase convergence proof (§3.4): per-entry forced-sequence analysis,
individual refire bounds, O(n⁴) convergence.

During this same AP development phase, the CLB exploration scripts
(`clb_convergence_proof103.py` through `clb_convergence_proof107.py`)
discovered a strictly better convergence proof:

- Φ_full = max reachable fc (non-increasing on every bad step)
- Constant-Φ_full subgraph is a DAG: 6-tuple automaton (617 transitions,
  324 states, rank 24) + boundary-fixed interior hop impossibility
- Two-level potential Ψ = Φ_full·(R+1) + rank gives O(n²) convergence
- No per-entry case analysis of B1-B4 anomalous entries needed

**The AP was never updated to reflect this discovery.** The Φ_full proof
existed only in the Python scripts. The AP was finalized with the old
table-chase proof, and the formalization plan (`lean_formalization_plan.md`)
was written from the AP.

### March 12-13 — Lean agent begins, follows the AP

The Lean formalization agent starts building convergence infrastructure.
It follows the AP faithfully (§3.4):

- Part A: copy-neighbor DAG with (fc, Ψ) potential
- Part B: B1-B4 anomalous entry refire bounds via forced boundary sequences
- Part C: combine A+B for total convergence

The agent builds TP-preservation infrastructure, endpoint-refined certificates,
boundary-slack coding, witnessed state decompositions — all faithful to the
AP's table-chase approach. The formalization plan's Phase 3B explicitly
describes this approach. The agent is doing exactly what it was told.

### March 14 morning — Divergent infrastructure reaches ~14,000 lines

Files created: `EndpointRefinedWitnessCert.lean` (4918 lines),
`EndpointRefinedProjectedCert.lean` (1743 lines), `BoundarySlackCert.lean`
(896 lines), `BoundarySlackCopyReachCert.lean` (755 lines), and several
others. `Main.lean` grows to 5276 lines of conditional convergence theorems.

The cert-based routes (`cup2EndpointRefinedWitnessCertStep`,
`cup2EndpointRefinedProjectedCertStep`) have false hypotheses — the
decomposition doesn't work as hoped. The agent is stuck but keeps building
more infrastructure trying to make it work.

### March 14 afternoon — Lean agent encounters the Python result

Exploration 31 in the Lean exploration log documents the Φ_full approach
from the Python scripts. But by now, 14,000+ lines of infrastructure exist.
The agent doesn't scrap and restart — it tries to patch the existing
approach instead.

### March 14 — Orchestrator intervenes

The divergence is identified. A new UB agent introduces an honest axiom
(`cup2AnomalousSegmentWf`) to unblock the upper bound assembly, a rewrite
plan (`ub_rewrite_plan.md`) is created, and a fresh agent executes it:
deletes 11 dead files, trims SixTuple.lean from 4359 to 778 lines, creates
PhiFull.lean (165 lines), ConstLayerDAG.lean (148 lines), new Main.lean
(57 lines). Total Convergence/ drops from ~23,000 to 3,673 lines.

## Root cause

### A race condition between parallel proof tracks

The Φ_full + 6-tuple proof was discovered during the **AP development phase
itself**, not later during Lean formalization. Multiple Python agents were
exploring convergence in parallel (the commit bundles proof88 through
proof107 — a 20-script batch). The AP was being written concurrently, based
on whichever proof route was mature enough at writing time.

The commit on March 11 tells the story:

> `CLB convergence proof88-107 + verify_fast C rewrite + paper outline + Lean plan`

The Φ_full discovery (proof103-107), the AP (paper outline), and the Lean
formalization plan were all committed **in the same commit**. The Φ_full
route matured late in the exploration batch — likely after §3.4 of the AP
was already drafted around the earlier-maturing B1-B4 table-chase proof.

The AP crystallized around the table-chase proof. The Lean plan was derived
from the AP. The Φ_full scripts sat in the same repo, uncommitted alongside
the document that didn't reference them, and everything was bundled together
in one checkpoint commit.

This is not a failure of cross-track communication between independent
systems. It's a race condition within a single development phase: parallel
proof exploration and document writing were running concurrently, the
document locked in the earlier proof, the better proof finished moments
too late, and nobody noticed the gap before the commit shipped.

Everything downstream followed correctly from incorrect input:
- The formalization plan (`lean_formalization_plan.md`) faithfully transcribed
  the AP's Phase 3B (B1-B4 forced sequences)
- The Lean agent faithfully followed the formalization plan
- The Lean agent built exactly what it was told to build
- The Lean agent eventually stumbled on the Python scripts (Exploration 31)
  but by then had 14,000 lines of sunk infrastructure

### Contributing factors

**Sunk cost momentum.** Once ~14,000 lines existed, the Lean agent tried to
make the existing approach work rather than starting over. The cert-based
routes had false hypotheses, but the agent kept building more machinery
(projected certs, boundary-slack variants) trying to find a path.

**Exploration log masked the stall.** The Lean exploration log grew to 100+
explorations, creating an appearance of progress. Many explorations were
"discovery loops" — rediscovering the same blockers in slightly different
framings. The volume of activity obscured the fact that the core approach
was stuck.

**No line-count alarm.** The convergence proof should have been ~500-800 lines
based on the analytical argument's complexity. It reaching 5,000+ lines was
a red flag that went unnoticed.

## Lessons

1. **Checkpoint commits need a reconciliation pass.** When a batch commit
   bundles exploration results alongside a document or plan derived from
   those results, someone (human or orchestrator agent) must verify that
   the document reflects the best result in the batch — not just whichever
   result was mature when drafting started. The March 11 commit contained
   both the answer (proof107) and the wrong instructions (AP §3.4 / Lean
   plan Phase 3B) in the same commit. A 10-minute review would have caught
   the gap.

2. **Parallel proof exploration needs a winner-selection step.** When
   multiple agents explore alternative proof routes concurrently, there
   must be an explicit moment where the best route is selected and all
   downstream artifacts (AP, formalization plan, agent instructions) are
   updated to reflect it. Without this, the document crystallizes around
   whichever route matured first, not whichever route is best.

3. **Punch lists over exploration logs.** The exploration log format
   encourages open-ended discovery. For formalization tasks with known
   proof structures, a punch list with explicit axiom targets is more
   effective.

4. **Detect divergence early.** If the Lean code exceeds 2x the expected
   line count for a component, that's a signal to audit whether the
   approach matches the analytical proof. The convergence proof should
   have been ~500-800 lines; it reaching 5,000+ was a red flag.

5. **The AP and the Lean formalization don't need to use the same proof.**
   The AP's table-chase reads cleaner for human reviewers. The Φ_full
   approach is better for machine verification. Both prove the same
   theorem. But the divergence should be documented, not accidental.

## Current state

- Convergence/ is 3,673 lines (down from ~23,000)
- One assembly axiom remains: `cup2BadConstFutureStep_wf` in ConstLayerDAG.lean
- The proof follows the analytical structure: Φ_full + 6-tuple + interior hop
- The AP (v2 and v4) still describes the old table-chase proof (§3.4)
- The formalization plan still describes Phase 3B with B1-B4 forced sequences

## Action items

- [ ] Close `cup2BadConstFutureStep_wf` axiom (wire TP.lean + CopyDAG.lean +
      SixTuple.lean + Interior.lean together)
- [ ] Add remark to AP noting the Lean formalization uses the Φ_full approach
      (§3.4 alternative)
- [ ] Consider updating formalization plan Phase 3B/3C to match actual Lean
      structure (optional — plan is less critical now that the code exists)
