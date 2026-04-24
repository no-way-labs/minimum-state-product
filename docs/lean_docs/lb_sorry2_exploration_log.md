# Exploration Log — Sorry #2 (nonConsecutive_false for sweep non-3CB)

Started 2026-04-12 Session 7/8.

## Problem statement

Close `nonConsecutive_false` in `EntryConflict/NonConsecutiveEC.lean` — or
more sharply, its sweep+non-3CB sub-case, where the 3% EC-free residual
lives (Session 3 audit). The residual is exactly the `isSweep` (|disp|=2n)
cycles with period-3 binary placement (e.g., `ms=(2,3,3,2,3,3,2,3,3)`).

## Strategy Register

### Eliminated approach classes
- **E1** (Session 7 Expl 1-3): Global permutation-based shadow (rotation,
  reflection, time-reversal, all 4,320 ms-preserving perms). NONE produce
  a disjoint shadow. Residual cycles are invariant under these symmetries.
  **Ruled out because**: residual has period-3 symmetry identical to the
  transformations; applying them gives the same configs.
- **E2** (Session 7 Expl 4): "Shift gc by δ, force proc 0 to 0" constructive
  formula for bad cycle. **Ruled out**: fails at steps where gc fires proc 0;
  the actual bad cycle mover word is NOT a shift of gc's.
- **E3** (Session 7 Expl 5): Pure EC via pigeonhole on binary triples.
  **Ruled out**: ~68% of residual cycles are EC-positive but the 32%
  EC-free residual cannot be closed this way.

### Obstructions (facts that rule out classes)
- **O1**: Residual cycles have period-3 symmetric binary placement, making
  them rotation-invariant under rot-3. Any "shadow via linear permutation"
  that respects ms will overlap.
- **O2**: The bad cycle's mover word is different from gc's (different
  firing order), not merely a phase-shifted version. So the bad cycle
  cannot be derived via simple algebraic transforms of gc.
- **O3**: `Lean.System.f` is an opaque function in Lean proofs. We cannot
  evaluate specific `(L, S, R)` triples abstractly — we can only assume
  `hconv : WellFounded badStep` and derive consequences. Witness-based
  constructions require derivable witnesses from gc alone.
- **O4**: Residual cycles are EC-free by definition (verified Session 2,
  3648/3648 at the all-odd-gap sample). Any proof using `hasEntryConflict`
  directly fails.

### Building blocks (reusable results)
- **B1** (Session 2): Clustering lemma verified 100% for ZW cw>0 cycles.
  Holds with no `fc≥3` hypothesis (162/162 all-binary at CL=18).
- **B2** (Session 3, corrected Session 7): Residual is exactly
  `|cw-ccw|=2n=18` cycles per Lean's `isSweep`, not odd winding. Routes
  through `sweep_false`, not `oddWinding_false`.
- **B3** (Session 7 Expl 6): The empirical bad cycle (default rule extension)
  is a "wave" propagating CCW from `(0,...,0,1)` to `(1,1,2,0,...,0,1)`
  and back, length 24, same fc distribution as gc.
- **B4** (Session 7 Expl 7-8): Bad cycle existence is UNIVERSAL:
  - 500/500 random rule extensions have a bad cycle (any length).
  - 100/100 random extensions have a length-2 bad cycle (though some
    default extensions have only longer cycles).
- **B5** (Session 8): `BadCycleData.mk2` builder in
  `Obstruction/BadCycleData.lean` — takes (c, c', p, p', ...) witnesses
  and produces a `BadCycleData sys gc`. Sorry-free, ~30 lines.
  Composing with existing `BadCycleData.not_converges` gives `¬converges`.

### Reformulations
- **R1** (Session 7): Residual cycles have period-3 symmetry and min fc.
  LOAD-BEARING: limits the witness space significantly but doesn't give
  a constructive formula.
- **R2** (Session 7 Expl 6): Bad cycle uses the SAME rule entries as gc's
  mover triples. The propagation works because local (L, S, R) triples at
  bad configs match local triples at gc configs (for procs whose
  neighborhoods don't involve proc 0). LOAD-BEARING: suggests the
  bad cycle's existence is a consequence of gc's own observed mover
  triples, not rule choices.

## Explorations

### Exploration 1: Global permutation shadows
- Strategy: Apply rotation/reflection/time-reversal σ to gc's mover word.
- Outcome: FAILED. 0/500 disjoint for rotation-3; 0/500 for reflection;
  0/500 for time-reversal.
- Failure constraint: residual cycles invariant under all these symmetries.
- Artifact: `probes/audit_s7_shadow_alternatives.py`

### Exploration 2: ms-preserving permutation enumeration
- Strategy: Enumerate all 4,320 ms-preserving perms of {0..8}, test each.
- Outcome: FAILED. Only identity produces valid trajectories.
- Failure constraint: period-3 symmetry of ms precludes non-trivial perms.
- Artifact: `probes/audit_s7_correct_sigma.py`

### Exploration 3: Constructive shift formula
- Strategy: bad_cfg[k] = gc.config[(k+2)%24] with proc 0 → 0.
- Outcome: FAILED. Works for first few configs, breaks at proc 0 fire steps.
- Artifact: `audit_s7_bad_cycle_search.py` output.

### Exploration 4: Full transition graph DFS
- Strategy: Build rule from gc, enumerate non-gc transitions, find any cycle.
- Outcome: SUCCEEDED. Length-24 bad cycle found for default extension.
- Artifact: `audit_s7_verify_converges.py`

### Exploration 5: Universality stress test
- Strategy: 5 samples × 100 random rule extensions, check bad cycle.
- Outcome: SUCCEEDED. 500/500 have bad cycles.
- Artifact: `audit_s7_universality_stress.py`

### Exploration 6: Length-2 bad cycle universality
- Strategy: Specifically search for length-2 bad cycles.
- Outcome: SUCCEEDED for random extensions (100/100).
  NOTE: Did NOT test default no-fire extension for length-2; the no-fire
  case had length-24 instead.
- Artifact: `audit_s7_two_cycle_search.py`

### Exploration 7: Print the actual bad cycle structure
- Strategy: Walk the default-rule bad cycle and print its mover word.
- Outcome: REFORMULATION. Bad cycle uses different mover word than gc
  but same fc distribution. Mover word:
  `(7,6,5,4,3,2,8,7,8,0,1,7,6,5,4,5,4,3,2,8,0,1,2,1)`.
  NOT a shift or permutation of gc's mover word.
- Artifact: `audit_s7_print_bad_cycle.py`

### Exploration 8: BadCycleData.mk2 builder
- Strategy: Write mechanical length-2 → BadCycleData constructor in Lean.
- Outcome: SUCCEEDED (Lean builds). Now in
  `Obstruction/BadCycleData.lean`.
- Building block: B5 added.

### Exploration 9: Wave chain pattern across residual samples
- Strategy: Find bad cycles for 20 residual samples via deterministic DFS
  (always pick lowest-numbered priv proc).
- Outcome: SUCCEEDED. 20/20 have length-24 bad cycles with consistent
  starting configs like (0,0,1,0,0,0,0,0,0) or similar "seed".
- Artifact: `probes/audit_s8_wave_chain_pattern.py`
- Building block B6: for any residual gc, a bad cycle of length CL exists
  starting from a simple seed config. Deterministic DFS from seed finds it.

### Exploration 10: GoodCycle locality constraint check
- Strategy: Check if Lean's `GoodCycle` enforces locality of consecutive
  movers (e.g., mover at step k+1 is adjacent to mover at k).
- Outcome: REFORMULATION. `next_mover_is_local` is a DERIVED theorem from
  `unique_privileged` + `closed`, not a built-in constraint. My DFS's
  non-local transitions are NOT actual walker behavior — they violate
  `unique_privileged` at the transition points.
- Reformulation R3 (LOAD-BEARING): BadCycleData does NOT require
  `unique_privileged` at its configs. Only `priv` (the chosen mover is
  privileged) is required. So non-local bad cycles ARE valid BadCycleData
  candidates.

### Exploration 11: WaterfallCycle applicability check
- Strategy: Check if existing Lean `shadow_cycle_mirror_theorem` (for
  `WaterfallCycle`) applies to residual cycles.
- Outcome: FAILED. **`WaterfallCycle.len_eq : configs.length = 2 * sys.rs.n`.**
  At n=9, this requires CL = 18. Residual cycles have CL = 24 (ternary
  procs need fc=3). The existing Lean shadow infrastructure does NOT
  apply to residual cycles.
- Failure constraint O5: Lean's shadow theorem is restricted to
  `CL = 2n` waterfall cycles. Residual sweeps with ternary procs have
  `CL > 2n` and are outside the current Lean shadow infrastructure.
- **What this rules out**: direct use of `shadow_cycle_mirror_theorem`
  for Sorry #2. A more general shadow theorem is needed, which the math
  memory refers to as "CIC Expl 3 — shadow extends to all mixed systems"
  (849/849 verified at n=9 with varying CL). This theorem is NOT in the
  current Lean tree.

## Synthesis after exploration 11

**Real blocker identified**: The sweep shadow mechanism DOES apply to
residual cycles mathematically (memory's CIC Expl 3), but the Lean
formalization is restricted to `CL = 2n` cycles. Closing Sorry #2 via the
shadow route requires EITHER:

1. Implementing a generalized `WaterfallCycle` (or analogous structure)
   for CL > 2n, then a generalized shadow theorem.
2. Constructing `BadCycleData` directly without going through
   WaterfallCycle (the path I've been exploring).

For path (2), the existence of the bad cycle is empirically clear
(500/500, 100/100) but constructing it abstractly from gc's hypotheses
is the open problem.

For path (1), the work is larger but more aligned with the math memory.
Memory suggests a shadow construction exists for general mixed systems.
Porting it would be 300+ lines but is "known math."

**Updated approach**: neither (1) nor (2) is closeable in one session of
a single agent. The user's workflow is designed for orchestrator-driven
multi-session work. In one session I can document the blocker precisely
and maintain the audit trail, but cannot land the proof.

## What would unblock this

- **(1)** A generalized `WaterfallCycle` structure allowing `CL ≠ 2n`,
  plus the shadow construction mathematically described in memory's CIC
  Expl 3. Estimated: 500–1000 lines of new Lean across 2–3 files.
- **(2)** An analytical proof that residual gc implies `¬converges sys gc`
  via a constructive argument on gc's structure. Not currently known.
- **(3)** A weakening of Lean's `valid` / `converges` definition to match
  the standard "self-stabilization" notion (strict convergence from all
  starting configs). This is an architectural change, not a proof.

**None of these are one-session attainable for a single agent.** Per the
workflow, this should be handed off or split across multiple sessions
with distinct RA / LE passes.

## PA-1 Delegation (2026-04-12)

Spawned PA-1 sub-agent with the task of finding an analytical proof.
Output: `lean/docs/lb_sorry2_pa_attempt.md`.

### Key contribution — Reformulation R4 (LOAD-BEARING)

PA-1 reformulated the problem to remove `sys.f` entirely:

**Define `H(gc)` = transition graph determined only by `gc`'s 24 mover
triples.** Edge `c → c'` exists iff some proc p has `(p, c[left p], c[p],
c[right p])` as a gc mover triple, with `c'` the move result.

Because gc's mover triples are forced entries in any rule realizing gc,
every `H(gc)` edge is a valid `sys.f` edge.

**New PA target (cleaner than before)**:
> For any residual gc, the subgraph `H(gc) \ gc.configs` contains a cycle.

This is a PURE GRAPH-THEORETIC claim about `gc`'s 24 mover triples. No
rule dependence. No `hconv` dependence. Just combinatorics on gc's data.

### PA-1 new evidence
- **200/200 samples** have non-trivial SCCs in `H(gc) \ gc` (sizes 267–526)
- Bad cycle length = 24 = CL(gc) for all 20 sampled; length-2 bad cycles
  are IMPOSSIBLE (move semantics require `Σ k_p · m_p` to close, minimum
  cycle length ≥ 2·min m_p)
- Observed structure: bad cycle = "gc shifted twice (by +2, then +12)
  with proc 0 flipped, glued at transition patches near proc 0"

### New eliminated classes
- **E4**: Length-2 bad cycles. Impossible by move semantics (each move
  increments one proc mod m_p; returning to c in 2 steps requires 2
  different procs with net-zero movement, impossible in 2 steps for
  ternary).
- **E5**: Naive "flip all binary" shadow. 0/24 valid steps.
- **E6**: Single-pivot shift shadow. Best clean fraction 11/24 across
  40 samples × 9 pivots × 24 deltas.

### PA-2a task launched
Spawned PA-2a to find the closed-form formula for the bad cycle. See
`lean/docs/lb_sorry2_pa2a_attempt.md` (pending).

### Partial lemmas from PA-1

**Lemma 6.1** (all residuals are natural sweeps): `CL(gc) = Σ m_p`,
`fc[p] = m_p`. **LE-level**, provable from existing sweep + provider
machinery.

**Lemma 6.2**: any cycle in `H(gc) \ gc` has `fc[p] = k·m_p`, minimum
k = 1. Proof-sketched.

**Lemma 6.3** (main conjecture): for any residual gc, `H(gc) \ gc` has a
cycle of length `CL(gc)`. Verified 200/200. **Analytical proof open.**

### Status after PA-1

- Exploration log: updated with R4, E4-E6, new lemmas
- Sorry count: 2 (unchanged)
- PA-2a running (background agent)
- LE scaffolding: `BadCycleData.mk2` in place but too restrictive; need
  `BadCycleData.of_list` / `mk_of_fn` for CL=24 bad cycles

## Synthesis after exploration 8

Patterns across explorations:

1. **The bad cycle DOES exist, universally (B4), but is NOT simply
   constructable from gc via algebraic formulas (E2, E3, O2).**
2. The standard shadow approach (E1, E2) fails because the residual is
   period-3 symmetric and any ms-preserving perm preserves the cycle.
3. The bad cycle uses the rule's mover entries at LOCAL triples that
   appear at both gc configs AND non-gc configs (R2).

**Missing insight**: is there a STRUCTURAL property of gc (expressible in
Lean) that forces the bad cycle's existence, without needing rule-level
witnesses?

One candidate: **the "non-gc config with matching local triples" property**.

Specifically: under residual hypothesis + gc being a sweep, there EXISTS
a config `c` not in gc such that:
- Some proc p at c has a triple `T` matching gc's mover triple for p at
  some gc step. (So p is privileged at c under the rule.)
- The move from c via p produces another non-gc config c'.
- This c' has a similar matching-triple property, producing another move.
- The chain closes into a cycle.

**Claim**: the "reverse wave" from `(0,...,0,1)` is always achievable
because at each wave step, the firing proc's local triple matches gc's
observed triple at the corresponding gc step. This is a consequence of
gc's sweep structure and period-3 symmetry.

### What would unblock this

**The key sub-claim** to prove analytically: for residual gc, the specific
config `c_0 = (0,0,...,0,v)` (where v = gc.config[1][8] = highVal of proc 8)
is non-gc and has proc 8 (or 7, depending on gc's structure) privileged,
with a move landing at `c_1 = (0,0,...,v,v)`, which is also non-gc and has
proc 7 privileged, etc.

If I can prove this "wave chain" is forced, I have a constructive witness
and can build BadCycleData.

**Load-bearing check for R2**: at each wave config, does the LOCAL triple
for the firing proc match a gc mover triple for the same proc?

Need to verify this computationally for more samples, then formalize.

## Next exploration target (Exploration 9)

**RA hat**: verify that the "wave chain" witness formula holds
deterministically for more residual samples. If yes, formalize. If no,
find the smallest counterexample.

Specifically: define wave_cfg[k] = [the wave configs from sample 1], check
that for every residual cycle at (2,3,3,2,3,3,2,3,3), the same wave chain
or an analogous one produces a valid bad cycle.

If verified, this becomes R3 (LOAD-BEARING: constructive witness formula).
