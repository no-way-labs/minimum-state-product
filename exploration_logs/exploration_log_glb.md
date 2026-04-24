# Exploration Log

## Strategy Register

### Eliminated approach classes
- Literal per-processor `state -> Z3` homomorphism proofs, where every non-binary move must collapse to a fixed `+1 mod 3` transition on the recurrent cycle, are too rigid for the known optimal `n = 5..8` witnesses (exploration 1). Structural reason: the quaternary-assisted witnesses use richer local transition graphs, so any viable phase proof has to work at the level of interfaces or delayed signal transport, not raw state labels.
- Dynamic phase-quotient proofs that require the moving processor to change its phase class on every good-cycle step are too rigid even for the one-binary Sol-3 family (exploration 2). Structural reason: there are useful low-defect `Z3` quotients, but they track moving defect edges rather than forcing the mover's own phase label to flip every time.
- Directly reading the target product `2·3^(n-1)` off the abstract width-`2` quotient alone is too weak (exploration 4). Structural reason: the width-`2` quotient exposes a stable two-ended role skeleton, but one endpoint can have only two abstract mover roles while still needing three raw states, so abstract phase-role counts do not determine raw multiplicities by themselves.
- Good-cycle local automaton minimization is too weak to force the target product (exploration 5). Structural reason: in the one-binary Sol-3 family, the top endpoint compresses to a 2-state deterministic local automaton on the good cycle, so the extra third raw state is not forced by good-cycle behavior alone and must serve off-cycle stabilization.
- Naive raw cut-chain variation does not by itself recover the quaternary support zone in the known `n = 5..8` optimal witnesses, even after scanning all cyclic cuts; positive-variation movers still spread too widely (explorations 11 and 13 probes). Structural reason: the small optima do not live in the raw Sol-3 coordinate system, so the cut-chain picture needs more than a bare raw cut choice before it can generalize.
- Arbitrary minimum-width phase quotients are too noncanonical to carry the source-count picture (exploration 12). Structural reason: for the same witness, different satisfying quotient gauges can shift, blur, or even eliminate positive phase-variation sources under some cuts, so “solve for any width-minimizer and cut the chain” is not a stable representation.
- Short-budget survivor-free `p2_cycle_screen` runs are not reliable negative evidence against the new bound architecture (exploration 14). Structural reason: a `20s / 200000` screen on the valid shape `(2,3,3,3,3,3,3,3,2)` finds zero survivors even though a locally consistent 25-step bounce scaffold exists there, so that screening regime can miss the relevant good-cycle shape entirely.

### Obstructions
- In the canonical product-`8748` two-binary Sol-3-v1 probes, adding a second binary creates either a branching three-phase mediator configuration or a dead configuration rather than a single privileged interface (exploration 1). This is not a theorem for arbitrary systems, but it is the first concrete sign that a second binary behaves like a second phase puncture.
- The known optimal witnesses for `n = 5,6,7,8` do not admit any processor-local `Z3` quotient with defect width `2`; their minimum phase-defect widths are `3,3,4,4` respectively (exploration 2).
- In the canonical product-`8748` two-binary Sol-3-v1 probes with an internal extra binary, the cut-chain variation can increase at that extra binary as well as at the top endpoint, so the system has more than one variation source before any convergence analysis is applied (exploration 10).
- Minimum-width quotient source counts are gauge-sensitive: in trial phase-width minimizers for the known `n = 5..8` witnesses and the one-binary `n = 9` family, some cuts produced no positive phase-variation source at all, while others produced several, so source-count is not an invariant of an arbitrary minimizing quotient (exploration 12).
- In the exact `n = 9` frontier `(7776,8748)`, there are no 3-binary multisets at all. After Case 1 and Case 2, the live residue consists only of mixed families with `4,5,6` binaries (exploration 14).

### Building blocks
- The `n = 9` one-binary witness `(2,3,3,3,3,3,3,3,3)` has an exact recurrent cycle consisting of step-function configurations with a single moving phase boundary and mover pattern `7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8` (exploration 1).
- In that witness, every interior ternary moves in exactly three local contexts `((0,0,1)->1)`, `((1,1,2)->2)`, `((0,2,2)->0)`, while the distinguished binary moves in exactly two contexts `((1,0,1)->1)`, `((2,1,2)->0)` (exploration 1).
- In all known optimal witnesses for `n = 5,6,7,8`, every binary processor lies within ring distance `<= 3` of a processor with at least four states (exploration 1).
- `scripts/glb_phase_probe.py` (exploration 1): extracts the one-binary recurrent cycle, reports the mover-context summary, computes binary-to-support distances in the small witnesses, and prints canonical two-binary product-`8748` failure modes.
- Phase-defect width: for a good cycle, map each local state to a phase in `Z/3Z` and count defect edges where adjacent phases differ; require all three phase values to appear and require the unique mover to be adjacent to at least one defect. This yields a concrete minimization problem over processor-local `Z3` maps (exploration 2).
- The one-binary Sol-3-v1 family has phase-defect width exactly `2` for every tested `n = 5..12` (exploration 2).
- `scripts/glb_phase_width.py` (exploration 2): computes the minimum feasible phase-defect width for the built-in small optimal witnesses and the one-binary Sol-3 family by solving a local `Z3` quotient problem on the recurrent good cycle.
- Support-chain radius: in the known small optimal witnesses, every binary move can be matched to a contiguous recent mover chain starting from a small neighborhood of the unique `>=4`-state processor, with minimum required radii `1,0,2,3` for `n = 5,6,7,8` respectively (exploration 3).
- In the one-binary Sol-3 family, the width-`2` quotients found for every tested `n = 5..12` have the same abstract mover-role count pattern `[2,3,3,...,3,2]` across processors (exploration 4).
- In the one-binary Sol-3 family, the gap between full local-rule complexity and good-cycle local automaton complexity is concentrated at the top endpoint: at `n = 5` and `n = 9`, the gap vectors are `[0,0,0,0,1]` and `[0,0,0,0,0,0,0,0,1]` respectively (exploration 6).
- The known optimal witnesses have convergence-gap vectors:
  - `n5`: `[0,0,0,1,2]`
  - `n6`: `[0,0,0,1,0,0]`
  - `n7`: `[0,0,0,0,1,1,0]`
  - `n8`: `[0,0,1,1,1,0,0,1]`
  (exploration 7).
- In the one-binary Sol-3 family, the product of the good-cycle local automaton sizes is exactly `4·3^(n-2)`, and the full local-rule product is larger by exactly a factor `3/2`, yielding `2·3^(n-1)` (exploration 8).
- The one-binary Sol-3 family has the convergence-gap vector `[0,0,...,0,1]` and convergence multiplier `3/2` at every explicitly checked size `n = 5,6,7,8,9` (exploration 9).
- Cut-chain variation: after cutting the ring at `P0`, define
  `V(cfg) = |{ i in {0,...,n-2} : cfg[i] != cfg[i+1] }|`.
  In the one-binary Sol-3-v1 family, `V` can increase only when the top endpoint `P_{n-1}` moves, for every tested `n = 5..12`, and the good cycle has `V in {0,1}` throughout (exploration 10).
- `scripts/glb_variation_probe.py` (exploration 10): computes cut-chain variation delta counts, the movers that can increase variation, and good-cycle variation values for the one-binary family and canonical near-bound Sol-3-v1 probes.
- Top-source move contexts distinguish ternary source strength from binary source strength:
  - one-binary `n = 9` top moves in contexts `(0,0,0)->1`, `(0,2,0)->1`, `(1,0,1)->2`, `(1,1,1)->2`
  - endpoint-binary probe `(2,3,3,3,3,3,3,3,2)` top moves in contexts `(0,0,0)->1`, `(1,1,1)->0`, `(2,0,0)->1`
  so the binary source cannot emit the phase-`2` lift that the ternary source can (exploration 11 probe).
- `scripts/glb_sub8748_inventory.py` (exploration 14): inventories the exact `n = 9` frontier `(7776,8748)`, classifies families by Case 2, and summarizes the `644` safe necklaces by binary run type.
- Exact `n = 9` frontier below `8748`: `24` multisets total, `12` fully blocked by Case 2, `12` mixed, and `644` safe necklaces in total (exploration 14).
- The safe sub-`8748` frontier collapses to only `11` cyclic binary run types:
  - `k = 4`: `(1,1,1,1)`, `(2,1,1)`, `(2,2)`, `(3,1)`
  - `k = 5`: `(2,1,1,1)`, `(2,2,1)`, `(3,1,1)`, `(3,2)`
  - `k = 6`: `(2,2,2)`, `(3,2,1)`, `(3,3)`
  (exploration 14).
- `scripts/glb_seeded_bounce_probe.py` (exploration 14): probes a calibrated 25-step bounce mover sequence
  `0,1,...,8,7,...,1,0,1,...,8`
  against the bound shape and the exact sub-`8748` frontier.
- The calibrated 25-step bounce mover sequence admits a locally consistent good cycle on the bound shape `(2,3,3,3,3,3,3,3,2)` and fails on one representative of each of the `11` safe binary run types below `8748` (exploration 14).
- The calibrated 25-step bounce scaffold is componentwise minimal: lowering any interior coordinate of `(2,3,3,3,3,3,3,3,2)` from `3` to `2` destroys local consistency for that mover sequence (exploration 15 probe).

### Known reformulations
- Phase-puncture picture: the one-binary witness is best viewed as a hidden three-phase interface system with one omitted phase site. LOAD-BEARING: high. The recurrent cycle is not an arbitrary bounce; it is a single interface sweeping through three residue levels, and the binary appears exactly where one phase is missing.
- Causal-delay picture: treat extra binary processors as needing directional information to arrive through radius-1 updates from a nearby higher-state “support” processor. LOAD-BEARING: high. The known `n <= 8` optimal witnesses satisfy a sharp empirical radius-`3` support condition for every binary, matching the “out of earshot” narrative at `n = 9`.
- Phase-defect width: instead of asking for a literal phase on every raw state transition, ask for the smallest number of phase boundaries needed to represent the whole good cycle after a processor-local quotient to `Z/3Z`. LOAD-BEARING: high. It cleanly distinguishes the one-binary Sol-3 family (width `2`) from the known small optimal witnesses (width `3` or `4`) and gives a finite optimization target for future structural proofs.
- Support zone rather than support node: the quaternary in the known `n <= 8` witnesses should not be treated as a single magic processor; the relevant causal object is a small neighborhood around it from which contiguous mover chains can feed every binary move. LOAD-BEARING: high. `n = 8` already saturates radius `3`, which aligns exactly with the “out of earshot at n = 9” story.
- Width-`2` role skeleton: the one-binary family appears to have a canonical abstract shape with two endpoint movers of role-count `2` and an interior run of role-count `3`. LOAD-BEARING: moderate. This looks like the right abstract normal form for width-`2` cycles, but by itself it does not recover the raw-state product.
- Separate good-cycle complexity from stabilization complexity: some raw states may be needed only to achieve convergence from bad configurations, not to realize the eventual good cycle itself. LOAD-BEARING: high. Exploration 5 shows the top ternary of the one-binary family can be compressed to a 2-state local automaton on the good cycle, so any full lower bound must use off-cycle convergence data, not just recurrent-cycle structure.
- Convergence gap per processor: define the local convergence burden as
  `(minimum full local transducer size) - (minimum good-cycle local automaton size)`.
  LOAD-BEARING: high. In the one-binary family the observed gap is zero everywhere except at the top endpoint, which isolates the extra off-cycle state very sharply.
- Support-zone convergence burden: in the known `n = 5..8` optimal witnesses, positive convergence gap is not arbitrary; it clusters on or near the same quaternary-centered support zones seen in exploration 3, with `n = 8` also showing a top-endpoint gap. LOAD-BEARING: high. This is the first direct bridge between the support-zone picture and the new convergence-gap invariant.
- Case-1 gap as convergence multiplier: the classical weak arithmetic bound `4·3^(n-2)` can be reinterpreted as a recurrent/good-cycle complexity product, and the missing factor `3/2` needed to reach `2·3^(n-1)` is exactly the local convergence upgrade of one endpoint from `2` states to `3`. LOAD-BEARING: very high. This is the first clean “why the answer is `2·3^(n-1)`” explanation that matches the actual one-binary family numerically.
- Cut-ring variation-source picture: cut the ring at the distinguished binary and track the linear variation `V(cfg)` on the resulting chain. LOAD-BEARING: high. In the one-binary family, all non-top moves only transport or annihilate variation, while the top endpoint is the unique source that can create a new interface on the chain; the canonical internal two-binary failures create a second source exactly at the extra binary (exploration 10).
- Exact sub-`8748` frontier as binary skeletons: for `n = 9`, the whole unresolved interval below `8748` reduces to `24` multisets, `12` mixed families with safe orientations, and only `11` cyclic binary run types. LOAD-BEARING: high. This is the first genuinely small finite search space for the new lower-bound target (exploration 14).
- Calibrated 25-step bounce scaffold: the mover sequence
  `0,1,...,8,7,...,1,0,1,...,8`
  is a concrete locally consistent wave on `(2,3,3,3,3,3,3,3,2)` and appears incompatible with the sub-`8748` run types tested so far. LOAD-BEARING: moderate to high. It gives a witness-shaped good-cycle normal form to test against the new exact frontier (exploration 14).
- Seeded scaffold lower bound: for the calibrated 25-step bounce mover sequence, the state vector `(2,3,3,3,3,3,3,3,2)` is already componentwise minimal. LOAD-BEARING: high. This is the first direct good-cycle-level mechanism in the project that yields the exact product `4·3^7` without using off-cycle convergence accounting (exploration 15 probe).

## Session Start (2026-03-09)

Resuming from exploration 0.

No prior `exploration_log_glb.md` existed in the repository, so there is no earlier GLB-specific state to reuse.

Next attempt: test whether the `n = 9` one-binary witness exposes a proof-facing phase/interface invariant, then compare it against the known `n = 5..8` optimal witnesses and a few exact-boundary two-binary failures.

## Exploration 1

### Strategy
Probe the lower bound through a new phase/interface lens: extract the exact recurrent cycle of the `n = 9` one-binary witness, compare that structure against the proven `n = 5..8` optimal witnesses, and use a few canonical product-`8748` two-binary Sol-3-v1 failures as a sanity check for the “second binary creates a second puncture” hypothesis.

### Outcome
STALLED

### Failure Constraint
The strongest naive version of the phase idea is false: the known optimal `n = 5..8` witnesses do not admit an obvious literal `state -> Z3` quotient in which every non-binary move is simply `+1 mod 3` on raw state labels. The quaternary gadgets refine phase in a more complicated way, so any proof must track interfaces or delayed directional signals, not just individual local state values.

### What This Rules Out
- Any lower-bound proof that tries to read the hidden ternary phase directly off each processor’s raw state label will run into the same obstruction on the known small optimal witnesses.
- Any “explain everything by Sol-3 labels” story is too narrow. The right invariant, if it exists, has to survive quaternary refinement and mixed local transition graphs.

### Surviving Structure
- The `n = 9` one-binary witness is much more rigid than expected: every good configuration is a step function with only two adjacent phase levels present, and the cycle is exactly the motion of a single boundary through those levels.
- The simplest exact-boundary two-binary Sol-3-v1 probes fail in the way the phase-puncture story predicts:
  - `(2,2,3,3,3,3,3,3,3)` fails on the branching configuration `(1,1,1,0,2,2,2,2,2)`, where processors `3` and `4` are both privileged.
  - `(2,3,3,3,2,3,3,3,3)` fails on the branching configuration `(1,1,1,1,1,1,0,2,2)`, where processors `6` and `7` are both privileged.
  - `(2,3,3,3,3,3,3,3,2)` fails on the dead configuration `(1,1,1,1,1,1,1,1,0)`.
- The known `n = 5..8` optimal witnesses do fit a weaker causal picture: every binary lies within distance `<= 3` of a `4`-state processor, so extra binaries never sit far from a higher-state local “support” gadget.

### Reformulations
- The promising object is not “a system with one token” but “a system with one moving phase boundary.” In the `n = 9` witness, the token is literally the unique interface between two adjacent phase levels. A second binary appears to create a second puncture in that phase picture, which naturally leads to either a second active interface or a hole where no move exists.

LOAD-BEARING ASSESSMENT: High. This reframing explains both the exact `3n-2` bounce cycle and the canonical two-binary failures in the same language.

- The quaternary-assisted witnesses suggest a second reformulation: a higher-state processor is not just “bigger,” it is a local support node that can store directional information long enough for nearby binaries to act correctly. This turns the “out of earshot” slogan into a concrete finite-speed information question.

LOAD-BEARING ASSESSMENT: High. If this can be made precise, the lower bound becomes a causal-delay theorem rather than a shadow-cycle theorem.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/glb_phase_probe.py --mode step --n 9` extracted the exact one-binary recurrent cycle:
  - cycle length `25`
  - mover pattern `7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8`
  - configurations:
    - `(0,0,0,0,0,0,0,0,1)`
    - `(0,0,0,0,0,0,0,1,1)`
    - `(0,0,0,0,0,0,1,1,1)`
    - `(0,0,0,0,0,1,1,1,1)`
    - `(0,0,0,0,1,1,1,1,1)`
    - `(0,0,0,1,1,1,1,1,1)`
    - `(0,0,1,1,1,1,1,1,1)`
    - `(0,1,1,1,1,1,1,1,1)`
    - `(1,1,1,1,1,1,1,1,1)`
    - `(1,1,1,1,1,1,1,1,2)`
    - `(1,1,1,1,1,1,1,2,2)`
    - `(1,1,1,1,1,1,2,2,2)`
    - `(1,1,1,1,1,2,2,2,2)`
    - `(1,1,1,1,2,2,2,2,2)`
    - `(1,1,1,2,2,2,2,2,2)`
    - `(1,1,2,2,2,2,2,2,2)`
    - `(1,2,2,2,2,2,2,2,2)`
    - `(0,2,2,2,2,2,2,2,2)`
    - `(0,0,2,2,2,2,2,2,2)`
    - `(0,0,0,2,2,2,2,2,2)`
    - `(0,0,0,0,2,2,2,2,2)`
    - `(0,0,0,0,0,2,2,2,2)`
    - `(0,0,0,0,0,0,2,2,2)`
    - `(0,0,0,0,0,0,0,2,2)`
    - `(0,0,0,0,0,0,0,0,2)`
- The unique mover contexts in that cycle are:
  - `P0`: `((1,0,1)->1)`, `((2,1,2)->0)`
  - `P1..P7`: `((0,0,1)->1)`, `((1,1,2)->2)`, `((0,2,2)->0)`
  - `P8`: `((1,1,1)->2)`, `((0,2,0)->1)`
- `python3 scripts/glb_phase_probe.py --mode support` found binary-to-`>=4` distances:
  - `n5`: `[(0,1),(1,2),(2,2)]`
  - `n6`: `[(0,3),(1,2),(2,1)]`
  - `n7`: `[(1,3),(2,3),(3,2)]`
  - `n8`: `[(0,3),(1,2),(6,3)]`
- `python3 scripts/glb_phase_probe.py --mode two-binary` found the canonical product-`8748` failures listed above.

STRUCTURAL RESULTS:
- The exact `n = 9` one-binary witness is a single-interface bounce, not just an arbitrary recurrent cycle.
- A second binary in the simplest exact-boundary probes produces either:
  - a branching three-phase mediator, or
  - a dead configuration.
- The known `n = 5..8` optimal witnesses all satisfy the empirical support-radius condition “every binary is within distance `3` of a `4`-state processor.”

TOOLS:
- Added `scripts/glb_phase_probe.py`.
  - Inputs:
    - built-in one-binary Sol-3-v1 family
    - built-in `n = 5..8` witness tables
    - canonical product-`8748` two-binary state vectors
  - Outputs:
    - exact recurrent cycle and mover contexts for the one-binary witness
    - binary-to-support distance summaries for the small witnesses
    - validation/failure summaries for the two-binary probes

REPRESENTATIONS:
- Single-interface phase-boundary representation of the one-binary witness.
- Causal-support representation in which `m >= 4` processors act as local direction-storage gadgets for nearby binaries.

### What Would Unblock This
- A proof-facing definition of the hidden phase/interface object that applies to the quaternary-assisted `n = 5..8` witnesses as well as the one-binary `n >= 9` family. The smallest useful artifact would be a quotient or interface encoding that reproduces at least one known `n <= 8` witness cycle.
- A finite-speed lemma: formalize that directional information created at a support processor can propagate at most one hop per move under radius-1 rules, then compare that delay to when a non-distinguished binary must next make a direction-sensitive move.
- A clean characterization of what counts as “support.” The current empirical version uses `m >= 4`, but the real object may be a local gadget spanning several processors rather than a single high-state node.

### Key Parameters
- Primary witness probed: `n = 9`, state counts `(2,3,3,3,3,3,3,3,3)`.
- Known optimal witnesses compared: `n = 5,6,7,8`.
- Two-binary boundary probes:
  - `(2,2,3,3,3,3,3,3,3)`
  - `(2,3,3,3,2,3,3,3,3)`
  - `(2,3,3,3,3,3,3,3,2)`

### Open Questions
- Can the phase-puncture picture be made canonical for arbitrary valid systems, or is it only a useful coordinate system for the known witnesses?
- Is the empirical support radius `3` an accident of the current small witnesses, or the real threshold behind the `n = 9` phase transition?
- Can one show that any non-distinguished binary must receive direction-change information from a support gadget before its next move, and that this is impossible once a binary is “out of earshot”?

## Synthesis after exploration 1

The important split is now visible. The one-binary `n = 9` witness is so rigid that it practically tells you what theorem wants to be true: a valid cycle is a single moving interface in a hidden three-phase medium. The small optimal witnesses say the same thing more indirectly: extra binaries only appear when a nearby higher-state gadget can hold the missing directional information for them. The naive state-label quotient is dead, but the stronger causal/interface version is alive. The next useful work is to make “support” and “signal travel time” precise enough to survive beyond the explicit witnesses.

## Exploration 2

### Strategy
Turn the phase/interface idea into a finite optimization problem: for each witness, search for processor-local maps `phi_i : state(P_i) -> Z/3Z` that minimize the maximum number of defect edges on the recurrent good cycle, where a defect edge is one whose endpoint phases differ, all three phase values must appear somewhere, and the unique mover must sit next to at least one defect.

### Outcome
SUCCEEDED

### Failure Constraint
The stronger dynamic version of the same idea fails: if one also requires the mover's own phase class to change on every good-cycle step, the system becomes unsatisfiable even for the one-binary Sol-3 family. So the useful quotient tracks defect motion, not per-step mover recoloring.

### What This Rules Out
- Any proof attempt that identifies the token with “the processor whose phase class changes” is too rigid. The right quotient-level object is the moving defect set, not the mover's local phase label.
- Any claim that the small optimal witnesses are just width-`2` one-boundary systems in disguise is false. Their minimum defect widths are strictly larger.

### Surviving Structure
- The optimization problem itself is stable and informative:
  - known optimal witnesses have minimum widths `3,3,4,4` at `n = 5,6,7,8`
  - the one-binary Sol-3 family has width `2` at every tested `n = 5..12`
- The minimizing quotients for the small optimal witnesses are substantially more static than the one-binary family. In particular, the one-binary family is the unique tested regime where a width-`2` quotient exists at all.
- This gives a clean structural split:
  - one-binary Sol-3 family = two-defect regime
  - known `n <= 8` optima = three/four-defect regime

### Reformulations
- Replace the vague “hidden ternary phase” slogan with a concrete invariant:

  phase-defect width = minimum `K` such that the good cycle admits a processor-local quotient to `Z/3Z` with at most `K` defect edges per configuration and with the mover adjacent to a defect.

LOAD-BEARING ASSESSMENT: High. This is the first finite object that distinguishes the `n >= 9` one-binary ladder from the known `n <= 8` optimum witnesses without referring to shadow cycles or orientation searches.

- The failed dynamic strengthening also clarifies the representation: a good quotient need not recolor the mover itself. It is enough that the defect set moves. That is a more faithful interface picture.

LOAD-BEARING ASSESSMENT: Moderate to high. It narrows the design space for future phase-based arguments.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/glb_phase_width.py --group small --timeout-ms 3000`:
  - `n5_opt`, state counts `(2,2,2,3,4)`, minimum width `3`
  - `n6_opt`, state counts `(2,2,2,4,3,3)`, minimum width `3`
  - `n7_opt`, state counts `(3,2,2,2,3,4,3)`, minimum width `4`
  - `n8_opt`, state counts `(2,2,3,4,3,3,2,3)`, minimum width `4`
- `python3 scripts/glb_phase_width.py --group family --timeout-ms 15000`:
  - `one_binary_n5` through `one_binary_n12` all have minimum width `2`
- Sample minimizing quotients found during the probe:
  - `n6_opt` admits a width-`3` quotient with phase image `[0,1,1,2,2,0]` on every displayed good configuration, giving fixed defects at edges `[0,2,4]`
  - `one_binary_n9` admits a width-`2` quotient whose displayed phase images are
    - `[0,0,0,0,0,0,0,0,2]`, defects `[7,8]`
    - `[0,0,0,0,0,0,0,2,2]`, defects `[6,8]`
    - ...
    - `[1,2,2,2,2,2,2,2,2]`, defects `[0,8]`
    so the two-defect pair literally sweeps around the ring.
- Direct dynamic probe:
  - width-`K` plus “mover changes phase class every step” is unsatisfiable for `one_binary_n9` at `K = 2`, and also unsatisfiable for `n5_opt` at `K = 3` and `n6_opt` at `K = 3`.

STRUCTURAL RESULTS:
- Width `2` is a stable normal form for the one-binary Sol-3 family on every tested `n = 5..12`.
- Width `2` is impossible for the known optimal witnesses at `n = 5,6,7,8`.
- The small optimal witnesses separate naturally into:
  - width `3` at `n = 5,6`
  - width `4` at `n = 7,8`

TOOLS:
- Added `scripts/glb_phase_width.py`.
  - Input:
    - built-in `n = 5..8` optimal witnesses
    - built-in one-binary Sol-3 family `n = 5..12`
  - Output:
    - minimum phase-defect width for each selected system

REPRESENTATIONS:
- Phase-defect width on good cycles via processor-local `Z3` quotient maps.
- Dynamic strengthening test:
  same quotient, plus the extra rejected condition “the mover's phase class changes every step.”

### What Would Unblock This
- A proof that any valid system with only one binary has phase-defect width `2`, or at least that the one-binary Sol-3 family is the canonical width-`2` regime.
- A structural argument that any valid width-`3+` regime needs a bounded support zone or a denser scaffold of defect edges, making it impossible or too expensive once `n >= 9` and the product is below `2·3^(n-1)`.
- Data on any other valid mixed witnesses, if they exist, to see whether width `3+` persists beyond the known small optima or whether width `2` is forced by larger `n`.

### Key Parameters
- Width definition:
  - processor-local quotient to `Z/3Z`
  - all three phase values used somewhere
  - at most `K` defect edges per good configuration
  - mover adjacent to at least one defect edge
- Small optimal witnesses tested: `n = 5,6,7,8`
- One-binary family tested: `n = 5..12`

### Open Questions
- Is width `2` actually forced for every valid system once `n >= 9`?
- If width `3+` is possible in principle for larger `n`, what support gadget or defect scaffold carries it, and what product cost does that force?
- Can the observed jump `3,3,4,4` in the known small optima be explained by a bounded-radius defect scaffold centered on the quaternary gadget?

## Synthesis after exploration 2

There is now a second structural split on top of the causal story. The one-binary family is not just “simpler”; it is the only tested regime that compresses to a genuine two-defect phase system. The small optimal witnesses need a wider defect scaffold even after quotienting away raw state labels, and that scaffold is static enough that the mover can run inside it without changing its own phase class. So the lower-bound problem can now be phrased two ways that look compatible rather than competing:

- causal version: extra binaries need nearby support to carry directional information;
- phase-width version: extra binaries force the system into a width-`3+` defect scaffold rather than the width-`2` single-interface regime.

The next productive move is to connect those two views. If width `3+` can be shown to require a bounded support zone whose arithmetic cost exceeds the sub-`2·3^(n-1)` budget for `n >= 9`, that would be a real lower-bound path rather than another witness-specific observation.

## Exploration 3

### Strategy
Refine the vague support-gadget idea into a direct mover-history test: for each known optimal `n = 5..8` witness, find the smallest radius `r` such that every binary move on the recurrent cycle is the endpoint of some contiguous recent mover chain starting from the radius-`r` neighborhood of the unique `>=4`-state processor.

### Outcome
SUCCEEDED

### Failure Constraint
The support object is not always the bare quaternary itself. Requiring the chain to start exactly at the `>=4`-state processor fails for `n = 5,7,8`; a neighborhood around it is necessary.

### What This Rules Out
- Any proof plan that models support as a single distinguished processor only is too narrow. Even in the known optimal small witnesses, some binary moves are only explained once the support object is expanded to a small zone.
- Any account that claims the `n = 8` witness has slack in the support radius is wrong. The mover-history test already saturates radius `3`.

### Surviving Structure
- The mover-history support-zone radius is:
  - `n5`: radius `1`
  - `n6`: radius `0`
  - `n7`: radius `2`
  - `n8`: radius `3`
- So the known `n <= 8` witnesses fit a clean causal ladder:
  - quaternary alone suffices at `n = 6`
  - a radius-`1` neighborhood suffices at `n = 5`
  - a radius-`2` neighborhood is needed at `n = 7`
  - a radius-`3` neighborhood is needed at `n = 8`
- The `n = 8` witness is therefore already right at the apparent causal limit suggested by the “out of earshot” story.

### Reformulations
- Replace “the quaternary carries direction” with a precise history-based version:

  support-chain radius = minimum `r` such that every binary move is preceded by a contiguous recent mover chain whose first mover lies in the radius-`r` neighborhood of the unique `>=4`-state processor.

LOAD-BEARING ASSESSMENT: High. This gives the first concrete causal meaning to the phrase “in earshot.”

- Combined with exploration 2, the current picture is:
  - width `3+` small-optimal regimes use a bounded support zone around the quaternary;
  - one-binary width-`2` regimes do not need that extra support scaffold.

LOAD-BEARING ASSESSMENT: High. It suggests a route where width `3+` and bounded support zone are two views of the same phenomenon.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/glb_phase_probe.py --mode support-chains` returned:
  - `n5`, state counts `(2,2,2,3,4)`, support processor `4`, binary movers `[1,2]`, minimum support-chain radius `1`
  - `n6`, state counts `(2,2,2,4,3,3)`, support processor `3`, binary movers `[1,2]`, minimum support-chain radius `0`
  - `n7`, state counts `(3,2,2,2,3,4,3)`, support processor `5`, binary movers `[1,2,3]`, minimum support-chain radius `2`
  - `n8`, state counts `(2,2,3,4,3,3,2,3)`, support processor `3`, binary movers `[1,6]`, minimum support-chain radius `3`
- Example failed/needed radii:
  - `n8`: radius `2` is insufficient, but radius `3` covers every binary move
  - `n7`: radius `1` is insufficient, but radius `2` covers every binary move

STRUCTURAL RESULTS:
- The support object in the known small witnesses is a bounded neighborhood of the quaternary, not necessarily the quaternary alone.
- The required support-chain radius grows to `3` by `n = 8`, exactly one step before the conjectured phase transition at `n = 9`.

TOOLS:
- Extended `scripts/glb_phase_probe.py` with `--mode support-chains`.
  - Input:
    - built-in `n = 5..8` optimal witnesses
  - Output:
    - minimum support-chain radius for each witness

REPRESENTATIONS:
- Support-chain radius on recurrent cycles via recent mover-history segments.

### What Would Unblock This
- A structural proof that any extra binary in a width-`3+` regime must lie inside a bounded support zone whose radius is at most `3`.
- A way to relate support-chain radius to product cost: if keeping multiple binaries in earshot requires a support zone of a certain size or state complexity, can that be turned into a product lower bound?
- A bridge lemma connecting support-chain radius to phase-defect width, so the causal and quotient views become formally equivalent or at least mutually constraining.

### Key Parameters
- Witnesses tested: known optimal `n = 5,6,7,8`
- Support processor: the unique processor with `m >= 4` in each witness
- Radius definition: neighborhood radius around that support processor in cyclic distance

### Open Questions
- Is radius `3` the true universal earshot bound for quaternary-assisted mixed witnesses?
- Can one prove that any valid width-`3+` regime with multiple binaries needs such a support zone, not just in the known examples?
- Does the support-chain radius admit a purely local reformulation in terms of rule tables or privileged contexts, avoiding direct use of the whole mover sequence?

## Synthesis after exploration 3

The two experimental directions are starting to line up. Exploration 2 says the small optimal witnesses are not hidden width-`2` systems; they need a wider defect scaffold. Exploration 3 says that wider scaffold is not free-floating; it is fed from a bounded support zone around the quaternary, and the known examples push that zone out to radius `3` by `n = 8`. This is the clearest current lower-bound narrative:

- one-binary family = width `2`, no extra support zone needed;
- multi-binary small optima = width `3+`, supported by a quaternary-centered zone whose earshot grows to radius `3` and then appears to run out.

The next proof-oriented move is to turn “radius `3` earshot” into a theorem rather than an empirical summary. If that radius cap can be established and tied to width `3+`, the `n = 9` phase transition stops looking accidental.

## Exploration 4

### Strategy
Push the width-`2` line as far as possible: extract explicit width-`2` `Z/3Z` quotients for the one-binary Sol-3 family across `n = 5..12`, record the resulting abstract mover-role counts by processor, and test whether those abstract counts alone are already enough to read off the target product `2·3^(n-1)`.

### Outcome
STALLED

### Failure Constraint
The width-`2` quotient does reveal a rigid abstract role pattern, but abstract roles alone do not determine raw state multiplicities. In particular, one endpoint of the one-binary family has only two abstract mover roles in the quotient while still using three raw states in the actual system. So a product proof cannot stop at the abstract width-`2` level; it needs an additional refinement invariant.

### What This Rules Out
- Any proof that tries to conclude “role-count `2` implies binary” directly from the abstract quotient will fail.
- Any lower-bound argument that never looks beyond abstract phase roles cannot explain why the upper-bound architecture is `2,3,3,...,3` rather than, say, `2,3,3,...,2`.

### Surviving Structure
- The width-`2` quotient pattern is strikingly stable across the whole tested one-binary family:
  - mover-role counts are exactly `[2,3,3,...,3,2]` for every `n = 5..12`
- So width-`2` cycles seem to have a two-ended abstract skeleton:
  - one endpoint role-count `2`
  - an interior run of role-count `3`
  - another endpoint role-count `2`
- The failure happens one level lower: abstract endpoint role-count `2` does not tell whether that endpoint needs two raw states or three raw states.

### Reformulations
- Separate two layers explicitly:
  1. abstract width-`2` role skeleton,
  2. raw-state refinement multiplicity inside each abstract role/phase.

LOAD-BEARING ASSESSMENT: High. This identifies exactly what is missing from the width-`2` story: not another abstract quotient, but a refinement invariant that measures how many raw states are needed to realize a given abstract phase behavior.

- The promising refined object is phase-refinement multiplicity: how many raw states a processor needs to implement its observed abstract phase behavior on the good cycle.

LOAD-BEARING ASSESSMENT: Moderate to high. This may be the missing ingredient needed to turn the width-`2` skeleton into the arithmetic product `2·3^(n-1)`.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Width-`2` role-count vectors found for the one-binary family:
  - `n5`: `[2,3,3,3,2]`
  - `n6`: `[2,3,3,3,3,2]`
  - `n7`: `[2,3,3,3,3,3,2]`
  - `n8`: `[2,3,3,3,3,3,3,2]`
  - `n9`: `[2,3,3,3,3,3,3,3,2]`
  - `n10`: `[2,3,3,3,3,3,3,3,3,2]`
  - `n11`: `[2,3,3,3,3,3,3,3,3,3,2]`
  - `n12`: `[2,3,3,3,3,3,3,3,3,3,3,2]`
- Example width-`2` abstract mover roles at `n = 9`:
  - processor `0`: `(0,0,1 -> 1)`, `(2,1,2 -> 0)`
  - processors `1..6`: `(0,0,1 -> 1)`, `(1,1,2 -> 2)`, `(0,2,2 -> 0)`
  - processor `8`: `(1,0,1 -> 2)`, `(2,2,0 -> 0)`
- Example refinement gap at `n = 9`:
  - endpoint processor `8` has only two abstract mover roles in the quotient but still has three raw states in the actual system, so the abstract quotient does not determine raw multiplicity.

STRUCTURAL RESULTS:
- The one-binary family has a stable two-ended width-`2` abstract role skeleton on all tested `n = 5..12`.
- Abstract role counts alone are insufficient to recover the target product.

REPRESENTATIONS:
- Width-`2` abstract mover-role skeleton.
- Phase-refinement multiplicity as the missing post-quotient layer.

### What Would Unblock This
- A concrete definition of phase-refinement multiplicity that can be computed from a good cycle and that lower-bounds raw state count per processor.
- A proof that in any width-`2` fair cycle:
  - one endpoint can have refinement multiplicity `1` in each used phase (binary),
  - the other endpoint must refine at least one abstract phase into two raw states,
  - interior processors need three raw phase roles.
- A way to test phase-refinement multiplicity on known witnesses beyond the one-binary family.

### Key Parameters
- Systems tested: one-binary Sol-3 family `n = 5..12`
- Quotient type: phase-defect width `2`
- Summary statistic extracted: number of distinct abstract mover roles per processor

### Open Questions
- Can phase-refinement multiplicity be defined in a way that is invariant across different satisfying width-`2` quotients?
- Is the second width-`2` endpoint always genuinely ternary in any valid realization, or only in the Sol-3 family?
- Can the width-`2` role skeleton plus a refinement-multiplicity lemma already force the full product `2·3^(n-1)`?

## Synthesis after exploration 4

The width-`2` picture is now split cleanly into a solved part and an unsolved part. The solved part is the abstract geometry: the one-binary family really does look like a two-ended width-`2` scaffold with role counts `[2,3,...,3,2]`. The unsolved part is the arithmetic refinement: abstract endpoint role-count `2` does not tell whether that endpoint is binary or ternary. So the next good attack is not another quotient. It is a refinement invariant, ideally local, that measures how many raw states are needed to realize a given abstract phase behavior. That is the missing bridge from width geometry to product arithmetic.

## Exploration 5

### Strategy
Test whether the missing arithmetic can be recovered from good-cycle local memory alone: model each processor on the good cycle as a deterministic finite-state machine driven by neighbor signals and compute the minimum number of internal states needed to realize the observed local behavior, first with actual raw-neighbor inputs and then with width-`2` abstract phase inputs.

### Outcome
FAILED

### Failure Constraint
Good-cycle local memory is not enough. In the one-binary Sol-3 family at `n = 9`, the minimum deterministic on-cycle local-state counts with raw-neighbor inputs are `[2,3,3,3,3,3,3,3,2]`; with width-`2` abstract phase inputs they remain compatible with a 2-state top endpoint. So the extra third raw state at the top is not forced by recurrent-cycle behavior and must be justified by off-cycle convergence requirements.

### What This Rules Out
- Any proof that only studies the eventual good cycle, even with local automaton minimization, will miss at least some of the necessary state cost.
- Any attempt to derive the full product `2·3^(n-1)` from width-`2` recurrent behavior alone is structurally incomplete.

### Surviving Structure
- The local-automaton representation is still informative:
  - bottom endpoint requires `2` local states on the good cycle
  - interior processors require `3`
  - top endpoint compresses to `2` on the good cycle
- This cleanly isolates where the missing arithmetic lives:
  - not in eventual-cycle local behavior,
  - but in convergence/stabilization from bad configurations.

### Reformulations
- Split the lower-bound problem into two costs:
  1. recurrent-cycle realization cost,
  2. convergence-to-cycle cost.

LOAD-BEARING ASSESSMENT: High. Exploration 5 shows these are genuinely different. The top endpoint's third state is a convergence resource, not a recurrent-cycle resource.

- The right missing invariant is no longer “phase refinement multiplicity on the good cycle.” It is some off-cycle refinement measure: how many extra local memory states are needed to funnel arbitrary bad configurations into the width-`2` scaffold.

LOAD-BEARING ASSESSMENT: High. This redirects the search away from pure cycle geometry and toward convergence structure.

### Concrete Artifacts
COMPUTED EXAMPLES:
- For the `n = 9` one-binary Sol-3 family `(2,3,3,3,3,3,3,3,3)`, minimum deterministic local-state counts on the good cycle using raw-neighbor inputs are:
  - `[2,3,3,3,3,3,3,3,2]`
- Using one found width-`2` abstract phase quotient as the neighbor input alphabet still leaves the top endpoint compatible with `2` local states on the good cycle.

STRUCTURAL RESULTS:
- The top endpoint's third raw state in the one-binary family is not forced by good-cycle local behavior.
- Therefore any full proof of `M_n >= 2·3^(n-1)` must use convergence/off-cycle information, not only recurrent-cycle structure.

REPRESENTATIONS:
- Good-cycle local automaton minimization by processor, with either raw-neighbor or abstract-phase neighbor inputs.

### What Would Unblock This
- A convergence-facing invariant that measures extra local memory needed to absorb bad configurations into a width-`2` good cycle.
- A way to express “off-cycle correction responsibility” locally enough to assign unavoidable extra states to specific processors.
- Computations on how many distinct bad-to-good recovery modes feed into the top endpoint in the one-binary family.

### Key Parameters
- System tested: one-binary Sol-3 family at `n = 9`
- Input alphabets tested:
  - actual raw neighbor states
  - one satisfying width-`2` abstract phase quotient

### Open Questions
- Can the extra top-endpoint state be characterized directly as a convergence mode?
- Is there an off-cycle automaton-minimization problem whose optimum matches the actual state counts more closely than the good-cycle version?
- Can the convergence cost be related to the same support-zone picture that appears in the multi-binary small optima?

## Synthesis after exploration 5

This was a useful failure. The lower bound now has a sharper fault line: recurrent-cycle geometry explains the width-`2` scaffold, but it does not explain the full state count. The missing cost lives in convergence. That fits the broader story rather well:

- width and role skeleton explain what the eventual cycle looks like;
- support zones explain how more complicated multi-binary regimes manage directional information;
- the last unexplained states are exactly the ones needed to funnel arbitrary bad configurations into the correct scaffold.

So the next productive direction is not another quotient or another mover-pattern probe. It is to measure convergence burden locally, ideally in a way that can still be compared across the one-binary family and the quaternary-assisted small optima.

## Exploration 6

### Strategy
Localize the convergence cost inside the one-binary family by comparing two processor-by-processor quantities:
1. the minimum deterministic local-state count needed to realize the observed good-cycle behavior,
2. the minimum number of states in the full local transition table after Moore-style state minimization.

The difference is a purely local convergence gap.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The extra off-cycle cost in the one-binary family is not smeared across many processors. At least in the tested cases, it is not an “everyone needs a little more memory” phenomenon.
- Any proof outline that distributes the missing convergence burden evenly over the ring is inconsistent with the observed local structure.

### Surviving Structure
- For the one-binary family, the good-cycle local automaton sizes and full minimized local-rule sizes are:
  - `n = 5`:
    - good-cycle sizes `[2,3,3,3,2]`
    - full local sizes `[2,3,3,3,3]`
    - gap `[0,0,0,0,1]`
  - `n = 9`:
    - good-cycle sizes `[2,3,3,3,3,3,3,3,2]`
    - full local sizes `[2,3,3,3,3,3,3,3,3]`
    - gap `[0,0,0,0,0,0,0,0,1]`
- So in both tested sizes, every processor except the top endpoint has no extra local convergence burden beyond what the good cycle already forces.
- The top endpoint is exactly where the missing third state lives.

### Reformulations
- Define the local convergence gap at processor `i` as:

  `gap_i = (minimum size of full local transducer for processor i) - (minimum size of good-cycle local automaton for processor i)`.

LOAD-BEARING ASSESSMENT: High. This puts the previously vague “extra state for convergence” into a per-processor numeric invariant.

- In the one-binary family, the whole off-cycle correction cost appears to collapse to a single endpoint. That is a much stronger and more usable statement than the earlier global observation that “the good cycle only needs width `2`.”

LOAD-BEARING ASSESSMENT: High. It suggests a proof route where one identifies processors that must pay nonzero convergence gap.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `n = 5`, one-binary family `(2,3,3,3,3)`:
  - good-cycle local-state minima `[2,3,3,3,2]`
  - full local-rule minima `[2,3,3,3,3]`
  - convergence gap `[0,0,0,0,1]`
- `n = 9`, one-binary family `(2,3,3,3,3,3,3,3,3)`:
  - good-cycle local-state minima `[2,3,3,3,3,3,3,3,2]`
  - full local-rule minima `[2,3,3,3,3,3,3,3,3]`
  - convergence gap `[0,0,0,0,0,0,0,0,1]`

STRUCTURAL RESULTS:
- In the tested one-binary family sizes, the extra off-cycle local memory is concentrated entirely at the top endpoint.
- The bottom binary has zero convergence gap in these tests: its two states are already forced by good-cycle local behavior.

REPRESENTATIONS:
- Processorwise convergence gap = full local-rule complexity minus good-cycle local complexity.

### What Would Unblock This
- Compute the same convergence-gap vector for more one-binary sizes and for the known `n = 5..8` optimal witnesses, to see whether multi-binary/quaternary-assisted systems spread the convergence burden over a support zone instead of a single endpoint.
- A proof that any width-`2` family must have at least one processor with positive convergence gap, and ideally that this processor must be ternary.
- A local characterization of what top-endpoint contexts force the positive convergence gap.

### Key Parameters
- Family tested: one-binary Sol-3-v1
- Sizes tested in this exploration: `n = 5` and `n = 9`
- Two local complexity notions compared:
  - good-cycle automaton size
  - full local-rule minimized size

### Open Questions
- Does the convergence gap vector stay `[0,...,0,1]` for every `n` in the one-binary family?
- What do the convergence-gap vectors of the known `n = 5..8` optimal witnesses look like?
- Is positive convergence gap the right local quantity to compare against the quaternary-centered support zones in the small optimal witnesses?

## Synthesis after exploration 6

The convergence story is getting sharper, not blurrier. Exploration 5 established that the missing state cost is off-cycle. Exploration 6 says that, in the one-binary family, this off-cycle cost is not diffuse: it sits almost entirely at one endpoint. That is a strong hint that the eventual lower bound will need three layers, not one:

- width/role geometry for the recurrent scaffold,
- support-zone geometry for carrying directional information,
- convergence-gap accounting for the extra states that make the scaffold globally attracting.

The next natural comparison is now clear: compute convergence-gap vectors for the known `n = 5..8` optimal witnesses and see whether their positive gap is spread over the same quaternary-centered support zones found in exploration 3.

## Exploration 7

### Strategy
Carry out that comparison directly: compute the convergence-gap vectors for the known optimal witnesses `n = 5,6,7,8` and compare the locations of positive gap against the quaternary-centered support zones from exploration 3.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- Positive convergence gap is not distributed arbitrarily across the ring in the known small optima.
- The quaternary support zone is not just a mover-history artifact; it also shows up in the local off-cycle memory accounting.

### Surviving Structure
- The convergence-gap vectors for the known optimal witnesses are:
  - `n5`, state counts `(2,2,2,3,4)`: gap `[0,0,0,1,2]`
  - `n6`, state counts `(2,2,2,4,3,3)`: gap `[0,0,0,1,0,0]`
  - `n7`, state counts `(3,2,2,2,3,4,3)`: gap `[0,0,0,0,1,1,0]`
  - `n8`, state counts `(2,2,3,4,3,3,2,3)`: gap `[0,0,1,1,1,0,0,1]`
- Relative to the support-chain radii from exploration 3:
  - `n5`: positive gap at processors `3,4`, inside the radius-`1` zone around quaternary `4`
  - `n6`: positive gap only at quaternary `3`, matching radius `0`
  - `n7`: positive gap at `4,5`, inside the radius-`2` zone around quaternary `5`
  - `n8`: positive gap at `2,3,4` near the quaternary `3`, plus processor `7` at the top endpoint
- So the positive convergence burden is strongly aligned with the support-zone picture, with `n8` adding a second concentration at the opposite endpoint.

### Reformulations
- Positive convergence gap is the local memory shadow of the support zone. The support-chain radius from exploration 3 and the convergence-gap vector are not competing descriptions; they are two projections of the same correction scaffold.

LOAD-BEARING ASSESSMENT: High. This is the clearest bridge so far between causal support and off-cycle state cost.

- The `n8` witness suggests a two-pole correction scaffold:
  - a quaternary-centered support zone,
  - and an opposite endpoint that carries residual convergence burden.

LOAD-BEARING ASSESSMENT: Moderate to high. This mirrors the one-binary family, where the positive convergence gap also sits at a single endpoint.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `n5`, state counts `(2,2,2,3,4)`:
  - good-cycle local sizes `[2,2,2,2,2]`
  - full local sizes `[2,2,2,3,4]`
  - gap `[0,0,0,1,2]`
- `n6`, state counts `(2,2,2,4,3,3)`:
  - good-cycle local sizes `[2,2,2,3,3,3]`
  - full local sizes `[2,2,2,4,3,3]`
  - gap `[0,0,0,1,0,0]`
- `n7`, state counts `(3,2,2,2,3,4,3)`:
  - good-cycle local sizes `[3,2,2,2,2,3,3]`
  - full local sizes `[3,2,2,2,3,4,3]`
  - gap `[0,0,0,0,1,1,0]`
- `n8`, state counts `(2,2,3,4,3,3,2,3)`:
  - good-cycle local sizes `[2,2,2,3,2,3,2,2]`
  - full local sizes `[2,2,3,4,3,3,2,3]`
  - gap `[0,0,1,1,1,0,0,1]`

STRUCTURAL RESULTS:
- The known small optima carry positive convergence gap on or near the same quaternary-centered support zones found by the mover-history method.
- `n8` already exhibits both ingredients now visible in the one-binary family:
  - a support-zone concentration,
  - and an endpoint convergence charge.

REPRESENTATIONS:
- Convergence-gap vectors for the known optimal witnesses.

### What Would Unblock This
- A proof that positive convergence gap must be supported by the same bounded-radius correction zone that carries directional information.
- Computation of convergence-gap vectors for additional candidate/invalid mixed families near `n = 9` to see whether failure begins exactly when the required positive-gap zone cannot be localized.
- A theorem relating total positive convergence gap to support-chain radius.

### Key Parameters
- Witnesses tested: known optimal `n = 5,6,7,8`
- Quantities compared:
  - good-cycle local-state minima
  - full local-rule minima
  - convergence-gap vectors
  - support-chain radii from exploration 3

### Open Questions
- Is the endpoint convergence gap in `n8` the first sign of the same endpoint burden that becomes dominant in the one-binary family?
- Can one show that positive convergence gap must lie inside a bounded-radius support zone, except possibly at one opposite endpoint?
- Does the sum or support of the convergence-gap vector admit a clean arithmetic relation to the product bound?

## Synthesis after exploration 7

This is the first point where three different views are visibly converging on the same structure.

- Exploration 3 gave a quaternary-centered support zone.
- Exploration 6 gave a local convergence-gap invariant.
- Exploration 7 shows that, in the known small optima, those two objects live in the same places.

So the emerging picture is no longer just “out of earshot.” It is more precise:

- width `3+` regimes need a localized correction scaffold,
- that scaffold stores directional information and carries positive convergence gap,
- and by `n = 8` it already stretches to radius `3` and begins to charge an opposite endpoint.

The next useful move is to see whether this scaffold can be detected or bounded in failed `n = 9` mixed families without doing full witness search, because that is the shortest path from current evidence to a real impossibility statement.

## Exploration 8

### Strategy
Interpret the old arithmetic gap through the new convergence-gap lens by comparing, in the one-binary family, the product of good-cycle local automaton sizes against the product of the full minimized local-rule sizes.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The `3/2` gap between the old Case-1 bound and the conjectured bound is not a mysterious global artifact. In the one-binary family it is completely localized.
- Any explanation of the conjectured bound that ignores the arithmetic role of convergence gap is missing the simplest available account of the factor `3/2`.

### Surviving Structure
- In the one-binary family at the tested sizes:
  - `n = 5`:
    - good-cycle sizes `[2,3,3,3,2]`, product `108 = 4·3^3`
    - full local sizes `[2,3,3,3,3]`, product `162 = 2·3^4`
    - ratio `162 / 108 = 3/2`
  - `n = 6`:
    - good-cycle sizes `[2,3,3,3,3,2]`, product `324 = 4·3^4`
    - full local sizes `[2,3,3,3,3,3]`, product `486 = 2·3^5`
    - ratio `3/2`
  - `n = 8`:
    - good-cycle sizes `[2,3,3,3,3,3,3,2]`, product `2916 = 4·3^6`
    - full local sizes `[2,3,3,3,3,3,3,3]`, product `4374 = 2·3^7`
    - ratio `3/2`
  - `n = 9`:
    - good-cycle sizes `[2,3,3,3,3,3,3,3,2]`, product `8748 = 4·3^7`
    - full local sizes `[2,3,3,3,3,3,3,3,3]`, product `13122 = 2·3^8`
    - ratio `3/2`
- So the old arithmetic lower bound `4·3^(n-2)` is exactly the good-cycle product of the one-binary family, and the conjectured sharp bound is obtained by one endpoint convergence upgrade `2 -> 3`.

### Reformulations
- Recast the lower-bound target as:

  `target product = recurrent-cycle complexity product × convergence multiplier`.

For the one-binary family, the recurrent part is exactly `4·3^(n-2)` and the convergence multiplier is exactly `3/2`.

LOAD-BEARING ASSESSMENT: Very high. This is the clearest numeric explanation so far of why the sharp bound should be `2·3^(n-1)` rather than `4·3^(n-2)`.

- The lower-bound problem can now be posed as: prove that every valid subcritical system must pay at least one endpoint convergence upgrade on top of the recurrent-cycle complexity.

LOAD-BEARING ASSESSMENT: High. This turns the missing factor `3/2` into a concrete structural claim rather than a generic “case-1 arithmetic is weak.”

### Concrete Artifacts
COMPUTED EXAMPLES:
- One-binary family product decompositions:
  - `n5`: `108 -> 162`
  - `n6`: `324 -> 486`
  - `n8`: `2916 -> 4374`
  - `n9`: `8748 -> 13122`
- In every tested case above, the ratio `(full local product) / (good-cycle local product)` is exactly `3/2`.

STRUCTURAL RESULTS:
- The classical Case-1 lower bound `4·3^(n-2)` is exactly the recurrent/good-cycle local-complexity product of the one-binary family.
- The missing sharpness factor `3/2` is exactly a localized convergence-gap charge at one endpoint in that family.

REPRESENTATIONS:
- Product decomposition:
  recurrent/good-cycle local product × convergence multiplier.

### What Would Unblock This
- Show that any valid width-`2` regime must incur at least one endpoint convergence upgrade `2 -> 3`.
- Understand whether multi-binary width-`3+` regimes pay the same total convergence multiplier in a more distributed way, or whether they necessarily pay more.
- Extend the product decomposition beyond the one-binary family to other known/putative regimes.

### Key Parameters
- Family tested: one-binary Sol-3-v1
- Sizes checked explicitly in this exploration: `n = 5,6,8,9`
- Quantities compared:
  - good-cycle local-state product
  - full local-rule product
  - ratio of the two

### Open Questions
- Is the `3/2` convergence multiplier universal for all width-`2` valid systems?
- Can the weak Case-1 arithmetic bound be upgraded to the sharp bound by proving a single unavoidable endpoint convergence charge?
- Do width-`3+` small-optimal witnesses admit a similar product decomposition, and if so what replaces the factor `3/2`?

## Synthesis after exploration 8

This is the first place where the lower-bound target itself has a genuinely structural interpretation. The arithmetic gap is no longer just “case 1 is off by a factor `1.5`.” In the one-binary family:

- `4·3^(n-2)` is the exact recurrent-cycle local-complexity product,
- the missing factor `3/2` is a single localized convergence upgrade,
- and together they give `2·3^(n-1)`.

That is the best current candidate for the real proof mechanism. The next natural challenge is to see whether failed `n = 9` mixed families can be shown to lack any way to realize this same decomposition: either they cannot achieve the recurrent scaffold cleanly, or they cannot localize the necessary convergence multiplier.

## Exploration 9 (probe)

### Strategy
Check whether the endpoint-only convergence gap and the exact multiplier `3/2` are stable across the intermediate one-binary family sizes `n = 6,7,8`, rather than being artifacts of the previously checked sample sizes.

### Outcome
SUCCEEDED

### Concrete Artifacts
- For the one-binary family:
  - `n = 6`:
    - good-cycle local sizes `[2,3,3,3,3,2]`
    - full local sizes `[2,3,3,3,3,3]`
    - gap `[0,0,0,0,0,1]`
    - ratio `3/2`
  - `n = 7`:
    - good-cycle local sizes `[2,3,3,3,3,3,2]`
    - full local sizes `[2,3,3,3,3,3,3]`
    - gap `[0,0,0,0,0,0,1]`
    - ratio `3/2`
  - `n = 8`:
    - good-cycle local sizes `[2,3,3,3,3,3,3,2]`
    - full local sizes `[2,3,3,3,3,3,3,3]`
    - gap `[0,0,0,0,0,0,0,1]`
    - ratio `3/2`

## Synthesis after exploration 9

The one-binary family law is now stable on the entire checked range `n = 5..9`:

- recurrent/good-cycle product = `4·3^(n-2)`,
- convergence-gap vector = `[0,0,...,0,1]`,
- full product = recurrent product × `3/2` = `2·3^(n-1)`.

That turns exploration 8 from a suggestive decomposition into a serious candidate theorem. The next useful attack is no longer on the one-binary family itself; it is on showing that any valid `n >= 9` competitor below `2·3^(n-1)` cannot realize the same decomposition.

## Exploration 10

### Strategy
Replace the diffuse ring-defect picture by a cut-chain one: cut the ring at the distinguished processor `P0`, define the linear variation
`V(cfg) = |{ i in {0,...,n-2} : cfg[i] != cfg[i+1] }|`,
and test whether the one-binary family has a unique local source of variation creation; then compare that source pattern against the canonical near-bound two-binary Sol-3-v1 failures.

### Outcome
SUCCEEDED

### Failure Constraint
The raw ring-defect support is too blunt for this purpose: on the uncut ring, defect-support size can increase at both `P0` and `P_{n-1}`, so it does not isolate the true source asymmetry. Cutting at `P0` is essential.

### What This Rules Out
- Any proof attempt that tracks only undirected defect support on the ring is too coarse; it misses the one-sided source structure visible after cutting at the distinguished binary.
- Any near-bound architecture with an internal extra binary that can create new cut-chain variation at that binary is incompatible with the single-interface bounce picture unless some additional support scaffold suppresses that source.
- Unique source count alone is not sufficient: the endpoint-binary probe `(2,3,3,3,3,3,3,3,2)` still has only one variation source, but it is invalid. So the eventual theorem will need both:
  - a source-count statement, and
  - a source-strength statement saying the unique source must be ternary rather than binary.

### Surviving Structure
- In the one-binary Sol-3-v1 family, every middle move copies one neighbor and therefore cannot increase cut-chain variation `V`; the bottom binary move sets `P0` equal to `P1` when it acts, so it also cannot increase `V`. Only the top endpoint can increase `V`, because only edge `(n-2,n-1)` of the cut chain is affected by a top move.
- This is not just true at `n = 9`; it holds for every tested size `n = 5..12`.
- On the one-binary good cycle, `V` takes only the values `0` and `1`. So the good cycle is literally a single moving interface on the cut chain, with the top endpoint acting as the only place where a new interface can be created.
- The canonical invalid near-bound probes split into two qualitatively different failure modes:
  - internal extra binary:
    cut-chain variation has a second source at that binary, matching the branching-failure picture;
  - endpoint binary pair:
    cut-chain variation still has a unique source at the top endpoint, but the top is now binary and the system dies on a dead configuration, matching the “source too weak” picture.

### Reformulations
- Cut-ring variation-source picture: instead of thinking in terms of “how many binaries” or “how many defects on the ring,” cut at `P0` and ask where new linear variation can be created. In the one-binary family there is exactly one source, namely `P_{n-1}`.

LOAD-BEARING ASSESSMENT: High. This is the first representation that makes the endpoint convergence burden look causally inevitable rather than numerically accidental.

- Source-count vs. source-strength split:
  - source-count asks how many processors can create new variation on the cut chain;
  - source-strength asks whether the surviving source can emit the needed three-phase bounce rather than only a binary echo.

LOAD-BEARING ASSESSMENT: High. This cleanly separates the two canonical sub-`2·3^(n-1)` failure modes and explains why they fail for different structural reasons.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/glb_variation_probe.py --mode family --n-min 5 --n-max 12` showed:
  - for every `n = 5..12`, `only_top_increases=True`;
  - good-cycle variation values are always exactly `[0,1]`;
  - sample:
    - `n = 9`, state counts `(2,3,3,3,3,3,3,3,3)`:
      - path-variation delta counts `{-2: 10206, -1: 24786, 0: 24057, 1: 1458}`
      - positive-variation movers `{8: 1458}`
      - good-cycle length `25`
      - good-cycle variation values `[0,1]`
    - `n = 12`, state counts `(2,3,3,3,3,3,3,3,3,3,3,3)`:
      - path-variation delta counts `{-2: 393660, -1: 905418, 0: 885735, 1: 39366}`
      - positive-variation movers `{11: 39366}`
- `python3 scripts/glb_variation_probe.py --mode canonical` showed:
  - `(2,2,3,3,3,3,3,3,3)`:
    - invalid by branching at `(1,1,1,0,2,2,2,2,2)`
    - positive-variation movers `{1: 729, 8: 972}`
  - `(2,3,3,3,2,3,3,3,3)`:
    - invalid by branching at `(1,1,1,1,1,1,0,2,2)`
    - positive-variation movers `{4: 972, 8: 972}`
  - `(2,3,3,3,3,3,3,3,2)`:
    - invalid by dead configuration `(1,1,1,1,1,1,1,1,0)`
    - positive-variation movers `{8: 1458}`
- In the one-binary family, the count of `+1` variation moves matches `2·3^(n-3)` on every tested `n = 5..12`.

STRUCTURAL RESULTS:
- For the one-binary Sol-3-v1 family, cut-chain variation can increase only at the top endpoint `P_{n-1}`.
- Internal extra binaries in the canonical near-bound probes act as additional variation sources.
- Endpoint-binary failure shows that having a unique source is not enough; the unique source must also be strong enough to realize the three-phase bounce.

TOOLS:
- Added `scripts/glb_variation_probe.py`.
  - Inputs:
    - one-binary Sol-3-v1 family `n = 5..12`
    - canonical near-bound probes
    - optional custom Sol-3-v1 state-count vectors
  - Outputs:
    - path-variation delta counts
    - movers that can increase cut-chain variation
    - good-cycle variation values when a recurrent single-successor cycle exists

REPRESENTATIONS:
- Linear variation on the cut chain `P0..P_{n-1}`.
- Source-count/source-strength split for near-bound failures.

### What Would Unblock This
- A proof that any valid width-`2` or bounce-like regime admits a canonical cut-chain variation notion with exactly one source.
- A theorem that any internal binary outside a bounded support zone creates an additional variation source on any such cut chain.
- A local argument that the unique source must be ternary, which would recover the endpoint convergence upgrade `2 -> 3` directly from source strength.
- Comparison of the same source picture with the known `n = 5..8` optimal witnesses, where the current guess is that the quaternary-centered support zone behaves like a small source zone rather than a single source node.

### Key Parameters
- One-binary family tested: `n = 5..12`, always with state counts `(2,3,3,...,3)`.
- Canonical invalid probes tested:
  - `(2,2,3,3,3,3,3,3,3)`
  - `(2,3,3,3,2,3,3,3,3)`
  - `(2,3,3,3,3,3,3,3,2)`
- Variation definition:
  number of unequal adjacent pairs on the linear chain after cutting the ring at `P0`.

### Open Questions
- Can the cut-ring source picture be defined invariantly, without relying on the raw Sol-3 residue labels of the explicit witness family?
- Is the quaternary-centered support zone in the known `n <= 8` optima exactly a bounded “source zone” in this same sense?
- Can the endpoint convergence multiplier `3/2` be reinterpreted as the minimal cost of making the unique source ternary rather than binary?
- Does every valid subcritical competitor fail either by having multiple sources or by making the unique source too weak?

## Synthesis after exploration 10

The lower-bound target now has a second “why” explanation that matches the earlier convergence-gap story rather than competing with it.

- Exploration 8/9 said:
  `2·3^(n-1) = recurrent scaffold cost × endpoint convergence multiplier`.
- Exploration 10 says:
  the recurrent scaffold is not just any width-`2` cycle; it is a cut chain with one moving interface and exactly one variation source, located at the top endpoint.

Those two views line up well:

- the unique source is exactly where the one-binary family pays its positive convergence gap;
- internal extra binaries fail by becoming second sources, which matches the branching-failure picture;
- endpoint binary failure shows why the missing factor is not merely “one source exists” but “the source must be ternary.”

So the next serious theorem target is sharper than before:

- source-count lemma:
  subcritical valid systems cannot have more than one effective variation source;
- source-strength lemma:
  the unique source must have at least three states.

If both can be formalized in a representation that survives beyond the explicit Sol-3 family, they would explain the conjectured lower bound almost exactly:

- one binary at the bottom,
- ternary fillers carrying a single interface,
- one ternary source at the top,
- hence product `2·3^(n-1)`.

## Exploration 11 (probe)

### Strategy
Check two side questions: whether the same raw cut-chain variation at the fixed cut `P0` already localizes a source zone in the known `n = 5..8` optimal witnesses, and whether the endpoint-binary failure can be seen directly in the top endpoint’s local move contexts.

### Outcome
SUCCEEDED

### Concrete Artifacts
- `python3 - <<'PY' ...` on the known optimal witnesses `n = 5,6,7,8` with the same raw cut-chain variation `V` at cut `P0` gave positive-variation movers:
  - `n5`: `{0: 24, 2: 24, 3: 16, 4: 12}`
  - `n6`: `{0: 72, 2: 18, 3: 48, 4: 56, 5: 32}`
  - `n7`: `{0: 144, 1: 144, 3: 72, 4: 108, 5: 144, 6: 72}`
  - `n8`: `{0: 432, 1: 216, 2: 216, 3: 504, 4: 360, 5: 576, 6: 432}`
  This does **not** isolate a small quaternary-centered source zone, so the raw cut-at-`P0` picture does not transfer directly to the small optimal witnesses.
- Top endpoint move contexts:
  - one-binary `n = 9`, state counts `(2,3,3,3,3,3,3,3,3)`:
    `(0,0,0)->1`, `(0,2,0)->1`, `(1,0,1)->2`, `(1,1,1)->2`
- endpoint-binary probe `(2,3,3,3,3,3,3,3,2)`:
    `(0,0,0)->1`, `(1,1,1)->0`, `(2,0,0)->1`
  The ternary source can emit the phase-`2` lift on the all-`1` plateau, while the binary source cannot.

## Exploration 12

### Strategy
Try to lift the cut-chain source picture from the raw one-binary family to the known `n = 5..8` optimal witnesses by solving for one minimum-width `Z/3Z` phase quotient, then measuring phase-variation sources on the quotiented chain for each possible cut.

### Outcome
FAILED

### Failure Constraint
Minimum-width phase quotients are too noncanonical. Even after fixing the width and a normalization like `phi_0(0)=0`, different satisfying quotient gauges can shift the apparent source set dramatically, and for some witnesses/cuts the resulting phase-variation has no positive source at all. So the source picture is not invariant under “pick any width-minimizing quotient.”

### What This Rules Out
- Any proof plan that says “first solve the phase-width minimization problem, then read source count off any satisfying quotient” will hit gauge-dependence immediately.
- Any attempt to transfer exploration 10 to the small optimal witnesses by a bare quotient-and-cut recipe is structurally incomplete; it needs either:
  - a canonical gauge choice,
  - a stronger quotient notion,
  - or a source invariant defined without choosing a quotient representative.

### Surviving Structure
- The failure is informative rather than destructive: it says the cut-chain source picture is probably real only after some causal gauge-fixing, not at the level of arbitrary minimizing phase labels.
- The gauge dependence appears even in the one-binary family, so this is not a pathology of the small optimal witnesses alone.
- Some quotient/cut pairs still show suggestive clustering:
  - `n8` had a tested minimizing quotient with best cut giving positive movers `{6: 144}`;
  - but `n6` and `n7` had tested minimizing quotients with cuts giving no positive movers at all;
  - and the one-binary `n9` family, under one arbitrary width-`2` quotient, had best cut giving positive movers `{6: 1458, 7: 972}` rather than a unique source.
- So the correct statement is likely not “minimum-width quotient = canonical source coordinates.” The source picture must use more structure than width minimization alone.

### Reformulations
- Gauge-fixed source picture: the cut-chain source story should probably be viewed as a gauge-fixed enhancement of the phase picture, not as a property of the naked width-minimizing quotient class.

LOAD-BEARING ASSESSMENT: High. This sharply narrows how the source idea can be generalized: not by arbitrary quotient choice, but by a quotient tied to actual causal direction, support zones, or recovery dynamics.

### Concrete Artifacts
COMPUTED EXAMPLES:
- For one tested minimum-width quotient of `n6_opt`, there were cuts with no positive phase-variation movers at all.
- For one tested minimum-width quotient of `n7_opt`, there were also cuts with no positive phase-variation movers.
- For one tested minimum-width quotient of `n8_opt`, the best cut had positive movers `{6: 144}`.
- For one tested minimum-width quotient of the one-binary `n = 9` family, the best cut had positive movers `{6: 1458, 7: 972}`, so even the family with a genuine raw unique source can lose uniqueness under an arbitrary width-`2` gauge.

STRUCTURAL RESULTS:
- Source-count under quotiented path variation is not invariant under arbitrary minimum-width quotient choice.

REPRESENTATIONS:
- Quotiented cut-chain phase variation after a chosen width-minimizing `Z/3Z` map and a chosen cut.

### What Would Unblock This
- A canonical gauge-fixing principle for the phase quotient, ideally tied to mover direction, support chains, or convergence burden rather than mere width minimality.
- A quotient-free definition of effective source count.
- A source-zone invariant that can be computed directly from rule tables or mover histories and then compared to the phase-width/support-zone data.

### Key Parameters
- Witnesses tested:
  - `n5_opt` at width `3`
  - `n6_opt` at width `3`
  - `n7_opt` at width `4`
  - `n8_opt` at width `4`
  - one-binary `n = 9` at width `2`
- For each tested quotient, every cyclic cut was checked.

### Open Questions
- Is there a natural gauge in which the one-binary family recovers its raw unique-source picture and the small optimal witnesses recover a bounded source zone?
- Can convergence-gap data provide the missing gauge-fixing information?
- Is effective source count better defined from off-cycle recovery behavior than from recurrent-cycle phase quotients?

## Synthesis after exploration 12

The source idea survived, but its first obvious generalization did not.

- Exploration 10 found a strong raw source invariant in the one-binary family.
- Exploration 11 showed the raw fixed cut does not transfer directly to the small optimal witnesses.
- Exploration 12 shows that arbitrary width-minimizing quotients are also too loose: they wash out the source picture rather than transporting it.

That leaves a narrower but clearer target:

- source count is probably a real causal invariant,
- but it is not encoded in arbitrary quotient coordinates,
- so the missing ingredient is a canonical gauge, likely supplied by support history or convergence burden.

This lines up well with the rest of the log:

- support-chain radius already captures causal direction flow,
- convergence gap already localizes off-cycle correction cost,
- the source picture now looks like the dynamic object those two invariants are trying to describe.

The next attempt should therefore connect source count to one of those two more rigid structures, rather than to bare phase-width minimization.

## Exploration 13 (probe)

### Strategy
Test whether the small optimal witnesses only failed the source-zone picture because of the wrong raw cut choice, by scanning all cyclic cuts for the raw cut-chain variation on `n = 5,6,7,8`.

### Outcome
FAILED

### Concrete Artifacts
- Best raw cuts found by minimizing the number of positive-variation movers:
  - `n5`, state counts `(2,2,2,3,4)`:
    best cut `0`, positive movers `{0: 24, 2: 24, 3: 16, 4: 12}`
  - `n6`, state counts `(2,2,2,4,3,3)`:
    best cut `4`, positive movers `{0: 72, 2: 18, 3: 24, 4: 40, 5: 48}`
  - `n7`, state counts `(3,2,2,2,3,4,3)`:
    best cut `6`, positive movers `{0: 96, 1: 144, 3: 72, 4: 108, 5: 96, 6: 144}`
  - `n8`, state counts `(2,2,3,4,3,3,2,3)`:
    best cut `0`, positive movers `{0: 432, 1: 216, 2: 216, 3: 504, 4: 360, 5: 576, 6: 432}`
- So changing the raw cut does not recover a bounded quaternary-centered source zone in the known small optima.

## Exploration 14

### Strategy
Retask to the new sharp lower-bound target `4·3^(n-2)` by doing two things in parallel:
1. inventory the exact `n = 9` frontier `(7776,8748)` after Case 1 and Case 2,
2. calibrate a witness-shaped good-cycle probe against the new bound architecture `(2,3,3,3,3,3,3,3,2)` and then test that probe on the entire reduced frontier.

### Outcome
SUCCEEDED

### Failure Constraint
The old quick-screen intuition is no longer calibrated. A `20s / 200000` run of `p2_cycle_screen.py` on the valid bound shape `(2,3,3,3,3,3,3,3,2)` finds zero survivors, even though a locally consistent 25-step bounce scaffold exists there. So short survivor-free screens are not trustworthy lower-bound evidence against the new witness regime.

### What This Rules Out
- Any lower-bound attack that treats short-budget survivor-free `p2_cycle_screen` output as meaningful negative evidence is too weak for the new target.
- Any approach that keeps the sub-`8748` frontier at the raw “24 multisets” level is leaving obvious structure on the table; the right finite object is the much smaller set of binary skeletons.
- The calibrated 25-step two-ended bounce scaffold is not a generic phenomenon across the exact frontier below `8748`: it already fails on one representative of every safe binary run type tested.

### Surviving Structure
- The exact `n = 9` frontier below `8748` is unexpectedly small:
  - `24` multisets total,
  - `12` fully blocked by Case 2,
  - `12` mixed,
  - `644` safe necklaces total.
- There are no 3-binary multisets anywhere in `(7776,8748)`. After Case 1 and Case 2, the live residue has only `4,5,6` binaries.
- The `644` safe necklaces collapse to only `11` cyclic binary run types:
  - `k = 4`: `(1,1,1,1)`, `(2,1,1)`, `(2,2)`, `(3,1)`
  - `k = 5`: `(2,1,1,1)`, `(2,2,1)`, `(3,1,1)`, `(3,2)`
  - `k = 6`: `(2,2,2)`, `(3,2,1)`, `(3,3)`
- A simple explicit 25-step mover sequence,
  `0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8`,
  admits a locally consistent good cycle on `(2,3,3,3,3,3,3,3,2)`.
- The same 25-step seed fails on:
  - one canonical safe orientation of every live sub-`8748` multiset,
  - one representative of each of the `11` safe binary run types.

### Reformulations
- Exact sub-`8748` frontier as binary skeletons: the real finite target at `n = 9` is not 24 multisets but 11 cyclic binary run types with attached nonbinary state masses.

LOAD-BEARING ASSESSMENT: High. This is the first reduction that looks small enough for a genuine structural case split rather than brute-force drift.

- Calibrated 25-step bounce scaffold: instead of talking vaguely about “a bounce cycle,” use the explicit mover sequence
  `0,1,...,8,7,...,1,0,1,...,8`
  as a proof-facing scaffold.

LOAD-BEARING ASSESSMENT: Moderate to high. It is the first concrete good-cycle normal form aligned with the new upper-bound architecture and it already separates the bound shape from every tested sub-`8748` skeleton representative.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/glb_sub8748_inventory.py` returned:
  - `24` frontier multisets in `(7776,8748)`
  - binary histogram `{4: 1, 5: 4, 6: 7, 7: 8, 8: 4}`
  - Case-2 split `{'blocked': 12, 'mixed': 12}`
  - safe-necklace total `644`
- Frontier families with safe necklaces:
  - `8000`: `(2,2,2,2,2,2,5,5,5)`
  - `8064`: `(2,2,2,2,2,3,3,4,7)`
  - `8064`: `(2,2,2,2,2,2,3,3,14)`
  - `8064`: `(2,2,2,2,2,2,3,6,7)`
  - `8192`: `(2,2,2,2,2,4,4,4,4)`
  - `8192`: `(2,2,2,2,2,2,4,4,8)`
  - `8448`: `(2,2,2,2,2,2,3,4,11)`
  - `8640`: `(2,2,2,2,3,3,3,4,5)`
  - `8640`: `(2,2,2,2,2,3,3,3,10)`
  - `8640`: `(2,2,2,2,2,3,3,5,6)`
  - `8640`: `(2,2,2,2,2,2,3,3,15)`
  - `8640`: `(2,2,2,2,2,2,3,5,9)`
- Binary run-type counts from the same script:
  - `k = 4`:
    - `(1,1,1,1)`: `20`
    - `(2,1,1)`: `120`
    - `(2,2)`: `40`
    - `(3,1)`: `80`
  - `k = 5`:
    - `(2,1,1,1)`: `29`
    - `(2,2,1)`: `87`
    - `(3,1,1)`: `87`
    - `(3,2)`: `87`
  - `k = 6`:
    - `(2,2,2)`: `10`
    - `(3,2,1)`: `56`
    - `(3,3)`: `28`
- `python3 scripts/p2_cycle_screen.py 2,3,3,3,3,3,3,3,2 --time-limit 20 --max-cycles 200000 --progress-seconds 5`
  gave:
  - `screened=2 survivors=0 elapsed=20.000s`
  even though the architecture is now known to admit a valid system.
- `python3 scripts/glb_seeded_bounce_probe.py --mode witness --timeout-ms 5000`
  found a locally consistent good cycle of length `25` on `(2,3,3,3,3,3,3,3,2)` for mover sequence
  `0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8`.
- The corresponding explicit cycle is:
  - `(0,0,0,0,0,0,0,0,0)`
  - `(1,0,0,0,0,0,0,0,0)`
  - `(1,1,0,0,0,0,0,0,0)`
  - `(1,1,1,0,0,0,0,0,0)`
  - `(1,1,1,1,0,0,0,0,0)`
  - `(1,1,1,1,1,0,0,0,0)`
  - `(1,1,1,1,1,1,0,0,0)`
  - `(1,1,1,1,1,1,1,0,0)`
  - `(1,1,1,1,1,1,1,1,0)`
  - `(1,1,1,1,1,1,1,1,1)`
  - `(1,1,1,1,1,1,1,2,1)`
  - `(1,1,1,1,1,1,2,2,1)`
  - `(1,1,1,1,1,2,2,2,1)`
  - `(1,1,1,1,2,2,2,2,1)`
  - `(1,1,1,2,2,2,2,2,1)`
  - `(1,1,2,2,2,2,2,2,1)`
  - `(1,2,2,2,2,2,2,2,1)`
  - `(0,2,2,2,2,2,2,2,1)`
  - `(0,0,2,2,2,2,2,2,1)`
  - `(0,0,0,2,2,2,2,2,1)`
  - `(0,0,0,0,2,2,2,2,1)`
  - `(0,0,0,0,0,2,2,2,1)`
  - `(0,0,0,0,0,0,2,2,1)`
  - `(0,0,0,0,0,0,0,2,1)`
  - `(0,0,0,0,0,0,0,0,1)`
- `python3 scripts/glb_seeded_bounce_probe.py --mode frontier-canonical --timeout-ms 5000`
  failed on one canonical safe orientation of every live sub-`8748` multiset.
- Representative seeded failures by binary run type:
  - `(4,(1,1,1,1))`: `(2,3,2,3,2,3,2,4,5)`
  - `(4,(2,1,1))`: `(2,2,3,2,3,2,3,4,5)`
  - `(4,(2,2))`: `(2,2,3,2,2,3,3,4,5)`
  - `(4,(3,1))`: `(2,2,2,3,2,3,3,4,5)`
  - `(5,(2,1,1,1))`: `(2,2,3,2,3,2,4,2,7)`
  - `(5,(2,2,1))`: `(2,2,3,2,2,3,2,4,7)`
  - `(5,(3,1,1))`: `(2,2,2,3,2,3,2,4,7)`
  - `(5,(3,2))`: `(2,2,2,3,2,2,3,4,7)`
  - `(6,(2,2,2))`: `(2,2,5,2,2,5,2,2,5)`
  - `(6,(3,2,1))`: `(2,2,2,5,2,2,5,2,5)`
  - `(6,(3,3))`: `(2,2,2,5,2,2,2,5,5)`
  and every one of these returned
  `no locally consistent good cycle exists for this mover sequence`.

STRUCTURAL RESULTS:
- The new exact lower-bound frontier below `8748` has no 3-binary families; the live residue begins at 4 binaries.
- The live residue has only `11` binary run types.
- The 25-step two-ended bounce scaffold is locally consistent on the bound shape `(2,3,3,3,3,3,3,3,2)` and incompatible with every tested sub-`8748` skeleton representative.

TOOLS:
- Added `scripts/glb_sub8748_inventory.py`.
- Added `scripts/glb_seeded_bounce_probe.py`.

REPRESENTATIONS:
- Exact frontier inventory in the interval `(7776,8748)`.
- Binary run type as the architecture-level skeleton.
- Calibrated 25-step bounce scaffold as a seeded good-cycle normal form.

### What Would Unblock This
- A bounded full scan of `scripts/glb_seeded_bounce_probe.py --mode frontier-all` with progress and per-orientation timeout chosen so the run is guaranteed to finish, to determine whether *any* safe sub-`8748` orientation admits the calibrated 25-step scaffold.
- A theorem that any valid near-bound `n = 9` system must realize this 25-step scaffold, or a closely related two-ended bounce scaffold with the same on-cycle state lower bounds `[2,3,3,3,3,3,3,3,2]`.
- A way to compare other plausible bounce mover sequences of similar shape against the same `11` run types.

### Key Parameters
- Frontier interval: `(7776,8748)`.
- Live residue:
  - `12` mixed multisets,
  - `644` safe necklaces,
  - `11` binary run types.
- Calibrated seeded mover sequence:
  `0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8`.

### Open Questions
- Does any safe sub-`8748` orientation admit the calibrated 25-step scaffold, or do the representative failures already reflect a universal seeded obstruction?
- Is the 25-step scaffold the right canonical normal form for all near-optimal `n = 9` witnesses, or only one gauge of the new upper-bound witness?
- Can the seeded failures on the `11` run types be explained analytically by an internal-binary obstruction, rather than by SAT output alone?

## Synthesis after exploration 14

The new target is finally finite in a way that matters.

- Arithmetic plus Case 2 does not just leave “some gap below `8748`.”
  It leaves exactly `12` mixed families and `11` binary skeletons.
- The old quick screens are not calibrated to the new witness regime.
- But there is now a concrete witness-shaped scaffold to test instead: a 25-step two-ended bounce wave on `(2,3,3,3,3,3,3,3,2)`.

This changes the search strategy materially. The most promising theorem target is no longer “rule out 24 multisets somehow.” It is:

- classify which binary skeletons can support the calibrated two-ended bounce scaffold,
- prove the sub-`8748` skeletons cannot,
- and then argue that any valid near-bound system must use that scaffold or a very close relative.

That is the first path in this project that looks like it could close the exact `n = 9` lower bound without drifting into broad enumeration.

## Exploration 15 (probe): the calibrated 25-step scaffold is componentwise minimal

Strategy:
- Test whether the calibrated witness-shaped mover sequence
  `0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8`
  already forces the exact local-state profile `(2,3,3,3,3,3,3,3,2)` at the good-cycle level.
- Concretely: keep the seeded mover sequence fixed, verify the base vector is SAT, then lower one coordinate at a time and see whether the seeded good-cycle constraints become UNSAT.

What I computed:
- `python3 scripts/glb_seeded_bounce_probe.py --mode minimality --timeout-ms 5000`

Outcome:
- SUCCEEDED. The calibrated seeded scaffold is not merely compatible with `(2,3,3,3,3,3,3,3,2)`; it is componentwise minimal.
- The base vector is SAT:
  - `(2,3,3,3,3,3,3,3,2)` admits a locally consistent seeded good cycle.
- Every single interior downgrade kills the scaffold:
  - lowering processor `1`: `(2,2,3,3,3,3,3,3,2)` is UNSAT
  - lowering processor `2`: `(2,3,2,3,3,3,3,3,2)` is UNSAT
  - lowering processor `3`: `(2,3,3,2,3,3,3,3,2)` is UNSAT
  - lowering processor `4`: `(2,3,3,3,2,3,3,3,2)` is UNSAT
  - lowering processor `5`: `(2,3,3,3,3,2,3,3,2)` is UNSAT
  - lowering processor `6`: `(2,3,3,3,3,3,2,3,2)` is UNSAT
  - lowering processor `7`: `(2,3,3,3,3,3,3,2,2)` is UNSAT

Interpretation:
- This is the sharpest lower-bound building block so far.
- The seed does not just separate the bound witness from sampled sub-`8748` residue; it certifies that this specific 25-step two-ended bounce scaffold already carries the exact product lower bound `2 * 3^7 * 2 = 8748`.
- So a plausible proof route is now:
  1. show any valid near-bound `n = 9` system must realize this scaffold or a close relative,
  2. show every such scaffold forces the componentwise pattern `[2,3,3,3,3,3,3,3,2]`,
  3. conclude product at least `4 * 3^7`.

Why this matters:
- It eliminates the old convergence-gap distraction completely in this regime.
- The exact lower bound is now visible at the seeded good-cycle level.
- The remaining problem is not “where does the extra factor come from?” but “why must any valid small-product witness contain this two-ended phase wave?”

## Exploration 16 (probe): the obstruction survives the whole bounce-word orbit

Strategy:
- Check whether the seeded separation found in explorations 14-15 is really about one arbitrarily anchored mover word, or about the whole two-ended bounce scaffold.
- I extended `scripts/glb_seeded_bounce_probe.py` with bounded mover-variant families:
  - `shifts`: all `25` cyclic shifts of the calibrated word
    `0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8`
  - `dihedral`: the `50` distinct cyclic shifts of that word and its reversal.
- Then I tested these mover families against:
  1. the bound architecture `(2,3,3,3,3,3,3,3,2)`,
  2. one representative safe orientation from each of the `11` live binary run types below `8748`,
  3. one canonical safe orientation from each of the `12` live multisets below `8748`.

What I computed:
- `python3 scripts/glb_seeded_bounce_probe.py --mode variant-witness --variant-family shifts --timeout-ms 3000`
- `python3 scripts/glb_seeded_bounce_probe.py --mode variant-run-types --variant-family shifts --timeout-ms 1000`
- `python3 scripts/glb_seeded_bounce_probe.py --mode variant-frontier-canonical --variant-family shifts --timeout-ms 1000`
- `python3 scripts/glb_seeded_bounce_probe.py --mode variant-witness --variant-family dihedral --timeout-ms 3000`
- `python3 scripts/glb_seeded_bounce_probe.py --mode variant-run-types --variant-family dihedral --timeout-ms 1000`

Outcome:
- The witness architecture is orbit-robust:
  - all `25/25` cyclic shifts are SAT on `(2,3,3,3,3,3,3,3,2)`;
  - all `50/50` dihedral variants are SAT on `(2,3,3,3,3,3,3,3,2)`;
  - no `unknown` results appeared.
- The entire sub-`8748` residue is orbit-incompatible at the representative level:
  - each of the `11` binary run types is `0/25` against the shift orbit;
  - each of the same `11` run types is `0/50` against the dihedral orbit;
  - again there were no `unknown` results.
- The stronger family-level statement also holds for the `12` canonical live frontier orientations:
  - every one of them is `0/25` against the full cyclic-shift orbit.

Interpretation:
- The calibrated 25-step scaffold is not a fragile artifact of one phase origin.
- On the bound architecture, the whole bounce-word orbit is realizable.
- On every tested sub-`8748` architecture class, the whole shift orbit fails, and the run-type representatives even fail under reversal as well.
- This materially sharpens the theorem target. We no longer need to argue about one ad hoc seeded word. We can aim for:
  - any near-bound valid `n = 9` witness must realize some member of this two-ended bounce orbit;
  - every such orbit member forces the componentwise lower bound `[2,3,3,3,3,3,3,3,2]`;
  - all sub-`8748` binary skeletons are incompatible with that orbit.

Why this matters:
- The scaffold now behaves like a bona fide normal form rather than a one-off SAT curiosity.
- The separation between `8748` and the lower-product residue is now visible at the level of orbit geometry:
  - witness shape: realizable for the entire bounce orbit;
  - subcritical residue: unrealizable for every tested orbit representative and every canonical live multiset.
- That is the first experimentally stable obstruction in this project that matches the new exact-bound candidate `4 * 3^(n-2)`.

## Exploration 17 (theorem/probe): binary parity explains the entire dihedral frontier obstruction

Strategy:
- Try to explain the exploration-16 orbit obstruction without SAT black boxes.
- Key question: what invariant does a binary processor satisfy on any good cycle, regardless of the other rules?

Main lemma:
- If processor `i` is binary, then on any good cycle it must move an even number of times.
- Reason: every privileged move changes the local state; for a binary processor every change flips `0 <-> 1`; after traversing the whole cycle the system returns to the same configuration, so the total number of flips at `i` must be even.

Immediate consequence for the calibrated 25-step dihedral family:
- For every mover word in the family, the mover counts are
  - `P0`: `2`
  - `P1..P7`: `3`
  - `P8`: `2`
- So only processors `0` and `8` can possibly be binary on a good cycle from this family.
- This recovers the exact componentwise lower bound `[2,3,3,3,3,3,3,3,2]` for the whole dihedral family without any SMT minimality check.

What I computed:
- Added parity-aware full scan mode to `scripts/glb_seeded_bounce_probe.py`.
- Ran
  - `python3 scripts/glb_seeded_bounce_probe.py --mode variant-frontier-all --variant-family dihedral --timeout-ms 1000`

Outcome:
- COMPLETE exact frontier exhaustion for the dihedral family:
  - total safe orientations below `8748`: `644`
  - total checks against the `50` dihedral variants: `32200`
  - parity-blocked before SAT: `32200`
  - SAT hits: `0`
  - unknowns: `0`
- Multiset-by-multiset, every live family is blocked in the same way.

Interpretation:
- Exploration 16’s empirical separation is now a theorem for the whole dihedral bounce family.
- We no longer need SAT at all to rule out sub-`8748` architectures against that family.
- The only remaining issue is not the lower bound inside the family, but family necessity: why must a valid near-bound witness realize some scaffold with a similarly restrictive mover-count pattern?

Why this matters:
- This is the cleanest lower-bound mechanism found so far.
- It converts the best current computational obstruction into a one-line analytical invariant:
  binary processors force even mover multiplicity.
- It also shows that the exact lower bound `8748` is visible at the good-cycle level in a very robust way: two even-multiplicity endpoints, seven odd-multiplicity interior processors.

## Exploration 18 (probe): the right class is larger than the bounce orbit, but still tiny

Strategy:
- Test nearby mover-sequence classes directly rather than assuming the 25-step bounce orbit is unique.
- Model mover words as fair adjacent walks on the cut chain `0..8`, meaning successive movers differ by `1`, the word has length `25`, starts at `0`, ends at `8`, and visits every processor at least once.
- Enumerate these words, classify by turnaround count, apply the binary-parity filter first, and run the seeded SAT check only on the survivors.

What I built:
- Added `scripts/glb_adjacent_walk_scan.py`.

What I computed:
- `python3 scripts/glb_adjacent_walk_scan.py --mode turn-summary`
- `python3 scripts/glb_adjacent_walk_scan.py --mode sat-scan --turn-counts 2,4 --timeout-ms 1000`
- `python3 scripts/glb_adjacent_walk_scan.py --mode sat-scan --turn-counts 6 --timeout-ms 1000`
- `python3 scripts/glb_adjacent_walk_scan.py --mode sat-scan --turn-counts 8 --timeout-ms 1000`
- Also inspected mover-count patterns among parity-compatible `2/4/6`-turn words.

Raw combinatorics:
- Total fair adjacent words of length `25`: `177859`
- Turnaround distribution:
  - `2`: `1`
  - `4`: `140`
  - `6`: `2730`
  - `8`: `18130`
  - `10`: `50960`
  - `12`: `64428`
  - `14`: `35035`
  - `16`: `6435`

Key structural fact:
- The unique `2`-turn word is exactly the standard bounce
  `0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8`.
- So if one ever proves that a near-bound witness must have an adjacent mover word with exactly two turnarounds, the mover word is forced combinatorially.

SAT results on the bound architecture `(2,3,3,3,3,3,3,3,2)`:
- `2` turns:
  - total `1`
  - parity-compatible `1`
  - SAT `1`
- `4` turns:
  - total `140`
  - parity-compatible `7`
  - SAT `1`
- `6` turns:
  - total `2730`
  - parity-compatible `161`
  - SAT `0`
- `8` turns:
  - total `18130`
  - parity-compatible `1246`
  - SAT `0`
- No `unknown` results appeared in any of these scans.

The new valid `4`-turn word:
- The unique `4`-turn SAT survivor is
  `0,1,0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,2,3,4,5,6,7,8`.
- I checked completion explicitly:
  - `solve_good_cycle_from_movers(...)` finds a seeded cycle of length `25`;
  - `solve_cycle_with_smt(...)` completes it to a valid system.
- So the claim “any near-bound valid witness must realize the exact bounce orbit” is false.

Important refinement:
- Every parity-compatible `2`-turn and `4`-turn adjacent word has the same mover-count vector
  `[2,3,3,3,3,3,3,3,2]`.
- At `6` turns there are already `45` distinct compatible mover-count vectors, and one of them is still `[2,3,3,3,3,3,3,3,2]`, but all `6`-turn words are UNSAT anyway.
- Therefore:
  - mover-count vector `[2,3,...,3,2]` is not sufficient by itself;
  - low turnaround complexity appears to matter;
  - the right theorem target is broader than the dihedral bounce orbit, but still much smaller than the full adjacent-word space.

Interpretation:
- The best current candidate normal form is no longer “the bounce orbit.”
- It is closer to:
  - fair adjacent length-`25` mover words,
  - with binary-parity-compatible multiplicities,
  - and very low turnaround complexity.
- The data so far says:
  - the valid corner is tiny (`2`-turn: `1/1`, `4`-turn: `1/7`, `6`-turn: `0/161`, `8`-turn: `0/1246` after parity pruning),
  - while the entire subcritical frontier is still completely blocked against the dihedral bounce family by parity alone.

Why this matters:
- This rescopes the endgame correctly.
- Step 3 should not try to prove “must be the exact bounce word.”
- It should try to prove something like:
  valid near-bound witnesses must have an adjacent mover word with endpoint-even / interior-odd multiplicities and very low turnaround complexity.
- If that can be done, the parity lemma supplies the lower bound immediately.

## Exploration 19 (probe/theorem): invalid low-turn words fail by repeating an already-determined local context

Strategy:
- Compare the unique valid `4`-turn survivor against the nearest invalid adjacent words, instead of comparing only mover counts.
- Hypothesis: the invalid words are not failing for diffuse global reasons; they are forcing some processor to see a local context that was already determined earlier in the cycle, but with the wrong mover/nonmover output.

What I built:
- Added `scripts/glb_seeded_unsat_core.py` to extract minimized unsat cores from the seeded-cycle encoding.

What I computed:
- Enumerated the `7` parity-compatible `4`-turn words.
- Checked SAT on all `7`; only the bottom-end insertion survives:
  - valid:
    `0,1,0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,2,3,4,5,6,7,8`
  - invalid:
    all other `6` parity-compatible `4`-turn words.
- Ran `glb_seeded_unsat_core.py` on the invalid `4`-turn words and on the closest invalid `6`-turn same-count word
  `0,1,0,1,2,1,2,3,4,5,6,7,8,7,6,5,4,3,2,3,4,5,6,7,8`.

Core pattern for the invalid `4`-turn words:
- Every invalid `4`-turn word collapses to a single distinguished-bottom context constraint:
  - `ctx_0_0_u`
- Concretely:
  - insertion near `P1`: `ctx_0_0_10`
  - insertion near `P2`: `ctx_0_0_9`
  - insertion near `P3`: `ctx_0_0_10`
  - insertion near `P4`: `ctx_0_0_12`
  - insertion near `P5`: `ctx_0_0_17`
  - insertion near `P6`: `ctx_0_0_16`
- The matching move label is always a bottom move `move_*_0`.

Interpretation of that core:
- At time `0`, processor `0` sees its initial all-zero local context and is the mover, so that context is committed to output `1`.
- In each invalid `4`-turn word, the mover pattern later forces processor `0` to revisit the same local context while not being the mover.
- That would require the same context to output `0`, contradicting determinism.
- So these words are ruled out by a clean analytic mechanism:
  repeating the initial `P0` context with the wrong mover status.

The valid `4`-turn word explains the exception:
- Its extra backtrack is exactly at the distinguished bottom end.
- When `P0` returns to `0`, `P1` has advanced to `2`, so the local context at `P0` is not the original all-zero context.
- Hence the repeated-context contradiction does not fire.

What shows up at `6` turns:
- The nearest invalid `6`-turn word with the same mover-count vector `[2,3,3,3,3,3,3,3,2]`
  also collapses to `ctx_0_0_10`.
- So the repeated-bottom-context obstruction survives beyond the `4`-turn family.
- Sampling other invalid `6`-turn words shows a second related failure mode:
  a processor such as `P2` is forced to move on its original all-zero local context (`ctx_2_0_4`).

The new local-context lemma template:
- At the all-zero anchor, every processor `i > 0` is initially nonmover on context `(0,0,0)`.
- Therefore no processor `i > 0` may ever later be a mover on that same local context.
- Likewise, processor `0` is initially a mover on `(0,0,0)`, so it may never later be a nonmover on that same local context.
- Extra turnarounds appear to be ruled out precisely when they force one of these forbidden repeats.

Why this matters:
- This is the first actual mechanism I have for “why low turnaround.”
- It is no longer just “only two adjacent words survive.”
- It is:
  extra turnarounds create forbidden repeats of already-determined initial contexts.
- That is the kind of statement that plausibly scales to an analytical proof.

## Exploration 20 (lemma/probe): one move is impossible, so many high-turn words die before SAT

Main lemma:
- In any good cycle, a processor cannot move exactly once.
- Reason: only that processor’s own moves can change its local state; if it changes once and never changes again, the cycle cannot return to the initial configuration.

What I changed:
- Added this as a pre-SAT filter in `scripts/glb_adjacent_walk_scan.py` (`cycle_count_compatible`).

What I computed:
- For `10`-turn adjacent words on `(2,3,3,3,3,3,3,3,2)`:
  - parity-compatible: `4088`
  - still cycle-count-compatible after removing one-move words: `1337`

Interpretation:
- A large fraction of the high-turn space is impossible for a trivial cycle-closure reason before any local-context SAT work.
- So the emerging general lower-bound toolbox is now:
  1. binary processors must move an even number of times;
  2. every processor in a fair cycle must move at least twice;
  3. extra turnarounds force forbidden repeats of already-determined initial contexts.

Why this matters:
- This is the first plausible bridge from the `n = 9` mover-word experiments to a general-`n` lower bound.
- Items (1) and (2) are completely general.
- Item (3) is currently strongest for adjacent path-like mover words, but it looks like the missing mechanism behind “must be low-turn.”

## Exploration 21 (theorem/probe): any adjacent word of length `3n-2` already forces mover counts `[2,3,...,3,2]`

This is the cleanest general-`n` statement I found this turn.

The edge-triple lemma:
- Let `m_0,...,m_{3n-3}` be a mover word on the cut chain `0..n-1` such that
  - `m_0 = 0`,
  - `m_{3n-3} = n-1`,
  - `|m_{t+1} - m_t| = 1` for every `t`.
- Then every edge `(i,i+1)` is traversed exactly `3` times.

Proof sketch:
- Let `x_i` be the total number of transitions across edge `(i,i+1)`.
- Since the walk starts to the left of edge `i` and ends to its right, the net number of left-to-right minus right-to-left traversals across that edge is `1`.
- Therefore `x_i` is odd and at least `1`.
- The total number of transitions is `3n-3 = 3(n-1) = sum_i x_i`.
- There are `n-1` edges and each `x_i` is an odd positive integer, so the only possibility is `x_i = 3` for every edge.

Vertex-count corollary:
- Endpoints appear exactly twice:
  - `P0` appears `2` times,
  - `P_{n-1}` appears `2` times.
- Every interior processor `P_i` for `1 <= i <= n-2` appears exactly `3` times.
- So any adjacent mover word of length `3n-2` has mover multiplicity vector
  `[2,3,3,...,3,2]`, regardless of turnaround count.

Lower-bound corollary:
- Combine this with the binary parity lemma:
  a binary processor must move an even number of times.
- Therefore for any good cycle with an adjacent mover word of length `3n-2`,
  only the two endpoints can be binary.
- Hence the local-state lower bound `[2,3,3,...,3,2]` follows immediately.

Answer to the valid `4`-turn question:
- Yes. The valid `4`-turn word is componentwise minimal for exactly this reason.
- At `n=9` I also checked it computationally by lowering each interior `3` to `2`; every downgrade is UNSAT.

General-`n` evidence from the `4`-turn family:
- The `4`-turn adjacent words of length `3n-2` are indexed by the position of the extra backtrack pair.
- For `n=10` and state counts `(2,3,3,3,3,3,3,3,3,2)`:
  - bottom insertion (`k=0`) is SAT,
  - interior insertions (`k=1,2`) are UNSAT.
- The first interior insertion already shows the same minimized unsat-core pattern as `n=9`:
  - `ctx_0_0_7`
  - together with a bottom move label `move_4_0`
- So the repeated-initial-`P0`-context obstruction is not an `n=9` artifact; it persists at `n=10`.

What this buys conceptually:
- If one can prove that any valid near-bound witness has an adjacent mover word of length `3n-2`, the lower bound is basically done:
  - the edge-triple lemma fixes the mover multiplicities,
  - parity forces all interior processors to be nonbinary,
  - giving `[2,3,...,3,2]` and product `4 * 3^(n-2)`.

What remains:
- The hard step is now sharply isolated:
  prove adjacency/length/low-turn necessity for valid near-bound systems.
- But the multiplicity part is no longer mysterious at all once adjacency and length are granted.

## Exploration 22 (answers to the remaining lower-bound subquestions)

### 1. Does the valid `4`-turn word also force `[2,3,...,3,2]` componentwise?

Yes.

At `n=9`:
- I checked the valid `4`-turn word
  `0,1,0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,2,3,4,5,6,7,8`
  on `(2,3,3,3,3,3,3,3,2)`.
- Lowering any interior `3` to `2` makes the seeded good-cycle constraints UNSAT.

At `n=10`:
- The bottom-insertion `4`-turn word
  `0,1,0,1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,2,3,4,5,6,7,8,9`
  is SAT on `(2,3,3,3,3,3,3,3,3,2)`.
- Lowering any interior coordinate to `2` again makes the seeded cycle UNSAT.

So the exact componentwise lower bound is not tied to the standard bounce word.
It holds for the valid low-turn alternative as well.

### 2. Can parity + “no processor moves exactly once” alone force stronger multiplicities?

Only partially.

What they do force:
- binary processors move an even number of times;
- every processor moves either `0` or at least `2` times, and fairness eliminates `0`.

What they do **not** force by themselves:
- They do **not** imply length `3n-2`.
- They do **not** imply multiplicities `[2,3,...,3,2]` on a ring-adjacent mover word.

Concrete counterexample:
- the cyclic double sweep
  `0,1,2,...,n-1,0,1,2,...,n-1`
  is ring-adjacent and gives multiplicity vector `[2,2,...,2]`.
- It satisfies fairness, parity for any binary processors, and the no-single-move lemma.
- So these two lemmas alone are still too weak.

Interpretation:
- parity + no-single are necessary filters,
- but the missing strength is still in the context-repeat / low-turn mechanism.

### 3. Does the context-repeat obstruction extend beyond `n=9`?

Yes, at least for the first nontrivial family where it should.

For the `4`-turn family:
- At `n=10`, bottom insertion (`k=0`) is SAT, while interior insertions (`k=1,2`) are UNSAT.
- The first interior insertion yields minimized core
  - `ctx_0_0_7`
  - together with bottom move `move_4_0`.
- At `n=11`, the same pattern persists:
  - bottom insertion (`k=0`) is SAT,
  - first interior insertion (`k=1`) is UNSAT.

So the “only bottom-end hesitation survives” phenomenon continues at least through `n=11`,
and the unsat core still points to a repeated initial `P0`-context contradiction.

### Current best formulation of the open lemma

The sharpest statement I can currently defend is:

- In the adjacent length-`3n-2` regime, extra interior turnarounds appear to force a repeat of an already-determined initial local context, usually at `P0` and sometimes at the first interior processor past the extra turnaround.
- Bottom-end hesitation is exceptional because by the time `P0` moves again, its neighbor has advanced far enough to change the local context, so the repeat does not occur.

This is not yet a full proof for all low-turn adjacent words, but it is now supported by:
- exact `n=9` low-turn scans,
- unsat-core structure at `n=9`,
- the same family pattern at `n=10`,
- and the same SAT/UNSAT split at `n=11`.

## Exploration 23 (probe): the repeated context is exactly the all-zero triple

This answers the most concrete open question from the current lower-bound program.

Question:
- In the recurring minimized cores of the form `ctx_0_0_u`, what local context at `P0` is actually repeating?

Answer:
- For the invalid `4`-turn family at `n=9,10,11`, the repeated context can be pinned down exactly:
  - local context at `P0` is `(L,S,R) = (0,0,0)`,
  - at time `0` the output is `1` because `P0` is the mover,
  - at the later time `u` the output is `0` because `P0` is not the mover.

Concrete realizations:
- `n=9`, invalid `4`-turn word
  `0,1,2,1,0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,3,4,5,6,7,8`
  has minimized core `ctx_0_0_10` + `move_4_0`,
  and under the full move/stay constraints plus same-context and opposite-output requirements:
  - `left_t = left_u = 0`
  - `self_t = self_u = 0`
  - `right_t = right_u = 0`
  - `output_t = 1`
  - `output_u = 0`
- `n=10`, first invalid `4`-turn insertion has the same exact realized triple:
  - minimized core `ctx_0_0_7` + `move_4_0`
  - realized context again `(0,0,0)` with outputs `1` then `0`
- `n=11`, same story:
  - minimized core `ctx_0_0_6` + `move_4_0`
  - realized context again `(0,0,0)` with outputs `1` then `0`

So the cross-`n` pattern is not just “some repeated `P0` context.”
It is specifically the all-zero initial context of `P0`.

Why this matters:
- It makes the intended proof shape much more concrete.
- The obstruction is now:
  the mover word forces `P0` to revisit its initial all-zero local context while no longer being the mover.
- That is exactly the deterministic contradiction one wants for a clean lower-bound lemma.

## Exploration 24 (probe): the invalid `4`-turn family has a whole forbidden all-zero window at `P0`

Define the `4`-turn family on the cut chain by
- `W_{n,k}` = go up to `k+1`, back to `0`, sweep to `n-1`, back down to `k+1`, then sweep up again,
- where `k = 0` is the valid bottom insertion and `k >= 1` are interior insertions.

What I computed:
- For `n = 10,11,12` and `k = 0,1,2,3`, I checked whether the move/stay constraints admit a time `u`
  such that:
  - `P0` is in context `(0,0,0)` at time `0`,
  - `P0` is again in context `(0,0,0)` at time `u`,
  - `output_0 != output_u`.

Pattern:
- For the valid bottom insertion `k = 0`: no such time exists.
- For every tested interior insertion `k >= 1`: there is a whole interval of such times,
  experimentally
  - `u = 2k+4, 2k+5, ..., n+2k+1`.

Examples:
- `n=11, k=1`: `u = 6..14`
- `n=11, k=2`: `u = 8..16`
- `n=11, k=3`: `u = 10..18`
- `n=12, k=1`: `u = 6..15`
- `n=12, k=2`: `u = 8..17`
- `n=12, k=3`: `u = 10..19`

Interpretation:
- Interior turnarounds do not create one isolated bad time.
- They create an entire forbidden window during which `P0` can sit in its all-zero context with the wrong mover status.
- Bottom-end hesitation is exceptional because this window disappears completely at `k = 0`.

This is the cleanest family-level evidence so far for the slogan:
- bottom hesitation is allowed,
- interior hesitation recreates the initial `P0` context.

## Exploration 25 (probe): interior processors also exhibit all-zero context-repeat obstructions

The obstruction is not exclusive to `P0`.

Sample:
- For the invalid `6`-turn word
  `0,1,0,1,2,3,2,3,4,5,6,7,8,7,6,5,4,3,4,5,6,7,8`
  the minimized unsat core can land on `ctx_2_0_4`.
- Solving the corresponding same-context / opposite-output realization shows:
  - processor `2` repeats local context `(0,0,0)`,
  - at time `0` processor `2` is a nonmover so output is `0`,
  - at time `4` processor `2` is the mover so output must be nonzero.

So the broader principle seems to be:
- once the mover word creates a local spur around processor `i`,
  it can force processor `i` to encounter its initial all-zero local context with the opposite mover status.

This is promising because it suggests a processor-local obstruction, not merely a bottom-end special case.

## Exploration 26 (important correction): double sweep is not killed by context-repeat at the good-cycle level

I checked the ring-adjacent double sweep on the bound architecture:
- mover word `0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8`
- state counts `(2,3,3,3,3,3,3,3,2)`

Outcome:
- `solve_good_cycle_from_movers(...)` finds a locally consistent seeded cycle of length `18`.
- But `solve_cycle_with_smt(...)` reports
  `propagation proves this cycle cannot complete`.

Interpretation:
- Context-repeat is not the universal killer for all invalid mover words.
- It is the best current mechanism for ruling out low-turn cut-chain alternatives.
- Double sweep fails later, at completion / convergence, not already at the seeded good-cycle level.

Why this matters:
- It prevents an overclaim.
- The remaining theorem target is not simply “every invalid mover word repeats an initial context.”
- It is more plausibly:
  - low-turn cut-chain words are controlled by the all-zero context-repeat obstruction,
  - wraparound / sweep words are controlled by a different completion obstruction,
  - valid near-bound witnesses are forced into the tiny surviving low-turn class.

## Exploration 27 (probe): direct wrap at `P0` does not create an on-cycle table collision

Question:
- When a sweep reaches `P_{n-1}` and then wraps to `P0`, does the wrap-arrival context at `P0` directly collide with a previously determined `P0` table entry?

For the double sweep on `(2,3,3,3,3,3,3,3,2)`:
- mover word:
  `0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8`
- the seeded cycle exists and forces the following `P0` contexts on-cycle:
  - `(0,0,0) -> 1` at the initial `P0` move,
  - `(0,1,1) -> 1` just before `P8` moves,
  - `(1,1,1) -> 0` at the wrap-arrival `P0` move,
  - `(1,0,0) -> 0` just before the final `P8` move.

So the wrap-arrival context at `P0` is `(1,1,1)`, not `(0,0,0)`.
It does **not** directly collide with the initial `P0` table entry.

Conclusion:
- the no-wrap obstruction is not a direct seeded-cycle contradiction at the wrap point.
- wrap failure must enter later, through completion / convergence.

## Exploration 28 (probe): double sweep fails immediately by a binary off-cycle SCC

What I built:
- Added `scripts/glb_completion_diagnose.py` to inspect endpoint contexts and the first fatal forced SCC seen by propagation.

What I computed:
- `python3 scripts/glb_completion_diagnose.py --movers 0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8`

Outcome:
- The seeded cycle exists.
- Completion does **not** fail by dead configurations or by an SMT impossibility later on.
- It fails immediately in the propagation phase because the forced singleton entries already create a fatal off-cycle SCC.

Structure of that SCC:
- size `168`
- entirely binary (`all_binary = True`)
- ring defect histogram:
  - `2` defects: `56`
  - `4` defects: `112`
- internal mover histogram is perfectly uniform:
  - each processor `0..8` appears exactly `42` times
- many nodes have forced outdegree `2` or `3`, e.g.
  - `(1,1,0,1,1,1,1,1,1)` has forced internal moves by processors `0` and `3`
  - `(1,1,0,0,1,1,1,1,1)` has forced internal moves by processors `0,2,4`

Interpretation:
- Double sweep forces a second recurrent binary subsystem off the good cycle.
- This is a different failure mode from the low-turn context-repeat obstruction.
- It is much closer in flavor to a shadow/bad-SCC phenomenon than to a local table conflict.

Contrast with bounce:
- Running the same diagnosis on the successful bounce word does **not** reveal such an initial fatal SCC.
- So wraparound seems to expose a binary off-cycle recurrent structure that the no-wrap words avoid.
- The valid `4`-turn no-wrap word behaves the same way:
  - seeded cycle exists,
  - no fatal SCC appears in the initial propagation snapshot,
  - the only blocker in the diagnostic run was the SMT timeout, not propagation.

## Exploration 29 (stronger family statement): the bad `P0` all-zero window is forced by move/stay alone

This sharpens the `4`-turn family obstruction substantially.

For the interior-insertion family `W_{n,k}` with `k >= 1`, I asked only for:
- domain constraints,
- anchor `c_0 = 0`,
- and the single-mover move/stay equations from the fixed mover word.

No local-context determinism was used.

Result:
- In the experimentally observed bad window
  `u = 2k+4, ..., n+2k+1`,
  the triple at `P0` is already forced to be
  `(P_{n-1}, P0, P1) = (0,0,0)`.

Examples checked:
- `n=11, k=1`, at `u=6,10,14`:
  - `P10 = 0`, `P0 = 0`, `P1 = 0` are each singleton-forced
- `n=11, k=2`, at `u=8,12,16`:
  - again `P10 = 0`, `P0 = 0`, `P1 = 0` are singleton-forced

So for this family the proof shape is now nearly explicit:
- time `0`: `P0` sees `(0,0,0)` and moves, forcing output `1`;
- throughout the bad window: `P0` is forced back into context `(0,0,0)` while not moving, forcing output `0`;
- determinism gives contradiction.

This is stronger than the earlier unsat-core observation because the repeated all-zero context is not merely compatible with the core:
- it is already forced by the mover word’s move/stay equations.

Why this matters:
- It is the first real family-level no-wrap lemma candidate.
- It suggests that for cut-chain words with an interior return to the bottom, the contradiction can be proved combinatorially before invoking any global completion machinery.

## Exploration 30 (formalization): interior-return obstruction for the `4`-turn family

I can now state the `P0` obstruction as an actual lemma for the family

`W_{n,k} = 0,1,...,k+1,k,...,0,1,2,...,n-1,n-2,...,k+1,k+2,...,n-1`

with `n >= 3` and `1 <= k <= n-2`.

This is exactly the `4`-turn family:
- `k=0` is the bottom insertion, the unique valid branch seen so far,
- `k>=1` are the interior-return variants.

**Lemma (interior return obstruction for `W_{n,k}`):**
Let `C_0,C_1,...,C_{L-1}` be a seeded good cycle with mover word `W_{n,k}`,
anchored at the all-zero configuration `C_0 = 0^n`.
Then for every configuration index

`u in {2k+4, 2k+5, ..., n+2k+1}`

the local context at `P0` is forced to be `(C_u[n-1], C_u[0], C_u[1]) = (0,0,0)`,
while `P0` is not the mover at time `u`.
Hence no deterministic transition function can realize this mover word.

**Proof.**

1. `P0` moves exactly twice in `W_{n,k}`, at steps `0` and `2k+2`.
   After step `2k+2`, `P0` never moves again.
   Therefore the state of `P0` is constant on configurations
   `C_{2k+3}, C_{2k+4}, ..., C_{L-1}, C_0`.
   Since `C_0[0] = 0`, that constant must be `0`.
   So `C_u[0] = 0` for all `u >= 2k+3`.

2. `P1` moves exactly three times, at steps `1`, `2k+1`, and `2k+3`.
   After step `2k+3`, `P1` never moves again.
   By the same closure argument, its state is constant on
   `C_{2k+4}, C_{2k+5}, ..., C_{L-1}, C_0`, hence equal to `C_0[1] = 0`.
   So `C_u[1] = 0` for all `u >= 2k+4`.

3. `P_{n-1}` first moves at step `n+2k+1`.
   Therefore it has not moved yet on any configuration `C_u` with `u <= n+2k+1`,
   so `C_u[n-1] = C_0[n-1] = 0` for all such `u`.

Combining 1-3 gives

`(C_u[n-1], C_u[0], C_u[1]) = (0,0,0)`

for every `u in [2k+4, n+2k+1]`.
But `P0` is not the mover at any such time `u`, so determinism forces
`f_0(0,0,0) = 0` there.
At time `0`, `P0` *is* the mover on the same context `(0,0,0)`, so
`f_0(0,0,0) != 0`.
Contradiction.

Therefore no seeded good cycle can realize `W_{n,k}` for any `k >= 1`.

This upgrades the earlier SAT evidence to a fully combinatorial obstruction for
the whole interior-insertion family.

## Exploration 31 (formalization): what is and is not proved for wraparound

The wraparound side is now cleanly separated from the cut-chain obstruction.

**Proved computationally for the canonical wraparound sweep at `n=9`:**
- mover word
  `S = 0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8`
- state counts `(2,3,3,3,3,3,3,3,2)`

Facts:
- The seeded good cycle exists.
- The wrap step itself does **not** collide with the initial `P0` table entry:
  the on-cycle `P0` contexts are
  - `(0,0,0) -> a` at the initial `P0` move with `a != 0`,
  - `(0,1,1) -> 1`,
  - `(1,1,1) -> 0` at wrap-arrival,
  - `(1,0,0) -> 0`.
- Completion fails immediately because the forced singleton entries already
  create a disjoint off-cycle SCC of size `168`.
- That SCC lies entirely in the binary cube `{0,1}^9`.
- Its ring-defect profile is exactly:
  - `56` states with `2` defects,
  - `112` states with `4` defects.
- Every processor `0..8` appears equally often as an internal mover
  (`42` times each inside the SCC).
- Many SCC nodes have `2` or `3` forced internal moves, so the daemon can stay
  in this recurrent binary subsystem forever.

This is already enough to certify that the double sweep cannot complete to a
valid self-stabilizing system.

**Important non-result:**
- The old `find_shadow_cycle(...)` checker from `verify_lower_bound.py` does
  **not** find a simple shadow cycle in these determined entries.
- So I cannot honestly identify the `168`-node bad SCC with the earlier
  published/verified sweep shadow object yet.
- The right statement is:
  wraparound creates a binary off-cycle recurrent component, shadow-like in
  flavor but currently stronger and more general than the old single-cycle
  shadow witness.

So the no-wrap theorem currently splits as follows:
- interior returns to the bottom are ruled out analytically by the repeated
  all-zero `P0` context lemma above;
- the canonical genuine wraparound sweep is ruled out computationally by an
  explicit binary SCC obstruction;
- identifying that SCC with an existing AA / shadow theorem remains open.

## Exploration 32 (coverage probe): every no-wrap cut-chain survivor except bounce has an early bottom return

I extended `scripts/glb_adjacent_walk_scan.py` with two new reproducible modes:
- `--mode filter-summary`
- `--mode bottom-return-summary`

For `n=9`, mover length `25`, and state counts `(2,3,3,3,3,3,3,3,2)`, the
cut-chain fair adjacent universe has:

- total words: `177859`
- parity-compatible: `16031`
- parity + no-single compatible: `4844`

Breakdown by turnaround count:
- `2`: `1`
- `4`: `7`
- `6`: `121`
- `8`: `484`
- `10`: `1337`
- `12`: `1668`
- `14`: `1011`
- `16`: `215`

The key structural fact is stronger:
- Among these `4844` cut-chain survivors, the **only** word that reaches `8`
  before returning to `0` is the standard bounce.
- Every other survivor, regardless of turnaround count, returns to `0`
  strictly before its first visit to `8`.

So direction A has sharpened considerably. For the whole no-wrap cut-chain
branch, it is enough to prove:

> any parity-compatible, no-single, length-`25` cut-chain mover word with an
> early return to `0` before first reaching `8` is impossible.

That statement would eliminate all `4843` non-bounce no-wrap survivors at once.

Completed seeded-SAT scans now give:
- `2` turns: `1/1` SAT
- `4` turns: `1/7` SAT
- `6` turns: `0/121` SAT
- `8` turns: `0/484` SAT
- `10` turns: `0/1337` SAT
- `12` turns: `0/1668` SAT
- `14` turns: `0/1011` SAT
- `16` turns: `0/215` SAT

Immediate interpretation:
- Lemma 1 is already a full proof for the `4`-turn interior-return family.
- The new coverage fact shows that the same qualitative shape
  (returning to `0` before the first top hit) is in fact universal across the
  entire surviving no-wrap branch.
- So the remaining no-wrap problem is not about many unrelated word types; it
  is a single generalized interior-return lemma.

## Exploration 33 (theorem): all early-bottom-return cut-chain words are impossible except the unique bottom insertion

This is the generalization of Lemma 1.

Let `M = (m_0, ..., m_{L-1})` be an adjacent mover word on the cut chain
`0,1,...,n-1` with:
- `L = 3n-2`,
- `m_0 = 0`,
- `m_{L-1} = n-1`,
- and every step adjacent: `|m_{t+1} - m_t| = 1`.

Let
- `tau = min{ t : m_t = n-1 }` be the first top hit.

Suppose `M` has an **early bottom return**, meaning some `m_r = 0` with
`0 < r < tau`.

Then exactly one of the following holds:

1. `M` is the unique bottom-insertion word

   `0,1,0,1,2,3,...,n-1,n-2,...,1,2,...,n-1`;

2. `last_0 < tau` and `last_1 < tau`,
   where `last_i = max{ t : m_t = i }`.

In case (2), the same repeated-all-zero-context contradiction as Lemma 1
applies, so no seeded good cycle can realize `M`.

### Proof

First, early return forces a lower bound on `tau`.

Before time `tau`, the walk starts at `0`, returns to `0` at least once, and
eventually reaches `n-1` for the first time. Therefore:
- edge `(0,1)` is traversed at least `3` times before `tau`,
- every other edge `(i,i+1)` for `1 <= i <= n-2` is traversed at least `1`
  time before `tau`.

Hence the prefix length satisfies

`tau >= 3 + (n-2) = n+1`.                                    (A)

Now ask whether the suffix after the first top hit can revisit `0`.
From `n-1`, visiting `0` and still ending at `n-1` requires at least
`2(n-1)` more edge traversals. But the suffix length is

`(L-1) - tau = (3n-3) - tau <= 2n-4`

by (A), which is strictly smaller than `2n-2 = 2(n-1)`.
So the suffix cannot revisit `0`. Therefore

`last_0 < tau`.                                              (B)

Next ask whether the suffix after the first top hit can revisit `1`.
From `n-1`, visiting `1` and still ending at `n-1` requires at least
`2(n-2)` edge traversals. So if the suffix revisits `1`, then

`(3n-3) - tau >= 2n-4`,

equivalently

`tau <= n+1`.                                                (C)

Combining (A) and (C), any early-return word with a post-top visit to `1`
must satisfy

`tau = n+1`.

But equality in (A) means the prefix uses exactly:
- `3` traversals of edge `(0,1)`,
- `1` traversal of every edge `(i,i+1)` for `1 <= i <= n-2`.

That forces the prefix uniquely:

`0,1,0,1,2,3,...,n-1`.

Likewise equality in (C) means the suffix from the first top hit uses exactly
`2(n-2)` edges, so to visit `1` and return to `n-1` it must be the unique
minimal down-and-up path

`n-2,n-3,...,1,2,3,...,n-1`.

Therefore the **only** early-return word with any post-top visit to `1` is the
bottom-insertion word

`0,1,0,1,2,3,...,n-1,n-2,...,1,2,...,n-1`.

So for every other early-return word, the suffix never visits `1`, hence

`last_1 < tau`.                                              (D)

Combining (B) and (D), any non-insertion early-return word satisfies
`last_0 < tau` and `last_1 < tau`.

Now let `C_0, ..., C_{L-1}` be a seeded good cycle realizing such a word,
anchored at `C_0 = 0^n`, and choose

`u = max(last_0, last_1) + 1`.

Since `u <= tau`, processor `P_{n-1}` has not moved yet, so `C_u[n-1] = 0`.
Since `u > last_0`, processor `P0` never moves again after time `u-1`, and by
closure to `C_0` its state is `C_u[0] = 0`.
Similarly `u > last_1` implies `C_u[1] = 0`.

Thus the local context at `P0` in configuration `C_u` is exactly `(0,0,0)`.
But `P0` is not the mover at time `u`, so determinism forces `f_0(0,0,0) = 0`.
At time `0`, `P0` *is* the mover on the same context `(0,0,0)`, so
`f_0(0,0,0) != 0`.
Contradiction.

Therefore:
- every early-return cut-chain word other than the bottom insertion is
  analytically impossible;
- the only remaining no-wrap cut-chain words are the standard bounce and the
  unique bottom insertion.

This closes the no-wrap cut-chain branch modulo the already verified fact that
both surviving words are realizable on `(2,3,...,3,2)`.

## Exploration 34 (wrap counts): the ring-adjacent wrap branch is much larger than the cut-chain branch

Important correction:
- the `177859` figure was the size of the **no-wrap cut-chain** universe only.
- If we instead count all fair ring-adjacent cyclic mover words of length `25`
  on `0..8`, anchored to start at mover `0`, then the full universe is much
  larger.

Exact counts at `n=9`:
- fair ring-adjacent cyclic words, length `25`, start `0`, end in `{1,8}`:
  `2163150`
- among them, words that use the wrap edge `{8,0}` internally:
  `1985291`
- parity-compatible on `(2,3,3,3,3,3,3,3,2)`:
  `486021`
- parity + no-single compatible:
  `43660`

So the wrap branch is computationally finite but not tiny.

## Exploration 35 (important correction): not every wrap linearization fails

The statement

> every wraparound word fails

is false if interpreted literally at the level of a linearized mover word.

Example:

`0,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1`

is a wrap linearization, yet it is just the mirror / dihedral version of the
known valid bounce family. `solve_good_cycle_from_movers(...)` finds a seeded
good cycle for it on `(2,3,...,3,2)`.

So the real wrap problem is narrower:
- not “rule out every word with an internal `8<->0` step”;
- instead “rule out genuinely new cyclic classes beyond the already known valid
  bounce / insertion families.”

This is why a pure linearized wrap/no-wrap dichotomy is not the right final
invariant.

## Exploration 36 (bridge to the `492` phenomenon): the double-sweep `168` SCC sits inside a `492`-node binary trap

For the canonical double sweep

`0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8`

on `(2,3,3,3,3,3,3,3,2)`, I computed the full binary forced region determined
by the seeded cycle entries.

Results:
- binary non-good configurations total: `494`
- among them, binary configurations with at least one forced move staying
  outside the good cycle: `492`
- those `492` nodes decompose into exactly three binary SCCs of sizes
  `72`, `168`, and `252`

So the previously observed `168` SCC is only one component of a larger
`492`-node binary recurrent region.

This strongly matches the older “universal binary sweep trap” narrative:
- numerically, the `492` count is exact;
- structurally, it is indeed a binary off-cycle recurrent region.

What I still cannot honestly claim:
- I do **not** yet have the external AA object in this repo as an explicit set
  of configurations, so I cannot certify set-theoretic equality with AA’s trap.
- But for the double sweep itself, the `168` SCC is certainly a subset of a
  `492`-node binary trap induced by the same determined entries.

## Exploration 37 (edge-counts on the ring): parity alone does not kill wrap classes

For any cyclic ring-adjacent mover word of length `25` on the `9`-cycle, let
`y_i` be the number of cyclic traversals of edge `(i,i+1 mod 9)`.

Then:
- `sum_i y_i = 25`
- mover counts satisfy `c_i = (y_{i-1} + y_i)/2`
- integrality of all `c_i` forces all `y_i` to have the same parity
- since the total is odd, every `y_i` must be odd

Adding:
- `c_i >= 2` for all `i` from fairness + no-single
- `c_0, c_8` even from binary parity

still leaves many possibilities.

I enumerated all odd positive edge-count vectors with these necessary
constraints:
- total feasible vectors: `457`
- distribution by wrap-edge count `y_8`:
  - `y_8 = 1`: `215`
  - `y_8 = 3`: `202`
  - `y_8 = 5`: `22`
  - `y_8 = 7`: `18`

So there is no simple parity/multiplicity contradiction that kills wrap words
by itself. The ring edge-count constraints are far too weak.

## Exploration 38 (wrap-family classification): exact wrap counts and edge-vector compression

I added `scripts/glb_ring_family_scan.py` to classify the `n=9`, length-`25`
ring-adjacent wrap branch against the known bounce / insertion families.

For fair ring-adjacent cyclic words on `0..8`, anchored to start at mover `0`,
the exact counts are:
- total fair words: `2163150`
- internal-wrap words: `1985291`
- internal-wrap + parity: `486021`
- internal-wrap + parity + no-single: `43660`

Against the original family classifier (time rotation / reversal of the known
bounce and bottom-insertion words), those `43660` survivors split as:
- family words: `6` total (`3` bounce, `3` bottom insertion)
- unknown rotation classes: `19728`
- unknown dihedral classes: `9864`
- unknown cyclic edge-count vectors: `457`

The strongest computational compression is at the edge-vector level.
I ran one seeded-cycle SAT check per unknown edge vector:
- `457/457` representatives checked
- `0` SAT hits
- `2` first-pass timeouts, both resolved UNSAT at higher timeout

So every tested nonfamily edge-vector representative is locally inconsistent as
a good cycle on `(2,3,3,3,3,3,3,3,2)`.

## Exploration 39 (family edge vector scan): one extra seeded 4-turn class survives

The edge vector of the known bounce / insertion families is exactly
`(3,3,3,3,3,3,3,3,1)`.

Among the `19728` unknown wrap rotation classes, exactly `252` share this edge
vector. I checked all `252` at seeded-cycle level with a `200 ms` timeout and
reran the single timeout at higher budget.

Results:
- `251/252` are UNSAT
- `1/252` is SAT

The unique extra SAT word is

`0,8,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,6,5,4,3,2,1`

Its signed-step pattern has `4` turns, so it is a clean “top insertion”
analog of the known bottom insertion:
- same mover multiplicities `[2,3,3,3,3,3,3,3,2]`
- same cyclic edge vector `(3,3,3,3,3,3,3,3,1)`

Important interpretation:
- this is **not** a time rotation / reversal of the known bottom insertion;
- it is a label-shifted mirror of insertion, so the original family classifier
  was too narrow for the labeled ring problem.

What I checked beyond seeded SAT:
- `solve_cycle_with_smt(...)` does **not** quickly certify or refute completion
  for this top-insertion seed;
- but the same is true for the known bottom insertion under the same short
  completion budget, so this does not currently separate them.

So the wrap branch is now best understood as follows:
- all tested nonfamily edge-vector representatives are UNSAT;
- inside the family edge vector there is exactly one additional seeded 4-turn
  class beyond the previously named bounce / bottom-insertion pair;
- whether that top-insertion seed completes to a full valid system remains open
  in this log.

## Exploration 40 (full cached-rotation exhaustion): the unknown wrap branch is completely resolved at seeded-cycle level

The edge-vector compression is **not** sufficient by itself: the family edge
vector `(3,3,3,3,3,3,3,3,1)` already contains both SAT and UNSAT rotation
classes.

So I ran the honest exhaustive check on the cached unknown wrap rotation-class
 list `scripts/glb_wrap_unknown_rotation_reps_n9.txt`, using
`scripts/glb_ring_family_scan.py --mode cached-rotation-file-sat` in four
disjoint slices:
- `1..5000`
- `5001..10000`
- `10001..15000`
- `15001..19728`

Each slice used:
- first pass timeout `200 ms`
- rerun timeout `2000 ms` for any first-pass `unknown`

Exact results:
- slice `1..5000`: `0` SAT hits, `1` first-pass timeout, rerun `UNSAT`
- slice `5001..10000`: `0` SAT hits, `2` first-pass timeouts, rerun `UNSAT`
- slice `10001..15000`: `0` SAT hits, `4` first-pass timeouts, rerun `UNSAT`
- slice `15001..19728`: `1` SAT hit, `1` first-pass timeout, rerun `UNSAT`

Aggregate total on the full unknown branch:
- `19728` unknown wrap rotation classes checked
- `1` SAT hit total
- `8` first-pass timeouts total
- all `8` rerun to `UNSAT`
- therefore `19727/19728` are UNSAT

The unique SAT hit is exactly the previously identified top-insertion word

`0,8,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,6,5,4,3,2,1`

and no other unknown wrap rotation class survives.

Therefore, at `n=9`, length `25`, seeded good cycles on
`(2,3,3,3,3,3,3,3,2)` are completely classified on the wrap branch:
- bounce family
- bottom insertion family
- top insertion family

No other wrap rotation class admits even a locally consistent seeded good
cycle.

## Exploration 41 (Case 3c structural collapse): the mixed-quaternary gap is exactly one quaternary

For the remaining lower-bound case

- exactly `3` binary processors,
- non-consecutive,
- at least one processor with `m_i >= 4`,
- product `< 4·3^(n-2)`,

the product budget collapses the state multiset completely.

Let the non-binary processors have state counts `q_1, ..., q_{n-3}` with each
`q_j >= 3`, and suppose at least one `q_j >= 4`.

Then

`2^3 · (q_1...q_{n-3}) < 4·3^(n-2)`

so

`q_1...q_{n-3} < (36/8)·3^(n-4) = 4.5·3^(n-4)`.

Relative to the all-ternary baseline `3^(n-3)`, the multiplicative slack is
strictly less than `3/2`. But each replacement `3 -> q_j >= 4` contributes a
factor at least `4/3`, so:
- any `q_j >= 5` is impossible (factor `5/3 > 3/2`);
- two quaternaries are impossible (factor `(4/3)^2 = 16/9 > 3/2`);
- therefore there is exactly one quaternary and all remaining non-binary
  processors are ternary.

So Case 3c reduces to a single architecture family:

`(2,2,2,4,3,3,...,3)` up to cyclic orientation.

At `n=9`, this means:
- unique multiset: `(2,2,2,3,3,3,3,3,4)` with product `7776`;
- total cyclic rotation classes: `56`;
- removing the `6` classes with `3` consecutive binaries leaves exactly `50`
  genuinely non-consecutive Case 3c orientations.

This is the cleanest reduction of the remaining gap so far.

## Exploration 42 (Case 3c seeded-family scan): none of the three known length-25 mover families survive

I tested the exact `n=9` Case 3c family on all `50` non-consecutive rotation
classes against every anchored start-at-`0` linearization of the three valid
length-`25` mover families already classified on the bound architecture:

- bounce: `2` anchored variants,
- bottom insertion: `2` anchored variants,
- top insertion: `2` anchored variants.

Total seeded-cycle checks:
- `50` orientations × `6` mover words = `300` SAT checks.

Results:
- bounce family: `0/100` hits
- bottom insertion family: `0/100` hits
- top insertion family: `0/100` hits
- no solver `unknown`s at `1000 ms`

So the remaining Case 3c obstruction is not “the same mover words as the
optimal one-binary family, but on the wrong architecture.” All six anchored
low-turn length-`25` families are already dead on the exact mixed-quaternary
architecture family.

Combined with the earlier cut-chain closure:
- any adjacent no-wrap length-`25` word is already impossible with `3` binary
  processors by edge-triple + binary parity;
- and now the only explicitly surviving wrap families from the bound case are
  also impossible on Case 3c.

Therefore any `n=9` Case 3c witness, if it exists, must use a genuinely new
wrap mover word rather than any bounce / insertion family linearization.

## Exploration 43 (bounded adjacent SAT for Case 3c): current bottleneck

I added `scripts/glb_case3c_adjacent_sat.py`, a strengthened bounded-cycle SAT
probe that imposes:
- exact cycle length,
- fairness + the no-single-move lemma,
- binary parity,
- local mover succession on the ring (`m_{t+1} in {m_t-1, m_t, m_t+1}` modulo `n`).

This is the right search model for a genuine Case 3c good cycle, but it is not
yet fast enough to classify the `50` orientations:
- even with strict `±1` mover succession and timeout `10000 ms`, representative
  Case 3c orientations still returned `unknown`;
- unconstrained bounded-cycle SAT is even worse and returns `unknown` on all
  `50` orientations at `length = 25`.

So the current computational bottleneck is no longer seeded-cycle SAT on fixed
mover words. It is free mover-word search under real good-cycle constraints.

## Exploration 44 (Case 3c edge-deviation lemma): three binaries force a `{1,1,5}` edge signature

For a cyclic ring-adjacent mover word of length `25` on `n=9`, write `y_i` for
the number of traversals of ring edge `(i,i+1 mod 9)`. As before:

- each `y_i` is odd and positive;
- `sum_i y_i = 25`;
- mover counts are `c_i = (y_{i-1} + y_i)/2`;
- for every binary processor `i`, parity forces `c_i` even.

Now set

`y_i = 3 + 2 z_i`

so each `z_i >= -1` and

`sum_i z_i = -1`.

Binary parity at processor `i` means

`(y_{i-1} + y_i)/2` is even,

equivalently `y_{i-1}` and `y_i` are opposite modulo `4`, equivalently

`z_{i-1}` and `z_i` have opposite parity.

For Case 3c there are `3` binary processors, so around the cyclic parity word
`(z_i mod 2)` there are at least `3` forced parity changes. But the total
number of parity changes on a cycle must be even, so there are at least `4`
parity changes in total. Hence there are at least `2` odd runs, so at least
`2` odd `z_i`.

But `sum_i z_i = -1` is odd, so the number of odd `z_i` must itself be odd.
Therefore there are at least `3` odd `z_i`.

This already implies:
- every Case 3c length-`25` ring-adjacent word differs from the family vector
  `(3,3,3,3,3,3,3,3,1)` in at least `3` edge positions, not just `1`;
- the one-binary family edge signature is combinatorially impossible with
  `3` binaries.

Moreover, minimizing the number of nonzero `z_i` subject to
- `z_i >= -1`,
- `sum_i z_i = -1`,
- at least `3` odd `z_i`,

forces the multiset of nonzero `z_i` to be exactly

`{-1, -1, +1}`.

Translating back to edge counts, the unique minimum-deviation signature is

`{1, 1, 5, 3, 3, 3, 3, 3, 3}`.

I verified computationally that this minimum is attained for every one of the
`50` non-consecutive `n=9` Case 3c rotation classes, and that the same
signature occurs in every class.

So the remaining Case 3c good-cycle problem is now sharply constrained:
- no length-`25` witness can have the one-binary family edge profile;
- any adjacent length-`25` witness must already contain a `5`-traversed edge
  and two `1`-traversed edges.

This is the first combinatorial invariant I have that is genuinely specific to
the three-binary mixed-quaternary case, rather than inherited from the
one-binary bound architecture.

## Exploration 45 (true Case 3c correction + minimum-signature core scan): the pairwise-nonadjacent family has only 20 classes, and the first `{1,1,5}` representatives are all seeded-UNSAT

I found and fixed an important counting issue in the previous Case 3c scan.
The earlier `50` count only excluded **triple**-consecutive binaries; it did
not enforce the actual Case 3c hypothesis that the `3` binaries are pairwise
nonadjacent. For the real `n = 9` Case 3c family

`(2,2,2,3,3,3,3,3,4)`

the counts are:
- `56` rotation classes total,
- `50` classes with no run of `3` consecutive binaries,
- but only `20` classes with pairwise nonadjacent binaries.

So the genuine Case 3c search space is much smaller than I had been using.

I then built `scripts/glb_case3c_core_scan.py` and refactored
`scripts/glb_seeded_unsat_core.py` so I could scan this true Case 3c family
systematically on the minimum edge-deviation branch.

Key setup:
- I restricted to the minimum possible Case 3c edge signature from exploration
  44:

  `{1,1,5,3,3,3,3,3,3}`.

- Among fair ring-adjacent length-`25` words starting at `0`, there are
  exactly `61600` words with this signature that also satisfy the
  no-single-move lemma.
- For each of the `20` true Case 3c orientations, I took the **first**
  signature-compatible word (this depends only on the binary placement, not on
  the quaternary location, since the parity filter only sees the binary sites)
  and ran the seeded good-cycle SAT check plus minimized unsat-core extraction.

Results:
- `20/20` true Case 3c orientations are seeded-UNSAT already on that first
  minimum-signature representative.
- The minimized cores collapse mostly to just two families:
  - `ctx_2_7_11 / move_9_2`, plus nearby variants
    `ctx_2_7_12`, `ctx_2_7_14`, `ctx_2_7_15`;
  - `ctx_0_2_11 / move_11_0`.
- Aggregate minimized-core counts on the `20` classes:
  - `('ctx_2_7_11', 'move_9_2')`: `8`
  - `('ctx_0_2_11', 'move_11_0')`: `4`
  - `('ctx_2_7_12', 'move_9_2')`: `4`
  - `('ctx_2_7_14', 'move_9_2')`: `1`
  - `('ctx_2_7_15', 'move_9_2')`: `1`
  - two runs returned a minimized core with no `ctx_*` label selected, but
    rerunning one of them directly produced the same `ctx_0_2_11 / move_11_0`
    pattern, so I do not think those are genuinely different obstructions.

So the minimum-signature Case 3c obstruction is no longer diffuse. On the true
pairwise-nonadjacent family it already appears to be a small number of repeated
local table conflicts, centered either at:
- the bottom binary `P0`, or
- the binary/near-binary site `P2` in the anchored representatives.

This is the first solid evidence that the mixed-quaternary `3`-binary case may
admit an actual overlap-style theorem rather than needing a brute-force cycle
exhaustion.

## Exploration 46 (minimum-signature normal form): every first compatible true-Case-3c word has the same long prefix

I extracted the first `{1,1,5}`-signature-compatible word for each of the
`7` binary-placement classes (up to rotation) inside the true `n = 9` Case 3c
family. The striking part is that they are almost identical.

Every one of them has the same length-`18` prefix:

`0,8,7,6,5,4,3,2,1,2,1,0,8,7,6,5,4,3`

and then differs only in a short upper-half wiggle:

- `(0,2,4)`: `...,4,3,4,5,6,7,8`
- `(0,2,5)`: `...,4,5,4,5,6,7,8`
- `(0,2,6)`: `...,4,5,6,5,6,7,8`
- `(0,2,7)`: `...,4,5,6,7,6,7,8`
- `(0,3,5)`: `...,4,5,4,5,6,7,8`
- `(0,3,6)`: `...,4,5,6,5,6,7,8`
- `(0,3,7)`: `...,4,5,6,7,6,7,8`

So the minimum-signature branch is not presenting many unrelated candidate
words. It is presenting one rigid template:
- a forced bottom insertion prefix `...,1,2,1,0,...`,
- then a second hesitation in the upper half, whose location shifts with the
  binary gaps.

This lines up very well with the unsat-core scan from exploration 45:
- the `ctx_0_2_11 / move_11_0` family is exactly a bottom-site conflict;
- the `ctx_2_7_u / move_9_2` family is exactly an early interior-site conflict
  propagated from the same prefix.

I think this is the first genuinely proof-shaped normal form for the mixed
three-binary minimum-signature case.

## Exploration 47 (raw duplicate lemma for the shared prefix): the first minimum-signature representatives already force `C_7 = C_11`

I found a much cleaner obstruction than the earlier `ctx_*` summaries.
For the dominant minimum-signature normal form, the contradiction appears
*before* local-context consistency is even considered.

I added `scripts/glb_raw_cycle_core.py` to inspect the raw anchored-cycle
problem consisting only of:
- state domains,
- anchor `C_0 = 0^n`,
- the fixed mover/stay pattern,
- pairwise distinctness of cycle configurations.

For representative true Case 3c first words from the gap types `(1,1,4)`,
`(1,2,3)`, and `(2,2,2)`, the raw unsat core collapses to a single duplicate
requirement:

- minimum-signature words: core contains only `distinct_7_11`.

So the shared prefix

`0,8,7,6,5,4,3,2,1,2,1,0`

already forces the global configurations at times `7` and `11` to coincide.

This is not a vague “too few states” phenomenon; it has a direct combinatorial
proof.

At time `7`:
- movers `0,8,7,6,5,4,3` have already occurred once,
- processors `1` and `2` have not moved yet,
- so `C_7[1] = C_7[2] = 0`.

Between times `7` and `11`, the mover subword is exactly

`2,1,2,1`.

During that subword:
- only processors `1` and `2` move;
- processor `2` makes its last two moves before wrap, so by time `11` it must
  be back at `0`, because it never moves again before the cycle closes to
  `C_0 = 0^n`;
- processor `1` also makes its last two moves before wrap, so by the same
  argument it must also be back at `0` by time `11`;
- every other processor is unchanged across the interval `[7,11]`.

Hence `C_7 = C_11` on every raw realization of that mover word. Distinctness
fails, so the seeded cycle is impossible even before any deterministic local
rule constraints are imposed.

I also extracted one explicit witness by removing `distinct_7_11`:
- for the `(1,2,3)` representative
  `0,8,7,6,5,4,3,2,1,2,1,0,8,7,6,5,4,3,4,5,4,5,6,7,8`,
  a satisfying raw assignment has
  - `C_7 = (1,0,0,1,1,1,2,2,1)`,
  - `C_8 = (1,0,1,1,1,1,2,2,1)`,
  - `C_9 = (1,1,1,1,1,1,2,2,1)`,
  - `C_10 = (1,1,0,1,1,1,2,2,1)`,
  - `C_11 = (1,0,0,1,1,1,2,2,1)`.

So the earlier `ctx_0_2_11 / move_11_0` family was a shadow of a more basic
fact: the prefix forces an actual return of the whole configuration, not just a
repeated local context.

This is the strongest proof-shaped statement I have so far for Case 3c.

## Exploration 48 (first pilot beyond minimum signature): larger signatures also show raw duplicate obstructions, though the exact pair shifts

I sampled larger compatible edge signatures for the `(1,2,3)` gap class by
taking the first compatible mover word in lexicographic order for each sorted
edge signature.

The first few signatures are:
- `{1,1,5,3^6}` with prefix `0,8,7,6,5,4,3,2,1,2,1,0`
- `{1,1,1,7,3^5}` with prefix `0,8,7,6,5,4,3,4,3,2,1,2`
- `{1,1,1,5,5,3^4}` with the same `...,4,3,4,3,2,1,2` prefix
- `{1,1,1,1,9,3^4}` with prefix `0,8,7,6,5,6,5,4,3,4,3,2`

So the exact shared 12-step prefix does **not** persist across all larger
signatures, but the same structural motif does:
- an untouched adjacent pair executes a local return block
  `i, i-1, i, i-1`,
- after which both processors are frozen until wrap.

Raw-core pilot:
- on `0,8,7,6,5,4,3,4,3,2,1,2,1,0,8,7,6,5,6,5,6,5,6,7,8`,
  the raw core singles out `distinct_5_9`;
- on `0,8,7,6,5,6,5,4,3,4,3,2,1,2,1,0,8,7,8,7,8,7,8,7,8`,
  the raw core singles out `distinct_3_15`.

So the larger-signature branch still looks like a raw duplicate-configuration
obstruction rather than a delicate local-table obstruction. What changes is the
location of the first forced return block.

LOAD-BEARING ASSESSMENT:
- exploration 47 is high and likely theorem-grade;
- exploration 48 is still exploratory, but it strongly suggests the right
  general statement is about forced return blocks in the mover word, not about
  the specific minimum `{1,1,5}` signature.

## Exploration 49 (Return Staircase Lemma): the raw duplicate mechanism has a clean general proof

I formalized the right abstraction in `scripts/glb_return_staircase.py`.

### Lemma (Return Staircase Lemma)

Let `M` be any adjacent mover word on a ring of size `n`, and let
`C_0, C_1, ..., C_{L-1}` be a raw anchored cycle realization:
- `C_0 = 0^n`,
- exactly one processor moves at each step according to `M`,
- `C_L = C_0`,
- all cycle configurations are supposed distinct.

Suppose there is an interval `[t,u)` and a contiguous processor segment

`S = {a, a+1, ..., b}`

(indices cyclic if needed) such that:
- only processors in `S` move during `[t,u)`,
- every processor in `S` moves **exactly twice** during `[t,u)`,
- no processor in `S` moves before time `t`,
- no processor in `S` moves at or after time `u`.

Then `C_t = C_u`, so the raw anchored cycle is impossible.

### Proof

For every processor `j` outside `S`, no move occurs in `[t,u)`, so
`C_t[j] = C_u[j]`.

For every processor `j` in `S`:
- since `j` has not moved before time `t`, we have `C_t[j] = 0`;
- since `j` does not move at or after time `u` and the cycle closes to
  `C_0 = 0^n`, we also have `C_u[j] = 0`.

Hence `C_t[j] = C_u[j]` for all processors `j`, so `C_t = C_u`. This
contradicts pairwise distinctness of the good cycle. ∎

This is strictly stronger and cleaner than the earlier `ctx_*` description.
The old local-context cores are consequences of the raw duplicate, not the
primary mechanism.

### Special case: Return Block

If `|S| = 2`, the subword on `[t,u)` is exactly a local return block

`i, i-1, i, i-1`

or its mirror. So the originally sought Return Block Lemma is the
2-processor case of the Return Staircase Lemma.

## Exploration 50 (signature ladder evidence): the first five compatible signatures in every true `n=9` gap class already contain return staircases

I tested the first five compatible edge signatures for each of the four true
gap patterns at `n = 9`:
- `(1,1,4)`,
- `(1,2,3)`,
- `(1,3,2)`,
- `(2,2,2)`.

For each class I enumerated the first compatible fair adjacent word for each
sorted edge signature and ran the staircase detector.

Result:
- all `20/20` sampled words contain a return staircase;
- the first staircase is always one of:
  - `t=7, u=11`, support `(1,2)`, subword `(2,1,2,1)`,
  - `t=5, u=9`, support `(3,4)`, subword `(4,3,4,3)`,
  - `t=3, u=7`, support `(5,6)`, subword `(6,5,6,5)`,
  - or a longer nested staircase such as
    `(6,5,6,5,4,3,4,3,2,1,2,1)`.

So for the first five signatures in every true Case 3c gap class, the same
pattern appears:
- extra upper-half hesitations do **not** destroy the obstruction;
- they only shift the staircase upward.

This is strong evidence that the correct general theorem is:
- every Case 3c mover word contains a return staircase,
- therefore every raw anchored cycle is impossible,
- therefore Case 3c admits no good cycle at all.

What is still open is the universal existence statement for *all* compatible
Case 3c mover words, not the staircase-to-duplicate implication. That latter
implication is now proved cleanly.

## Exploration 51 (correction: staircases are too narrow; return cones are the right object)

I checked the universal existence claim for the **staircase** condition and it
is false.

For the representative true Case 3c class

`(2,3,2,3,3,2,3,3,4)`

I exhaustively scanned two compatible edge signatures:
- minimum signature `{1,1,5,3^6}` with `8064` compatible words,
- next signature `{1,1,1,7,3^5}` with `2816` compatible words.

Using the staircase detector from exploration 49:
- `6192/8064` minimum-signature words have **no** nontrivial staircase,
- `1216/2816` next-signature words have **no** nontrivial staircase.

So the naive global claim “every compatible Case 3c word contains a return
staircase” is false.

However, those apparent counterexamples are still raw-unsat, and their raw
cores reveal a broader structure:
- word
  `0,8,7,6,5,4,3,2,1,2,1,2,3,4,3,2,1,0,8,7,6,5,6,7,8`
  has raw core `distinct_5_17`,
- word
  `0,8,7,6,5,4,3,4,5,4,3,2,1,2,1,2,1,2,1,0,8,7,6,7,8`
  has raw core `distinct_4_11`.

Both are explained by a stronger object that I am now calling a **return cone**.

### Definition (Return Cone)

An interval `[t,u)` in a mover word is a return cone if:
- the movers in `[t,u)` form a contiguous processor segment `S`,
- every processor in `S` is untouched before `t`,
- every processor in `S` is frozen after `u`.

Unlike a staircase, there is **no restriction** on how many times each
processor in `S` moves inside the interval.

### Lemma (Return Cone Lemma)

Any return cone forces `C_t = C_u` in every raw anchored cycle realization.

Proof:
- processors outside `S` do not move in `[t,u)`, so their states agree at
  `t` and `u`;
- processors in `S` have state `0` at time `t` because they have not moved yet;
- processors in `S` also have state `0` at time `u` because they never move
  again before the cycle closes to `C_0 = 0^n`.
Hence all coordinates agree and `C_t = C_u`. ∎

So the Return Staircase Lemma from exploration 49 is just the special case in
which every processor in the cone moves exactly twice.

## Exploration 52 (strong evidence for universal return cones): exhaustive on two full signatures for a representative class

I reran the same exhaustive scan as above, but now with the return-cone
detector.

For the representative class `(2,3,2,3,3,2,3,3,4)`:
- among all `8064` compatible minimum-signature words, **every one** has a
  nontrivial return cone;
- among all `2816` compatible next-signature words, **every one** has a
  nontrivial return cone.

So while staircases are not universal, return cones look like the correct
universal object, at least on the two largest low-deviation branches I have
checked exhaustively.

Concrete counterexample-to-staircase words above both exhibit explicit cones:
- `t=5, u=17`, support `(1,2,3,4)`,
- `t=4, u=11`, support `(3,4,5)`.

This is the best current formulation of the Case 3c mechanism:
- compatible words may avoid strict 2-move staircases,
- but they still seem forced to contain a contiguous untouched-to-frozen cone,
- and any such cone kills the raw anchored cycle immediately.

## Exploration 53 (two-singleton-edge theorem): lengths `25` and `27` are analytically dead for true Case 3c

I now have a clean graph-theoretic theorem behind the cone mechanism.

### Theorem

Let `M` be a cyclic adjacent mover word on the ring `C_n`. If there are at
least two distinct ring edges that are traversed exactly once by `M`, then `M`
has a nontrivial return cone on the cyclic time circle.

### Proof sketch

Take two singly traversed edges `e_a`, `e_b`. Removing them disconnects the
ring into two contiguous processor segments `S` and `T`.

Because each of `e_a`, `e_b` is crossed exactly once, the walk can enter `S`
only once and leave `S` only once. Therefore the set of times at which the
mover lies in `S` is a single cyclic interval on the time circle. The same is
true for `T`.

At the start of the `S` interval, no processor of `S` has been visited yet
within that cyclic interval; at the end, no processor of `S` is visited again
before the interval closes. So `S` is a return cone in the cyclic sense. Since
both `S` and `T` are proper segments, at least one of them is nontrivial. ∎

Combined with the Return Cone Lemma from exploration 51, this kills any raw
cycle word with at least two singleton edges.

### Case 3c consequence at `n = 9`

For every true pairwise-nonadjacent Case 3c gap class, I checked the feasible
edge-vector conditions:
- at length `25`, every feasible vector has at least `2` edges with count `1`;
- at length `27`, every feasible vector also has at least `2` edges with count
  `1`;
- length `29` is the first place where one-singleton vectors appear.

So true Case 3c good-cycle candidates of lengths `25` and `27` are now
analytically impossible:
- binary-parity / no-single feasibility implies at least two singleton edges,
- two singleton edges imply a nontrivial return cone,
- a nontrivial return cone implies a duplicate configuration,
- therefore no raw anchored cycle exists.

This is the first completely clean closure of a nontrivial length range in the
mixed three-binary case.

## Exploration 54 (binary-bounce context lemma): a direct local obstruction for one-singleton branches

The right local object beyond return cones is now clear.

### Lemma (Binary-Bounce Context)

Fix a processor `p`. Suppose there are times `t < u` such that:
- `p` is not the mover at time `t`,
- `p` is the mover at time `u`,
- `p` does not move in `[t,u)`,
- one neighbor `q` of `p` does not move in `[t,u)`,
- the other neighbor `b` of `p` is binary and moves exactly twice in `[t,u)`.

Then no seeded good cycle can realize that mover word.

### Proof

At times `t` and `u`, processor `p` sees the same local context:
- `p` itself has the same state because it does not move in `[t,u)`,
- `q` has the same state because it does not move in `[t,u)`,
- `b` has the same state because it is binary and moves exactly twice in
  `[t,u)`.

But the required outputs differ:
- at time `t`, `p` is a nonmover, so its output equals its current state;
- at time `u`, `p` is the mover, so its output differs from its current state.

So the same `(L,S,R)` context would force two different outputs, contradicting
determinism. ∎

I implemented a detector for this pattern in
`scripts/glb_return_staircase.py` under `--mode binary-bounce`.

Concrete checks:
- the raw-sat / locally-unsat word
  `0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,2,3,2,3,4,5,6,5,6,7,8`
  has witnesses
  - `t=16, u=19, p=3, b=2, q=4`, subword `(2,1,2)`,
  - `t=13, u=24, p=6, b=5, q=7`, subword `(5,4,3,2,1,2,3,2,3,4,5)`;
- the earlier endpoint-family word
  `0,8,7,6,5,4,3,2,1,2,3,2,1,0,8,7,6,5,4,3,2,3,4,5,6,5,6,7,8`
  has direct witnesses
  - `t=9, u=12, p=1, b=2, q=0`, subword `(2,3,2)`,
  - `t=7, u=10, p=3, b=2, q=4`, subword `(2,1,2)`.

So the endpoint `ctx_0_*` minimal cores were not the real obstruction; the
same words already contain direct binary-bounce witnesses on processors
adjacent to binaries.

## Exploration 55 (endpoint-core peeling): `ctx_0_*` stacks are superficial

For the representative one-singleton word
`0,8,7,6,5,4,3,2,1,2,3,2,1,0,8,7,6,5,4,3,2,3,4,5,6,5,6,7,8`,
the minimal core was initially `ctx_0_2_13 / move_13_0`.

I then iteratively removed the exposed `ctx_*` label and recomputed a minimized
unsat core. The chain was:
- `ctx_0_2_13`,
- `ctx_0_3_13`,
- `ctx_0_4_13`,
- `ctx_0_5_13`,
- `ctx_0_6_13`,
- `ctx_0_7_13`,
- `ctx_0_8_13`,

after which the solver exposed interior cores:
- `ctx_3_7_10`,
- `ctx_4_5_24`,
- `ctx_6_17_24`,
- then higher variants such as `ctx_7_17_27`, `ctx_7_18_27`, ...

So the endpoint-family cores are peelable. Once they are stripped away, the
underlying obstruction is exactly the binary-bounce mechanism on processors
adjacent to binary sites.

The same phenomenon occurs on later endpoint-stack words:
- for the `u=15` family, peeling `ctx_0_2_15, ..., ctx_0_8_15` exposes
  `ctx_1_10_14`,
- for the `u=17` family, peeling `ctx_0_2_17, ..., ctx_0_8_17` exposes
  `ctx_1_10_16`.

This is strong evidence that `ctx_0_*` is a cosmetic minimization artifact, not
the actual Case 3c mechanism.

## Exploration 56 (full `L=29` singleton closure on the representative class): every one-singleton branch is analytically dead

I wrote `scripts/glb_case3c_vector_scan.py` to enumerate feasible edge vectors
for a fixed state-count class and test the one-singleton branches directly.

For the representative true Case 3c class
`(2,3,2,3,3,2,3,3,4)` at mover length `29`:
- there are `1452` feasible edge vectors total,
- singleton histogram is `{1: 24, 2: 348, 3: 810, 4: 270}`.

The two-singleton theorem from exploration 53 already kills the `2/3/4`
singleton branches. So only the `24` one-singleton vectors remain.

I then exhaustively checked every word on every one-singleton vector using the
binary-bounce detector:
- vector `(1,3,5,3,3,5,3,3,3)`: `2592/2592` words have a binary-bounce witness,
- vector `(1,3,5,3,5,3,3,3,3)`: `2592/2592`,
- vector `(1,5,3,3,3,5,3,3,3)`: `1728/1728`,
- ...
- vector `(5,5,3,3,3,1,3,3,3)`: `6912/6912`.

In fact all `24/24` one-singleton vectors are fully closed this way:
every word on every branch has a direct binary-bounce witness.

Therefore mover length `29` is analytically impossible for the representative
true Case 3c class `(2,3,2,3,3,2,3,3,4)`.

This is the first complete analytic closure of the `L=29` frontier in any true
Case 3c class.

## Exploration 57 (`L=29` full true-class closure at `n=9`): every one-singleton branch dies in every gap pattern

True pairwise-nonadjacent `n=9` Case 3c has only four gap-pattern
representatives:
- `(2,3,2,3,2,3,3,3,4)` with gap pattern `(1,1,4)`,
- `(2,3,2,3,3,2,3,3,4)` with gap pattern `(1,2,3)`,
- `(2,3,2,3,3,3,2,3,4)` with gap pattern `(1,3,2)`,
- `(2,3,3,2,3,3,2,3,4)` with gap pattern `(2,2,2)`.

For each of those four representatives at mover length `29`, I used
`scripts/glb_case3c_vector_scan.py --mode scan-singletons` to exhaust every
one-singleton edge vector and every Eulerian word on that vector.

Results:
- gap `(1,1,4)`: `24/24` singleton vectors, all words have a binary-bounce
  witness;
- gap `(1,2,3)`: `24/24` singleton vectors, all words have a binary-bounce
  witness;
- gap `(1,3,2)`: `24/24` singleton vectors, all words have a binary-bounce
  witness;
- gap `(2,2,2)`: `24/24` singleton vectors, all words have a binary-bounce
  witness.

So at length `29`, every true `n=9` Case 3c class is now analytically dead:
- `2/3/4` singleton vectors are killed by the two-singleton-edge theorem
  (exploration 53),
- `1` singleton vectors are killed by exhaustive binary-bounce detection
  (explorations 54 and 56, now lifted to all four gap patterns).

Therefore true `n=9` Case 3c is impossible at mover lengths
`25`, `27`, and `29`.

This pushes the open frontier to length `31`.

## Exploration 58 (`L=31` representative-class closure): the singleton/binary-bounce mechanism survives one more length level

I extended the same vector analysis to mover length `31` for the
representative true Case 3c class `(2,3,2,3,3,2,3,3,4)`.

Using `scripts/glb_case3c_vector_scan.py`:
- feasible edge vectors at length `31`: `2964`,
- singleton histogram: `{1: 96, 2: 948, 3: 1530, 4: 390}`.

So again there are no zero-singleton vectors. That means:
- `2/3/4` singleton branches are still dead by the two-singleton-edge theorem,
- only the `96` one-singleton vectors remain.

I then exhausted all `96/96` one-singleton vectors for this class. Every
Eulerian word on every such vector had a binary-bounce witness. The branch
sizes were substantially larger than at `L=29`, ranging from `3888` words up to
`15552` words, but the conclusion stayed uniform:
- every scanned branch reported `all_binary_bounce=True`,
- no counterexample word was found.

Therefore mover length `31` is analytically impossible for the representative
true Case 3c class `(2,3,2,3,3,2,3,3,4)`.

So for that class, true Case 3c is now dead at lengths
`25`, `27`, `29`, and `31`.

The next unexplained frontier is length `33`, where zero-singleton edge vectors
first appear.

## Exploration 59 (`L=33` zero-singleton reconnaissance): the first zero-singleton branch is almost entirely binary-bounce

For the representative class `(2,3,2,3,3,2,3,3,4)`, length `33` is the first
place where zero-singleton edge vectors occur.

Using `scripts/glb_case3c_vector_scan.py` indirectly through a direct edge-vector
enumeration, I found:
- feasible vectors at length `33`: `5654`,
- singleton histogram: `{0: 8, 1: 312, 2: 1974, 3: 2730, 4: 630}`,
- so there are only `8` zero-singleton vectors to worry about in the
  representative class.

I then took the first zero-singleton vector
`(3,3,5,3,3,5,3,3,5)` and exhaustively scanned all `46512` Eulerian words on
that branch against the current analytic detectors:
- proper return cone,
- binary-bounce context.

Result:
- `46503/46512` words have a binary-bounce witness,
- `0/46512` words have a proper return cone,
- exactly `9/46512` words survive both detectors.

So even in the first true zero-singleton regime, binary-bounce is still doing
almost all the work.

The first surviving exception is
`0,1,2,3,2,3,4,5,6,5,6,7,8,0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8,0,8`.

That word is:
- raw-sat,
- cone-free,
- binary-bounce-free,
- but locally unsat, with minimized seeded core
  `ctx_1_1_25` together with move labels `move_31_0`, `move_1_1`, `move_0_0`.

So the `L=33` frontier is not an explosion of new behavior. At least on the
first zero-singleton branch, it compresses to a tiny exceptional set of `9`
locally inconsistent words.

## Exploration 60 (`L=31` full true-class closure at `n=9`): every gap pattern is dead through length `31`

I finished the `L=31` singleton-vector scans on the other three true Case 3c
gap-pattern representatives:
- `(2,3,2,3,2,3,3,3,4)` for gap `(1,1,4)`,
- `(2,3,2,3,3,3,2,3,4)` for gap `(1,3,2)`,
- `(2,3,3,2,3,3,2,3,4)` for gap `(2,2,2)`.

Each of those classes has:
- `96` one-singleton vectors at length `31`,
- and the scan reported `all_binary_bounce=True` on all `96/96` vectors.

Combined with exploration 58 for the representative gap `(1,2,3)`, this gives:
- every true `n=9` Case 3c gap pattern is analytically impossible at length
  `31`.

So true `n=9` Case 3c is now dead at all lengths
`25`, `27`, `29`, and `31`.

The open frontier at `n=9` has therefore moved to:
- zero-singleton vectors at length `33`,
- and then whatever happens beyond that regime.

## Exploration 61 (the `L=33` exceptional set collapses to one core family)

I extracted the full exceptional set from exploration 59: the `9` words on the
zero-singleton branch `(3,3,5,3,3,5,3,3,5)` that have neither a proper return
cone nor a binary-bounce witness.

I then ran minimized seeded unsat cores on all `9/9` exception words.

Outcome:
- every one of the `9` words is still locally unsat,
- every one collapses to the same context family at processor `1`,
  namely `ctx_1_1_u` with `u in {23,25}`.

More explicitly:
- `6/9` words give `ctx_1_1_25`,
- `3/9` words give `ctx_1_1_23`.

The move-label details vary slightly, but the obstruction location does not:
it is always the same processor-`1` context repeating against the initial
bottom move structure.

So the first zero-singleton branch is already compressed to a single proof
target:
- explain the `ctx_1_1_{23,25}` obstruction analytically,
- then eliminate all `9` survivors at once.

This is much better than a generic zero-singleton search: the branch is not
producing many qualitatively different failures.

## Exploration 62 (the `9` exceptions form a `3 x 3` normal form): one lower wiggle and one upper wiggle across three forward sweeps

The `9` exceptional words from exploration 61 are not arbitrary. They have a
very clean combinatorial description.

Let
- `S = 0,1,2,3,4,5,6,7,8`
  be the plain forward sweep,
- `L = 0,1,2,3,2,3,4,5,6,7,8`
  be the forward sweep with the lower `2323` wiggle,
- `U = 0,1,2,3,4,5,6,5,6,7,8`
  be the forward sweep with the upper `656` wiggle.

Then the `9` exceptional words are exactly the `3 x 3` choices of:
- which of the three forward sweeps is replaced by `L`,
- which of the three forward sweeps is replaced by `U`,
followed by the closing `0,8`.

Examples:
- `L,U,S,0,8`,
- `L,S,U,0,8`,
- `S,L,U,0,8`,
- ...
- `S,U,L,0,8`.

So the first zero-singleton frontier is already normal-form rigid:
- base skeleton: three forward sweeps,
- one lower wiggle on edge `2-3`,
- one upper wiggle on edge `5-6`,
- and nothing else.

Combined with exploration 61, this means the open `L=33` subproblem is now:
- prove that every member of this `3 x 3` family forces the same
  `ctx_1_1_{23,25}`-type contradiction.

## Exploration 63 (the exceptional-family core is exactly the initial `P1` context): `ctx_1_1_{23,25}` means `(1,0,0)`

I checked raw anchored-cycle realizations on representative members of the
exceptional `3 x 3` family.

For both the `u=23` and `u=25` subfamilies, the core context at processor `1`
is literally the initial context:
- at time `1`, processor `1` sees `(P0,P1,P2) = (1,0,0)` and is the mover,
- at time `u in {23,25}`, processor `1` again sees `(P0,P1,P2) = (1,0,0)` and
  is a nonmover.

Concrete realizations:
- for
  `0,1,2,3,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,5,6,7,8,0,8`,
  the repeated time is `u=23`,
- for
  `0,1,2,3,2,3,4,5,6,5,6,7,8,0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8,0,8`,
  the repeated time is `u=25`.

In both cases:
- output at time `1` is `1` because processor `1` moves,
- output at time `u` is `0` because processor `1` stays.

So the `L=33` exceptional family has now collapsed to a completely explicit
proof target:
- show that every `3 x 3` exceptional word forces processor `1` to revisit its
  initial local context `(1,0,0)` at time `23` or `25` as a nonmover.

That is a much sharper analytical statement than the original generic
`ctx_1_1_u` core label.

## Exploration 64 (complete representative zero-vector census at `L=33`): the frontier splits into five tiny families

I finished the zero-singleton vector census for the representative class
`(2,3,2,3,3,2,3,3,4)` at mover length `33`.

The `8` zero-singleton vectors have exception counts (after removing all words
with a proper return cone or a binary-bounce witness):

1. `(3,3,5,3,3,5,3,3,5)` -> `9` exceptions
2. `(3,3,5,3,5,3,3,3,5)` -> `0`
3. `(3,5,3,3,3,5,3,3,5)` -> `0`
4. `(3,5,3,3,5,3,3,3,5)` -> `36`
5. `(5,3,5,3,3,5,3,3,3)` -> `36`
6. `(5,3,5,3,5,3,3,3,3)` -> `0`
7. `(5,5,3,3,3,5,3,3,3)` -> `3`
8. `(5,5,3,3,5,3,3,3,3)` -> `12`

So the entire zero-singleton frontier for the representative class compresses to
just `60` exceptional words across all `8` vectors.

These `60` words already split into distinct mechanism types:

- vector `1`:
  - `9` seeded-unsat words,
  - all in the `3 x 3` family from explorations 61-63,
  - all collapse to `ctx_1_1_{23,25}`.

- vectors `2,3,6`:
  - `0` exceptions,
  - every word is already killed by binary-bounce.

- vector `4`:
  - `36` exceptions,
  - the first sampled exception is seeded-sat but completion-dead,
  - propagation produces a bad SCC of size `484`.

- vector `5`:
  - `36` exceptions,
  - the first sampled exception is also seeded-sat but completion-dead,
  - again with a propagated bad SCC of size `484`.

- vector `7`:
  - `3` exceptions,
  - the first sampled exception is seeded-unsat with core `ctx_3_3_25`.

- vector `8`:
  - `12` exceptions,
  - the first sampled exception is seeded-unsat with a small mixed context core
    involving `ctx_2_28_31`, `ctx_2_0_27`, and `ctx_0_0_30`.

So the representative `L=33` frontier is now finite and typed:
- one `9`-word local family at `P1`,
- two `36`-word completion families,
- one `3`-word local family at `P3`,
- one `12`-word mixed local family near `P0/P2`,
- and three zero vectors with no survivors at all.

## Exploration 65 (exact `L=33` representative classification): the `60` exceptions split into `seed-unsat` and completion bands with no unknowns

I replaced the earlier sampled statements by an exact branch-by-branch
classification using `scripts/glb_case3c_exception_classify.py`.

For the representative class `(2,3,2,3,3,2,3,3,4)` at mover length `33`:

- vector `(3,5,3,3,5,3,3,3,5)`:
  - `36` exceptions total,
  - `24` are completion-dead with propagated SCC sizes
    `{476:4, 480:4, 484:8, 492:4, 496:4}`,
  - `12` are seeded-unsat with endpoint-heavy cores
    such as `ctx_0_0_22`, `ctx_0_2_11`, `ctx_0_4_13`, `ctx_1_10_30`,
    `ctx_1_19_32`.

- vector `(5,3,5,3,3,5,3,3,3)`:
  - `36` exceptions total,
  - `12` are completion-dead with propagated SCC sizes
    `{480:4, 484:4, 492:4}`,
  - `24` are seeded-unsat, with cores spread across processors `1,2,4`
    (`ctx_1_1_16`, `ctx_1_3_23`, `ctx_2_6_15`, `ctx_4_10_19`, ...).

- vector `(5,5,3,3,3,5,3,3,3)`:
  - `3` exceptions total,
  - all `3` are seeded-unsat,
  - cores are exactly `ctx_3_3_25` twice and `ctx_3_3_23` once.

- vector `(5,5,3,3,5,3,3,3,3)`:
  - `12` exceptions total,
  - all `12` are seeded-unsat,
  - the core distribution is
    `ctx_8_1_25` five times,
    `ctx_8_1_23` twice,
    and one each of
    `ctx_0_0_30`, `ctx_8_1_21`, `ctx_2_28_31`, `ctx_2_0_27`, `ctx_2_8_27`.

So there are no solver-unknown remnants in the representative `L=33`
zero-singleton frontier. Every surviving word is now classified as either:
- locally inconsistent with an explicit repeated-context core, or
- locally realizable but completion-dead with a finite propagated SCC.

## Exploration 66 (`L=33` zero-singleton universality across true gap classes): every true Case 3c class has exactly `8` zero vectors

I added a `zero-vectors` mode to `scripts/glb_case3c_vector_scan.py` and
compared all four true `n=9` Case 3c gap-pattern representatives at mover
length `33`.

Results:
- representative gap `(1,2,3)`:
  `8` zero vectors
  ```
  (3,3,5,3,3,5,3,3,5)
  (3,3,5,3,5,3,3,3,5)
  (3,5,3,3,3,5,3,3,5)
  (3,5,3,3,5,3,3,3,5)
  (5,3,5,3,3,5,3,3,3)
  (5,3,5,3,5,3,3,3,3)
  (5,5,3,3,3,5,3,3,3)
  (5,5,3,3,5,3,3,3,3)
  ```

- gap `(1,1,4)`:
  `8` zero vectors
  ```
  (3,3,5,3,5,3,3,3,5)
  (3,3,5,5,3,3,3,3,5)
  (3,5,3,3,5,3,3,3,5)
  (3,5,3,5,3,3,3,3,5)
  (5,3,5,3,5,3,3,3,3)
  (5,3,5,5,3,3,3,3,3)
  (5,5,3,3,5,3,3,3,3)
  (5,5,3,5,3,3,3,3,3)
  ```

- gap `(1,3,2)`:
  `8` zero vectors
  ```
  (3,3,5,3,3,3,5,3,5)
  (3,3,5,3,3,5,3,3,5)
  (3,5,3,3,3,3,5,3,5)
  (3,5,3,3,3,5,3,3,5)
  (5,3,5,3,3,3,5,3,3)
  (5,3,5,3,3,5,3,3,3)
  (5,5,3,3,3,3,5,3,3)
  (5,5,3,3,3,5,3,3,3)
  ```

- gap `(2,2,2)`:
  `8` zero vectors
  ```
  (3,3,3,5,3,3,5,3,5)
  (3,3,3,5,3,5,3,3,5)
  (3,3,5,3,3,3,5,3,5)
  (3,3,5,3,3,5,3,3,5)
  (5,3,3,5,3,3,5,3,3)
  (5,3,3,5,3,5,3,3,3)
  (5,3,5,3,3,3,5,3,3)
  (5,3,5,3,3,5,3,3,3)
  ```

So the `L=33` phenomenon is not representative-specific noise. Across every
true gap pattern:
- there are always exactly `312` one-singleton vectors and `8` zero-singleton
  vectors,
- the zero vectors are always the same "three 5's placed around a 3-skeleton"
  combinatorics, just shifted by the binary-gap pattern.

This makes the next theorem target much sharper:
- classify those `8` shifted zero-vector branches once and for all,
- then push the same mechanism to longer odd lengths.

## Exploration 67 (first zero-vector branch is universal across all true gap classes): always `9` survivors, same `ctx_1_1_25` seed core

I tested the first zero-singleton branch in the three non-representative true
`n=9` Case 3c gap classes using `scripts/glb_case3c_vector_scan.py --mode scan-zero`.

Results:
- gap `(1,1,4)` with state counts `(2,3,2,3,2,3,3,3,4)` and first zero vector
  `(3,3,5,3,5,3,3,3,5)`:
  - `46512` words,
  - `9` exceptions after return-cone and binary-bounce filtering.

- gap `(1,3,2)` with state counts `(2,3,2,3,3,3,2,3,4)` and first zero vector
  `(3,3,5,3,3,3,5,3,5)`:
  - `46512` words,
  - `9` exceptions.

- gap `(2,2,2)` with state counts `(2,3,3,2,3,3,2,3,4)` and first zero vector
  `(3,3,3,5,3,3,5,3,5)`:
  - `46512` words,
  - `9` exceptions.

So the representative `9`-survivor phenomenon is not accidental. It persists
in every true gap pattern, with the zero vector simply shifted along the ring.

I then checked the first survivor in each of those three branches with
`scripts/glb_seeded_unsat_core.py`. In all three cases the minimized seeded
core is again exactly:
- `ctx_1_1_25`,
- together with `move_31_0`, `move_1_1`, `move_0_0`.

So the first zero-vector branch seems genuinely universal:
- same survivor count (`9`),
- same anchoring at processor `1`,
- same repeated-initial-context mechanism `ctx_1_1_25`,
- only the location of the interior wiggles shifts with the binary-gap pattern.

This is the strongest evidence so far that the `L=33` frontier can be killed by
a small library of shifted local lemmas, rather than by a separate search for
each gap class.

## Exploration 68 (`L=33` branch normal forms): the representative exceptional families are tiny block languages

I added `scripts/glb_block_signature.py` to summarize anchored mover words by
their `0`-delimited sweep blocks and local wiggles.

For the representative true Case 3c class `(2,3,2,3,3,2,3,3,4)`, the
representative `L=33` exceptional branches now have explicit block normal
forms:

- vector `(3,3,5,3,3,5,3,3,5)` (the `9`-word local family):
  - every exception is exactly three forward sweeps with
    one lower `232` wiggle, one upper `565` wiggle, and final tail `0,8`,
  - i.e. the old `3 x 3` family from explorations 61-63.

- vector `(5,5,3,3,3,5,3,3,3)` (the `3`-word local family):
  - the `3` exceptions are exactly
    `F[] | F[] | F[565] | F[121]`,
    with the `565` wiggle placed in one of the three forward sweeps.

- vector `(5,5,3,3,5,3,3,3,3)` (the `12`-word local family):
  - the `12` exceptions are reverse-oriented:
    `R[] | R[] | R[454] | F[121]`,
    together with the obvious shifts of the `454` block and final `121` tail.

- vector `(3,5,3,3,5,3,3,3,5)` (the `36`-word completion family):
  - first exception signature:
    `R[] | R[] | R[565,121] | R[]`.

- vector `(5,3,5,3,3,5,3,3,3)` (the other `36`-word completion family):
  - first exception signature:
    `F[010] | F[232,454] | F[] | F[]`.

So the representative `L=33` frontier is not a large amorphous set. It is a
small union of block languages over monotone sweeps plus 1-2 local wiggles.

Verified with:
- `python3 -m py_compile scripts/glb_block_signature.py`
- `python3 scripts/glb_block_signature.py --movers ...`
- `python3 scripts/glb_case3c_vector_scan.py --mode dump-zero-exceptions ...`

## Exploration 69 (`L=33` universality strengthens): the first zero-vector branch is universal up to shifted wiggles

I finished the exact exception classification for the first zero-vector branch
in the remaining true gap classes.

Results:
- gap `(1,1,4)`:
  - `9` exceptions,
  - all `9` seeded-unsat,
  - `ctx_counter = {ctx_1_1_23: 3, ctx_1_1_25: 5, ctx_4_17_26: 1}`.

- gap `(1,3,2)`:
  - `9` exceptions,
  - all `9` seeded-unsat,
  - `ctx_counter = {ctx_1_1_23: 3, ctx_1_1_25: 5, ctx_1_1_26: 1}`.

- gap `(2,2,2)`:
  - `9` exceptions,
  - all `9` seeded-unsat,
  - `ctx_counter = {ctx_1_1_21: 1, ctx_1_1_23: 4, ctx_1_1_25: 4}`.

So the first zero-vector branch is now universal in the strongest honest sense:
- always `9` exceptions,
- always local/seeded-unsat,
- always dominated by the same processor-`1` repeated-context family
  `ctx_1_1_u`,
- only the repeat time `u` shifts slightly with the gap pattern.

The explicit words show the same block picture as the representative branch:
three forward sweeps, one lower wiggle, one upper wiggle, and final tail `0,8`,
with the wiggle edges shifted by the binary-gap pattern.

Verified with:
- `python3 -u scripts/glb_case3c_exception_classify.py --state-counts 2,3,2,3,3,3,2,3,4 --edge-counts 3,3,5,3,3,3,5,3,5`
- `python3 -u scripts/glb_case3c_exception_classify.py --state-counts 2,3,3,2,3,3,2,3,4 --edge-counts 3,3,3,5,3,3,5,3,5`

## Exploration 70 (`L=33` branch counts are matching across gap classes): the representative zero-vector census is becoming universal

The running `scan-zero` jobs on the three non-representative gap classes have
already matched the representative branch counts on the first six zero vectors:

- branch `1`: `9` exceptions,
- branch `2`: `0`,
- branch `3`: `0`,
- branch `4`: `36`,
- branch `5`: `36`,
- branch `6`: `0`.

The first-exception words on branches `4` and `5` also match the same block
types as in the representative class, just gap-shifted:
- reverse-oriented branch `4` has a long reverse sweep carrying two local
  wiggles,
- forward-oriented branch `5` has an initial `010` block and one forward sweep
  carrying two wiggles.

So the emerging picture is that the full `L=33` zero-vector frontier may be
completely universal across all four true gap classes:
- same branch counts,
- same local/completion split,
- same small block languages,
- only shifted by the binary-gap pattern.

That is exactly the kind of rigidity needed before trying to push a real
theorem beyond `L=33`.

## Exploration 71 (`L=35` first look): the zero-vector regime persists but stays in the “three sweeps plus wiggles” world

For the representative class `(2,3,2,3,3,2,3,3,4)` at mover length `35`:
- there are `24` zero vectors.

These are exactly the vectors with four `5`s and five `3`s, e.g.
`(3,3,5,3,3,5,3,5,5)`, `(3,5,3,3,5,3,5,3,5)`, ..., `(5,5,3,5,5,3,3,3,3)`.

So the length-`35` frontier is still in the same coarse combinatorial regime:
- base winding `3`,
- monotone sweeps around the ring,
- and a small number of extra local wiggles.

The open question is no longer qualitative. It is whether the `L=33`
local/completion obstructions extend cleanly once a fourth wiggle is added.

## Exploration 72 (support-superset theorem for zero vectors): every higher zero-vector support contains an `L=33` base support

There is a clean combinatorial theorem behind the growing zero-vector counts.

Fix a true `n=9` Case 3c class and a zero-singleton edge vector `y` at any odd
length `L >= 33`. Write
- `y_i = 3 + 2 z_i`,
with `z_i >= 0`.

For a binary processor `b`, the mover count is
`c_b = (y_{b-1} + y_b)/2 = 3 + z_{b-1} + z_b`.
Binary parity forces `c_b` to be even, so
- `z_{b-1} + z_b` is odd.

Therefore, for each binary site:
- the support `supp(z) = { i : z_i > 0 }` must meet the adjacent edge pair
  `{b-1, b}`.

In true Case 3c there are exactly three pairwise disjoint binary-adjacent edge
pairs. So:
- any zero-vector support must choose at least one edge from each of the three
  pairs,
- the minimal supports are exactly the `2^3 = 8` choices of one edge from each
  pair,
- those `8` minimal supports are exactly the `L=33` zero-vector supports.

I checked this computationally for all four true gap classes at lengths
`35` and `37`, and for the representative class also at `39`:
- every zero-vector support at those lengths contains one of the `8`
  `L=33` supports as a subset.

Concrete checks:
- all four true classes:
  - `L=35`: `subset_ok = True`,
  - `L=37`: `subset_ok = True`;
- representative class:
  - `L=39`: `subset_ok = True`.

So the higher-length zero-vector frontier is not producing fundamentally new
supports. It is only adding extra support on top of one of the `L=33` base
patterns.

This sharply reframes the remaining problem:
- prove that the Case 3c obstructions for an `L=33` base support are monotone
  under adding extra support/wiggles.

Verified with:
- `python3 -c \"from scripts.glb_case3c_vector_scan import feasible_edge_vectors ...\"`

## Exploration 73 (`L=33` full zero-vector count matrix): three gap classes share the same branch counts; the equal-gap class degenerates

The remaining `scan-zero` and exact-branch classifier jobs now give a complete
count picture for the `L=33` zero-vector frontier across all four true gap
classes.

Using the zero-vector ordering produced by
`scripts/glb_case3c_vector_scan.py --mode zero-vectors`:

- gap `(1,2,3)` representative:
  - counts = `[9, 0, 0, 36, 36, 0, 3, 12]`

- gap `(1,1,4)`:
  - counts = `[9, 0, 0, 36, 36, 0, 3, 12]`

- gap `(1,3,2)`:
  - counts = `[9, 0, 0, 36, 36, 0, 3, 12]`

- gap `(2,2,2)`:
  - counts = `[9, 0, 0, 36, 36, 0, 0, 9]`

So the first three true gap classes are literally identical at the zero-vector
count level. The equal-gap class `(2,2,2)` is the only special case:
- its seventh branch disappears,
- its eighth branch shrinks from `12` to `9`.

Exact local classifications now in hand:
- `(1,3,2)` branch `7` (`(5,5,3,3,3,3,5,3,3)`) has
  `3` seeded-unsat words with
  `ctx_counter = {ctx_3_3_23: 1, ctx_3_3_25: 2}`;
- `(2,2,2)` branch `8` (`(5,3,5,3,3,5,3,3,3)`) has
  `9` seeded-unsat words with
  `ctx_counter = {ctx_8_1_21: 1, ctx_8_1_23: 4, ctx_8_1_25: 4}`.

So the entire local part of the `L=33` frontier is now concentrated into a
small library of shifted repeated-context families at processors `1`, `3`,
and `8`.

## Exploration 74 (the `36`-word branches are exact block-placement languages): one isolated tail block plus two wiggle blocks

I used `scripts/glb_block_signature.py` to classify the two representative
`36`-word branches by block language rather than by raw words.

### Branch `(3,5,3,3,5,3,3,3,5)`

There are exactly `36` signatures, each occurring once. They are precisely the
placements of:
- an isolated short block `F[080]`,
- a reverse wiggle block `R[454]`,
- a reverse wiggle block `R[121]`,
across four sweep slots, with `R[454]` and `R[121]` allowed to cohabit as
`R[454,121]`.

So the count is exactly:
- `4` choices for `F[080]`,
- `3 x 3` choices for the two reverse wiggle blocks,
- total `4 * 9 = 36`.

### Branch `(5,3,5,3,3,5,3,3,3)`

Again there are exactly `36` signatures, each once. They are precisely the
placements of:
- an isolated short block `F[010]`,
- a forward wiggle block `F[232]`,
- a forward wiggle block `F[565]`,
across four sweep slots, with `F[232]` and `F[565]` allowed to cohabit as
`F[232,565]`.

So again the count is:
- `4` choices for `F[010]`,
- `3 x 3` choices for the two wiggle blocks,
- total `36`.

This is much stronger than “there are 36 exceptions.” These branches are now
exact microblock-placement languages.

I also ran exact classifiers on the shifted `(1,3,2)` versions of both
`36`-word branches, and the totals match the representative class exactly:

- shifted branch `(3,5,3,3,3,5,3,3,5)`:
  - `36` exceptions total,
  - `24` completion-unsat,
  - `12` seed-unsat,
  - `scc_counter = {476:4, 480:4, 484:8, 492:4, 496:4}`;

- shifted branch `(5,3,5,3,3,3,5,3,3)`:
  - `36` exceptions total,
  - `12` completion-unsat,
  - `24` seed-unsat,
  - `scc_counter = {480:4, 484:4, 492:4}`.

The `ctx_*` labels shift, but the local/completion split and the SCC size bands
are unchanged.

So the `36`-word families are not representative-specific artifacts either.
They are stable block languages with a stable local/SCC obstruction mix.

## Exploration 75 (`L=35` compressed-signature probes): the first four-wiggle supersets still inherit the `L=33` obstructions

The raw `L=35` branch scans are large (`139392` words on the first
representative branches), so I switched to compressed three-sweep signature
models built from the support theorem.

### Local-side superset: support `{2,5,7,8}`

This support contains the representative `L=33` local base support `{2,5,8}`.
I generated the natural tail-`08` three-sweep sublanguage:
- three forward sweeps,
- one `232` wiggle,
- one `565` wiggle,
- one `787` wiggle,
- final tail `0,8`,
with the three interior wiggles assigned arbitrarily to the three sweeps.

That gives exactly `27` candidate signatures.

Result:
- all `27/27` are seeded-unsat,
- none admits a locally consistent good cycle.

So at least on this natural three-sweep sublanguage, adding the extra `787`
wiggle did not rescue the old `ctx_1` family. It made nothing locally
realizable.

### Completion-side superset: support `{1,4,7,8}`

This support contains the representative `L=33` completion base support
`{1,4,8}`.

I generated the analogous reverse-oriented tail-`08` three-sweep sublanguage:
- three reverse sweeps,
- one `121` wiggle,
- one `454` wiggle,
- one `787` wiggle,
- final tail `0,8`,
again with the three wiggles assigned arbitrarily to the three sweeps.

That also gives `27` candidate signatures.

Result:
- `9/27` are seeded-unsat,
- `18/27` are seeded-sat.

For a representative seeded-sat word
`0,8,7,8,7,6,5,4,5,4,3,2,1,0,8,7,6,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0,8`,
completion fails immediately:
- the seeded good cycle exists,
- SMT completion rejects it by propagation alone,
- the propagated fatal SCC has size only `8`,
- it is mixed-state (`all_binary = False`),
- and its internal mover histogram is `{0:4, 1:2, 2:4}`.

So the completion-side obstruction also survives the extra wiggle, and in this
compressed model it actually becomes *smaller* and more local than the earlier
`476-496` SCC band at `L=33`.

This is the first real monotonicity evidence past `L=33`:
- extra support does not seem to create new good cycles,
- it either preserves local inconsistency or preserves a completion-level trap.

## Exploration 76 (`glb_three_sweep_scan.py`): a reusable compressed scanner for higher-support monotonicity

I turned the ad hoc compressed support probes into
`scripts/glb_three_sweep_scan.py`.

It generates three-sweep block languages from:
- an orientation (`forward` / `reverse`),
- a set of interior wiggle edges,
- a boundary mode (`tail08`, `short080`, `tail121`, etc.),
and then classifies the resulting candidate words by seeded-cycle SAT or by
seeded/completion outcome.

This is the right scale for the higher-support monotonicity question: tens to
hundreds of block signatures, not `139392` raw words.

### Reproduced results

- local-side compressed branch:
  - `python3 scripts/glb_three_sweep_scan.py --state-counts 2,3,2,3,3,2,3,3,4 --orientation forward --interior-edges 2,5,7 --boundary-mode tail08 --mode seed --timeout-ms 500`
  - output:
    - `word_count = 27`,
    - `counter = {'seed_unsat': 27}`.

- completion-side compressed branch:
  - `python3 scripts/glb_three_sweep_scan.py --state-counts 2,3,2,3,3,2,3,3,4 --orientation reverse --interior-edges 1,4,7 --boundary-mode tail08 --mode completion --cycle-timeout-ms 2500 --completion-timeout-ms 2500`
  - output:
    - `word_count = 27`,
    - `counter = {'seed_unsat': 9, 'completion_unsat': 18}`,
    - `scc_counter` includes two tiny `(8, False)` traps as well as larger
      propagated SCCs.

I also checked the larger local-side grammar that allows either a final `08`
tail or an inserted `080` short block. In the full `135`-word grammar:
- `134` were seeded-unsat,
- `1` timed out at a very short timeout budget.

So the extra-support local branch is essentially dead already in compressed
signature space, while the completion branch remains alive only up to the
same kind of completion obstruction seen earlier.

## Exploration 77 (the `L=33` local frontier is now explicit by word shape): the `P1` and `P3` families are exact microblock languages

I dumped the surviving representative `L=33` local branches as raw mover words.

### Branch `(3,3,5,3,3,5,3,3,5)` (`9` words)

The `9` survivors are exactly:
- three forward sweeps,
- one lower wiggle `2323`,
- one upper wiggle `5656`,
- final tail `08`,
with the two wiggles placed independently among the first three sweeps.

So this is literally a `3 x 3` block-placement family.

### Branch `(5,5,3,3,3,5,3,3,3)` (`3` words)

The `3` survivors are exactly:
- three forward sweeps,
- one upper wiggle `5656`,
- final tail `121`,
with the `5656` wiggle placed in one of the first three sweeps.

So the `ctx_3_3_{23,25}` family is also a tiny exact microblock language, not
an amorphous leftover set.

### Branch `(5,5,3,3,5,3,3,3,3)` (`12` words)

The `12` survivors are exactly:
- three reverse sweeps,
- one `4545` wiggle,
- one `121` block,
with those two local features placed among the first four `0`-anchored blocks.

So the whole seeded-unsat representative `L=33` frontier is now compressed into
three exact microblock languages:
- `P1`: `3 x 3`,
- `P3`: `3`,
- bottom-local mixed family: `12`.

## Exploration 78 (negative result: naive even-return is too weak): the `P1/P3/P8` families are not frozen-neighbor repeats

I added a broader detector `find_even_return_contexts(...)` to
`scripts/glb_return_staircase.py`.

The idea was:
- let the target processor be frozen,
- allow either neighbor to be either fixed or binary with any positive even
  number of moves,
- infer that the local context repeats with opposite mover/nonmover status.

This detector is mathematically valid, but it does **not** hit the surviving
`L=33` local families.

Exact representative counts:
- `(3,3,5,3,3,5,3,3,5)`: still `9` survivors after the old
  return-cone + binary-bounce filters and after the new even-return filter;
- `(5,5,3,3,3,5,3,3,3)`: still `3`;
- `(5,5,3,3,5,3,3,3,3)`: still `12`.

So the real obstruction in the `ctx_1/ctx_3/ctx_8` families is not “processor
frozen while neighbors return.” It is an **anchored return** phenomenon: the
processor itself may move multiple times and later revisit its initial local
context.

This is important because it rules out a tempting but false simplification.

## Exploration 79 (`L=35` compressed completion branch): the propagated failure can collapse to an `8`-node bottom-local cube

For the compressed representative completion-side support
`{1,4,7,8}` with word

`0,8,7,8,7,6,5,4,5,4,3,2,1,0,8,7,6,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0,8`

I extracted the full propagated fatal SCC.

It is exactly the `8` configurations

`{(x0,x1,x2,2,2,1,2,2,0) : x0,x2 in {0,1}, x1 in {0,1}}`

with internal forced moves on processors `{0,1,2}`:

- `(0,0,0,2,2,1,2,2,0)` -> move `0` or `2`
- `(0,0,1,2,2,1,2,2,0)` -> move `0`
- `(0,1,0,2,2,1,2,2,0)` -> move `1`
- `(0,1,1,2,2,1,2,2,0)` -> move `2`
- `(1,0,0,2,2,1,2,2,0)` -> move `2`
- `(1,0,1,2,2,1,2,2,0)` -> move `1`
- `(1,1,0,2,2,1,2,2,0)` -> move `0`
- `(1,1,1,2,2,1,2,2,0)` -> move `0` or `2`

So the higher-support completion obstruction can be genuinely local:
- fixed tail `(2,2,1,2,2,0)`,
- bottom triple `(P0,P1,P2)`,
- recurrent forced region on `8` states.

The induced forced rule fragment is:
- `P0`: `(0,0,0) -> 1`, `(0,1,0) -> 1`, `(0,1,1) -> 0`, with
  `(0,0,1)` fixed to `0` on this branch;
- `P1`: `(0,1,0) -> 0`, `(1,0,1) -> 1`;
- `P2`: `(0,0,2) -> 1`, `(1,1,2) -> 0`.

So there is at least one honest completion theorem candidate now:
- certain higher-support branches force a bottom-local cube trap by propagation
  alone.

## Exploration 80 (important split: the `L=33` completion family does **not** force the same local cube fragment)

I then checked the representative `L=33` completion branch

`0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,5,4,3,2,1,2,1,0,8`

which is seeded-sat and completion-dead with propagated SCC size `484`.

The expected `L=35` cube fragment is **not** forced there. Comparing the key
domains:

- `L=35` branch:
  - `P0(0,0,0) = {1}`
  - `P0(0,0,1) = {0}`
  - `P0(0,1,0) = {1}`
  - `P0(0,1,1) = {0}`
  - `P1(0,1,0) = {0}`
  - `P1(1,0,1) = {1}`
  - `P2(0,0,2) = {1}`
  - `P2(1,1,2) = {0}`

- `L=33` completion branch:
  - `P0(0,0,0) = {1}`
  - `P0(0,0,1) = {0,1}`
  - `P0(0,1,0) = {1}`
  - `P0(0,1,1) = {0,1}`
  - `P1(0,1,0) = {1}`
  - `P1(1,0,1) = {2}`
  - `P2(0,0,2) = {0,1}`
  - `P2(1,1,2) = {0,1}`

So the `L=35` bottom-cube trap is real, but it is **not** the universal
completion obstruction. The `L=33` completion families are forcing something
different and more global.

This is a load-bearing correction:
- I should not overclaim a single completion mechanism yet.
- The honest split is now:
  - local `L=33` families = anchored-return obstructions,
  - higher-support compressed completion family = bottom-local cube trap,
  - representative `L=33` completion family = distinct large propagated trap.

## Exploration 81 (`P1` family rigidity): all `9` words share the same anchored-return count profile

I ran exact core extraction on all `9` words in the representative
`(3,3,5,3,3,5,3,3,5)` branch.

Every one has core `ctx_1_1_u` with `u in {23,25}` and, crucially, the same
move counts on the interval `[1,u)`:

- `P0`: `2` moves,
- `P1`: `3` moves,
- `P2`: `4` moves,
- `P3`: `3` moves,
- `P4`: `2` moves.

So the `P1` family is not merely a repeated-context phenomenon in the solver.
It has a uniform combinatorial profile:
- `P1` makes exactly its full ternary cycle of `3` moves and then freezes;
- `P2` is binary and moves an even `4` times;
- `P0` is binary and moves an even `2` times after time `1`.

That gives the clean proof route:
- at time `1`, `P1` sees its initial context `(1,0,0)` and is the mover;
- by time `u`, `P1` has completed its full 3-move ternary cycle and is back at
  state `0`,
- `P2` is back at `0` by binary parity,
- `P0` is back at its time-`1` state `1` by binary parity,
- so `P1` sees `(1,0,0)` again while nonmoving.

So the `P1` family is now essentially proved analytically; the only remaining
writeup task is to phrase the count argument cleanly against the exact
`3 x 3` block language from exploration 77.

## Exploration 82 (the mixed branch really splits): `8` pure `ctx_8` words plus `4` bottom-local mixed words

I extracted unsat-core labels for all `12` words in the representative
mixed/local branch `(5,5,3,3,5,3,3,3,3)`.

Exact split:

- pure `P8`-core words (`8` total):
  - `ctx_8_1_21`,
  - `ctx_8_1_23` three times,
  - `ctx_8_1_25` twice,
  - `ctx_8_1_30` twice.

- bottom-local mixed words (`4` total):
  - two with the core triple
    `ctx_0_0_30`, `ctx_2_28_31`, `ctx_2_0_27`,
  - one with
    `ctx_2_8_27`, `ctx_1_19_32`, `ctx_0_22_31`,
  - and the fourth mixed word is the symmetric repeat of the first pattern.

So the branch is no longer mysterious:
- most of it (`8/12`) is still a pure anchored-return family centered at `P8`,
- the remaining `4/12` already belong to the bottom-local `P0/P1/P2` mechanism.

This is a meaningful structural compression of the local `L=33` frontier:
- `P1` family,
- `P3` family,
- pure `P8` family,
- four explicit bottom-local mixed outliers.

## Exploration 86 (anchored-return as a detector): it kills the entire branch-8 family, not just the obvious pure `P8` words

I upgraded the anchored-return proof into a reusable detector
`find_anchored_return_contexts(...)` in
`scripts/glb_return_staircase.py`, and then checked it on explicit sample
words.

Three immediate outcomes:

1. It fires exactly the way the proof predicts on representative pure words:
   - `P1` sample: witness at `t=1`, with both neighbors binary-even.
   - `P3` sample: witness at `t=3`, with `P2` binary-even and `P4`
     anchored-finished.
   - pure `P8` sample: witness at `t=1`, with `P7` anchored-finished and `P0`
     binary-even.

2. On the full explicit `12`-word list from branch
   `(5,5,3,3,5,3,3,3,3)`, the detector returns `True` for **all 12 words**.

3. So the earlier “`8` pure `P8` words plus `4` bottom-local mixed words”
   split was only a split at the unsat-core label level, not at the theorem
   level. The anchored-return lemma is already strong enough to subsume the
   entire branch.

This is a major simplification of the local Case 3c picture:
- branch `(3,3,5,3,3,5,3,3,5)` is anchored-return,
- branch `(5,5,3,3,3,5,3,3,3)` is anchored-return,
- branch `(5,5,3,3,5,3,3,3,3)` is anchored-return.

So the remaining uncertainty is shifting away from the seeded-unsat local
families and onto the completion-dead branches.

## Exploration 87 (the `36`-word branches factor into `4 x 9` kernels): exact tail-grammar decomposition

I finally found exact small kernels inside the two `36`-word representative
completion branches.

### Reverse kernel for branch `(3,5,3,3,5,3,3,3,5)`

The exact `9`-word family

`generate_words((1,4), 'reverse', 'tail08')`

consists of:
- three reverse sweeps,
- one `121` wiggle,
- one `454` wiggle,
- final tail `08`.

On this `9`-word family the outcomes are:
- `6` completion-unsat,
- `3` seeded-unsat.

So the old `24 + 12` split of the full `36`-word branch is exactly
`4 x (6 + 3)` if the four block placements are kept separate.

### Forward kernel for branch `(5,3,5,3,3,5,3,3,3)`

The exact `9`-word family

`generate_words((2,5), 'forward', 'tail01')`

consists of:
- three forward sweeps,
- one `232` wiggle,
- one `565` wiggle,
- final tail `01`.

On this `9`-word family the outcomes are:
- `3` completion-unsat,
- `6` seeded-unsat.

Again the old `12 + 24` split of the full `36`-word branch is exactly
`4 x (3 + 6)`.

So the completion frontier is no longer a pair of opaque `36`-word sets.
It is:
- one reverse `9`-word kernel, copied in four block placements;
- one forward `9`-word kernel, copied in four block placements.

This is the cleanest structural reduction I have on the completion side so far.

## Exploration 88 (the seeded-unsat halves of the `9`-word kernels are tiny core families)

I started extracting the seeded-unsat labels on the two exact `9`-word kernels
from exploration 87.

### Reverse `tail08` kernel

For the `3` seeded-unsat words in
`generate_words((1,4), 'reverse', 'tail08')`, the cores are already collapsing
to a tiny bottom-local family:

- two words give
  `ctx_0_2_11` together with `ctx_1_10_30`,
- the third gives
  `ctx_0_2_13` together with `ctx_1_12_30`.

So the local half of the reverse kernel is a `3`-word family with one core pair
up to a small time shift.

### Forward `tail01` kernel

For the `6` seeded-unsat words in
`generate_words((2,5), 'forward', 'tail01')`, the first cores I extracted are:

- `ctx_4_8_17`, `ctx_2_1_15`, `ctx_2_2_26`,
- `ctx_2_2_32`, `ctx_1_1_21`.

So the forward kernel’s local half is also collapsing, but to a different small
family centered around processors `1,2,4`.

This matters because the remaining local work on the completion side is now
very sharply localized:
- reverse kernel: `3` seeded-unsat words with one bottom-local core pair family,
- forward kernel: `6` seeded-unsat words with a small shifted `1/2/4` core
  family.

So even before the completion-unsat words are understood, the two `9`-word
kernels have already split into:
- a tiny local kernel,
- plus a tiny completion kernel.

## Exploration 89 (the completion kernels are fully classified by SCC type): the old branch histograms are exactly `4` copies

I finished the completion-side classification on the two exact `9`-word kernels
from exploration 87.

### Reverse `tail08` kernel

The `6` completion-unsat words in
`generate_words((1,4), 'reverse', 'tail08')` have propagated fatal SCC sizes:

- `476`,
- `480`,
- `484` twice,
- `492`,
- `496`.

So its SCC histogram is:

`{476: 1, 480: 1, 484: 2, 492: 1, 496: 1}`.

### Forward `tail01` kernel

The `3` completion-unsat words in
`generate_words((2,5), 'forward', 'tail01')` have propagated fatal SCC sizes:

- `480`,
- `484`,
- `492`.

So its SCC histogram is:

`{480: 1, 484: 1, 492: 1}`.

This exactly explains the old representative `36`-word branch histograms:

- reverse branch `(3,5,3,3,5,3,3,3,5)`:
  - old histogram `{476:4, 480:4, 484:8, 492:4, 496:4}`
  - = `4` copies of the reverse kernel histogram;

- forward branch `(5,3,5,3,3,5,3,3,3)`:
  - old histogram `{480:4, 484:4, 492:4}`
  - = `4` copies of the forward kernel histogram.

So the completion side has now reduced all the way down to **nine concrete
words**:
- `6` reverse completion words,
- `3` forward completion words,
with the full `36`-word branches obtained just by the old fourfold placement
symmetry.

## Exploration 90 (the `9`-word kernels have a one-line local/completion split): it is controlled by the bottom wiggle position

I printed the exact block signatures of the two `9`-word kernels.

### Reverse kernel signatures

The `9` signatures are:

1. `R[] | R[] | R[454,121] | R[]`
2. `R[] | R[121] | R[454] | R[]`
3. `R[] | R[454] | R[121] | R[]`
4. `R[] | R[454,121] | R[] | R[]`
5. `R[121] | R[] | R[454] | R[]`
6. `R[121] | R[454] | R[] | R[]`
7. `R[454] | R[] | R[121] | R[]`
8. `R[454] | R[121] | R[] | R[]`
9. `R[454,121] | R[] | R[] | R[]`

Comparing with exploration 89:
- completion-unsat words are `1,2,3,4,7,8`,
- seeded-unsat words are `5,6,9`.

So the split is exact:

**Reverse local kernel criterion**
- seeded-unsat iff the bottom wiggle `121` occurs in the **first** reverse
  block;
- otherwise the word is completion-unsat.

### Forward kernel signatures

The `9` signatures are:

1. `F[232,565] | F[] | F[] | F[]`
2. `F[232] | F[565] | F[] | F[]`
3. `F[232] | F[] | F[565] | F[]`
4. `F[565] | F[232] | F[] | F[]`
5. `F[565] | F[] | F[232] | F[]`
6. `F[] | F[232,565] | F[] | F[]`
7. `F[] | F[232] | F[565] | F[]`
8. `F[] | F[565] | F[232] | F[]`
9. `F[] | F[] | F[232,565] | F[]`

Comparing with exploration 89:
- completion-unsat words are `1,2,3`,
- seeded-unsat words are `4,5,6,7,8,9`.

So again the split is exact:

**Forward local kernel criterion**
- completion-unsat iff the bottom wiggle `232` occurs in the **first** forward
  block;
- seeded-unsat otherwise.

This is the cleanest structural formulation yet for the completion-side local
residue. The kernel behavior is controlled entirely by the placement of the
bottom wiggle:
- reverse kernel: early `121` gives local contradiction;
- forward kernel: delayed `232` gives local contradiction.

## Exploration 91 (first real higher-support monotonicity): the bottom-wiggle split survives an added `787` wiggle exactly

I checked the one-step supersets of the two `9`-word kernels:

- reverse family:
  `generate_words((1,4,7), 'reverse', 'tail08')`, `27` words;
- forward family:
  `generate_words((2,5,7), 'forward', 'tail01')`, `27` words.

### Forward `27`-word family

Exact classification:
- `9` completion-unsat,
- `18` seeded-unsat,
- `0` other outcomes.

Bucketed by whether the **first** block contains the bottom wiggle `232`:

- first block has `232`:
  - `9/9` are completion-unsat;
- first block does **not** have `232`:
  - `18/18` are seeded-unsat.

So the `9`-word forward-kernel rule from exploration 90 survives the added
`787` wiggle *without exception*.

### Reverse `27`-word family

Exact classification:
- `18` completion-unsat,
- `9` seeded-unsat,
- `0` other outcomes.

Bucketed by whether the **first** block contains the bottom wiggle `121`:

- first block has `121`:
  - `9/9` are seeded-unsat;
- first block does **not** have `121`:
  - `18/18` are completion-unsat.

So the reverse-kernel rule from exploration 90 also survives the added `787`
wiggle *without exception*.

This is the strongest monotonicity evidence I have so far:
- adding an upper wiggle does not change the local/completion dichotomy;
- the dichotomy is still determined entirely by where the bottom wiggle first
  appears.

So at least on these `27`-word supersets, the Case 3c obstruction is not a
fragile `L=33` artifact. It scales one full support layer upward exactly.

## Exploration 84 (anchored-return lemma): the pure `P1/P3/P8` families are all the same proof

I finally found the right simplification for the pure local families.

### Lemma (Anchored Return)

Fix a processor `p` and times `t < u`.

Suppose:
- `p` is the mover at time `t`,
- `p` is a nonmover at time `u`,
- time `t` is before the first move of `p` after the anchor, so `p` is still in
  its anchored initial state at time `t`,
- all moves of `p` occur before time `u`, so `p` has already made its final
  move by time `u`,
- for each neighbor `q` of `p`, one of the following holds:
  - `q` is binary and makes an even number of moves in `[t,u)`, so its state at
    time `u` equals its state at time `t`;
  - or `q` is still in its anchored initial state at time `t` and also makes
    all of its cycle moves before time `u`, so its state at time `u` again
    equals that same anchored initial state.

Then processor `p` sees exactly the same local context at times `t` and `u`.
Since it is a mover at `t` and a nonmover at `u`, determinism is violated, so
no seeded good cycle can realize the mover word.

### Proof idea

The key observation is simpler than I had been making it:
- once a processor has already made its **last** move in the cycle, its state at
  every later time is its final cycle state;
- the cycle closes back to the anchored initial configuration;
- therefore that final state is exactly the anchored initial state.

So I do **not** need a per-processor “full `m`-step state cycle” argument.
I only need:
- time `t` chosen before the processor’s first move, and
- time `u` chosen after its last move.

That immediately collapses the pure local `L=33` families:

### Application to the representative `P1` family `(3,3,5,3,3,5,3,3,5)`

All `9` words have:
- `ctx_1_1_u` with `u in {23,25}`,
- `P0` moves `2` times in `[1,u)`,
- `P1` has already made all its moves by time `u`,
- `P2` moves `4` times in `[1,u)`.

At time `1`, `P1` sees `(1,0,0)` and moves.
At time `u`, `P1` is back at anchored state `0`, `P2` is back at `0` by binary
parity, and `P0` is back at its time-`1` state `1` by binary parity.
So `P1` sees `(1,0,0)` again as a nonmover.

### Application to the representative `P3` family `(5,5,3,3,3,5,3,3,3)`

By direct inspection of the three words:
- time `t = 3` is the first move of `P3`,
- the repeated core is `ctx_3_3_u` with `u in {23,25}`,
- `P2` makes an even number of moves between `3` and `u`,
- `P4` has not moved yet at time `3` and has already finished all its moves by
  time `u`,
- `P3` itself has already finished all its moves by time `u`.

So `P3` revisits its initial context `(1,0,0)` as a nonmover.

### Application to the pure `P8` words inside `(5,5,3,3,5,3,3,3,3)`

For all `8` pure `ctx_8_1_u` words, with `u in {21,23,25,30}`:
- `P0` moves exactly `2` times in `[1,u)`,
- `P7` makes exactly `3` moves in `[1,u)` and has already finished by time `u`,
- `P8` makes exactly `3` moves in `[1,u)` and has already finished by time `u`.

At time `1`, `P8` sees `(0,0,1)` and moves.
At time `u`, `P7` and `P8` are both back at anchored state `0`, while `P0` is
back at its time-`1` state `1` by binary parity.
So `P8` sees `(0,0,1)` again as a nonmover.

So the pure local Case 3c frontier is now conceptually unified:
- `P1`, `P3`, and pure `P8` are all instances of the same anchored-return
  lemma.
- only the `4` mixed bottom-local words remain outside that lemma on the local
  side.

## Exploration 85 (the four mixed bottom-local words split `3 + 1`): one repeated pattern and one true outlier

I extracted interval counts for the four mixed words from exploration 82.

### The repeated `3`-word pattern

Three of the four words share exactly the same core set:
- `ctx_0_0_30`,
- `ctx_2_0_27`,
- `ctx_2_28_31`.

For all three, the interval counts on processors `0,1,2` are identical:

- for `ctx_0_0_30`: counts on `[0,30)` are `(4,3,3)`,
- for `ctx_2_0_27`: counts on `[0,27)` are `(3,2,2)`,
- for `ctx_2_28_31`: counts on `[28,31)` are `(1,2,0)`.

So these are not three separate anomalies. They are one exact bottom-local
pattern repeated across the three placements of the `4545` wiggle.

### The true outlier

The fourth mixed word

`0,8,7,6,5,4,5,4,3,2,1,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,2,1,0,1`

has a different core triple:
- `ctx_2_8_27`,
- `ctx_1_19_32`,
- `ctx_0_22_31`.

Its bottom-local interval counts are:
- for `ctx_0_22_31`: `(0,2,2)`,
- for `ctx_1_19_32`: `(2,3,2)`,
- for `ctx_2_8_27`: `(2,2,2)`.

So the mixed local frontier is now only:
- one `3`-word repeated bottom-local pattern,
- one single exceptional word.

That is a much smaller target than the original `12`-word mixed branch.

## Exploration 83 (negative result: the big `L=33` completion trap really uses the quaternary state)

I checked the representative `L=33` completion-dead SCC from exploration 80 for
its per-processor value sets.

For the bad SCC of size `484`, the values used are:

- `P0`: `{0,1}`
- `P1`: `{0,1,2}`
- `P2`: `{0,1}`
- `P3`: `{0,1,2}`
- `P4`: `{0,1,2}`
- `P5`: `{0,1}`
- `P6`: `{0,1,2}`
- `P7`: `{0,1,2}`
- `P8`: `{0,1,2,3}`

So the large completion obstruction is **not** hiding inside a pure
`{2,3}`-state subsystem. The quaternary processor genuinely uses all four
states inside that recurrent propagated region.

This matters because it rules out the easiest possible reduction:
- I cannot simply identify the `484`-node trap with the old pure sweep/shadow
  artifact.
- Any completion-side theorem for true Case 3c has to account for the
  quaternary processor as an active participant in the bad SCC.

## Exploration 92 (completion fragments minimize to `33` rules): the big `484`-node traps already live in a much smaller forced rule set

I finally made the completion side concrete enough to manipulate directly.

I added `scripts/glb_case3c_completion_fragment.py`. Given a seeded-sat mover
word, it:
- builds the completion singleton map from the seeded cycle,
- greedily deletes singleton entries while preserving fatality under
  `has_fatal_forced_cycle_singletons(...)`,
- and reports the SCC induced by the reduced fragment.

On the representative reverse completion kernel word

`0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,5,4,3,2,1,2,1,0,8`

the numbers are:
- full forced singleton entries from the seeded cycle: `95`,
- minimal fatal fragment after greedy deletion: `33`,
- induced fatal SCC size from just that `33`-rule fragment: `484`.

So the huge propagated failure is not using the whole good cycle. A much smaller
explicit rule fragment already forces the same bad SCC.

The reduced reverse fragment is:

- `P0`: `(0,0,0)->1`, `(1,1,2)->0`, `(2,0,1)->1`, `(3,1,0)->0`
- `P1`: `(0,2,0)->1`, `(1,0,1)->2`, `(1,1,1)->2`, `(1,2,0)->0`
- `P2`: `(0,0,1)->1`, `(1,0,0)->1`, `(2,1,0)->0`, `(2,1,2)->0`
- `P3`: `(0,0,2)->1`, `(0,2,0)->0`, `(1,1,1)->2`
- `P4`: `(0,0,1)->2`, `(1,2,0)->1`, `(2,1,1)->2`, `(2,2,0)->0`
- `P5`: `(0,0,1)->1`, `(1,0,0)->1`, `(2,1,0)->0`, `(2,1,2)->0`
- `P6`: `(0,0,1)->1`, `(0,2,0)->0`, `(1,1,2)->2`
- `P7`: `(0,0,1)->1`, `(1,1,2)->2`, `(2,2,3)->0`
- `P8`: `(0,0,1)->1`, `(0,3,0)->0`, `(1,1,0)->2`, `(2,2,1)->3`

The induced SCC still has:
- size `484`,
- value sets `[[0,1],[0,1,2],[0,1],[0,1,2],[0,1,2],[0,1],[0,1,2],[0,1,2],[0,1,2,3]]`,
- outdegree histogram `{1:23, 2:167, 3:234, 4:60}`.

I repeated the same reduction on the representative forward completion kernel
word

`0,1,2,3,2,3,4,5,6,5,6,7,8,0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8,0,1`

and got the same phenomenon:
- full forced singleton entries: `95`,
- minimal fatal fragment: `33`,
- induced SCC size from the fragment alone: `484`.

Its reduced fragment is:

- `P0`: `(0,0,0)->1`, `(0,1,1)->0`, `(1,1,2)->0`, `(2,0,0)->1`
- `P1`: `(0,1,0)->0`, `(0,2,0)->0`, `(1,0,0)->2`, `(1,0,1)->1`
- `P2`: `(0,0,1)->1`, `(1,1,2)->0`, `(2,0,0)->1`, `(2,1,2)->0`
- `P3`: `(0,2,0)->1`, `(0,2,2)->0`, `(1,0,0)->2`, `(1,1,1)->2`
- `P4`: `(0,2,1)->0`, `(1,0,0)->1`, `(2,1,0)->2`
- `P5`: `(0,1,2)->0`, `(1,0,0)->1`, `(1,1,2)->0`, `(2,0,1)->1`
- `P6`: `(0,2,0)->1`, `(0,2,2)->0`, `(1,0,0)->2`, `(1,1,1)->2`
- `P7`: `(0,2,2)->0`, `(1,0,0)->1`, `(2,1,1)->2`
- `P8`: `(0,2,1)->0`, `(1,0,1)->1`, `(2,1,0)->2`

Again the fragment alone yields the full `484`-node bad SCC with value sets
`[[0,1],[0,1,2],[0,1],[0,1,2],[0,1,2],[0,1],[0,1,2],[0,1,2],[0,1,2]]`.

So the completion frontier is now sharper:
- the representative reverse and forward completion kernels are not “large
  diffuse propagation artifacts”;
- each already contains a concrete `33`-rule fatal core;
- the remaining work is to understand how the other kernel words shift these
  `33`-rule patterns, not to search the full `95`-rule seeded cycle.

I also ran the same greedy minimization across the full completion kernels:
- all `6/6` reverse completion words reduce to `33` singleton rules;
- all `3/3` forward completion words reduce to `33` singleton rules.

So `33` is not a representative accident. It is the stable scale of the
completion-side obstruction on the exact `9`-word kernels.

More structure than that survived the minimization:

- the `6` reverse completion fragments factor as
  `2` bottom templates on processors `0..3`
  times
  `3` upper templates on processors `4..6`,
  with processors `7,8` fixed across all six;
- the `3` forward completion fragments keep a single common bottom template on
  processors `0,1` and a single common tail on processors `7,8`, while the
  middle processors `2..6` vary through exactly `3` shifted templates.

So the completion residue is no longer a `6 + 3` cloud of special words. It has
already collapsed to a finite template grammar.

Two related negative results also came out of the same pass:
- the fatal SCC intersections across all reverse completion words (`140` states)
  and all forward completion words (`185` states) are nontrivial but do **not**
  by themselves form SCCs under the common singleton rules;
- the best simple cartesian-product intersections I found
  (`8` states on `(P0,P2,P7)` for reverse, `24` states on `(P0,P3,P5,P7)` for
  forward) are not closed either.

So the right completion object is not a tiny product cube. It is a moderately
structured `33`-rule fragment.

## Exploration 93 (the kernel local residue is fully explicit): reverse collapses to one bottom pair; forward collapses to three shifted families

The long unsat-core extraction on the seeded-unsat halves of the two `9`-word
kernels finally finished.

### Reverse local kernel

For the `3` seeded-unsat words in `generate_words((1,4), 'reverse', 'tail08')`
I now have the exact core collapse:

- two words have the pair
  `ctx_0_2_11`, `ctx_1_10_30`;
- the third has the shifted pair
  `ctx_0_2_13`, `ctx_1_12_30`.

So the reverse local kernel is exactly one bottom-local repeated-context
mechanism, with only a small time shift.

### Forward local kernel

For the `6` seeded-unsat words in `generate_words((2,5), 'forward', 'tail01')`
the cores split into three explicit shifted families:

- a `P2/P4` family:
  `ctx_2_0_15`, `ctx_2_2_32`, `ctx_4_8_17`;
- a shifted `P2/P4` family:
  `ctx_2_0_13`, `ctx_2_2_32`, `ctx_4_6_15`;
- a late `P1/P2` family:
  `ctx_2_2_26`, `ctx_1_1_21`,
  together with the one-step shift
  `ctx_1_1_19`, `ctx_2_2_32`.

So the forward local kernel is not a diffuse six-word artifact either. It is a
tiny library of shifted repeated-context obstructions centered on processors
`1,2,4`.

This means the entire seeded-unsat part of the completion-side frontier is now
fully explicit. The only real opacity left in true Case 3c is the completion
half of the two exact kernels, which now sits inside shifted `33`-rule fatal
fragments by exploration 92.

## Exploration 94 (the completion kernels have a `16 + 17` split): every `33`-rule fragment is exactly `16` stable rules plus `17` moving rules

I compared the minimized `33`-rule completion fragments across the full kernels.

The count identity is exact:
- reverse completion kernel: `6` fragments, each of size `33`,
  with `16` rules common to all `6` and `17` noncommon rules in every word;
- forward completion kernel: `3` fragments, each of size `33`,
  with `16` rules common to all `3` and `17` noncommon rules in every word.

So the completion side has a genuine fixed spine:
- not only are the fragments all the same size,
- they split uniformly into a stable kernel-common `16`-rule part and a
  `17`-rule moving part.

The reverse common `16` rules are:
- `P0`: `(0,0,0)->1`, `(3,1,0)->0`
- `P1`: `(1,2,0)->0`
- `P2`: `(0,0,1)->1`, `(2,1,0)->0`
- `P4`: `(2,2,0)->0`
- `P5`: `(0,0,1)->1`, `(2,1,0)->0`
- `P6`: `(0,0,1)->1`
- `P7`: `(0,0,1)->1`, `(1,1,2)->2`, `(2,2,3)->0`
- `P8`: `(0,0,1)->1`, `(0,3,0)->0`, `(1,1,0)->2`, `(2,2,1)->3`

The forward common `16` rules are:
- `P0`: `(0,0,0)->1`, `(0,1,1)->0`, `(1,1,2)->0`, `(2,0,0)->1`
- `P1`: `(0,1,0)->0`, `(0,2,0)->0`, `(1,0,0)->2`, `(1,0,1)->1`
- `P2`: `(2,0,0)->1`
- `P5`: `(1,0,0)->1`
- `P7`: `(0,2,2)->0`, `(1,0,0)->1`, `(2,1,1)->2`
- `P8`: `(0,2,1)->0`, `(1,0,1)->1`, `(2,1,0)->2`

This is the first honest kernel-common completion invariant I have. The moving
`17`-rule part still depends on the wiggle placement, but the fixed `16`-rule
spine already explains why every completion word keeps the same SCC scale and
the same boundary behavior.

## Exploration 95 (`L=35` completion monotonicity is not literal containment): new completion fragments appear, but they stay finite and structured

I tested the strongest possible monotonicity guess:
- do the `L=35` three-sweep supersets literally contain one of the `L=33`
  completion fragments?

The answer is **no**.

For the representative supersets
- reverse: `generate_words((1,4,7), 'reverse', 'tail08')`,
- forward: `generate_words((2,5,7), 'forward', 'tail01')`,

I checked every completion-unsat word against the exact `L=33` completion
fragments. Result:
- reverse: `18/18` completion words fail literal containment,
- forward: `9/9` completion words fail literal containment.

So higher support is not just “the old completion kernel plus extra irrelevant
rules”. The completion fragment genuinely changes when the extra `787` wiggle is
added.

### First representative misses

The first reverse miss still minimizes cleanly:
- full forced entries: `100`,
- minimal fatal fragment: `35`,
- induced bad SCC size: `531`.

The first forward miss also minimizes cleanly:
- full forced entries: `101`,
- minimal fatal fragment: `35`,
- induced bad SCC size: `501`.

So the good news is that the higher-support completion obstruction is still
small-rule and fully forced. The bad news is that it is not literally the old
`33`-rule object.

## Exploration 96 (`L=35` completion fragments are still highly rigid): forward is uniform `35`, reverse splits into `35` and tiny `6`-rule cubes

I scanned the full `27`-word representative completion families and minimized
every completion-unsat word.

### Reverse family `generate_words((1,4,7), 'reverse', 'tail08')`

Exact outcome:
- `9` seeded-unsat,
- `18` completion-unsat.

The minimized completion fragments split as:
- `13` words with fragment size `35`,
- `5` words with fragment size `6`.

So the reverse higher-support completion side is **not** uniform. But the split
is tiny and explicit.

The `5` size-`6` cases collapse to exactly **three** bottom-local cube
templates.

#### Reverse cube template A

Appears on two assignment patterns of the three wiggles `(121,454,787)` to the
three reverse sweeps:
- `(2,1,1)`,
- `(2,2,1)`,
with tuple order `(1,4,7)` and `0`-indexed sweep slots.

In block-signature form these are:
- `R[] | R[787] | R[454,121] | R[]`,
- `R[] | R[787,454] | R[121] | R[]`.

Its six-rule fragment is:
- `(0,(2,0,1))->1`
- `(0,(2,1,2))->0`
- `(1,(0,2,0))->1`
- `(1,(1,1,1))->2`
- `(2,(1,0,0))->1`
- `(2,(2,1,0))->0`

This forces an `8`-state SCC:
- variable processors `P0,P1,P2`,
- fixed tail `(P3..P8) = (0,0,0,0,0,2)`,
- internal mover histogram `{0:4, 1:2, 2:4}`.

#### Reverse cube template B

Appears on the single assignment
- `(1,1,0)`,
with signature
- `R[787] | R[454,121] | R[] | R[]`.

Its six-rule fragment is:
- `(0,(0,0,0))->1`
- `(0,(0,1,1))->0`
- `(1,(0,1,0))->0`
- `(1,(1,0,1))->1`
- `(2,(0,0,2))->1`
- `(2,(1,1,2))->0`

This forces an `8`-state SCC:
- variable processors `P0,P1,P2`,
- fixed tail `(P3..P8) = (2,0,0,0,0,0)`,
- the same internal mover histogram `{0:4, 1:2, 2:4}`.

#### Reverse cube template C

Appears on the single assignment
- `(1,0,0)` and `(1,2,0)`,
with signature
- `R[787,454] | R[121] | R[] | R[]`,
  and
- `R[787] | R[121] | R[454] | R[]`.

Its six-rule fragment is:
- `(0,(0,0,0))->1`
- `(0,(0,1,2))->0`
- `(1,(0,2,0))->0`
- `(1,(1,0,1))->2`
- `(2,(0,0,2))->1`
- `(2,(2,1,2))->0`

This also forces an `8`-state SCC:
- variable processors `P0,P1,P2`,
- fixed tail `(P3..P8) = (2,0,0,0,0,0)`,
- the same internal mover histogram `{0:4, 1:2, 2:4}`.

So on the reverse side, some `L=35` completion words actually become **easier**
than the `L=33` kernel: the whole propagated contradiction collapses to a
6-rule bottom-local cube.

### Forward family `generate_words((2,5,7), 'forward', 'tail01')`

Exact outcome:
- `18` seeded-unsat,
- `9` completion-unsat.

Here the completion side is perfectly uniform:
- all `9/9` completion words minimize to fragment size `35`.

So the forward higher-support completion branch behaves in the simplest
possible way:
- the extra `787` wiggle never produces a tiny cube trap,
- but it also never produces anything more complicated than a `35`-rule fatal
  fragment.

This is the best higher-support completion picture I have yet:
- forward `27`-word family: completely rigid at size `35`;
- reverse `27`-word family: `13` words at size `35`, `5` words at one of three
  explicit `6`-rule cube traps.

That means the completion gap is no longer “unbounded higher-support chaos”.
It is already collapsing into a small number of reusable fragment types.

## Exploration 97 (the size-`35` families have tiny stable spines): forward common core `5`, reverse common core `4`

I then looked only at the size-`35` higher-support completion families.

### Forward size-`35` family

All `9` forward completion words in
`generate_words((2,5,7), 'forward', 'tail01')`
minimize to size `35`.

Their intersection is only `5` rules:
- `P0`: `(0,0,0)->1`
- `P1`: `(0,1,0)->0`, `(0,2,0)->0`
- `P5`: `(1,0,0)->1`
- `P8`: `(0,3,1)->0`

So the forward higher-support completion family still has a stable spine, but it
is much smaller than the `16`-rule spine at `L=33`.

### Reverse size-`35` subfamily

Restricting the reverse `27`-word family to its `13` size-`35` completion
words, the common core is only `4` rules:
- `P0`: `(0,0,0)->1`
- `P1`: `(1,2,0)->0`
- `P2`: `(0,0,1)->1`, `(2,1,0)->0`

So the reverse size-`35` subfamily is even more bottom-local than the forward
one.

This is a useful directional fact:
- as support grows, the completion obstruction is **not** becoming more diffuse;
- its stable spine is shrinking toward a tiny bottom-local nucleus, while the
  variable part carries the rest of the propagated trap.

## Exploration 98 (important correction: anchored-return universality on mover words is false)

I tested the proposed pure mover-word universality target directly:

> any fair adjacent mover word with `>= 3` pairwise non-adjacent binary
> processors must satisfy at least one of
> return cone / binary-bounce / anchored-return.

This is false already at the known `n=9` Case 3c completion kernels.

For the representative reverse completion-kernel word

`0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,5,4,3,2,1,2,1,0,8`

and the representative forward completion-kernel word

`0,1,2,3,2,3,4,5,6,5,6,7,8,0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8,0,1`

the detector counts are exactly:
- return cones: `0`,
- binary-bounce witnesses: `0`,
- anchored-return witnesses: `0`.

Yet both words are fair adjacent words on the true `n=9` Case 3c architecture.
They fail only at completion, not by any of the three local obstructions.

So there is a hard boundary on what can be proved from mover-word scheduling
alone:
- return cone / binary-bounce / anchored-return are **not** a universal trichotomy;
- any correct general theorem must include an additional residue class beyond
  these three local mechanisms.

This means the right corrected target is no longer
“prove one of the three existing local obstructions always fires”.
It is instead:
- prove that if none of those three obstructions fires, then the mover word is
  forced into the explicit three-sweep residue grammar;
- and then kill that residue either by a general completion theorem or by a new
  fourth obstruction.

So the scheduling-only route has now been decisively delimited.

## Exploration 99 (the `L=35` residue grammar is assignment-exact): the surviving higher-support words are controlled entirely by wiggle-slot assignments

I finished the direct assignment-level classification of the representative
three-sweep `L=35` families.

### Reverse family `generate_words((1,4,7), 'reverse', 'tail08')`

Write an assignment tuple `(a_1, a_4, a_7)` where:
- edge `1` = bottom wiggle `121`,
- edge `4` = middle wiggle `454`,
- edge `7` = upper wiggle `787`,
and each `a_e in {0,1,2}` is the sweep slot carrying that wiggle.

Then the exact outcome split is:
- seed-unsat iff `a_1 = 0` (the bottom wiggle is in the first reverse sweep),
- otherwise completion-unsat.

So the old reverse kernel rule from `L=33` survives one layer upward exactly:
the first reverse block may not contain `121`.

Inside the completion branch (`a_1 in {1,2}`), the small-cube cases are exactly:
- `(1,0,0)`,
- `(1,1,0)`,
- `(1,2,0)`,
- `(2,1,1)`,
- `(2,2,1)`.

All other completion assignments give size-`35` fragments.

Equivalently, the reverse size-`6` subbranch is exactly the assignment region
`a_1 > 0`, `a_7 = a_1 - 1`, `a_4 >= a_7`.

So the reverse `L=35` completion side is now finite in the strongest possible
way: a complete decision table on the `3^3` wiggle-slot assignments.

### Forward family `generate_words((2,5,7), 'forward', 'tail01')`

Write the assignment tuple `(a_2, a_5, a_7)` for wiggles `232`, `565`, `787`.

Then the exact outcome split is:
- completion-unsat iff `a_2 = 0` (the bottom wiggle `232` is in the first
  forward sweep),
- seed-unsat otherwise.

And inside that completion branch, **every** assignment gives a size-`35`
fragment. So the forward `L=35` family is even simpler:
- no cube-trap subbranch,
- just the same “bottom wiggle in first sweep” criterion as before.

This is the cleanest mover-word statement I have past `L=33`:
- the higher-support residue is not a combinatorial explosion;
- it is literally a finite grammar over three-sweep words with outcomes
  determined by wiggle-slot assignment.

## Exploration 100 (`glb_residue_grammar.py`): every explicit residue family now parses under one common four-block grammar

I added `scripts/glb_residue_grammar.py`.

It classifies a mover word by:
- splitting into `0`-anchored blocks,
- recognizing either
  - `3` monotone sweep blocks plus a final tail (`tail08`, `tail01`, `tail121`),
  - or `3` monotone sweep blocks plus one isolated short block
    (`short080`, `short010`),
- and recording the sweep orientation and the local wiggles in each sweep block.

So the residue class is now a concrete object:
- `4` blocks total,
- `3` genuine sweep blocks,
- one boundary block (tail or short),
- all sweep blocks with the same orientation,
- local wiggles only of the `aba` form already tracked by
  `glb_block_signature.py`.

I then checked every explicit residue family currently known, and they all
classify with **zero** failures:

- `generate_words((2,5), 'forward', 'tail08')`: `9/9` classified
- `generate_words((1,4), 'reverse', 'tail08')`: `9/9` classified
- `generate_words((1,4), 'reverse', 'tail08_or_short080')`: `45/45` classified
- `generate_words((2,5), 'forward', 'tail01_or_short010')`: `45/45` classified
- `generate_words((5), 'forward', 'tail121')`: `3/3` classified
- `generate_words((4), 'reverse', 'tail121')`: `3/3` classified
- `generate_words((1,4,7), 'reverse', 'tail08')`: `27/27` classified
- `generate_words((2,5,7), 'forward', 'tail01')`: `27/27` classified

So all currently known Case 3c survivor languages at `L=33` and `L=35` sit
inside one explicit residue grammar. This is exactly the scaffolding I need for
the corrected theorem target from exploration 98:

- local tools do not form a universal trichotomy,
- but whenever they fail, every known survivor is forced into this common
  four-block three-sweep grammar.

This is not the final theorem yet, but it is now a precise, programmable target
instead of an informal picture.
