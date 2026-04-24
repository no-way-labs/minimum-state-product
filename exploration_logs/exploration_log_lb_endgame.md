# Exploration Log: LB Endgame

## Strategy Register

### Eliminated approach classes

- Shortcut via old sorry-free ANF rewrite (`d56c9ff`) is blocked by the current
  import cycle:
  `AllNormalFormFalse -> CaseObstructions -> PhaseExtraction -> AllNormalFormFalse`
  and by the residual callback sorry in `PhaseExtraction`
  (`binary_ring_impossibility_residual_callbacks`).
  Ruled out at Explorations 2 and 7.

- Direct “raw boundary reversal on `(left t, t)` implies immediate contradiction”
  is too weak.
  The opposite crossings alone do not control the outer neighbor `left²(t)`.
  Ruled out at Explorations 4 and 5.

### Obstructions

- The cross family is blocked on a sharper local lemma:
  after the last right-side activity, `right(t)` must be frozen and
  `left²(t)` must have controlled parity / restored value before the later
  `left(t) -> t` crossing. This is not implied by the current
  `LeftCrossPhaseHardResidue` packaging alone.

- `hk_last` splits into an easy non-adjacent subbranch and a hard adjacent
  subbranch. The easy subbranch is now closed by `hk_last_not_near_false`;
  the adjacent subbranch remains open.

### Building blocks

- Extracted explicit endgame residue families inside
  `AllNormalFormFalse.lean`:
  `LeftSameHardResidue`, `RightSameHardResidue`,
  `LeftCrossPhaseHardResidue`, `LeftCrossTerminalHardResidue`,
  `RightCrossPhaseHardResidue`, `RightCrossTerminalHardResidue`,
  `LeftCrossHardResidue`, `RightCrossHardResidue`.

- Cross sharp reductions now package the cross branches into those explicit
  residue families:
  `left_cross_sharp_reduction`,
  `right_cross_sharp_reduction`.

- New phase helper:
  `left_cross_phase_len2_suffixes_or_ec_live`.

- New `hk_last` helper:
  `hk_last_not_near_false`.

### Known reformulations

- Load-bearing:
  `hard_endgame_false` is no longer “the theorem tail”; it is a named local
  theorem over explicit residue families. This is the default representation
  for future work.

- Load-bearing:
  the cross/no-after branches are instances of a missing local
  “no one-sided t-bounce phase” obstruction rather than generic geometry.

- Medium confidence:
  the cross phase branch can be seen as opposite one-sided traversals through
  the same pivot endpoint, but the usable contradiction still requires
  interval control after the last right-side activity.

## Exploration 1

### Strategy
Extract the sprawling final branch structure into explicit residue types and
named reductions inside `AllNormalFormFalse.lean`.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  extracted same-start hard residues and later cross hard residues;
  isolated the live frontier to a single local theorem `hard_endgame_false`.

## Exploration 2

### Strategy
Look for a shortcut through the old 330-line sorry-free ANF rewrite
(`d56c9ff`) and its use of `subThreshold_obstruction`.

### Outcome
FAILED

### Failure Constraint
The old route depends on `CaseObstructions`, but importing it here recreates
the cycle
`AllNormalFormFalse -> CaseObstructions -> PhaseExtraction -> AllNormalFormFalse`.

### What This Rules Out
Any approach that tries to close the current theorem by directly importing
`CaseObstructions` or the old rewrite theorem without first restructuring the
dependency graph.

### Surviving Structure
- STRUCTURAL RESULTS:
  the old rewrite does certify that a non-local obstruction theorem would close
  the file immediately if it were available below the cycle.

### Concrete Artifacts
- COMPUTED EXAMPLES:
  old commit `d56c9ff` imports `CaseObstructions` directly and closes
  `allNormalForm_false` via `subThreshold_obstruction`.

## Exploration 3

### Strategy
Try to prove `left_cross_phase_false` directly from the extracted cross-phase
data using the existing contradiction libraries (`canonical_gap_backtrack_ec`,
`BAFArcAdj`, `BoundaryShadowEntry`, contiguous-run EC).

### Outcome
FAILED

### Failure Constraint
The extracted data supplies opposite one-sided traversals, but not the exact
4-step backtrack witness or the contiguous-run / global-min-gap hypotheses
required by the existing libraries.

### What This Rules Out
Any direct proof of the cross phase branch that only repackages the existing
libraries without strengthening the branch data.

### Surviving Structure
- STRUCTURAL RESULTS:
  the cross phase branch really is a boundary-edge reversal phenomenon;
  the mismatch is in the missing witness / interval control, not in the branch
  decomposition.

## Exploration 4

### Strategy
Formulate a direct left-binary boundary reversal lemma on the edge `(left t, t)`
from opposite crossings alone.

### Outcome
FAILED

### Failure Constraint
The opposite crossings alone do not force the same local context at `left(t)`
because the outer neighbor `left²(t)` may still change between them.

### What This Rules Out
Any “immediate contradiction from raw opposite crossings of `(left t, t)`”
argument that does not add control on `left²(t)`.

### Surviving Structure
- STRUCTURAL RESULTS:
  the right local edge for the cross obstruction is `(left t, t)`;
  the missing ingredient is outer-neighbor parity / interval control.

## Exploration 5

### Strategy
Try to get the missing outer-neighbor control directly from the later
left-sided phase data already packaged in the cross branch.

### Outcome
FAILED

### Failure Constraint
`phase0` gives only one guaranteed `left(t)` firing and does not by itself
provide the interval after the last right-side activity where `right(t)` is
frozen and `left²(t)` parity is controlled.

### What This Rules Out
Any proof that expects the current `LeftCrossPhaseHardResidue` data alone to
force the desired boundary-context equality at `left(t)`.

### Surviving Structure
- STRUCTURAL RESULTS:
  the needed theorem is sharper:
  “last right-side activity + left-sided bounded excursion -> boundary context
  recurs”.

## Exploration 6

### Strategy
Switch to branch 1 (`hk_last`) and prove the easy non-adjacent subbranch as a
standalone local lemma.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `hk_last_not_near_false` now closes the case where
  `p = moverAt k_out` is not adjacent to the step-0 mover.

## Exploration 7

### Strategy
Attack the hard adjacent `hk_last` subbranch and re-check whether the old
sorry-free obstruction route can be pulled below the import cycle.

### Outcome
STALLED

### Failure Constraint
The only clean bypass still available is blocked twice:
1. `CaseObstructions` cannot be imported here because of the current cycle.
2. The callback-free wrapper in `PhaseExtraction`
   (`subThreshold_binary_core_false_residual`) still sits behind the same
   cycle and depends on the residual callback theorem
   `binary_ring_impossibility_residual_callbacks`, which is itself still a
   `sorry`.

### What This Rules Out
Any “small refactor” shortcut that tries to expose `subThreshold_obstruction`
or `subThreshold_binary_core_false_residual` without first solving the
`PhaseExtraction` residual callback theorem or restructuring the dependency
graph more substantially.

### Surviving Structure
- STRUCTURAL RESULTS:
  `hk_last` is now cleanly split:
  easy non-adjacent case proved,
  hard adjacent case isolated.

### What Would Unblock This
- A lower-level, callback-free obstruction theorem below the
  `PhaseExtraction -> AllNormalFormFalse` edge, or
- a direct proof of the hard adjacent `hk_last` case in this file.

## Synthesis after exploration 7

- The residue extraction work was worthwhile: both the cross family and
  `hk_last` now fail for sharply identified reasons rather than diffuse tail
  complexity.
- The cross/no-after difficulty is consistently the same missing object:
  a local one-sided boundary obstruction with interval control.
- The import-cycle shortcut is not “almost available”; it is blocked by a real
  residual theorem upstream, so local proof work remains necessary unless the
  dependency graph is deliberately refactored.

## Exploration 8

### Strategy
Attack the hard adjacent `hk_last` branch directly by splitting on the first
local fire among `{left t, t, right t}` and proving the `t`-first subcase.

### Outcome
STALLED

### Failure Constraint
The `t`-first subcase closes cleanly, but the remaining “neighbor-first”
subcase still needs a new local argument. After extracting the first local fire
`smin`, the unresolved goal is exactly:

- `gc.moverAt smin = left t ∨ gc.moverAt smin = right t -> False`

under the adjacent `hk_last` hypotheses.

### What This Rules Out
This rules out any claim that the hard adjacent `hk_last` case is a single
opaque obstruction. It really splits into:

- easy non-adjacent branch,
- easy adjacent-but-`t`-first branch,
- hard adjacent neighbor-first branch.

### Surviving Structure
- STRUCTURAL RESULTS:
  `hk_last_first_local_t_false` is proved.
- STRUCTURAL RESULTS:
  `hk_last_near_false` is now reduced to one genuinely unknown subgoal:
  the neighbor-first case.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `hk_last_near_i0_not_local` proves the step-0 mover is not in
  `{left t, t, right t}` under adjacency.
- STRUCTURAL RESULTS:
  `hk_last_first_local_t_false` proves the first-local-fire-is-`t` subcase.
- TOOLS:
  local `Local`-set minimization pattern for the first fire in a specified
  neighborhood.

### What Would Unblock This
- A local theorem for the neighbor-first case:
  if the first fire in `{left t, t, right t}` is `left t` (or symmetrically
  `right t`) under the adjacent `hk_last` hypotheses, then False.

### Key Parameters
- Hard branch only:
  `p = moverAt k_out` adjacent to `i₀ = moverAt 0`,
  `k_out` last step,
  `p` outside the 5-set.

### Open Questions
- Can the neighbor-first case be closed by a direct entry conflict at `left t`
  / `right t` using the first local fire and binary parity?
- Or does it need a small local “backup EC processor” lemma as suggested by the
  older notes?

## Exploration 9

### Strategy
Target the adjacent `hk_last` neighbor-first subgoal directly by splitting on
the first local fire in `{left t, t, right t}` and trying to force a closing
segment contradiction when the first local fire is a neighbor.

### Outcome
STALLED

### Failure Constraint
The first-local-fire decomposition works, but after the `t`-first case is
removed, the remaining hypothesis

- `gc.moverAt smin = left t ∨ gc.moverAt smin = right t`

still does not by itself control the outer neighbor (`left² t` on the left,
`right² t` on the right). So the simple “compare step 0 to the first local
neighbor fire” entry-conflict attempt does not go through: the boundary
processor’s full local context need not be preserved up to `smin`.

### What This Rules Out
This rules out the naïve adjacent-case strategy:

- “first local fire is a neighbor” + “step-0 mover is not local” ->
  immediate entry conflict at that neighbor.

Any proof of the neighbor-first case needs extra control on the outer side of
the local triple.

### Surviving Structure
- STRUCTURAL RESULTS:
  `hk_last_near_false` is now explicitly reduced to the neighbor-first branch.
- STRUCTURAL RESULTS:
  the first-local-fire framework is sound and reusable.

### Concrete Artifacts
- TOOLS:
  `Local := {k | moverAt k = left t ∨ moverAt k = t ∨ moverAt k = right t}`
  and the minimization pattern using `Finset.min'`.
- STRUCTURAL RESULTS:
  `hk_last_near_i0_not_local`
  `hk_last_first_local_t_false`
  partial `hk_last_near_false`

### What Would Unblock This
- A local lemma for the neighbor-first case that also controls the outer
  neighbor after step 0, e.g. a “backup EC processor” lemma or a theorem that
  the closing segment after a neighbor-first local fire forces one side to stay
  frozen until the next `t`-event.

### Key Parameters
- `k_out` is the last step
- `p = moverAt k_out` is adjacent to `i₀ = moverAt 0`
- `i₀ ∉ {left t, t, right t}`
- first local fire `smin` is a neighbor

### Open Questions
- Can the neighbor-first case be split further into the problematic subcases
  `i₀ = left² t` and `i₀ = right² t`, with the non-matching cases closed
  immediately?
- Is the old “backup EC processor” idea at the opposite neighbor actually the
  right local finish here?

## Exploration 10

### Strategy
Refine the adjacent `hk_last` neighbor-first case by extracting the first later
`t`-fire after the first local neighbor fire, so the remaining unknown is
stated over an explicit interval.

### Outcome
STALLED

### Failure Constraint
The extraction succeeds, but the actual contradiction still needs a local
lemma on the interval from the first local neighbor fire `smin` to the first
later `t`-fire `s_t`. The current branch data does not yet prove enough about
the outer neighbor on that interval to force an entry conflict.

### What This Rules Out
This rules out any proof of the adjacent neighbor-first case that stays at the
coarse level “a neighbor fires before `t`”. The usable theorem must mention the
interval `[smin, s_t)` explicitly.

### Surviving Structure
- STRUCTURAL RESULTS:
  the hard adjacent case is now reduced to a theorem over:
  - first local neighbor fire `smin`
  - first later `t`-fire `s_t`
  - no `t` in `(smin, s_t)`

### Concrete Artifacts
- TOOLS:
  `ST := {k | smin.val < k.val ∧ moverAt k = t}` and `s_t := ST.min' ...`
  extraction pattern inside `hk_last_near_false`.
- STRUCTURAL RESULTS:
  the unknown subgoal is now pushed into the local theorem
  `hk_last_neighbor_first_false`.

### What Would Unblock This
- A lemma controlling the boundary context on `[smin, s_t)`, e.g.:
  the outer neighbor cannot change in a way that prevents an EC at the first
  later `t`-fire, or a backup EC at the opposite binary neighbor.

### Key Parameters
- `smin` = first fire in `{left t, t, right t}`
- `gc.moverAt smin = left t ∨ gc.moverAt smin = right t`
- `s_t` = first later `t`-fire after `smin`

### Open Questions
- Is the right invariant on `[smin, s_t)` an outer-neighbor parity statement,
  or a frozen-opposite-neighbor statement?
- Can the left-first and right-first cases be mirrored once one side is solved?

## Exploration 11

### Strategy
Split `hk_last_neighbor_first_false` into the two structurally different
 neighbor-first cases:
 1. the opposite neighbor appears before the next `t`-fire;
 2. only one neighbor appears before the next `t`-fire (one-sided until `t`).

### Outcome
STALLED

### Failure Constraint
The decomposition is correct and now explicit in Lean, but each branch still
needs its own local contradiction:

- opposite-neighbor-before-`t`: some local back-and-forth / context-repeat
  theorem on the interval `(smin, s_t)`;
- one-sided-until-`t`: a one-sided closing-segment contradiction.

### What This Rules Out
This rules out treating the neighbor-first branch as one homogeneous case.
Any successful proof must choose between:

- a two-neighbor local oscillation argument, or
- a one-sided closing-segment argument.

### Surviving Structure
- STRUCTURAL RESULTS:
  `hk_last_neighbor_first_false` now splits into four explicit subcases:
  - left-first then right-before-`t`
  - left-first one-sided-until-`t`
  - right-first then left-before-`t`
  - right-first one-sided-until-`t`
- STRUCTURAL RESULTS:
  the “one-sided until `t`” branches already produce no-fire lemmas for the
  opposite neighbor on `[smin, s_t)`.

### Concrete Artifacts
- TOOLS:
  `SR`/`SL` Finset minimization patterns for the first opposite-neighbor fire.
- STRUCTURAL RESULTS:
  `hright_nofire_until_t` and `hleft_nofire_until_t` are now explicit
  hypotheses in the one-sided subcases.

### What Would Unblock This
- A local theorem of one of these two forms:
  1. opposite-neighbor-before-`t` + first-fire ordering -> EC/False
  2. one-sided-until-`t` + closing at `k_out` last -> EC/False

### Key Parameters
- `smin`: first local neighbor fire
- `s_t`: first later `t`-fire
- optional `sR` / `sL`: first opposite-neighbor fire before `s_t`

### Open Questions
- Does the opposite-neighbor-before-`t` branch directly yield a local boundary
  backtrack witness?
- Does the one-sided-until-`t` branch force the same one-sided obstruction seen
  in the cross/no-after residues?

## Exploration 12

### Strategy
Prove the left-first / one-sided-until-`t` subcase of
`hk_last_neighbor_first_false` by splitting again on whether `left(t)` fires a
second time before the first later `t`-fire.

### Outcome
STALLED

### Failure Constraint
Two meaningful sub-subcases now exist:

- if `left(t)` fires again before `t`, the branch should go through
  `zeroSide_ec`;
- if `left(t)` does not fire again and `s_t > smin + 1`, the branch should go
  through `post_firing_match_ec`;
- only the immediate branch `s_t = smin + 1` remains genuinely open on this
  side.

I have written the Lean packaging for both successful routes, but it remains
unverified because the turn’s instruction was not to build.

### What This Rules Out
This rules out treating the one-sided-left branch as a single primitive
obstruction. It naturally splits into:

- repeat-left before `t`,
- no-repeat-left before `t`,
- immediate `left -> t`.

### Surviving Structure
- STRUCTURAL RESULTS:
  the one-sided-left branch is now almost completely reduced to
  `zeroSide_ec` / `post_firing_match_ec`.
- STRUCTURAL RESULTS:
  the only unresolved residue on that side is the immediate `left -> t`
  branch.

### Concrete Artifacts
- TOOLS:
  first-later-left extraction via `SL.min'`.
- STRUCTURAL RESULTS:
  explicit `hL_diff` built from
  `gc.state_ne_at_moverAt smin` plus no-fire preservation to the first later
  left fire.

### What Would Unblock This
- Verification of the new subcase code, and then a local lemma for the
  immediate `left -> t` branch.

### Key Parameters
- left-first only
- no `right(t)` before `s_t`
- split on `∃ sL, smin < sL < s_t ∧ moverAt sL = left t`

### Open Questions
- Does the immediate `left -> t` branch already force an EC at `t` from step 0?
- Once the left-first branch is verified, is the right-first branch a literal
  mirror copy?

## Exploration 13

### Strategy
Refine the immediate `left -> t` branch in the left-first / one-sided-until-`t`
case by making the successor relation explicit and putting both privileged
steps on the table.

### Outcome
STALLED

### Failure Constraint
The branch is now explicit enough to state the local problem cleanly:

- `s_t = smin + 1`
- `gc.configs.get s_t = move sys (gc.configs.get smin) (left t)`
- `left t` is privileged at `smin`
- `t` is privileged at `s_t`

But the contradiction still needs one more local step: either show this
immediate `left -> t` handoff cannot occur under the `hk_last` boundary
conditions, or turn it into a direct entry conflict.

### What This Rules Out
This rules out treating the immediate branch as merely “the leftover after
post-firing EC fails”. It is its own local transition problem.

### Surviving Structure
- STRUCTURAL RESULTS:
  the immediate branch is now reduced to a single local handoff
  `left t -> t` with no time gap.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `hs_t_succ`, `hs_t_eq`, `hsmin_step`, `hsmin_priv`, `hs_t_priv`.

### What Would Unblock This
- A local theorem about immediate privileged handoff
  `left t` at step `k` followed by `t` at step `k+1`
  under the `hk_last` boundary setup.

### Key Parameters
- left-first only
- no right before `s_t`
- `s_t = smin + 1`

### Open Questions
- Can `privileged_of_same_context` / `move_at_mover_eq_of_local_eq` close this
  immediate handoff directly?
- Or does it need a one-step boundary contradiction specialized to
  `left t -> t`?

## Exploration 14

### Strategy
Extract the immediate `left(t) -> t` handoff into its own theorem so the
remaining `sorry` is a single local transition lemma.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  new theorem stub
  `hk_last_immediate_left_t_false`
  in `AllNormalFormFalse.lean`.
- STRUCTURAL RESULTS:
  the left-first / one-sided-until-`t` branch now routes all non-immediate
  cases to existing EC lemmas and delegates only the immediate handoff to the
  new theorem.

## Exploration 15

### Strategy
Stop treating the immediate `left -> t` handoff as a raw privileged-step
problem. Rebuild it through the normal-phase machinery and reduce it to the
actual residual prefix shape. Then mirror the same reduction on the right.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `hk_last_immediate_left_t_false` no longer leaves the branch at the raw
  handoff statement. It now proves:
  immediate `left -> t`
  `=>`
  either EC or the exact prefix residual
  `left²(t) -> left(t) -> t`,
  packaged as `hk_last_immediate_left_t_prefix_false`.
- STRUCTURAL RESULTS:
  the right-one-sided mirror is now reduced the same way:
  immediate `right -> t`
  `=>`
  either EC or the exact prefix residual
  `right²(t) -> right(t) -> t`,
  packaged as `hk_last_immediate_right_t_prefix_false`.
- STRUCTURAL RESULTS:
  the right-first / one-sided-until-`t` branch no longer has a raw theorem-body
  `sorry`; the long-gap and repeated-right subcases now route through
  `post_firing_match_ec` / `zeroSide_ec_symm`, matching the left side.

### What This Rules Out
- The immediate handoff is not the right abstraction boundary.
- The real unresolved object is the 3-step prefix residual on each side.

### New Frontier
- `hk_last_immediate_left_t_prefix_false`
- left-first opposite-neighbor-before-`t`
- `hk_last_immediate_right_t_prefix_false`
- right-first opposite-neighbor-before-`t`
- final `hard_endgame_false`

## Exploration 16

### Strategy
Open up `hk_last_immediate_left_t_prefix_false` itself instead of leaving it as
a bare theorem stub. Use `hk_last` and `next_mover_is_local` to force the first
predecessor shape of the `left² -> left -> t` prefix.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  if `prev = 0`, then the cycle start mover is `left²(t)` and the last mover
  `k_out` is forced to be `left³(t)`.
- STRUCTURAL RESULTS:
  if `prev > 0`, then the predecessor of `prev` is forced to be
  `left²(t)` or `left³(t)` by `gc.next_mover_is_local`.

### What This Rules Out
- The `left² -> left -> t` prefix is not an isolated 3-step object anymore.
- Any completion must account for its immediate predecessor, and in the wrap
  case the predecessor is pinned to `k_out = left³(t)`.

### New Frontier
- base wrap case:
  `k_out = left³(t)`, `0 = left²(t)`, `1 = left(t)`, `2 = t`
- predecessor extension case:
  predecessor of `left²(t)` is `left²(t)` or `left³(t)`

## Exploration 17

### Strategy
Treat the wrap base case honestly as a prefix across the wrap, not a closed
4-step loop. Extract the first real events after the prefix: the first later
`right(t)` fire and the first later `t` fire after index `2`.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  in the wrap base branch of `hk_last_immediate_left_t_prefix_false`, the proof
  now extracts:
  - `s2`: the first later `t` fire after index `2`
  - `sR`: the first later `right(t)` fire after index `2`
  - the strict order split `sR < s2 ∨ s2 < sR`
- STRUCTURAL RESULTS:
  the “wrap base” is no longer treated as a fake closed 4-step cycle.
  The frontier is now the genuine post-prefix branch ordering.

### What This Rules Out
- A direct contradiction from the 4-step block alone is not the right target.
- The next contradiction depends on how the first later `right(t)` and the
  first later `t` interleave after the prefix.

### New Frontier
- wrap base + `sR < s2`
- wrap base + `s2 < sR`
- predecessor-extension case

## Exploration 18

### Strategy
Take the `s2 < sR` wrap-base continuation seriously as a one-sided `t`-to-`t`
segment. Extract the post-prefix start at index `3` and record whether the next
`t` is immediate or whether there is a genuine interval with zero right-side
activity up to the next `t`.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  in the wrap-base proof, `s2 < sR` now yields explicit data:
  - `post = s_t + 1`
  - either `post = s2` (immediate `t -> t`)
  - or `post < s2` together with
    `intervalFireCount (right t) post s2 = 0`
- STRUCTURAL RESULTS:
  the branch is now in the correct form for a one-sided phase argument,
  rather than a raw order comparison.

### New Frontier
- wrap base + immediate `t -> t` at `post = s2`
- wrap base + one-sided interval `post < s2` with zero right-side activity
- wrap base + `sR < s2`
- predecessor-extension case

## Exploration 19

### Strategy
Pause local drilling and assess whether `hk_last` is still the right front.

### Outcome
ASSESSMENT

### hk_last depth
- Current live `sorry`s in the `hk_last` subtree:
  - `hk_last_immediate_left_t_prefix_false`
  - `hk_last_immediate_right_t_prefix_false`
  - left-first opposite-neighbor-before-`t`
  - right-first opposite-neighbor-before-`t`
- So `hk_last` currently accounts for 4 of the 6 live `sorry`s in the file.
- The remaining 2 live `sorry`s are outside the `hk_last` subtree:
  - `hk_last`-independent right-prefix theorem mirror
    already counted above
  - final `hard_endgame_false`

### Progress signal
- The `hk_last` tree has become much better structured:
  - repeated-left / repeated-right subcases are closed
  - long-gap one-sided subcases are closed
  - immediate branches are reduced to explicit prefix theorems
  - wrap base is reduced to first-later-`t` / first-later-`right` order data
- But the remaining branches are no longer simple EC applications.
  They keep reducing to “one more event after the current prefix” rather than
  collapsing directly.

### Interpretation
- `hk_last` is getting more explicit, not more chaotic.
- But the surviving kernels are now clearly not routine uses of the existing
  EC lemmas.
- The current pattern suggests the right missing object is a stronger umbrella
  lemma for `hk_last`, not more theorem-local case peeling.

### Recommendation
- Do not abandon `hk_last` entirely.
  It is not flailing; it has been reduced to a small number of explicit kernels.
- But do stop pursuing it via raw branch-by-branch theorem-local splitting.
- Best next move:
  write one stronger extracted lemma that covers the `hk_last` continuation
  patterns uniformly, e.g.:
  - wrap-prefix continuation theorem:
    `left³,left²,left,t` plus the first later `t/right` ordering is impossible
  - or symmetric pair:
    `hk_last_wrap_left_false` / `hk_last_wrap_right_false`
- If that stronger lemma does not stabilize quickly, then the next best pivot
  is back to the cross family, because those branches are already packaged at a
  similarly explicit level and no longer depend on further `hk_last` recursion.

## Exploration 20

### Strategy
Prune the dead-end `hk_last` theorem-local case tree and get one empirical read
from the existing cycle-search infrastructure before doing more proof work.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  pruned the unfinished `hk_last` subtree in `AllNormalFormFalse.lean` down to:
  - `hk_last_not_near_false`
  - `hk_last_near_i0_not_local`
  - `hk_last_first_local_t_false`
  - a single `hk_last_near_false` sorry
  - `hard_endgame_false`
- COMPUTED EXAMPLES:
  file length dropped from `9363` lines to `8323` lines.
- COMPUTED EXAMPLES:
  added and ran
  `probes/hk_last_check.py`
  on default sub-threshold `n = 9` candidate state vectors:
  - `(2,2,2,4,3,3,3,3,3)`: `screened_cycles=200`, `hk_last_hits=0`
  - `(2,2,2,4,4,3,3,3,3)`: `screened_cycles=136`, `hk_last_hits=0`
  - `(2,2,2,5,3,3,3,3,3)`: `screened_cycles=86`, `hk_last_hits=0`

### Interpretation
- In the screened locally consistent good cycles on the default `n=9`
  sub-threshold candidate vectors, `hk_last` did not occur at all.
- That does not prove the branch impossible, but it is real evidence that
  `hk_last` is likely a pathological/non-generic frontier rather than the
  best first proof target.

### Recommendation
- Keep the Lean file pruned.
- Use the script result as a signal to deprioritize `hk_last` and pivot back to
  one of the non-`hk_last` top-level hard branches unless a much stronger
  `hk_last` umbrella theorem becomes obvious.

## Exploration 21

### Strategy
Expand the empirical `hk_last` check beyond the three default `n=9` vectors:
scan all sub-threshold multisets at `n = 5..9` with a small per-multiset cycle
budget, using the existing `p2_good_cycle_search` enumerator.

### Outcome
PARTIAL BUT DECISIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  total sub-threshold multiset counts:
  - `n=5`: `7`
  - `n=6`: `17`
  - `n=7`: `36`
  - `n=8`: `73`
  - `n=9`: `147`
- COMPUTED EXAMPLES:
  expanded script run on all multisets started from
  `probes/hk_last_check.py`
- COMPUTED EXAMPLES:
  completed summaries before truncating the long run:
  - `n=5`: `screened_cycles=311`, `hk_last_hits=0`
  - `n=6`: `screened_cycles=826`, `hk_last_hits=707`
  - `n=7`: `screened_cycles=1661`, `hk_last_hits=2986`
- COMPUTED EXAMPLES:
  early `n=8` output already showed many `hk_last` hits in the first dozens of
  multisets, so the “hk_last never occurs” hypothesis is already dead before
  finishing `n=8`/`n=9`.

### Interpretation
- The branch condition `hk_last` is emphatically **not** impossible in general.
- So the promising strategy is **not** “prove `hk_last_near_false` by proving
  the hypothesis cannot hold”.
- The right question is back to a structural one:
  why should the specific `hk_last` branch extracted inside the Lean proof be
  impossible under the additional ANF / residue hypotheses?

### Recommendation
- Keep the pruning.
- Do not spend more time on a global “`hk_last` never occurs” route.
- Pivot the proof effort away from that meta-strategy.

## Exploration 22

### Strategy
Diagnose one concrete high-frequency `hk_last` family computationally instead of
counting it. Pick the strongest `n=6` sub-threshold multiset with many
`hk_last` hits, enumerate its `hk_last` cycles, and classify how the existing
completion/verifier pipeline kills them.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_diagnosis.py`
- COMPUTED EXAMPLES:
  target chosen automatically:
  `state_counts = (2,2,2,2,2,10)`, product `320`, with `53` `hk_last` hits in
  the scan budget.
- COMPUTED EXAMPLES:
  analyzed `53` concrete `hk_last` instances for that family.
- COMPUTED EXAMPLES:
  every one of the `53` instances was killed **before SMT completion** by the
  forced-cycle screen:
  `forced_recurrent_component`
- COMPUTED EXAMPLES:
  the recurring signature was extremely rigid:
  - pivot `t = 2`
  - `mover[k_out] = 5`
  - `mover[0] = 0`

### Interpretation
- The computational killer is not “entry conflict on the good cycle”.
- It is a **global forced recurrent component / shadow-style obstruction**:
  the partial transition table determined by the `hk_last` cycle already forces
  a bad recurrent SCC outside the cycle.
- This is the strongest insight so far about `hk_last`.

### Recommendation
- The right proof strategy for `hk_last` is now much more likely to be a
  shadow/forced-SCC theorem than a local EC theorem.
- If `hk_last` is revisited in Lean, it should be revisited through a global
  forced-cycle obstruction, not through more local mover-word splitting.

## Exploration 23

### Strategy
Search the existing Lean lower-bound infrastructure for theorems that already
formalize the computational diagnosis:
forced recurrent component / shadow-style trap implies contradiction.

### Outcome
PARTIAL MATCH

### Concrete Artifacts
- FOUND:
  `LeanMn.LowerBound.MNU.ShadowTrap`
- FOUND:
  `LeanMn.LowerBound.MNU.shadowTrap_not_converges`
- FOUND:
  specific shadow-trap constructions in `CaseObstructions.lean`
- FOUND:
  canonical shadow construction and
  `shadow_cycle_mirror_theorem` in `Shadow/Theorem.lean`

### Missing bridge
- NOT FOUND:
  a generic theorem of the form
  “forced recurrent component implies `ShadowTrap`”
- NOT FOUND:
  a generic theorem of the form
  “forced recurrent component implies False”

### Interpretation
- The codebase already has the *target* obstruction object (`ShadowTrap`) and
  the final contradiction (`shadowTrap_not_converges`).
- The missing mathematical step is a new bridge from the `hk_last`
  determined-entry structure to that object.

### Recommendation
- If `hk_last` is pursued again in Lean, the next theorem to write should be a
  bridge theorem:
  `hk_last_forced_component_false` or
  `hk_last_forced_component_shadowTrap`.

## Exploration 24

### Strategy
Extract an actual off-cycle directed cycle from one diagnosed `hk_last`
instance and compare it directly with the Lean `ShadowTrap` fields.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_shadowtrap_extract.py`
- COMPUTED EXAMPLES:
  target witness:
  - `state_counts = (2,2,2,2,2,10)`
  - pivot `t = 2`
  - `k_out = 11`
  - mover word
    `(0,1,2,3,4,5,0,1,2,3,4,5)`
- COMPUTED EXAMPLES:
  extracted an off-cycle directed cycle of length `12` inside a bad SCC of size
  `40`:
  - `(0,1,1,0,1,1) --P1-->`
  - `(0,0,1,0,1,1) --P4-->`
  - `(0,0,1,0,0,1) --P3-->`
  - `(0,0,1,1,0,1) --P2-->`
  - `(0,0,0,1,0,1) --P5-->`
  - `(0,0,0,1,0,0) --P0-->`
  - `(1,0,0,1,0,0) --P1-->`
  - `(1,1,0,1,0,0) --P4-->`
  - `(1,1,0,1,1,0) --P3-->`
  - `(1,1,0,0,1,0) --P2-->`
  - `(1,1,1,0,1,0) --P5-->`
  - `(1,1,1,0,1,1) --P0-->`
  - back to `(0,1,1,0,1,1)`

### ShadowTrap fit
- This directed cycle already has the right computational shape for
  `ShadowTrap`:
  - nonempty list of off-cycle configs
  - distinct configs
  - closed by explicit privileged moves
- So the Lean bridge does not need to prove a vague SCC statement.
  It can aim directly for:
  `hk_last hypotheses -> ∃ explicit bad cycle -> ShadowTrap`

### Recommendation
- The bridge theorem should be formulated as explicit cycle data, not as an
  abstract SCC theorem.

## Exploration 25

### Strategy
Test whether the explicit bad-cycle / `ShadowTrap` shape extracted from one
`n=6` `hk_last` witness persists at larger `n`, or whether it was only an
`n=6` artifact.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  parameterized and ran
  `probes/hk_last_shadowtrap_extract.py`
  at `n=7` and `n=8`
- COMPUTED EXAMPLES:
  `n=7` target:
  - `state_counts = (2,2,2,2,2,2,14)`
  - picked witness with pivot `t = 2`, `k_out = 13`
  - extracted off-cycle bad cycle length `14`
- COMPUTED EXAMPLES:
  `n=8` target:
  - `state_counts = (2,2,2,2,2,2,2,22)`
  - picked witness with pivot `t = 2`, `k_out = 15`
  - extracted off-cycle bad cycle length `16`

### Cross-n pattern
- In all three checked cases (`n=6,7,8`), the extracted off-cycle bad cycle has
  length exactly `2n`.
- In all three checked cases, the bad cycle is explicit and closed under chosen
  forced moves.
- So the bridge shape is not an `n=6` accident; it looks genuinely stable.

### Interpretation
- The likely generic theorem shape is now:
  `hk_last hypotheses -> explicit off-cycle bad cycle of length 2n -> ShadowTrap`
- This is much stronger evidence than the earlier SCC diagnosis alone.

### Shadow machinery comparison
- For `n=6`, the extracted bad-cycle mover word first half
  `[1,4,3,2,5,0]`
  is a rotation of the existing `shadowPerm` order
  `[2,5,0,1,4,3]`.
- For `n=7`, the extracted first half
  `[4,3,6,0,1,2,5]`
  is a rotation of
  `[3,6,0,1,2,5,4]`.
- For `n=8`, the extracted first half
  `[3,6,5,4,7,0,1,2]`
  is a rotation of
  `[4,7,0,1,2,3,6,5]`.

So the bad-cycle mover pattern is not merely “shadow-like”; it appears to be
the same shadow permutation `σ`, up to rotation.

### Decision
- Use the existing shadow machinery.
- But probably **not** by direct application of
  `shadow_cycle_mirror_theorem`, because that theorem assumes a
  `WaterfallCycle`.
- The better reuse point is lower-level:
  `shadowPerm` / `ShadowTrap` / `shadowTrap_not_converges`.

## Exploration 26

### Strategy
Check whether the diagnosed `hk_last` **good cycles themselves** already satisfy
the `WaterfallCycle` definition, rather than only producing a shadow-style bad
cycle afterwards.

### Outcome
BREAKTHROUGH

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_waterfall_check.py`
- COMPUTED EXAMPLES:
  for the chosen `hk_last` witnesses at `n=6,7,8`, the good cycle itself
  satisfied the waterfall-form config equation:
  - `n=6`: `waterfall=True`, `highVal=(1,1,1,1,1,1)`
  - `n=7`: `waterfall=True`, `highVal=(1,1,1,1,1,1,1)`
  - `n=8`: `waterfall=True`, `highVal=(1,1,1,1,1,1,1,1)`
- COMPUTED EXAMPLES:
  the mover word in those witnesses is exactly the uniform sweep
  `(0,1,2,...,n-1)` repeated twice, i.e. length `2n`.

### Interpretation
- This is much stronger than the earlier shadow-cycle bridge.
- The computational evidence now points to:
  `hk_last hypotheses -> WaterfallCycle`
- If that can be formalized, the whole branch collapses immediately via the
  already proved `shadow_cycle_mirror_theorem`.

### Recommendation
- Promote the main `hk_last` target from:
  `hk_last -> ShadowTrap`
  to:
  `hk_last -> WaterfallCycle`
- Then use the existing theorem pipeline:
  `shadow_cycle_mirror_theorem` / `no_valid_sweep_system`

## Exploration 27

### Strategy
Test whether `hk_last -> WaterfallCycle` is actually generic, or whether the
waterfall witnesses seen so far were a thin special subfamily.

### Outcome
CORRECTION

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_sweep_diagnosis.py`
- COMPUTED EXAMPLES:
  for the strongest `hk_last` families at `n=6,7,8`, **every** screened
  `hk_last` instance had the same first-half mover word:
  - `n=6`: `(0,1,2,3,4,5)`
  - `n=7`: `(0,1,2,3,4,5,6)`
  - `n=8`: `(0,1,2,3,4,5,6,7)`
- COMPUTED EXAMPLES:
  but only a tiny fraction were full double sweeps / full waterfall cycles:
  - `n=6`: `double_sweep_hits=1` out of `53`
  - `n=7`: `double_sweep_hits=2` out of `110`
  - `n=8`: `double_sweep_hits=3` out of `177`
- COMPUTED EXAMPLES:
  likewise only those same tiny fractions were `0/1`-only cycles.

### Interpretation
- `hk_last -> WaterfallCycle` is **not** the right generic theorem.
- What seems generic is weaker:
  the first half of the mover word is the forward sweep
  `(0,1,...,n-1)`.
- The full doubled sweep / waterfall form is a special subfamily, not the whole
  `hk_last` family.

### Recommendation
- Roll back the “direct WaterfallCycle” target as the main plan.
- Keep the shadow/forced-SCC direction as the generic `hk_last` strategy.
- The right generic bridge is still likely:
  `hk_last -> explicit forced bad cycle / ShadowTrap`
  rather than
  `hk_last -> WaterfallCycle`

## Exploration 28

### Strategy
Test the exact `shadowMatchIndex`-style bridge computationally:
for each extracted bad-cycle step `k`, does there exist the expected good-cycle
index `j = p + n` or `j = p` (depending on activity) such that the local triple
 and next-center value match exactly?

### Outcome
BREAKTHROUGH

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_match_index.py`
- COMPUTED EXAMPLES:
  the `shadowMatchIndex`-style correspondence held exactly for the chosen
  `hk_last` witnesses at all tested sizes:
  - `n=6`: `rotation=3`, correspondence `True`
  - `n=7`: `rotation=6`, correspondence `True`
  - `n=8`: `rotation=5`, correspondence `True`

### Interpretation
- `hentryCore` is not just a plausible abstraction.
- The computational data says the extracted bad cycle already satisfies the
  exact local-context bridge used in `canonicalShadow_entry_of_local_context`,
  up to rotation.
- This is the strongest evidence yet that the remaining `closed` proof can be
  obtained by adapting the existing shadow entry proof almost verbatim.

## Exploration 29

### Strategy
Sanity-check whether the `shadowMatchIndex` correspondence is genuinely generic
 across the full `hk_last` family, or whether the earlier positive result came
 from a special waterfall witness.

### Outcome
CRITICAL CORRECTION

### Concrete Artifacts
- COMPUTED EXAMPLES:
  on the full `n=6` target family `state_counts = (2,2,2,2,2,10)`,
  `hk_last_cycles = 53`
- COMPUTED EXAMPLES:
  only `1` of those `53` cycles satisfied the full
  `shadowMatchIndex`-style correspondence

### Interpretation
- The `shadowMatchIndex` bridge is **not** generic across the whole `hk_last`
  family.
- The earlier positive result came from the special waterfall/double-sweep
  subfamily, not the generic branch.
- So a direct adaptation of `canonicalShadow_entry_of_local_context` is too
  strong as the generic `hk_last` proof strategy.

### Recommendation
- Keep the `ShadowTrap` target.
- But do **not** assume the good-cycle-to-shadow local-context matching formula
  globally.
- The generic bridge remains the forced bad cycle / `ShadowTrap` route, not the
  stronger `shadowMatchIndex` route.

## Exploration 30

### Strategy
Check whether the weaker existential `hentryCore` statement is generic across
the full `hk_last` family, even though the simple formula `j = q or q+n` is not.

### Outcome
BREAKTHROUGH

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_hentry_exist_check.py`
- COMPUTED EXAMPLES:
  on the full `n=6` target family
  `state_counts = (2,2,2,2,2,10)`:
  - `hk_last_cycles = 53`
  - `bad_cycle_steps = 2645`
  - `failures = 0`

### Interpretation
- The strong explicit formula for `j` is not generic.
- But the weaker existential bridge **is** generic across the full tested
  `hk_last` family:
  for every bad-cycle step, there exists some good-cycle step `j` matching
  the local triple and next-center value.
- So `hentryCore` is indeed the right theorem. The missing piece is not
  existence, but finding the right abstract proof of that existence.

## Exploration 31

### Strategy
Search for a structural explanation of `hmatch_ne` that does not depend on the
failed explicit index formula. Check whether the shadow triples that actually
occur are always contained in the set of mover-step triples already realized by
the good cycle at the same processor.

### Outcome
PROMISING

### Concrete Artifacts
- COMPUTED EXAMPLES:
  on the full `n=6` target family `state_counts = (2,2,2,2,2,10)`:
  `hk_last_cycles = 53`
- COMPUTED EXAMPLES:
  for all `53/53` hk_last cycles, and for every processor `q`,
  the set of shadow triples seen at `q` was a subset of the mover-step triples
  seen in the good cycle at `q`.

### Interpretation
- This is a plausible generic proof mechanism for `hmatch_ne`:
  the shadow construction does not invent new local mover triples;
  it only reuses triples already realized on the good cycle.
- If formalized, this would give `matchSet.Nonempty` without needing the
  failed explicit `j` formula.

## Exploration 33

### Strategy
Inspect the actual matching-index pattern behind `hmatch_ne` across the full
`n=6` target family, instead of only checking existence.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_match_pattern.py`
- COMPUTED EXAMPLES:
  on all `53` hk_last cycles:
  - `2645` bad-cycle steps checked
  - match multiplicities were structured, not random
- COMPUTED EXAMPLES:
  the matching indices `j` are always q-firing steps
  (`j mod n = q` in the dominant cases)
- COMPUTED EXAMPLES:
  when multiple matches occur, they typically recur with period `2n`
  inside the longer good cycle

### Interpretation
- The right theorem target is not a single explicit formula for `j`.
- The right structural statement is:
  the shadow triple at `q` belongs to the mover-step triple language of `q`,
  and the matching indices are exactly q-firing steps carrying that triple.
- This gives a plausible path to `matchSet.Nonempty`:
  prove the shadow triple is one of the mover-step triples realized by `q`,
  then pick any q-firing step with that triple.

## Exploration 34

### Strategy
Check how large the mover-step triple language can be in the generic hk_last
family by measuring actual `fireCount(q)` distributions on the full `n=6`
target family.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  on all `53` hk_last cycles in the `n=6` target family
  `state_counts = (2,2,2,2,2,10)`, the fire counts vary widely.
- COMPUTED EXAMPLES:
  per-processor distributions:
  - `q = 0,1,2,3`: mostly `8`, with a few `2/4/6/10`
  - `q = 4`: mostly `10`, with some `8` and rare `12`
  - `q = 5`: ranges from `2` up to `14`, concentrated around `11/12`

### Interpretation
- Generic hk_last cycles are **not** near the `fireCount = 2` / double-sweep
  regime.
- So there are many mover steps at each processor and therefore many mover-step
  triples available.
- This supports the existential strategy:
  `matchSet.Nonempty` is plausible because the good cycle has a rich mover-step
  triple language, not because each processor only fires twice.

## Exploration 35

### Strategy
Diagnose `disjoint` computationally: compare the extracted shadow configs
against the good-cycle configs and search for the smallest coordinate projection
 that separates the two sets.

### Outcome
BREAKTHROUGH

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_disjoint_diagnosis.py`
- COMPUTED EXAMPLES:
  in all checked sizes `n=6,7,8`, the extracted shadow configs were
  `0/1`-valued only (`binary_only_bad=True`)
- COMPUTED EXAMPLES:
  the smallest separating coordinate set was consistently:
  `{0, n-4, n-3, n-2}`
  specifically:
  - `n=6`: `(0,2,3,4)`
  - `n=7`: `(0,3,4,5)`
  - `n=8`: `(0,4,5,6)`
- COMPUTED EXAMPLES:
  on that 4-coordinate projection, the good-cycle patterns are staircase-like
  (`0000, 0001, 0011, 0111, 1000, 1100, 1110, 1111`)
  while the shadow patterns are the complementary non-staircase set
  (`0010, 0100, 0101, 0110, 1001, 1010, 1011, 1101`)

### Interpretation
- This looks exactly like a rotated version of the existing
  `shadow_not_waterfall` / 4-position incompatibility argument.
- So `disjoint` is likely the most tractable remaining field:
  it should be provable by adapting the existing 4-position separation proof
  to the hk_last rotation.

## Exploration 32

### Strategy
Try the most naive existential proof of the new theorem
`hk_last_forward_sweep_mover_triples` by choosing `j` from `gc.fair q`.

### Outcome
FAILED BUT INFORMATIVE

### Failure Constraint
- `gc.fair q` only gives an arbitrary firing step of `q`.
- The three local-triple equalities are not true for an arbitrary firing of
  `q`; the existential `∃ j` requires a *special* firing step of `q`.

### Interpretation
- The right proof of `hentryCore` is not “pick any q-fire”.
- It really must go through the match-set nonemptiness argument:
  some q-firing step realizes the needed triple, but not every one does.

## Exploration 36

### Strategy
Formalize `disjoint` directly inside the `ShadowTrap` constructor by adapting
the rotated 4-position separator from Exploration 35.

### Outcome
PARTIAL PROGRESS WITH CORRECTION

### Concrete Artifacts
- LEAN REFACTOR:
  `lean/LeanMn/LowerBound/EntryConflict/AllNormalFormFalse.lean`
  no longer leaves `ShadowTrap.disjoint` as a raw constructor-level `sorry`.
- LEAN REFACTOR:
  the field now reduces to the named theorem
  `shadow_cfg_ne_good_of_rotated_separator`
  taking explicit data
  `shadowCfg kk = gc.configs.get j`.
- COMPUTED EXAMPLES:
  rechecking the broader raw `hk_last` family shows the earlier separator
  diagnosis from a chosen witness is not generic enough by itself:
  the proposed rotated 4-coordinate projection does not separate *all* raw
  `hk_last` cycles from their bad cycles.

### Interpretation
- The optimistic “just copy the rotated 4-bit separator” route is too strong if
  stated at the raw `hk_last` level.
- The Lean frontier is still improved:
  `disjoint` is now isolated to one concrete separator theorem over an exact
  equality `shadowCfg kk = gc.configs.get j`, instead of list plumbing inside
  the `ShadowTrap` constructor.
- The likely correct theorem has to use the stronger hard-endgame context, not
  just broad computational `hk_last` data.

## Exploration 37

### Strategy
Check whether the simplest proof path is to abandon the formula-shadow route
for `disjoint`/`closed` and instead construct the forced off-cycle bad cycle
directly, since the computational diagnosis already showed the generic hk_last
obstruction is a forced recurrent component.

### Outcome
STRATEGIC ASSESSMENT

### Interpretation
- Mathematically, the direct forced-component route is cleaner:
  it would package both remaining local obligations
  (`disjoint` and `hmatch_ne`) at once by building an explicit off-cycle
  bad cycle.
- In the current Lean codebase, that route would require a new existence theorem
  for the forced bad cycle from the hk_last hypotheses.
- No such theorem or supporting infrastructure currently exists in Lean.
- From the current file state, the smaller local patch is still the existing
  formula-shadow route:
  - `disjoint` reduced to `shadow_cfg_ne_good_of_rotated_separator`
  - `closed` reduced to `hmatch_ne : matchSet.Nonempty`
- So the direct forced-component route is probably the right *mathematical*
  theorem in the long run, but not the shortest immediate Lean path from the
  current proof state.

## Exploration 38

### Strategy
Assess whether the computational disjoint separator should be trusted only after
filtering down to cycles that satisfy the *full* `hard_endgame_false`
hypotheses, not just raw `hk_last`.

### Outcome
IMPORTANT SCOPE CORRECTION

### Interpretation
- The theorem branch we are proving lives under `_hn : 9 ≤ sys.rs.n`.
- Therefore the often-used `n=6` hk_last family is only heuristic evidence; it
  cannot literally satisfy the theorem hypotheses.
- The current Python search infrastructure does not evaluate the proof-level
  hypotheses `hall_normal : ∀ phase, isNormalFormGap ...` or the downstream
  hard-endgame branch reductions.
- So any separator found from the raw `hk_last` scans must be treated as
  suggestive only unless it is revalidated under stronger theorem-specific
  conditions.

## Exploration 39

### Strategy
Check whether the existing shadow theorem
`canonicalShadowDisjoint` can be reused directly to close the `disjoint`
field in the current hk_last `ShadowTrap`.

### Outcome
FAILED AS A DIRECT SHORTCUT

### Interpretation
- `canonicalShadowDisjoint` has type:
  `shadowDisjoint (canonicalShadowConstruction wc)`
  under the hypothesis `wc : WaterfallCycle sys`.
- The current hk_last proof does not have a generic `WaterfallCycle`; that
  route was already ruled out by the broader hk_last diagnostics.
- The current `shadowCfg` is not definitionaly `canonicalShadowConstruction wc`
  for any available `wc`.
- So `canonicalShadowDisjoint` cannot be applied directly.
- The only reusable part is lower-level:
  `shadow_not_waterfall`, i.e. the 4-position incompatibility argument, but to
  use it we would still need the analogue of the `wc.waterfall` side for the
  good cycle, which is exactly the missing content of `disjoint`.

## Exploration 40

### Strategy
Try the simplest direct value-spectrum proof of
`shadow_cfg_ne_good_of_rotated_separator`:
if some good-cycle coordinate at step `j` uses a value outside the shadow
alphabet `{0, highVal i}`, then equality with `shadowCfg kk` is impossible.

### Outcome
PARTIAL SUCCESS

### Concrete Artifacts
- LEAN PROGRESS:
  `shadow_cfg_ne_good_of_rotated_separator` now closes the easy branch
  `∃ i, (gc.configs.get j i).val ≠ 0 ∧ (gc.configs.get j i) ≠ highVal i`.
- LEAN PROGRESS:
  the remaining `disjoint` core is now isolated to the opposite branch:
  every good-cycle coordinate already lies in the same value alphabet
  `{0, highVal i}` as the shadow config.

### Interpretation
- A one-coordinate mismatch argument is valid, but only for the easy branch.
- The actual hard case is structural:
  when the good config already uses only `0/highVal`, disjoint must come from
  hk_last / hard-endgame geometry rather than from raw value range.

## Exploration 41

### Strategy
Check the binary hard branch on a theorem-relevant size:
use the all-binary `n=9` family and compare hk_last good-cycle configs against
the shadow formula on 4-coordinate projections.

### Outcome
POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  on the all-binary `n=9` family `state_counts = (2,2,2,2,2,2,2,2,2)`,
  the first `18` screened good cycles all hit the raw `hk_last` condition.
- COMPUTED EXAMPLES:
  the hk_last witnesses there are pure sweeps, e.g.
  `(0,1,2,3,4,5,6,7,8)` repeated.
- COMPUTED EXAMPLES:
  with `shadowOff = 2` (so shadow mover `0` aligns with `i₀ = 0`),
  the 4-coordinate projection on `(0, n-4, n-3, n-2) = (0,5,6,7)` is
  cleanly separated:
  - good-cycle projections:
    `0000, 0001, 0011, 0111, 1000, 1100, 1110, 1111`
  - shadow projections:
    `0010, 0100, 0101, 0110, 1001, 1010, 1011, 1101`

### Interpretation
- In the genuinely binary `n=9` regime, the expected staircase/non-staircase
  separator works exactly.
- So if the hard `disjoint` branch can be shown to force a binary/waterfall-like
  local pattern in Lean, then a `shadow_not_waterfall`-style contradiction is
  very plausible.

## Exploration 42

### Strategy
Read the actual `hall_normal` / `isNormalFormGap` infrastructure to see whether
it already implies a value-level staircase property for good-cycle configs.

### Outcome
NEGATIVE AS A DIRECT SHORTCUT

### Interpretation
- `isNormalFormGap` and `normalForm_gap_constraint` are count-level statements:
  they constrain the interval fire counts
  `J = IFC(left t)` and `K = IFC(right t)` in a ternary phase.
- The downstream normal-form lemmas (`suffix_normal_zero_left_one_right`,
  `suffix_normal_zero_right_one_left`, `mixed_normal_has_one_sided_suffix`,
  `normal_phase_has_localized_short_suffix_or_ec`) also stay at the level of
  mover counts / localized suffix structure.
- There is no existing theorem there that directly says a good-cycle config is
  staircase or monotone as a value pattern.
- The only nearby counts-to-values bridge currently available is parity-based,
  e.g. `binary_config_eq_of_even_intervalFireCount`, which yields equality of
  binary values across intervals, not a staircase classification.
- So the real missing theorem is a new counts-to-values bridge from the
  hard-endgame normal-form structure to the binary staircase projection needed
  by `shadow_cfg_ne_good_of_rotated_separator`.

## Exploration 43

### Strategy
Test the “single-coordinate separator” idea directly on the clean binary
`n=9` hk_last regime by searching for the smallest separating projection
between the good-cycle configs and the shadow configs.

### Outcome
NEGATIVE FOR A SINGLE-COORDINATE ARGUMENT

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the all-binary `n=9` sweep/hk_last example, the smallest separating
  projection has size `4`, namely `(0,5,6,7) = (0,n-4,n-3,n-2)`.
- COMPUTED EXAMPLES:
  there is no separating projection of size `1`, `2`, or `3` in that model.

### Interpretation
- Even in the cleanest binary branch, `disjoint` is not witnessed by a single
  coordinate.
- So the current hard branch really is a multi-coordinate pattern mismatch, not
  a one-coordinate value contradiction.

## Exploration 44

### Strategy
Formalize the shadow half directly: prove from the `shadowActive/shadowShift`
formula alone that the shadow projection on `(0,n-4,n-3,n-2)` is never
staircase / monotone.

### Outcome
SUCCEEDED

### Concrete Artifacts
- LEAN PROGRESS:
  added `shadow_0_active_local` in
  `AllNormalFormFalse.lean`
- LEAN PROGRESS:
  added `shadow_projection_nonstair_local` in
  `AllNormalFormFalse.lean`
- LEAN PROGRESS:
  the hard branch of `shadow_cfg_ne_good_of_rotated_separator` now explicitly
  invokes `shadow_projection_nonstair_local`.

### Interpretation
- The shadow side of `disjoint` is no longer heuristic.
- The remaining hard content is now entirely on the good-cycle side:
  prove that the matching good-cycle projection is staircase under the
  hk_last / hard-endgame hypotheses.

## Exploration 45

### Strategy
Diagnose the proposed good-side staircase mechanism on the clean binary
`n=9` hk_last family: check whether raw binary hk_last already forces the
projection on `(0,n-4,n-3,n-2)` to be staircase.

### Outcome
NEGATIVE FOR RAW BINARY HK_LAST

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_good_staircase_mechanism.py`
- COMPUTED EXAMPLES:
  on the all-binary `n=9` family,
  `hk_last_cycles = 18`
- COMPUTED EXAMPLES:
  only `4` of those `18` cycles had the projection on `(0,5,6,7)` staircase
  at every step; `14` did not.
- COMPUTED EXAMPLES:
  even a reverse-sweep hk_last example fails the staircase test.

### Interpretation
- The good-side staircase property is not a consequence of raw
  `binary + hk_last`.
- So any Lean theorem proving the staircase side must use the stronger
  hard-endgame hypotheses (`hall_normal` plus the branch-specific extracted
  structure), not just the broad binary hk_last regime.

## Exploration 46

### Strategy
Try to extract good-side value constraints directly from `hall_normal` in the
current theorem shape.

### Outcome
STRUCTURAL MISMATCH IDENTIFIED

### Interpretation
- `hall_normal` is a pivot-local hypothesis: every available theorem from it is
  phrased around the chosen pivot `t` and its local neighbors
  `{left(left t), left t, t, right t, right(right t)}`.
- The currently formalized shadow separator is on the absolute processor set
  `(0, n-4, n-3, n-2)`.
- So even after proving the shadow side, there is no direct theorem path from
  the existing `hall_normal` infrastructure to a value statement about those
  absolute coordinates.
- This explains why the good-side staircase theorem is not emerging from the
  current shape: we likely need either
  1. a relabel/rotation step normalizing `i₀ = 0`, or
  2. a new shadow non-staircase theorem expressed in the same pivot-relative
     coordinates that the hard-endgame lemmas actually control.

## Exploration 47

### Strategy
Test whether the shadow non-staircase separator can simply be rewritten in a
fixed pivot-relative coordinate set, using the user suggestion
`moverAt 0 = left² t`.

### Outcome
NEGATIVE IN THE CURRENT PROOF STATE

### Concrete Artifacts
- CODEBASE CHECK:
  the current pruned hk_last branch does not contain a theorem or local fact
  of the form `gc.moverAt 0 = left (left t)`.
- COMPUTED EXAMPLES:
  the absolute shadow separator `(0, n-4, n-3, n-2)` becomes, relative to
  `i₀ = moverAt 0`, a family of rotating 4-sets rather than one fixed set.
  For example at `n=9` the relative sets are:
  `(0,5,6,7), (1,6,7,8), (2,7,8,0), ..., (8,4,5,6)`.

### Interpretation
- The current shadow separator is genuinely absolute-coordinate, not a fixed
  pivot-relative pattern around `i₀` or `t`.
- So the clean “option 2” restatement is not available yet in the current
  theorem shape.
- To make the good-side local hypotheses talk to the shadow separator, a real
  relabel/rotation step still seems necessary.

## Exploration 48

### Strategy
Reassess the whole hk_last architecture: continue forcing the shadow-formula
route, or pivot back to the original computational diagnosis and build the bad
cycle directly from the forced graph.

### Outcome
ARCHITECTURAL ASSESSMENT

### Interpretation
- There is no existing Lean theorem packaging “forced recurrent component”
  or “forced graph SCC” for the lower-bound development.
- So a direct forced-graph proof would need a new theorem from scratch.
- However, the generic *cycle* infrastructure we need already exists:
  - `badStep`
  - the direct finite-cycle contradiction pattern in
    `CaseObstructions.not_acc_of_finite_cycle`
- The current shadow-formula route has become structurally blocked on the
  absolute-coordinate / pivot-local mismatch, and both remaining local holes
  (`disjoint`, `hmatch_ne`) are symptoms of that mismatch.
- So the honest assessment is:
  the direct forced-graph bad-cycle construction is probably the *better
  architecture* for hk_last now, even though it requires a fresh theorem,
  because it avoids both stuck formula-bridge obligations at once.

## Exploration 49

### Strategy
Start the actual pivot: delete the shadow-formula/ShadowTrap scaffolding from
`hk_last_near_false` and replace it with the direct finite bad-cycle
contradiction architecture.

### Outcome
SUCCEEDED STRUCTURALLY

### Concrete Artifacts
- LEAN REFACTOR:
  removed the shadow-formula block (`shadowCfg`, `shadowOff`, `highVal`,
  `ShadowTrap`, `disjoint`, `closed`, `distinct`) from
  `hk_last_near_false`.
- LEAN REFACTOR:
  added a local copy of the generic finite-cycle contradiction:
  `not_acc_of_finite_cycle_local`.
- LEAN REFACTOR:
  reduced `hk_last_near_false` to one focused theorem:
  `hk_last_forced_bad_cycle`
  producing a finite `badStep` cycle.
- STATE CHANGE:
  `AllNormalFormFalse.lean` now has exactly 2 live `sorry`s:
  - `hk_last_forced_bad_cycle`
  - `hard_endgame_false`

### Interpretation
- The file is now on the right architecture for hk_last.
- The old shadow-formula dead end is gone.
- The remaining hk_last work is exactly the direct theorem suggested by the
  original computational diagnosis.

## Exploration 50

### Strategy
Test the user’s proposed starting point for the direct bad cycle:
“take the config after the last good-cycle step”.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in a binary `n=9` hk_last witness with mover word
  `(0,1,2,3,4,5,6,7,8)` repeated,
  `k_out` is the last index, so applying the last good step lands on
  `gc.configs.get 0` again.
- COMPUTED EXAMPLES:
  the first extracted off-cycle bad config from the forced SCC was instead a
  genuinely different state, e.g.
  `bad0 = (1,0,1,1,1,1,1,1,1)`,
  whereas `good_0 = (0,0,0,0,0,0,0,0,0)`.

### Interpretation
- The direct bad-cycle construction cannot start from “the config after the
  last good step”; that is just the wrapped good-cycle start.
- `hk_last_forced_bad_cycle` really has to build a genuinely off-cycle config
  inside the forced recurrent component, not a wrapped good configuration.

## Exploration 51

### Strategy
Trace the actual forced path from a concrete off-cycle `n=9` hk_last witness
to understand the Step 3 dichotomy (“reach the good cycle or cycle among bad
configs”).

### Outcome
POSITIVE FOR THE FORCED-CYCLE ROUTE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_forced_path_trace.py`
- COMPUTED EXAMPLES:
  starting from
  `bad0 = (1,0,1,1,1,1,1,1,1)`,
  the chosen forced path stayed entirely off the good cycle for 32 steps and
  then closed back on a previously visited bad state.
- COMPUTED EXAMPLES:
  the start state lies in a nontrivial off-cycle SCC of size `168`.

### Interpretation
- The computational Step 3 is real:
  from a genuinely off-cycle start state, the forced path can remain in the bad
  set and close without ever touching the good cycle.
- This is exactly the abstract content `hk_last_forced_bad_cycle` must package
  in Lean.

## Exploration 52

### Strategy
Clarify the logic of `hk_last_forced_bad_cycle`: does it need an arbitrary bad
orbit avoiding the good cycle, or a stronger finite invariant object?

### Outcome
TARGET SHARPENED

### Interpretation
- The theorem does **not** need to prove:
  “from any bad config, the forced orbit never reaches the good cycle”.
- The cleaner abstract target is:
  construct one nonempty finite bad kernel that is closed under a chosen forced
  successor map.
- Once such a finite closed bad kernel exists, a bad cycle follows by ordinary
  finiteness / repeated-state reasoning, and `_hconv` then gives the
  contradiction.
- So the core mathematical content of `hk_last_forced_bad_cycle` is really the
  existence of a finite closed bad kernel under the hk_last hypotheses.

## Exploration 53

### Strategy
Try to realize the first step of `hk_last_forced_bad_cycle` via pure counting:
use the finite state-space cardinality to obtain `∃ c ∉ gc.configs`.

### Outcome
PARTIAL PROGRESS / LIKELY WRONG FIRST ROUTE

### Concrete Artifacts
- LEAN PROGRESS:
  `hk_last_forced_bad_cycle` now contains the explicit cardinality identity
  `Fintype.card (Config sys.rs) = stateProduct sys.rs`.
- CODEBASE CHECK:
  no existing theorem was found that directly gives
  `gc.configs.length < stateProduct sys.rs`.
- CODEBASE CHECK:
  the older explicit bad-cycle proofs in `CaseObstructions` do **not** start
  from global counting; they start by constructing an off-cycle config
  explicitly via `flipConfig`.

### Interpretation
- The counting fact is useful context, but “off-cycle config by pigeonhole” is
  not currently a cheap Lean step.
- A more realistic Step 1 for hk_last is probably an explicit bad-state
  construction (as in the `CaseObstructions` flip-based shadows), not a global
  cardinality argument.

## Exploration 54

### Strategy
Compare the first concrete forced-kernel state to the good-cycle configs to
understand whether it is a distant new state or a small explicit modification
of some good config.

### Outcome
USEFUL STRUCTURE FOUND

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_forced_kernel_relation.py`
- COMPUTED EXAMPLES:
  for the binary `n=9` witness,
  `bad0 = (1,0,1,1,1,1,1,1,1)` is only Hamming distance `1` from two good
  configs:
  - `gc[9]  = (1,1,1,1,1,1,1,1,1)` differing only at position `1`
  - `gc[11] = (0,0,1,1,1,1,1,1,1)` differing only at position `0`

### Interpretation
- The first bad state is not a remote counting witness.
- It appears to be a *single flip of the right good config at the right
  processor*, just not a single flip of `gc.configs.get 0`.
- So the explicit-construction route is more plausible than the counting route,
  but it needs the correct good-cycle anchor state, not the naive step-0 one.

## Exploration 55

### Strategy
Check whether the “right good config / right processor” anchor has a stable
pattern across the first forward-sweep hk_last witnesses for `n = 6,7,8,9`.

### Outcome
STRONG ANCHOR PATTERN FOR THE SWEEP FAMILY

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_forced_kernel_anchor.py`
- COMPUTED EXAMPLES:
  for the forward-sweep witnesses at `n = 7,8,9`, the first bad state is always
  Hamming distance `1` from the midpoint config `gc[n]`, differing only at
  processor `1`.
- COMPUTED EXAMPLES:
  the same bad state is also Hamming distance `1` from `gc[n+2]`, differing
  only at processor `0`.
- COMPUTED EXAMPLES:
  `n = 6` is slightly exceptional in indexing, but still shows the same general
  phenomenon: the bad state is a one-flip modification of a nearby good config.

### Interpretation
- The first forced-kernel state is not arbitrary; in the sweep family it has a
  very rigid anchor in the good cycle.
- This is the best current evidence for an explicit-construction theorem:
  choose the correct anchor config (likely near the midpoint / second half) and
  flip one processor.

## Exploration 56

### Strategy
Reassess whether `hk_last → False` might admit a cleaner indirect proof that
does not construct a bad cycle at all.

### Outcome
NEGATIVE AS THE CURRENT BEST BET

### Interpretation
- The common structural feature across the tested hk_last witnesses is still the
  existence of a forced off-cycle component, not a simpler direct obstruction.
- Raw hk_last families include both sweep and non-sweep examples, so there is
  no single simpler cycle-type contradiction available at that level.
- The earlier direct routes (local EC, formula-shadow separation, fixed-anchor
  flip) all failed specifically because they were trying to replace the forced
  component with a simpler invariant that turned out not to be universal.
- So unless a new theorem-level invariant is discovered, the explicit
  bad-kernel / bad-cycle construction remains the most credible generic route
  to `hk_last → False`.

## Exploration 57

### Strategy
Analyze the full forced graph, not just one traced path, for non-sweep binary
`n=7` hk_last witnesses: do bad states have paths to the good cycle, or do they
live entirely in off-cycle basins?

### Outcome
VERY STRONG EVIDENCE FOR A CLOSED BAD BASIN

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_bad_basin_trace.py`
- COMPUTED EXAMPLES:
  across the first five non-sweep binary `n=7` hk_last witnesses, the forced
  graph on bad configs had:
  - exactly two nontrivial off-cycle SCCs of sizes `42` and `70`
  - reachability statistics
    `(to_good=False, to_bad_scc=True): 112`
    `(to_good=False, to_bad_scc=False): 2`
- COMPUTED EXAMPLES:
  in these samples, no bad config had a path to the good cycle.

### Interpretation
- The forced structure in the non-sweep hk_last regime looks much stronger than
  “one bad SCC exists”.
- It behaves like a closed bad basin, with many states feeding into off-cycle
  SCCs and no observed bad-to-good reachability.
- This supports the idea that `hk_last_forced_bad_cycle` may come from proving a
  finite bad kernel/basin is closed under forced successors, not from tracing a
  single orbit.

## Exploration 58

### Strategy
Search for a simple basin invariant: does a small coordinate projection
separate the entire non-sweep bad basin from the good cycle?

### Outcome
NEGATIVE FOR SMALL PROJECTIONS

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_bad_basin_invariant.py`
- COMPUTED EXAMPLES:
  for the first five non-sweep binary `n=7` hk_last witnesses, there is **no**
  separating coordinate projection of size `1`, `2`, `3`, or `4` between the
  whole good cycle and the whole bad basin.

### Interpretation
- The basin-closure theorem is not going to come from a tiny coordinate
  separator.
- Whatever makes the bad basin closed in the non-sweep hk_last regime is a more
  global / language-level invariant than a 4-bit pattern test.

## Exploration 59

### Strategy
Check the “bad-rank” idea on the actual forced graph: if `_hconv` made all bad
states well-founded, what fraction of the sampled bad basin already looks
infinite-rank computationally?

### Outcome
VERY STRONG SUPPORT FOR THE CLOSED-BASIN VIEW

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_bad_rank_check.py`
- COMPUTED EXAMPLES:
  for the first five non-sweep binary `n=7` hk_last witnesses:
  - `bad_total = 114`
  - `infinite_rank_nodes = 112`
  - `finite_rank_nodes = 2`
  - finite-rank distribution is just `{0 : 2}`

### Interpretation
- Computationally, almost the entire bad set sits in the infinite-rank basin
  feeding the off-cycle SCCs.
- This reinforces the right abstract theorem shape:
  a large closed bad basin / kernel, not a small explicit anchor or a local
  separator.

## Exploration 60

### Strategy
Test the “all processors privileged at once” shortcut on the non-sweep bad
basin: if some bad config had every processor forced/privileged, that could
give a very direct nontermination argument.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_all_privileged_check.py`
- COMPUTED EXAMPLES:
  across the first five non-sweep binary `n=7` hk_last witnesses:
  - `num_all_forced = 0`
  - the maximum number of simultaneously forced/privileged processors at a bad
    config is only `3`

### Interpretation
- The bad-basin contradiction is not coming from “everything is privileged”.
- This is another sign that the generic proof has to use the closed-basin
  structure itself, not a stronger local simplification.

## Exploration 61

### Strategy
Check whether `hBadNonempty` is at least computationally obvious in the binary
hk_last regime: compare actual hk_last cycle lengths against the full state
space size.

### Outcome
POSITIVE, WITH A SHARPER HYPOTHESIS SUGGESTED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the all-binary `n=7` hk_last family, every sampled hk_last cycle — sweep
  and non-sweep alike — has length exactly `14 = 2n`.
- COMPUTED EXAMPLES:
  the full state space size is `2^7 = 128`.

### Interpretation
- Computationally, `BadCfg` is very nonempty in the binary hk_last regime.
- But the evidence points more toward a sharp cycle-length theorem
  (`gc.configs.length = 2n` in this regime) than toward a direct raw
  state-product inequality proof.

## Exploration 62

### Strategy
Audit the actual Lean hypotheses in the hk_last branch to see whether any of
them already imply the existence of an off-cycle config.

### Outcome
NEGATIVE

### Interpretation
- The available hypotheses are all cycle-internal:
  `_hsub`, `_h3bin`, `hfull`, `hfc2`, `hfc_lt`, `hall_normal`, and the
  hk_last/outside-mover facts.
- None of them currently states or directly yields
  `∃ c : Config sys.rs, c ∉ gc.configs`.
- So `hBadNonempty` is a real theorem obligation, not a hidden corollary of the
  ambient context.

## Exploration 63

### Strategy
Test the simplest explicit off-cycle candidates in the binary `n=9` hk_last
family: the all-zero and all-one configs.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in all `18` sampled binary `n=9` hk_last cycles:
  - `(0,0,...,0)` lies on the good cycle
  - `(1,1,...,1)` also lies on the good cycle

### Interpretation
- There is no cheap “global extremal config” witness for `hBadNonempty`.
- The first off-cycle config really has to be a more delicate construction.

## Exploration 64

### Strategy
Check whether the proposed global counting proof of `hBadNonempty` is actually
supported by the Lean hypotheses in `allNormalForm_false`.

### Outcome
NEGATIVE / HYPOTHESIS MISMATCH

### Interpretation
- The suggested inequalities use assumptions that are **not** present in the
  theorem context.
- In particular:
  - `hfc2` is only `gc.fireCount t ≥ 2` for the single pivot `t`
  - `hfc_lt` is only `gc.fireCount t < gc.configs.length`
  - there is no hypothesis of the form `∀ i, gc.fireCount i ≥ 2`
  - there is no hypothesis of the form `∀ i, gc.fireCount i ≤ m_i - 1`
- So the proposed global counting argument cannot currently be formalized from
  the available Lean context.

## Exploration 65

### Strategy
Check whether there is at least an existing theorem in the codebase bounding
`gc.fireCount i` by the processor state count `m_i`, and test whether that
bound is nontrivial in the binary hk_last regime.

### Outcome
NEGATIVE AS A NEW LEAN TOOL, WEAK EVEN IF TRUE

### Concrete Artifacts
- CODEBASE CHECK:
  no theorem was found relating `fireCount i` directly to `m_i`.
- COMPUTED EXAMPLES:
  in the binary `n=7` hk_last sweep witness,
  `fireCount i = m_i = 2` for every processor.

### Interpretation
- Even if a theorem `fireCount i ≤ m_i` were proved, it would be tight in the
  simplest binary hk_last regime.
- So this route does not seem to expose a strong new structural gap by itself.

## Exploration 66

### Strategy
Test the actual truth of the proposed bound `fireCount i ≤ m_i` on hk_last
examples, rather than just looking for a theorem.

### Outcome
FALSE EVEN FOR HK_LAST

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the hk_last witness with mover word
  `(0,1,2,3,4,5)` repeated four times
  from the family `state_counts = (2,2,2,2,2,10)`,
  the fire counts are
  `[4,4,4,4,4,4]`.
- COMPUTED EXAMPLES:
  so the binary processors satisfy
  `fireCount i = 4 > 2 = m_i`.

### Interpretation
- The proposed counting theorem `fireCount i ≤ m_i` is simply false.
- So the `Σ fireCount_i ≤ Σ m_i < Π m_i` route is dead, even inside hk_last.

## Exploration 67

### Strategy
Search for a simple explicit off-cycle witness obtained by flipping a fixed pair
of coordinates of `gc[0]` in the binary hk_last families.

### Outcome
SURPRISINGLY STRONG POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the binary `n=7` hk_last family, `flip2(gc[0], 0, 2)` is off-cycle for
  all `14` sampled hk_last cycles.
- COMPUTED EXAMPLES:
  the same fixed pair `(0,2)` also stays off-cycle for all sampled binary
  hk_last cycles at `n=8` and `n=9`.

### Interpretation
- This is the first very simple explicit bad-config construction that survives
  multiple sizes and all sampled hk_last cycles in a regime.
- It is still only computational evidence and only in the all-binary regime,
  but it is much stronger than the failed one-flip and midpoint-anchor guesses.

## Exploration 68

### Strategy
Test the structural version of the double-flip witness:
flip the step-0 mover `i₀ = moverAt 0` together with the pivot `t`, and check
whether that stays off-cycle beyond the all-binary regime.

### Outcome
VERY STRONG POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_double_flip_genericity.py`
- COMPUTED EXAMPLES:
  for all sampled hk_last hits in the families
  - `(2,2,2,2,2,10)`
  - `(2,2,2,2,2,2,14)`
  - `(2,2,2,2,2,2,2,22)`
  - `(2,2,2,2,2,2,2,2,2)`
  the config `flip2(gc[0], i₀, t)` was off-cycle.
- LEAN PROGRESS:
  the candidate double-flip state `cFlip₂` is now defined directly inside
  `hk_last_forced_bad_cycle`.

### Interpretation
- This is the strongest explicit off-cycle witness found so far.
- It is still only computational evidence, but it now survives both binary and
  mixed sampled hk_last families, so it is a credible target for proving
  `hBadNonempty`.

## Exploration 69

### Strategy
Check the sharpest combinatorial formulation of the double-flip witness in the
binary hk_last regime: does any good-cycle config ever differ from `gc[0]` at
exactly the two positions `{i₀, t}`?

### Outcome
NEGATIVE IN THE SAMPLED BINARY `n=7` HK_LAST FAMILY

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_double_flip_pattern_check.py`
- COMPUTED EXAMPLES:
  across all `14` sampled binary `n=7` hk_last cycles, there is no step `j`
  and no hk_last pivot `t` such that `gc[j]` differs from `gc[0]` at exactly
  the two positions `{i₀, t}`.

### Interpretation
- In the binary hk_last regime, `cFlip₂` being off-cycle is not just “the exact
  witness wasn’t found”; the precise two-coordinate difference pattern never
  occurs on the good cycle.
- This is the cleanest current evidence for the intended `cFlip₂_not_mem`
  theorem, though still only in the sampled binary regime.

## Exploration 70

### Strategy
Test an even simpler explanation for `cFlip₂_not_mem`: maybe the good cycle
never has both coordinates `i₀` and `t` changed simultaneously relative to
`gc[0]`.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_twocoord_profile.py`
- COMPUTED EXAMPLES:
  in the sampled binary `n=7` hk_last cycles, the profile
  `(gc[j](i₀) ≠ gc[0](i₀), gc[j](t) ≠ gc[0](t)) = (True, True)`
  occurs frequently.

### Interpretation
- The good cycle can and does change `i₀` and `t` simultaneously relative to
  `gc[0]`.
- So `cFlip₂_not_mem` is not explained by a simple two-coordinate parity
  obstruction either.

## Exploration 71

### Strategy
Refine the two-coordinate idea from “both changed” to the stronger
value-correlation claim: maybe the exact `(i₀, t)` value pair of `cFlip₂`
never occurs on the good cycle.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the sampled binary `n=7` hk_last sweep witness with `i₀ = 0` and `t = 2`,
  the target pair for `cFlip₂` is `(1,1)`.
- COMPUTED EXAMPLES:
  that exact pair appears repeatedly on the good cycle at steps
  `j = 3,4,5,6,7`.

### Interpretation
- `cFlip₂_not_mem` is not explained by a two-coordinate value-correlation
  obstruction either.
- The exclusion of `cFlip₂` from the good cycle genuinely depends on a more
  global configuration pattern.

## Exploration 72

### Strategy
Test the proposed cycle-length bound coming from “`k_out` is the last outside
mover, so the cycle is mostly local after that”.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the binary hk_last families:
  - `n=7`: sampled hk_last cycles have length `14` with `4` outside movers
  - `n=9`: sampled hk_last cycles have length `18` with `8` outside movers
- COMPUTED EXAMPLES:
  in the mixed family `state_counts = (2,2,2,2,2,10)`, sampled hk_last cycles
  have lengths `12, 24, 36, 48, 60, ...` with outside-mover counts
  `2, 4, 6, 8, 10, ...`.

### Interpretation
- `k_out` being the last outside mover does **not** mean the cycle has only one
  outside episode in any strong counting sense.
- There can be many earlier outside movers, and the hk_last family can support
  arbitrarily longer sampled cycles in the same state-count family.
- So `hBadNonempty` is not going to come from a simple “mostly local hence
  short” length bound.

## Exploration 73

### Strategy
Inspect the tiny part of the bad set that is *not* in the infinite-rank basin:
if the kernel is almost all bad states, maybe the complement has a simple form.

### Outcome
INTERESTING SMALL-BOUNDARY PATTERN

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the first five non-sweep binary `n=7` hk_last witnesses, the bad states
  outside the infinite-rank basin are always exactly two configurations.
- COMPUTED EXAMPLES:
  those two configurations come in complementary alternating-style pairs, e.g.
  - `(0,1,1,0,1,0,1)` and `(1,0,0,1,0,1,0)`
  - `(0,0,1,0,1,0,1)` and `(1,1,0,1,0,1,0)`

### Interpretation
- The bad kernel may be describable as “all bad states except a tiny explicit
  boundary family”, at least in the sampled non-sweep binary regime.
- This is not yet a generic theorem, but it is the first sign of an explicit
  closed-kernel predicate more global than a local pattern test.

## Exploration 74

### Strategy
Check obligation (1) for the template kernel candidate `K₀`: does the explicit
double-flip seed `cFlip₂` actually satisfy `InMoverTemplate` in the sampled
hk_last families?

### Outcome
POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  for all sampled families tested in
  `probes/hk_last_double_flip_genericity.py`,
  `cFlip₂` matched at least one good mover neighborhood.
- COMPUTED EXAMPLES:
  the matches are often very small in number; examples include
  - forward families: typically `j = 3`
  - mixed / non-sweep samples: one or two matching steps

### Interpretation
- The template side of `cFlip₂ ∈ K₀` is strongly supported by computation.
- So within `badKernel_exists`, the off-cycle side is still the hard part, but
  the `InMoverTemplate` side of the seed witness looks much more tractable.

## Exploration 75

### Strategy
Check the first step where both `i₀` and `t` differ from `gc[0]` in the binary
hk_last regime: is the exact support `{i₀, t}` already impossible because
other positions have necessarily changed first?

### Outcome
POSITIVE STRUCTURAL PATTERN IN THE SAMPLED BINARY `n=7` FAMILY

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_first_both_changed_support.py`
- COMPUTED EXAMPLES:
  in all sampled binary `n=7` hk_last profiles, the first step where both `i₀`
  and `t` differ from `gc[0]` has support strictly larger than `{i₀, t}`.
- COMPUTED EXAMPLES:
  typical supports are interval-like, e.g.
  - `(0,1,2)` when `i₀=0, t=2`
  - `(0,4,5,6)` when `i₀=0, t=4`
  - `(1,2,3)` when `i₀=1, t=3`

### Interpretation
- In the sampled binary regime, the exact double-flip support `{i₀, t}` is
  ruled out because other positions necessarily flip before both endpoints are
  changed.
- This is the first genuine mechanism for `cFlip₂_not_mem`, though still only
  computational and only in the binary regime.

## Exploration 76

### Strategy
Check whether the proposed “walk fills the interval” proof is blocked on mover
connectivity or on the stronger value-support claim.

### Outcome
CONNECTIVITY AVAILABLE, VALUE-SUPPORT STILL MISSING

### Concrete Artifacts
- CODEBASE CHECK:
  `GoodCycle.next_mover_is_local` already gives the mover-walk adjacency theorem
  needed for the walk part of the argument.

### Interpretation
- The remaining gap is not proving that the mover sequence is a walk.
- The real missing theorem is the stronger statement that once the walk from
  `i₀` to `t` has traversed intermediate processors, those processors are still
  changed relative to `gc[0]` at the first step where `t` changes.
- That is a value-support theorem, not a mover-graph theorem.

## Exploration 77

### Strategy
Test the value-support theorem directly in the sampled binary `n=7` hk_last
regime: at the first step where `t` differs from `gc[0]`, are all positions on
the shorter interval from `i₀` to `t` also already changed?

### Outcome
STRONG POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_first_t_changed_interval.py`
- COMPUTED EXAMPLES:
  across `28` sampled `(cycle, t)` profiles in the binary `n=7` hk_last family,
  there were `0` failures: at the first step where `t` changes from `gc[0]`,
  every position on the shorter interval from `i₀` to `t` is already changed.

### Interpretation
- This is exactly the value-support mechanism needed to rule out the exact
  double-flip support `{i₀, t}` in the binary regime.
- It remains computational and binary-only for now, but it is the strongest
  current candidate for a real `cFlip₂_not_mem` proof strategy.

## Exploration 78

### Strategy
Assess whether the interval-filling mechanism can be dropped directly into the
current generic Lean theorem.

### Outcome
NOT YET

### Interpretation
- The verified mechanism is specific to the sampled binary regime and to the
  first step where `t` changes from `gc[0]`.
- The current theorem is still generic and does not assume binary state spaces
  along the whole interval from `i₀` to `t`.
- So the interval-filling mechanism is a strong proof idea, but not yet a
  drop-in Lean argument for the current generic `badKernel_exists`.

## Exploration 79

### Strategy
Test whether the interval-filling mechanism is actually binary-specific or if it
survives the sampled mixed-state hk_last families too.

### Outcome
VERY STRONG POSITIVE HEURISTIC FOR THE GENERIC ROUTE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the sampled mixed families
  - `(2,2,2,2,2,10)`
  - `(2,2,2,2,2,2,14)`
  - `(2,2,2,2,2,2,2,22)`
  the “first `t`-change fills the whole shorter interval from `i₀` to `t`”
  check had `0` failures.

### Interpretation
- The interval-filling support theorem is no longer just a binary curiosity.
- It now looks like the strongest genuinely generic mechanism we have for the
  off-cycle side of `cFlip₂`.

## Exploration 80

### Strategy
Check whether the proposed proof of `hk_p_exists` can really be derived from
`next_mover_is_local` alone by induction on arc distance.

### Outcome
NEGATIVE AS STATED

### Interpretation
- `next_mover_is_local` only says the mover word is an adjacent walk on the
  ring.
- An adjacent walk can still backtrack or take the longer arc before first
  hitting `t`.
- So the raw induction “the walk must hit every point on the shorter arc”
  does not follow from adjacency alone.
- The missing ingredient is a directional / no-backtracking theorem for the
  first-`t`-change segment, not just connectivity.

## Exploration 81

### Strategy
Test the stronger directional statement directly: before the first `t`-move,
is the mover word already monotone along the shorter arc from `i₀` to `t`?

### Outcome
VERY STRONG POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the sampled binary `n=7` hk_last profiles, the mover prefix up to the
  first `t`-move had `0` backtrack profiles.
- COMPUTED EXAMPLES:
  the same check had `0` failures in the sampled mixed families
  - `(2,2,2,2,2,10)`
  - `(2,2,2,2,2,2,14)`
  - `(2,2,2,2,2,2,2,22)`

### Interpretation
- The missing walk theorem is no longer speculative.
- Computationally, the first-`t`-move segment looks genuinely monotone on the
  shorter arc from `i₀` to `t`.
- This is the strongest current candidate for the generic Lean proof of the two
  interior branches of `first_t_change_fills_interval`.

## Exploration 82

### Strategy
Look for a local explanation of the monotone prefix: what mover-neighborhood
triples appear on the first-`t`-move segment, and how do they correlate with
the chosen direction?

### Outcome
PROMISING LOCAL-CONTEXT PATTERN

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_prefix_direction_reason.py`
- COMPUTED EXAMPLES:
  in the sampled families, the monotone prefix is driven by a tiny set of local
  mover triples:
  - right-moving prefixes: mostly `(0,0,0)` and then `(1,0,0)`
  - left-moving prefixes: mostly `(0,0,0)` and then `(0,0,1)`

### Interpretation
- The monotonicity may be provable as a local-context theorem rather than as a
  purely graph-theoretic walk theorem.
- This is still heuristic, but it gives a much sharper target than “prove the
  whole walk is monotone from adjacency alone”.

## Exploration 83

### Strategy
Test the strongest possible mover-word formulation: is the prefix up to the
first `t`-move literally equal to the shorter arc sequence from `i₀` to `t`?

### Outcome
EXTREMELY STRONG POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  across the sampled families
  - `(2,2,2,2,2,2,2)`
  - `(2,2,2,2,2,10)`
  - `(2,2,2,2,2,2,14)`
  - `(2,2,2,2,2,2,2,22)`
  there were `0` failures of the exact prefix-equality check.

### Interpretation
- The first-`t`-move segment appears not just monotone, but exactly equal to
  the shorter arc from `i₀` to `t`.
- This suggests the right Lean target may be a stronger prefix-equality theorem
  from which `first_t_change_fills_interval` follows immediately.

## Exploration 88

### Strategy
Check the numeric corollary of prefix equality: is the first step where `t`
changes always exactly one after the shorter-arc distance from `i₀` to `t`?

### Outcome
VERY STRONG POSITIVE HEURISTIC

### Concrete Artifacts
- COMPUTED EXAMPLES:
  across the sampled families
  - `(2,2,2,2,2,2,2)`
  - `(2,2,2,2,2,10)`
  - `(2,2,2,2,2,2,14)`
  - `(2,2,2,2,2,2,2,22)`
  there were `0` failures of
  `j_t = arcLen(i₀, t) + 1`.

### Interpretation
- The first-`t`-change timing itself already matches the shorter-arc geometry.
- This is the cleanest quantitative support yet for the stronger
  `mover_prefix_is_shorter_arc` theorem.

## Exploration 89

### Strategy
Check whether the needed upper bound on `j_t` could plausibly come from global
cycle-length hypotheses rather than local prefix structure.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the family `state_counts = (2,2,2,2,2,10)`, the hk_last cycle lengths
  grow through `12, 24, 36, 48, 60, ...`
  while the first-`t`-change index stays fixed at `j_t = 3`.

### Interpretation
- The upper bound on `j_t` is not coming from a global length bound like
  `gc.configs.length`.
- It has to be a genuinely local/prefix structural theorem.

## Exploration 90

### Strategy
Test whether interval filling in the binary regime actually requires a
no-backtracking theorem, or whether it already follows from the weaker fact
that the mover sequence is an adjacent walk that first hits `t`.

### Outcome
SURPRISING POSITIVE RESULT IN THE ABSTRACT BINARY SUPPORT MODEL

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in an abstract binary support model on rings `n = 7,8,9`, exhaustive search
  (up to moderate prefix lengths) found `0` counterexamples:
  whenever an adjacent walk starting at `i₀` first hits `t`, the set of
  positions visited an odd number of times already contains the whole shorter
  interval from `i₀` to `t`.

### Interpretation
- In the binary regime, interval filling may not actually need a separate
  no-backtracking theorem.
- The hard generic issue may instead be the non-binary value-support step, not
  the walk geometry itself.

## Exploration 90

### Strategy
Try to derive no-backtracking directly from `gc.distinct` by comparing the
would-be backtrack pattern `q, p, q` against earlier configs.

### Outcome
NEGATIVE AS A GENERIC DERIVATION

### Interpretation
- The tempting comparison `gc[k+1]` vs `gc[k-1]` after a backtrack still
  depends on the local context at `q` matching across the two `q`-fires.
- That matching is not guaranteed generically once `p` has fired in between.
- So `gc.distinct` alone does not exclude backtracking.
- This reinforces the same conclusion as before: the missing theorem is still a
  stronger local-context / frontier theorem, not a bare Nodup argument.

## Exploration 91

### Strategy
Reassess whether hk_last should be reduced into one of the other
`hard_endgame_false` branches instead of carrying its own kernel theorem.

### Outcome
NO ARCHITECTURAL WIN FOUND

### Interpretation
- The other hard branches (`LeftSameHardResidue`, `LeftCrossHardResidue`,
  `RightCrossHardResidue`, `RightSameHardResidue`) are still all consumed by the
  same final `hard_endgame_false` theorem.
- So reducing hk_last into one of them would mostly just move the unresolved
  burden into the same final sorry, not eliminate it.
- The hk_last-specific theorem remains a legitimate standalone target.

## Exploration 92

### Strategy
Check whether the hk_last branch is already killed by ordinary entry conflicts
on the good cycle, which would make the forced-bad-kernel route unnecessary.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_entry_conflict_check.py`
- COMPUTED EXAMPLES:
  in the sampled hk_last families
  - `(2,2,2,2,2,2,2)`
  - `(2,2,2,2,2,10)`
  - `(2,2,2,2,2,2,14)`
  - `(2,2,2,2,2,2,2,22)`
  - `(2,2,2,2,2,2,2,2,2)`
  there were `0` ordinary entry-conflict hits on the good cycles.

### Interpretation
- hk_last does not collapse directly to the existing EC machinery.
- The forced-bad-kernel route still appears to be the right architecture.

## Exploration 93

### Strategy
Consider constructing the first bad config directly from `hall_normal` by
violating a normal-form constraint, instead of using the `cFlip₂` / interval
support route.

### Outcome
NO IMMEDIATE CONFIG-LEVEL OBJECT

### Interpretation
- `hall_normal` is a predicate on ternary phases and interval fire counts, not
  on individual configurations.
- So there is no immediate notion of “this config violates normal form” that
  would automatically give an off-cycle witness.
- This route would need a new bridge from the phase-level normal-form
  constraints to a concrete configuration-level predicate before it could even
  state `hBadNonempty`.

## Exploration 94

### Strategy
Try to close the combinatorial parity induction via the proposed excursion
lemma: “a closed excursion from `d+1` back to `d+1` contributes even visits to
every interior point”.

### Outcome
FALSE AS STATED

### Interpretation
- The excursion-parity claim is simply false for vertex visits.
- Counterexample: the closed excursion `d+1 → p → d+1` visits the interior
  point `p` exactly once, which is odd.
- So the current induction sketch for `line_walk_first_exit_visits_odd` is not
  yet correct and should not be formalized further in this form.

## Exploration 95

### Strategy
Check the stronger replacement claim: “a first-hit adjacent walk from `0` to
`d` visits every interior point an odd number of times”.

### Outcome
FALSE IN THAT GENERALITY

### Concrete Artifacts
- COUNTEREXAMPLE:
  the walk `0, 1, 2, 1, 2, 3` first hits `3` at the end, but visits the
  interior point `1` exactly twice.

### Interpretation
- The abstract first-hit walk parity theorem is false.
- So the cut-crossing / odd-visits route should not remain as a live Lean
  target without a substantially stronger hypothesis.

## Exploration 96

### Strategy
Check whether the concrete counterexample walk `0,1,2,1,2,3` actually appears
as a prefix of any sampled hk_last good cycle.

### Outcome
NEGATIVE

### Concrete Artifacts
- COMPUTED EXAMPLES:
  across all sampled hk_last families checked, the exact prefix
  `(0,1,2,1,2,3)` never appears as the start of the mover word.

### Interpretation
- The counterexample to the abstract walk theorem does not seem to be realized
  by the sampled hk_last good cycles.
- So the missing theorem is still genuinely about the extra structure of good
  cycles, not a bug in the computational observations.

## Exploration 97

### Strategy
Reassess the source of the missing generic theorem after ruling out bare
adjacency, bare Nodup, counting, EC, and the false abstract walk parity route.

### Outcome
DEEP DIRECTION IDENTIFIED

### Interpretation
- There is no remaining simple graph-theoretic explanation visible from the
  current experiments.
- The only strong structured hypotheses left are the phase-level ones:
  `hall_normal` and the existing last-outside / localized-tail lemmas already
  developed in `AllNormalFormFalse.lean` and `PhaseExtractionBase.lean`.
- So the most plausible next proof direction is to mine those phase theorems
  for a prefix/suffix structural consequence strong enough to imply the mover
  prefix theorem, rather than searching for another standalone combinatorial
  lemma.

## Exploration 98

### Strategy
Check whether hk_last might contradict `hall_normal` directly, by forcing the
first ternary phase to start too far from `t` for normal form to apply.

### Outcome
NEGATIVE

### Interpretation
- `isNormalFormGap` itself does not constrain where a ternary phase starts.
- The phase infrastructure explicitly allows arbitrary non-`t` starts and then
  derives constraints only on the tail near the terminal `t`-fire.
- So hk_last does not directly contradict `hall_normal` simply because the
  first phase starts at `i₀` far from `t`.

## Exploration 102

### Strategy
Check the actual first-phase fire-count pair `(J,K)` in the sampled hk_last
families.

### Outcome
VERY STRONG POSITIVE PHASE-LEVEL PATTERN

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in all sampled hk_last first phases checked, the pair `(J,K)` is always
  exactly one-sided:
  - `(1,0)` or
  - `(0,1)`
- COMPUTED EXAMPLES:
  this holds in all sampled families, including mixed-state ones.

### Interpretation
- This is the first phase-level property that looks genuinely compatible with
  `hall_normal`: the hk_last first phase seems to lie in the strongest one-sided
  part of normal form.
- If this can be proved in Lean from the existing phase machinery, it may be
  the missing bridge from `hall_normal` to the mover-prefix structure.

## Exploration 103

### Strategy
Try to prove the “opposite neighbor never fires before the first `t`-fire” by a
pure ring-separation argument: maybe `t` separates `i₀` from the opposite
neighbor.

### Outcome
FALSE AS STATED

### Interpretation
- On a ring, the opposite neighbor can be reached by going the long way around
  without hitting `t` first.
- So the proposed geometric separation argument is not valid in general.
- This means Step 2 is still the same directional-walk theorem in disguise, not
  a simpler topological separation fact.

## Exploration 104

### Strategy
Check whether the bare normal-form predicate itself already rules out
`(J,K) = (1,1)` for the first phase, which would force the observed one-sided
pattern.

### Outcome
NEGATIVE

### Interpretation
- `isMechanismTriggering` only rules out:
  - both even
  - `(J ≥ 2, K = 0)`
  - `(J = 0, K ≥ 2)`
- So `(J,K) = (1,1)` is perfectly compatible with `isNormalFormGap`.
- Therefore the observed `(1,0)` / `(0,1)` first-phase pattern does not follow
  from bare normal form alone.

## Exploration 105

### Strategy
Check whether the localized-short-suffix theorem upgrades `(J,K) ≠ (0,0)` all
the way to `J + K = 1` in the first phase.

### Outcome
NEGATIVE

### Interpretation
- `normal_phase_has_localized_short_suffix_or_ec` only controls the terminal
  one-step suffix ending at the `t`-fire.
- It guarantees that the very last pre-`t` mover is `left t` or `right t`,
  which gives `J + K ≥ 1`.
- But it does **not** say there were no earlier `left t` / `right t` fires in
  the phase.
- So it does not by itself prove `J + K ≤ 1`.

## Exploration 106

### Strategy
Test the stronger uniqueness reading of the suffix theorem: if the terminal
suffix has length `1`, does that force the corresponding neighbor to fire only
once in the whole phase?

### Outcome
NEGATIVE

### Interpretation
- The theorem only gives existence of a later one-step suffix with the same
  endpoint `phase.s`.
- It does not imply that the last-step neighbor was the only occurrence of that
  neighbor in the whole phase.
- So the uniqueness-of-last-step argument does not establish `J + K ≤ 1`.

## Exploration 99

### Final Conclusion

After the full search in this session, the hk_last proof space is mapped well
enough to state the honest blocker precisely.

### Exact Missing Theorem
- The missing generic Lean infrastructure is a theorem of the following shape:
  under the hk_last hypotheses together with `hall_normal`, the first ternary
  phase (from the last `t`-move before step `0` to the first `t`-move after
  step `0`) has a strong prefix/value-support property.
- Equivalent useful formulations would be:
  - the mover prefix up to the first `t`-move is exactly the shorter arc from
    `i₀ = moverAt 0` to `t`
  - or the first step where `t` differs from `gc[0]` already has every point on
    the shorter arc from `i₀` to `t` changed from `gc[0]`
  - or any equivalent theorem strong enough to prove `cFlip₂ ∉ gc.configs`
    and close `badKernel_exists`

### Why Existing Approaches Fail
- Bare adjacency (`gc.next_mover_is_local`) is too weak: it allows backtracking.
- Bare `gc.distinct` / Nodup is too weak: it does not exclude backtracking or
  self-repeat in a generic local context.
- Raw counting routes fail:
  - no theorem gives `fireCount i ≤ m_i`
  - that inequality is false on sampled hk_last witnesses
  - `j_t` is purely local and does not come from global length bounds.
- Abstract walk parity routes fail:
  - excursion-parity for vertex visits is false
  - the stronger abstract first-hit odd-visit theorem is also false
    (counterexample: `0,1,2,1,2,3`).
- Phase machinery gives only the tail near `t`, not the whole prefix:
  `normal_phase_has_localized_short_suffix_or_ec` localizes the last one-step
  suffix before the `t`-move but does not force the earlier prefix.
- Direct EC routes fail empirically:
  sampled hk_last good cycles do not already contain an ordinary entry conflict.
- Global liveness is unavailable in the generic theorem:
  `unique_privileged` only applies on `gc.configs`, not on arbitrary configs.
- Explicit off-cycle witnesses:
  - one-flip witnesses are not generic
  - all-zero / all-one are often on the cycle
  - the double-flip witness `cFlip₂ = flip2(gc[0], i₀, t)` is the best explicit
    seed found, but proving it is off-cycle still needs the missing prefix/value
    theorem above.

### What New Infrastructure Would Close hk_last
- A new theorem in the generic lower-bound development connecting
  `hall_normal` + hk_last branch structure to the first-phase prefix, for
  example:
  - a theorem that the first normal phase from `i₀` to the first `t`-move is a
    one-sided sweep on the shorter arc
  - or any equivalent value-support theorem for the first `t`-change step
- In practice, the rest of the hk_last proof is already in place:
  once that theorem exists, it should close `cFlip₂ ∈ K₀`, hence
  `badKernel_exists`, hence `hk_last_forced_bad_cycle`.

### Proven Building Block
- `bool_transition_balance` **was** proved in Lean (ported from scratch):
  it gives the exact count relation between `true → false` and
  `false → true` transitions in a finite Boolean sequence with prescribed
  endpoints.
- This is a real reusable combinatorial lemma for future attempts at the
  walk/cut-crossing route, even though the larger abstract walk theorem turned
  out to be false in full generality.

## Exploration 100

### Strategy
Test one last alternate angle: use `_hconv` constructively from a specific
starting config or schedule, rather than as a contradiction against a bad
kernel.

### Outcome
NO USEFUL NEW LEVER

### Interpretation
- `_hconv` gives `Acc (badStep sys gc) c` for every config `c`, but it does not
  provide a canonical descent path or schedule from `c`.
- Without a generic liveness/uniqueness theorem for bad configs, there is no
  deterministic successor to extract from `_hconv` alone.
- So the constructive-convergence angle does not currently add anything beyond
  the existing bad-kernel / bad-cycle contradiction route.

## Exploration 101

### Strategy
Check whether `cFlip₂_not_mem` might admit a simpler Hamming-support proof:
compare the distance-2 support patterns that actually occur on the good cycle
against the exact support `{i₀, t}` of `cFlip₂`.

### Outcome
PARTIAL / NOT SUFFICIENT

### Concrete Artifacts
- COMPUTED EXAMPLES:
  wrote and ran
  `probes/hk_last_hamming_profile.py`
- COMPUTED EXAMPLES:
  the exact support `{i₀, t}` never appears as a distance-2 difference from
  `gc[0]` in the sampled families.
- COMPUTED EXAMPLES:
  however, other non-adjacent distance-2 supports do appear in some mixed
  families (for example `(3,5)` and `(4,6)`).

### Interpretation
- Support alone is not enough to isolate `cFlip₂`.
- The obstruction still depends on the *values* together with the support, not
  just the support shape.

## Exploration 84

### Strategy
Separate the global and prefix-local versions of the self-repeat obstruction:
do consecutive same-mover steps ever occur before the first `t`-move?

### Outcome
STRONG POSITIVE HEURISTIC FOR PREFIX SELF-EXCLUSION

### Concrete Artifacts
- COMPUTED EXAMPLES:
  while long hk_last cycles in the mixed families can have consecutive same
  movers globally, the prefix before the first `t`-move had `0` self-repeats in
  all sampled families:
  - `(2,2,2,2,2,2,2)`
  - `(2,2,2,2,2,10)`
  - `(2,2,2,2,2,2,14)`
  - `(2,2,2,2,2,2,2,22)`
  - `(2,2,2,2,2,2,2,2,2)`

### Interpretation
- The induction only needs a *prefix* self-exclusion theorem, not a global one.
- That theorem now looks computationally universal in the sampled hk_last
  families.

## Exploration 85

### Strategy
Try to prove the prefix self-exclusion theorem directly from the generic Lean
facts `gc.unique_privileged`, `gc.state_ne_at_moverAt`, and
`gc.next_mover_is_local`, without first proving the frontier-pattern theorem.

### Outcome
NEGATIVE AS A GENERIC DERIVATION

### Interpretation
- The sampled hk_last families do have prefix self-exclusion, but that does not
  follow from the current generic axioms alone.
- Excluding the `self` case really needs the additional frontier-pattern input
  (or some equivalent local-context theorem).
- So `unique_privileged + state_ne_at_moverAt + adjacency` are not yet enough
  to prove no-self-repeat in Lean.

## Exploration 86

### Strategy
Reassess whether `first_t_change_fills_interval` admits a substantially
different proof path that avoids the prefix-equality / no-backtracking theorem.

### Outcome
NO CLEAR ALTERNATIVE YET

### Interpretation
- The direct corollary route (`cFlip₂_not_mem`) and the stronger prefix route
  both reduce to the same missing content:
  a directional value-support theorem for the first-`t`-change segment.
- Changing the outer theorem target does not eliminate that dependency.
- So at the moment the proof appears bottlenecked on one genuine generic
  mechanism, not on choosing the wrong downstream statement.

## Exploration 87

### Strategy
Audit every hypothesis actually available inside `hk_last_forced_bad_cycle` and
ask which ones could realistically contribute to the missing directional
value-support theorem.

### Outcome
TARGETED ASSESSMENT

### Interpretation
- Most available hypotheses are setup/counting facts:
  `_hn`, `_hconv`, `_hno_safe`, `_hsub`, `_h3bin`, `hfull`, `hfc2`, `hfc_lt`.
- The hk_last-local facts `hk_last`, `hp_near`, `hk_outside`, `hi0_not_local`
  mostly locate `i₀` and the last outside mover relative to the pivot `t`.
- The only hypothesis family with real potential to force the missing
  directional support theorem is `hall_normal`, via the phase/suffix machinery
  around `t`.
- So the next serious proof attempt should probably reintroduce an actual
  ternary-phase / first-`t`-change object and try to use the normal-form lemmas
  there, rather than continuing to reason only from mover adjacency.

## Exploration 74

### Strategy
Check whether the missing closure theorem could collapse to a trivial liveness
axiom: “every bad config has some privileged successor”.

### Outcome
NEGATIVE / DEFINITIONAL BLOCKER

### Interpretation
- In this Lean development there is no global liveness hypothesis for all
  configurations.
- `GoodCycle.unique_privileged` only applies to configs already in
  `gc.configs`.
- So `forcedSucc_exists` is not automatic from the ambient definitions.
- The hk_last theorem really does need a separate argument that the chosen bad
  kernel is closed under `badStep`.
