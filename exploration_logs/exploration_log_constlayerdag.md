# Exploration Log

Scope: `ConstLayerDAG` last-sorry theorem search for
`cphiBoundary_nodrop_non617_impossible`.

## Strategy Register

**Eliminated approach classes:**

- Generic local-impossibility approaches for the strict non617 branch.
  Ruled out at exploration 1 because strict-`fc`-drop, TP-preserving,
  boundary-changing, non617 steps do exist.
- Generic strict-`FutureFc`-drop bridge theorems.
  Ruled out at exploration 1 because many strict non617 TP-preserving
  boundary-changing steps preserve `FutureFc`.
- Raw destination-cap approaches for `P1 : (0,1,2)`.
  Ruled out at exploration 4 because the raw destination family contains
  genuine TP-gain-`2` states.
- Broad symmetric `P012` transport proofs as the first implementation target.
  Effectively ruled out at exploration 6 because the theorem shape is too large
  relative to the information gained and the representation burden dominates.
- Fully local 7-field asymmetric step theorems with raw `P1` and `Pn2` rules.
  Ruled out at exploration 8 because the raw `P1` and `Pn2` local step lemmas
  are false on the projected state space.
- Generic privilege-to-side-condition helpers on the asymmetric source
  projection.
  Ruled out at exploration 21 because the statements
  “privileged `P1` implies exact projected `P1` side condition” and
  “nonnegative-rank privileged `Pn2` implies `cN2 = 0`”
  are false.
- Local/current-state `Pn2` provider theorems.
  Ruled out at exploration 26: there is a concrete Lean-checked `n = 9`
  TP-bad `idxN2` step with `cN2 = cN1 = 1`, so the remaining `Pn2` provider
  must genuinely use path-level reachability from the exact source start.
- Exact-source path-level `Pn2` provider theorems of the form
  “reachable TP-bad `idxN2` step implies `cN2 = 0`”.
  Ruled out at exploration 27: Lean checks an explicit TP-bad path from an
  exact source start to a state with `cN2 = cN1 = 1`, followed by a TP-bad
  `idxN2` step.

**Obstructions:**

- The final live residue is not a no-step theorem; strict non617 TP-preserving
  boundary-changing steps exist.
- The final live residue is not a generic `FutureFc`-drop theorem; strict
  non617 TP-preserving boundary-changing steps can preserve `FutureFc`.
- `P1 : (0,1,2)` has a genuine destination-side exception that survives
  `FutureFc` equality.
- On the asymmetric source projection, hidden-context dependence remains at
  least at `P1` and `Pn2`.
- Even on the corrected asymmetric source projection, local privilege alone
  does not recover the exact projected `P1` and `Pn2` side predicates.
- The `Pn2` forbidden core `cN2 = cN1 = 1` is not a benign residue:
  its raw `Pn2` successor always lands at negative rank in the source
  signature universe.
- The negative-rank `Pn2` successor fact does not, by itself, kill the
  `Pn2` provider. A concrete Lean-checked `n = 9` witness shows that
  TP-bad `idxN2` steps from the core `cN2 = cN1 = 1` do exist before adding
  the exact-source reachability hypothesis.
- The stronger exact-source reachability hypothesis still does not kill the
  `Pn2` core. Lean checks a length-4 TP-bad path from the exact source start
  `(0,1,2,2,2,2,1,0,1)` to the core state
  `(1,2,2,2,2,2,1,1,1)`, followed by a TP-bad `idxN2` step to
  `(1,2,2,2,2,2,1,2,1)`.

**Building blocks:**

- Raw Lean closure for `P1 : (1,0,2)` is live on the theorem path via
  `P0001C2Scratch` and `cphi_strict_p1_102_impossible`.
- Corrected 9-coordinate `P012` exact-family rank table:
  rank counts `95 / 136 / 84 / 43` at levels `0 / 1 / 2 / 3`.
- On the actual `P1 : (0,1,2)` source-family TP closure, `c[n-4] = 2` and
  `c[n-3] = 1` are invariants for `n = 9,10,11`.
- Actual asymmetric source projection `(c0,c1,c2,c3,c4,cN2,cN1)` has `305`
  projected states and projected-rank counts `184 / 75 / 46` at levels
  `0 / 1 / 2`, with both source and destination starts at rank `0`.
- On the actual asymmetric source projection:
  projected `P1` exists exactly for five source triples, and projected `Pn2`
  exists exactly when `cN2 = 0`.
- `P012SourceScratch.lean` now has a build-clean finite rank core for the
  asymmetric source projection, with exact projected side conditions for `P1`
  and `Pn2`.
- On the actual source-family TP closure, the right-seam moves `n-4` and `n-3`
  never preserve TP. Their privileged local triples are rigid:
  `n-4` uses `(1,2,1) -> 1`, `n-3` uses `(2,1,1) -> 0`.
- `P012SourceScratch.lean` now also has:
  - config projection `p012source_sigOfConfig`
  - source and destination start-rank wrappers
  - local seam obstruction lemmas `midTpLocal_one_two_one_false` and
    `midTpLocal_two_one_one_false`
- `P012SourceScratch.lean` now has the generic local TP-preservation lemmas
  (`p2TpLocal_of_tpPreserving`, `pn2TpLocal_of_tpPreserving`,
  `pn3TpLocal_of_tpPreserving`, `midTpLocal_of_tpPreserving`) and the actual
  source-family seam exclusions:
  `not_tpPreserving_idxN4_of_sourceFrame`,
  `not_tpPreserving_idxN3_of_sourceFrame`.
- `P012SourceScratch.lean` now also has:
  - off-window projection equality
  - right-frame preservation under non-seam moves
  - the minimal index helpers needed for source-side step cases
- `P012SourceScratch.lean` now also has:
  - generic boundary-fixed `fc` nonincrease
  - `localFcAfter = localFcBefore + localFcDelta`
  - the first tracked transport wrapper `p012source_sig_step_noninc_idx0`
- `P012SourceScratch.lean` now also has the first three tracked source-side
  transport wrappers:
  `p012source_sig_step_noninc_idx0`,
  `p012source_sig_step_noninc_idx1`,
  `p012source_sig_step_noninc_idx2`.
- `P012SourceScratch.lean` now also has the first left-interior transport
  wrapper:
  `p012source_sig_step_noninc_idx3`.
- `P012SourceScratch.lean` now also has the simple right-edge wrapper
  `p012source_sig_step_noninc_idxN1`.
- `P012SourceScratch.lean` now also has the final boundary-side wrapper
  `p012source_sig_step_noninc_idxN2`.
- `P012SourceScratch.lean` now also has the final parameterized tracked wrapper
  `p012source_sig_step_noninc_idx4`.
- `P012SourceScratch.lean` now has the honest assembly layer:
  - `p012source_step`
  - `p012source_tpReachable_bound`
  - `p012source_tpReachable_fc_le_of_sideconds`
  These isolate the remaining source-side residue to two provider lemmas:
  reachable-`idx1` implies `p012source_p1_live`, and reachable-`Pn2` implies
  `cN2 = 0`.
- The provider failures now have build-clean finite cores in
  `P012SourceScratch.lean`:
  - `p012source_p1_failure_core`
  - `p012source_pn2_failure_core`
  So the remaining source residue is no longer arbitrary provider search; it is
  two explicit bad cores.
- Finite audit of the forbidden cores:
  - `Pn2` core successors have rank `-1` in all cases
  - `idx1` core successors split between negative and nonnegative rank
    depending on the remaining coordinates
- `P012SourceScratch.lean` now also has:
  - `p012source_pn2_core_succ_rank_neg`
  - `p012source_pn2_failure_succ_rank_neg`
- Concrete Lean-checked local `Pn2` witness at `n = 9`:
  `src = (1,2,2,2,2,2,1,1,1)` steps by `idxN2` to
  `dst = (1,2,2,2,2,2,1,2,1)` with `cup2TpBadStepFwd`.
- Concrete Lean-checked exact-source path at `n = 9`:
  `(0,1,2,2,2,2,1,0,1)`
  `--idx0-->`
  `(1,1,2,2,2,2,1,0,1)`
  `--idx1-->`
  `(1,2,2,2,2,2,1,0,1)`
  `--idxN2-->`
  `(1,2,2,2,2,2,1,1,1)`
  `--idxN2-->`
  `(1,2,2,2,2,2,1,2,1)`.
- `P012ExactScratch.lean` already has a live theorem
  `p1_012_exact_src_tpReachable_fc_le_core`, and the file builds.
- `P012ExactScratch.lean` now also has a live theorem
  `p1_012_exact_dst_tpReachable_fc_le_core`, and the file builds.

**Known reformulations:**

- Future-equality strict residue as a 12-bucket family.
  LOAD-BEARING: high. This is the best current reduction of the live hole.
- Asymmetric source-family projection
  `(c0,c1,c2,c3,c4,cN2,cN1)` with `c[n-4]=2`, `c[n-3]=1` fixed.
  LOAD-BEARING: high for the source-side theorem.
- Parameterized source-side transport:
  prove the rank/fc induction once, with `idx1` and `Pn2` side-condition
  providers abstracted out, then solve only those two provider lemmas for the
  exact source start.
  LOAD-BEARING: high. This is now the default source-side proof shape.
- Provider-failure core reduction:
  first reduce the provider lemmas to their explicit finite bad cores inside
  the nonnegative-rank signature universe, then prove those cores cannot occur
  on actual reachable TP-bad steps.
  LOAD-BEARING: high. This is now the most focused follow-up to the
  parameterized transport theorem.
- Forbidden-core successor audit:
  classify what happens if the raw `idx1` / `Pn2` move is taken from a failure
  core before trying to prove the providers. This distinguishes
  “immediately exits the source universe” from “needs a sharper invariant.”
  LOAD-BEARING: medium-high. It already separates the easier `Pn2` residue from
  the harder `idx1` residue.
- Path-level `Pn2` provider only:
  the only surviving `Pn2` theorem shape is now
  “reachable from the exact source start + TP-bad `idxN2` step ⇒ ...”.
  Any current-state-only formulation is false.
  LOAD-BEARING: high. This prevents wasting time on the wrong `Pn2` theorem
  class.
- `Pn2` is not a provider residue anymore:
  it is a genuinely live branch in the exact source family, so it must be
  handled directly in the source-side theorem rather than filtered away.
  LOAD-BEARING: high. This is a genuine theorem-shape change.
- Exact-source reroute via `P012ExactScratch`:
  for the `P1:(0,1,2)` source side, use the already-built exact theorem
  `p1_012_exact_src_tpReachable_fc_le_core` instead of trying to rescue the
  provider-based `P012SourceScratch` route.
  LOAD-BEARING: very high. This is now the default route for that branch.
- Exact source/destination pair via `P012ExactScratch`:
  use the exact-source theorem for `PhiFull(src)` and the exact-destination
  theorem for `PhiFull(dst)`; the `P1:(0,1,2)` branch should now be attackable
  as a clean rank-gap comparison.
  LOAD-BEARING: very high. This is now the intended live-proof route.
- The current exact `P012` pair only covers the `c[n-4] = 2` slice.
  Under actual `n = 9` `idx1` steps with both `FutureFc` and `PhiFull`
  equality, `c[n-4]` still ranges over `0,1,2`, so the exact pair is only a
  partial branch tool, not a full splice.
  LOAD-BEARING: very high. This blocks the naive exact-theorem splice.
- Symmetric exact-family projection
  `(c0,c1,c2,c3,c4,cN4,cN3,cN2,cN1)`.
  LOAD-BEARING: medium. Good for data collection, too heavy as the first proof
  target.
- Raw 6-boundary bucket split for the `P1` buckets.
  LOAD-BEARING: medium-high. It already produced the live `P1 : (1,0,2)`
  closure.

## Exploration 1

### Strategy
Test whether the last residue can be killed by a generic impossibility or a
generic strict-`FutureFc`-drop theorem before doing bucket-specific work.

### Outcome
FAILED

### Failure Constraint
Exact scans at `n = 9,10,11` show strict-`fc`-drop, TP-preserving,
boundary-changing, non617 bad steps exist, and many of them preserve
`FutureFc`.

### What This Rules Out
Any approach whose main theorem is either:
`strict non617 TP-preserving boundary change is impossible`, or
`strict non617 TP-preserving boundary change forces strict FutureFc drop`.

### Surviving Structure
- Exact scans found no witness for:
  `strict fc drop ∧ TP-preserving ∧ boundary-changing ∧ non617 ∧ PhiFull(dst) = PhiFull(src)`.
- So the actual target still looked true even though the naive stronger
  statements were false.

### Reformulations
The real target is not a local move impossibility. It is a theorem about how
`PhiFull` behaves on a nontrivial strict branch.

LOAD-BEARING ASSESSMENT: high. This changed the search space from “find a local
contradiction” to “find a representation where `PhiFull` drop becomes visible.”

### Concrete Artifacts
- STRUCTURAL RESULTS:
  strict non617 TP-preserving boundary-changing steps exist.
- STRUCTURAL RESULTS:
  strict non617 TP-preserving boundary-changing steps can preserve `FutureFc`.
- STRUCTURAL RESULTS:
  no exact witness found for the actual equality target through `n = 11`.

### What Would Unblock This
A representation in which strict `PhiFull` drop is controlled by a finite
boundary or boundary-plus-window state.

### Key Parameters
Tested exact scans at `n = 9,10,11`.

### Open Questions
Is the strict branch determined by a finite bucket or local signature once
`FutureFc` equality is imposed?

## Exploration 2

### Strategy
Classify the strict non617 branch by `(mover, src6, dst6)` and then add the
live `FutureFc` equality filter to see whether the residue stabilizes.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
This does not rule out an approach class directly, but it does rule out
treating the live residue as an unstructured “all strict non617” problem.

### Surviving Structure
- Strict-fc-drop non617 TP-preserving boundary-changing behavior is stable by
  boundary bucket on exact scans.
- Under `FutureFc` equality, the live residue stabilizes to exactly `12`
  buckets across `n = 9,10,11,12`.

### Reformulations
The live residue can be stated as a fixed 12-bucket family rather than an
open-ended non617 class.

LOAD-BEARING ASSESSMENT: high. This is still the best global reduction for the
live hole.

### Concrete Artifacts
- COMPUTED EXAMPLES:
  12 surviving buckets under `FutureFc` equality:
  `P0:(1,0,1)`,
  `P1:(0,1,2)`,
  `P1:(1,0,2)`,
  `Pn1:(0,1,0)`,
  `Pn1:(1,0,1)`,
  `Pn2:(0,1,0)`,
  `Pn2:(0,2,0)`,
  `Pn2:(0,2,1)`,
  `Pn2:(1,2,0)`,
  `Pn3:(0,1,2)`,
  `Pn3:(1,0,1)`,
  `Pn3:(1,0,2)`.
- STRUCTURAL RESULTS:
  `P2` disappears completely under `FutureFc` equality.

### What Would Unblock This
Bucket-local contradictions or bucket-local transport theorems for the highest
leverage buckets.

### Key Parameters
Exact scans through `n = 12`.

### Open Questions
Which of the 12 buckets are genuinely easy, and which ones carry hidden deeper
state?

## Exploration 3

### Strategy
Exploit the apparently easy raw `P1 : (1,0,2)` bucket first, aiming for a raw
destination-cap theorem rather than a filtered theorem.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out delaying bucket work until a fully generic theorem is found. At
least one live bucket was easier to close directly.

### Surviving Structure
- The raw `P1 : (1,0,2)` family admits exact TP caps on both source and
  destination.
- This bucket is now peeled off in the live `ConstLayerDAG` theorem.

### Reformulations
Raw bucket closure is viable when the destination family already has exact
`PhiFull(dst) = fc(dst)` behavior.

LOAD-BEARING ASSESSMENT: medium-high. This was operationally important even if
it did not solve the last theorem.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  live theorem `cphi_strict_p1_102_impossible` in `ConstLayerDAG`.
- STRUCTURAL RESULTS:
  `p1_102_tpReachable_fc_le_core` and `p1_112_tpReachable_fc_le_core` in
  `P0001C2Scratch`.
- COMPUTED EXAMPLES:
  raw destination 6-boundaries for this bucket all had exact TP-gain `0`.

### What Would Unblock This
A comparable closure for the next bucket, or a proof that the next bucket
cannot be treated raw.

### Key Parameters
Lean closure plus exact `n = 9` bucket scans.

### Open Questions
Does the neighboring `P1 : (0,1,2)` bucket behave raw in the same way?

## Exploration 4

### Strategy
Test the analogous raw destination-cap route for `P1 : (0,1,2)`.

### Outcome
FAILED

### Failure Constraint
The raw `P1 : (0,1,2)` destination family contains a genuine bad subfamily with
destination TP-gain `2`; the bucket is not raw-cap friendly.

### What This Rules Out
Any theorem that tries to close `P1 : (0,1,2)` by a raw destination cap
analogous to `P1 : (1,0,2)`.

### Surviving Structure
- The bucket still looked finite/local.
- The natural next move was to replace raw 6-boundary data with a deeper exact
  family.

### Reformulations
`P1 : (0,1,2)` needs an exact-family treatment rather than a raw 6-boundary
one.

LOAD-BEARING ASSESSMENT: medium-high. This prevented wasting time on a false
raw theorem.

### Concrete Artifacts
- COMPUTED EXAMPLES:
  the raw destination family contains the bad subfamily `(0,0,2,1,1,1)` with
  exact destination TP-gain `2`.
- STRUCTURAL RESULTS:
  `P1 : (0,1,2)` is not a raw destination-cap family.

### What Would Unblock This
A deeper exact-family signature that captures the missing hidden state.

### Key Parameters
Exact raw destination-family scan at `n = 9`.

### Open Questions
What is the smallest deeper signature that makes `P1 : (0,1,2)` finite and
closed?

## Exploration 5

### Strategy
Build a symmetric exact-family scratch for `P1 : (0,1,2)` using the
9-coordinate signature
`(c0,c1,c2,c3,c4,cN4,cN3,cN2,cN1)`.

### Outcome
STALLED

### Failure Constraint
Even after correcting the finite rank table, the destination side has a genuine
exceptional start: `(0,0,2,2,2,2,1,0,1)` does not sit at the same base rank as
the other destination starts.

### What This Rules Out
Uniform symmetric exact-family cap theorems of the form
`PhiFull(dst) = fc(dst)` for all exact destinations in this bucket.

### Surviving Structure
- Corrected `P012` rank counts:
  `95 / 136 / 84 / 43` at levels `0 / 1 / 2 / 3`.
- Every exact source start has rank `0`.
- Every exact destination start has rank `0` except the single
  `c3 = 2, c4 = 2` case.

### Reformulations
The 9-coordinate symmetric exact family is still useful as a data-collection
representation, but it is too blunt as the first theorem target.

LOAD-BEARING ASSESSMENT: medium. It clarified the exception, but did not yet
give the right theorem shape.

### Concrete Artifacts
- TOOLS:
  `P012ExactScratch.lean` with corrected rank lists and start-rank lemmas.
- COMPUTED EXAMPLES:
  exceptional destination start
  `(0,0,2,2,2,2,1,0,1)` at nonzero rank.
- STRUCTURAL RESULTS:
  source starts are uniformly rank `0`.

### What Would Unblock This
Either a sharper asymmetric source theorem, or extra structure that isolates the
single destination exception.

### Key Parameters
Exact-family closure checked through `n = 11`; corrected fixed-point ranks
computed from that closure.

### Open Questions
Does the source side already admit a smaller asymmetric projection?

## Exploration 6

### Strategy
Try to turn the symmetric `P012` data into a config-level transport theorem for
`fc + rank` in Lean.

### Outcome
FAILED

### Failure Constraint
The proof burden shifted almost entirely to representation glue:
`cup2Boundary6` fields, `stateAsFin3`, and move rewrites generated a large
number of dependent extensionality mismatches. The theorem shape was too wide
for the amount of structural information it provided.

### What This Rules Out
Continuing to freehand a broad symmetric transport proof before shrinking the
state space or the move alphabet.

### Surviving Structure
- `P012ExactScratch.lean` remained buildable after backing the failed transport
  attempt out.
- Some projection/value helper lemmas survived and may still be reusable later.

### Reformulations
The right next representation should minimize boundary/value glue rather than
maximize symmetry.

LOAD-BEARING ASSESSMENT: high. This was the point where the implementation
target clearly needed to shrink.

### Concrete Artifacts
- TOOLS:
  build-clean corrected `P012ExactScratch.lean`.
- STRUCTURAL RESULTS:
  broad symmetric transport theorem was implementation-heavy and information-poor.

### What Would Unblock This
A smaller asymmetric scratch whose fields are close to the actual live move
alphabet.

### Key Parameters
Lean implementation attempt only; no new parameter scan.

### Open Questions
Can the actual source-family closure be projected to a smaller live state space?

## Exploration 7

### Strategy
Scan the actual TP-preserving source-family closure for `P1 : (0,1,2)` to find
the real invariants and move alphabet instead of guessing them from the
symmetric overapproximation.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out treating the source-family closure as symmetric in the right-hand
seam. In particular, `n-4` and `n-3` do not appear as live move sites on the
actual source-family TP closure for the tested `n`.

### Surviving Structure
- On the actual source-family closure, `c[n-4] = 2` and `c[n-3] = 1` are
  invariants for `n = 9,10,11`.
- The actual closure projects to
  `(c0,c1,c2,c3,c4,cN2,cN1)` with exactly `305` projected states, stable across
  `n = 9,10,11`.
- The projected graph has rank counts `184 / 75 / 46` at levels `0 / 1 / 2`.
- Both projected source starts and projected destination starts sit at rank `0`.

### Reformulations
Asymmetric source-family projection:
`(c0,c1,c2,c3,c4,cN2,cN1)`, with `c[n-4]=2` and `c[n-3]=1` treated as fixed
invariants, and `c5` only appearing as a live parameter for the `idx4` move.

LOAD-BEARING ASSESSMENT: high. This is the best current source-side
representation.

### Concrete Artifacts
- COMPUTED EXAMPLES:
  live move positions on actual source-family TP closure:
  `n=9: {0,1,2,3,4,7,8}`,
  `n=10: {0,1,2,3,4,5,8,9}`,
  `n=11: {0,1,2,3,4,5,6,9,10}`.
- STRUCTURAL RESULTS:
  `c[n-4]=2`, `c[n-3]=1` are actual invariants on the source-family TP closure.
- STRUCTURAL RESULTS:
  projected rank counts `184 / 75 / 46`.
- COMPUTED EXAMPLES:
  projected source starts `(0,1,2,c3,c4,0,1)` all rank `0`.
- COMPUTED EXAMPLES:
  projected destination starts `(0,0,2,c3,c4,0,1)` all rank `0`.

### What Would Unblock This
A Lean scratch built directly on the projected source-family graph, together
with the exact side conditions needed for the nonlocal `P1` and `Pn2` updates.

### Key Parameters
Exact source-family TP closure for `n = 9,10,11`.

### Open Questions
Which projected moves still depend on hidden context, and what is the smallest
extra side information needed?

## Exploration 8

### Strategy
Scaffold a new asymmetric source scratch (`P012SourceScratch`) on the 7-field
projection and test whether the raw local step lemmas already hold.

### Outcome
FAILED

### Failure Constraint
The raw local `P1` and `Pn2` step lemmas are false on the projected state
space. Hidden context dependence remains at exactly those sites.

### What This Rules Out
Any fully local 7-field source theorem that treats `P1` and `Pn2` as functions
of the projected state alone, with no extra side conditions or refined move
data.

### Surviving Structure
- The projected state space and its rank buckets are still valid.
- The failure is concentrated: `P1` and `Pn2` are the only raw local step
  families known to fail in the projected scratch.

### Reformulations
The asymmetric source scratch should not be defined by naive raw local
successors. It should be defined either:
1. by the actual projected graph extracted from real TP moves, or
2. by a refined signature/side condition that makes `P1` and `Pn2` local again.

LOAD-BEARING ASSESSMENT: high. This narrows the remaining hidden-context
problem to two move sites.

### Concrete Artifacts
- TOOLS:
  draft `P012SourceScratch.lean`.
- STRUCTURAL RESULTS:
  raw `P1` step lemma is false on the projected state space.
- STRUCTURAL RESULTS:
  raw `Pn2` step lemma is false on the projected state space.
- COMPUTED EXAMPLES:
  projected-rank counts remain `184 / 75 / 46`, with source and destination
  starts at rank `0`.

### What Would Unblock This
Exact side conditions for projected `P1` and projected `Pn2`, or a direct
encoding of the actual projected graph edges and worst-case `Δfc`.

### Key Parameters
Projected source-family graph extracted from the actual `n = 11` closure;
stability checked against `n = 9,10`.

### Open Questions
Can `P1` and `Pn2` be made local by splitting active/passive subclasses, or do
they require one more tracked coordinate?

## Synthesis after exploration 8

The live residue is now best viewed as two coupled problems:

1. a source-side theorem for `P1 : (0,1,2)` that should be handled in the
   asymmetric source representation, not the symmetric `P012` one
2. a destination-side exception that survives `FutureFc` equality and will need
   its own explicit treatment

Cross-pattern observations:

- The symmetric `P012` exact family was good enough to find the destination
  exception, but too expensive as a proof vehicle.
- The asymmetric source family is the opposite: it looks structurally right for
  the source theorem, but still needs sharper treatment of projected `P1` and
  `Pn2`.
- This suggests the eventual solution is probably mixed:
  asymmetric source theorem + separate destination exception + live bucket split
  in `ConstLayerDAG`.

## Exploration 9

### Strategy
Mine the actual projected `P1` and `Pn2` move conditions on the 7-field
source-family graph, so the asymmetric source scratch can use exact side
conditions instead of false raw local rules.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out continuing to treat projected `P1` and projected `Pn2` as unknown
hidden-context black boxes. Their existence conditions are now explicit on the
projected graph.

### Surviving Structure
- Projected `Pn2` is completely local on the actual projected source graph:
  it exists iff `cN2 = 0`.
- Projected `P1` is not arbitrary hidden context; it is controlled by a small
  finite set of source triples.

### Reformulations
The asymmetric source scratch should use explicit move-side predicates:

- `p012source_p1_live`
- `p012source_pn2_live`

rather than the raw local `P1`/`Pn2` theorems that were false.

LOAD-BEARING ASSESSMENT: high. This is the first concrete repair path for
`P012SourceScratch`.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  projected `Pn2` exists iff `cN2 = 0`.
- COMPUTED EXAMPLES:
  projected `P1` source triples are exactly
  `(0,1,2)`,
  `(0,2,2)`,
  `(1,1,2)`,
  `(1,0,2)`,
  `(1,0,0)`.
- COMPUTED EXAMPLES:
  projected `P1` successors are deterministic by source triple:
  `(0,1,2) -> (0,0,2)`,
  `(0,2,2) -> (0,0,2)`,
  `(1,1,2) -> (1,2,2)`,
  `(1,0,2) -> (1,1,2)`,
  `(1,0,0) -> (1,1,0)`.

### What Would Unblock This
Patch `P012SourceScratch` so its `P1` and `Pn2` step lemmas use these exact
side conditions, then test whether the finite `native_decide` inequalities
become true.

### Key Parameters
Actual source-family TP closure at `n = 11`, checked against the stabilized
7-field projection found in explorations 7 and 8.

### Open Questions
After adding exact side conditions for `P1` and `Pn2`, do any projected step
lemmas still fail? If yes, is `idx4` the only remaining hidden-context site?

## Exploration 10

### Strategy
Repair the asymmetric source scratch by replacing the false raw `P1` and `Pn2`
local rules with the exact projected side conditions found in exploration 9.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
This rules out abandoning the asymmetric source scratch as “too coarse.” The
projection itself was fine; only the raw move predicates were wrong.

### Surviving Structure
- `P012SourceScratch.lean` now builds.
- The finite rank core on the 7-field source projection is stable:
  rank counts `184 / 75 / 46`.
- Exact move-side predicates are enough to make the finite `native_decide`
  step lemmas for `P1` and `Pn2` true.

### Reformulations
The right source-side object is now clear:

- 7-field asymmetric source signature
  `(c0,c1,c2,c3,c4,cN2,cN1)`
- exact projected side predicates for the nonlocal sites
  `P1` and `Pn2`

LOAD-BEARING ASSESSMENT: high. This is the first build-clean scratch that
matches the actual projected source dynamics closely enough to be useful.

### Concrete Artifacts
- TOOLS:
  [P012SourceScratch.lean](./lean/LeanMn/Convergence/P012SourceScratch.lean)
- STRUCTURAL RESULTS:
  projected `P1` side predicate uses the exact five source triples
  found in exploration 9.
- STRUCTURAL RESULTS:
  projected `Pn2` side predicate is `cN2 = 0`.
- STRUCTURAL RESULTS:
  the asymmetric source scratch rank core builds with those predicates.

### What Would Unblock This
Add the config-level transport layer from actual source-family TP steps into
`P012SourceScratch`, then wrap it in a source-side TP cap theorem.

### Key Parameters
Finite projected source graph stabilized from `n = 9,10,11`; Lean artifact
built on that stabilized projected data.

### Open Questions
Can the transport layer be kept asymmetric and graph-driven, or does `idx4`
still force one more tracked coordinate on the Lean side?

## Exploration 11

### Strategy
Probe the actual source-family TP closure at the right seam to see whether the
missing `n-4` and `n-3` moves can be excluded by small local theorems instead
of hidden global context.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out spending time on source-side transport cases for `n-4` and `n-3`.
Those cases should be killed locally before they ever enter the transport
theorem.

### Surviving Structure
- `n-4` is privileged on the source-family closure exactly in the local triple
  `(1,2,1) -> 1`, and never TP-preserving.
- `n-3` is privileged on the source-family closure exactly in the local triple
  `(2,1,1) -> 0`, and never TP-preserving.

### Reformulations
The asymmetric source transport theorem should only need live step cases for:

- `0,1,2,3,4,n-2,n-1`

with `n-4,n-3` handled as local contradictions.

LOAD-BEARING ASSESSMENT: high. This sharply reduces the remaining case surface
for the source-side theorem.

### Concrete Artifacts
- COMPUTED EXAMPLES:
  on the actual `n = 11` source-family TP closure:
  - every privileged `n-4` local state is `(1,2,1) -> 1`, TP-preserving count `0`
  - every privileged `n-3` local state is `(2,1,1) -> 0`, TP-preserving count `0`
- STRUCTURAL RESULTS:
  `n-4` and `n-3` should be excluded by finite local lemmas, not by the global
  rank transport.

### What Would Unblock This
Add the corresponding local false-TP lemmas to `P012SourceScratch`, then write
the asymmetric source transport theorem using only the remaining live move
alphabet.

### Key Parameters
Exact source-family TP closure at `n = 11`; the local patterns are rigid in the
observed data.

### Open Questions
Does the same rigidity proof for `n-4` and `n-3` go through in Lean with just
the source-family invariants and local TP predicates?

## Exploration 12

### Strategy
Promote the asymmetric source scratch from a raw rank table to a usable theorem
base by adding config projection, start-rank wrappers, and local right-seam
obstruction lemmas.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out treating `P012SourceScratch` as merely an exploratory table file.
It is now a build-clean Lean artifact positioned for the next transport-theorem
attempt.

### Surviving Structure
- `P012SourceScratch.lean` builds.
- The file now has an actual `sigOfConfig` and start-rank lemmas for both the
  exact source and exact destination starts.
- The right-seam obstructions are Lean-localized as reusable lemmas, rather
  than just notes from external scans.

### Reformulations
The next source-side theorem should be phrased as a config-level transport into
`P012SourceSig`, not as a fresh search for another state space.

LOAD-BEARING ASSESSMENT: high. This turns the asymmetric projection into an
actual Lean platform for the next theorem attempt.

### Concrete Artifacts
- TOOLS:
  build-clean
  [P012SourceScratch.lean](./lean/LeanMn/Convergence/P012SourceScratch.lean)
- STRUCTURAL RESULTS:
  `p012source_sigOfConfig`
- STRUCTURAL RESULTS:
  `p012source_src_start_rank_of_config`
- STRUCTURAL RESULTS:
  `p012source_dst_start_rank_of_config`
- STRUCTURAL RESULTS:
  `midTpLocal_one_two_one_false`
- STRUCTURAL RESULTS:
  `midTpLocal_two_one_one_false`

### What Would Unblock This
Write the actual source-family transport theorem by case-splitting only on the
live move alphabet:
`0,1,2,3,4,n-2,n-1`, with `n-4,n-3` discharged immediately by the local seam
obstruction lemmas.

### Key Parameters
No new external parameter sweep; this was Lean-side consolidation of the
stabilized asymmetric source representation.

### Open Questions
Can the full source-side TP cap now be proved by adapting the
`pn011c1two_c2one_tpReachable_bound` pattern with a smaller move alphabet?

## Exploration 13

### Strategy
Promote the seam observations into Lean by adding the generic local
TP-preservation lemmas and proving that the source-family seam moves `n-4` and
`n-3` cannot be TP-preserving.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
This rules out carrying `n-4` and `n-3` as live cases in the next source-side
transport theorem. They are now dead by Lean-localized lemmas.

### Surviving Structure
- `P012SourceScratch.lean` remains build-clean.
- The generic local TP lemmas are now available inside the asymmetric source
  scratch.
- The right-seam exclusions are no longer empirical only; they are explicit
  Lean lemmas.

### Reformulations
The source-side step theorem should now split into:

- tracked live moves:
  `0,1,2,3,4,n-2,n-1`
- dead seam moves:
  `n-4,n-3`
- deep off-window moves with unchanged projection

LOAD-BEARING ASSESSMENT: high. This is the first point where the source-side
transport theorem has a realistically small case surface.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `not_tpPreserving_idxN4_of_sourceFrame`
- STRUCTURAL RESULTS:
  `not_tpPreserving_idxN3_of_sourceFrame`
- STRUCTURAL RESULTS:
  generic local TP lemmas inside
  [P012SourceScratch.lean](./lean/LeanMn/Convergence/P012SourceScratch.lean)

### What Would Unblock This
Write the actual `p012source_step` / `p012source_tpReachable_bound` theorem by
copying the `pn011c1two_c2one_step` architecture but using:

- source-family invariants `c[n-4] = 2`, `c[n-3] = 1`
- exact projected side conditions for `P1` and `Pn2`
- off-window projection equality
- the two seam-impossibility lemmas from this exploration

### Key Parameters
Lean-side implementation only; no new external scans were needed.

### Open Questions
Will the source-side transport theorem need one extra tracked coordinate for the
`idx4` case, or is the live `c5` parameter enough exactly as in the projected
graph?

## Exploration 14

### Strategy
Add the remaining shared glue for the asymmetric source transport theorem:
off-window projection equality, right-frame preservation, and the local index
helpers those proofs depend on.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
This rules out the idea that the source-side theorem still needs a new
representation before any actual step proof can be written. The representation
and its basic glue are now in place.

### Surviving Structure
- `P012SourceScratch.lean` remains build-clean.
- Off-window moves now preserve the projected source signature.
- Non-seam moves preserve the right frame `c[n-4] = 2`, `c[n-3] = 1`.

### Reformulations
The next theorem attempt should now be the actual source-side one-step lemma,
not more representation work.

LOAD-BEARING ASSESSMENT: high. This removes the last generic glue excuses; the
next attempt should finally be the real transport theorem.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  off-window projection equality in
  [P012SourceScratch.lean](./lean/LeanMn/Convergence/P012SourceScratch.lean)
- STRUCTURAL RESULTS:
  right-frame preservation under non-seam moves in the same file
- TOOLS:
  local index helpers `cup2Idx5`, `cup2IdxN5`, `cup2IdxN4`,
  `left_cup2IdxN4_eq_idxN5`, `right_cup2IdxN4_eq_boundaryIdxN3`,
  `left_cup2BoundaryIdxN3_eq_idxN4`

### What Would Unblock This
Write `p012source_step` and `p012source_tpReachable_bound` by adapting the
`pn011c1two_c2one` architecture to the smaller source-family move alphabet.

### Key Parameters
Lean-side implementation only; no new scans were needed.

### Open Questions
Can `p012source_step` be completed without reintroducing the symmetric `P012`
machinery, or will the `idx4` case still force a hybrid argument?

## Exploration 15

### Strategy
Write the first actual tracked transport case (`idx0`) in the asymmetric source
scratch, together with the generic `fc` bookkeeping lemmas it needs, to verify
that the projected transport architecture is viable.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out the possibility that the asymmetric source transport theorem is
blocked at the very first tracked case by the same representation issues that
killed the symmetric `P012` attempt.

### Surviving Structure
- The generic bookkeeping lemmas compile in `P012SourceScratch`.
- The first tracked wrapper `idx0` compiles.
- The projection/extensionality issues are now manageable in the asymmetric
  representation.

### Reformulations
The remaining tracked cases should be approached as a mechanical family:

- `idx0` established the pattern
- `idx1`, `idx2`, `idx3`, `idx4`, `n-2`, `n-1` should follow by repetition,
  with only `P1`, `Pn2`, and `idx4` needing extra side information

LOAD-BEARING ASSESSMENT: high. This is the first direct evidence that the
asymmetric source transport theorem is implementable, not just plausible.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_fc_noninc_of_boundary_fixed_tpStep`
- STRUCTURAL RESULTS:
  `localFcAfter_eq_localFcBefore_add_localFcDelta`
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idx0`

### What Would Unblock This
Continue the same pattern for the other tracked live cases, then assemble the
one-step theorem `p012source_step`.

### Key Parameters
Lean-side implementation only; no new scans.

### Open Questions
Will `idx1` and `n-2` integrate cleanly with the exact projected side
conditions, or is there still hidden context beyond those predicates?

## Exploration 16

### Strategy
Push the asymmetric source transport theorem from proof-of-concept to actual
implementation by adding the first three tracked wrappers `idx0`, `idx1`,
`idx2`.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out the worry that every tracked case would reopen the same
representation problems. The first three cases were manageable and now compile.

### Surviving Structure
- `idx0`, `idx1`, and `idx2` all compile in `P012SourceScratch`.
- `idx1` integrates cleanly with the exact projected `P1` side predicate.
- `idx2` integrates cleanly with the TP-local `P2` predicate.

### Reformulations
The source-side transport theorem now looks genuinely repetitive rather than
mysterious: after the seam exclusions, the remaining work is a sequence of
tracked wrappers plus the final case split theorem.

LOAD-BEARING ASSESSMENT: high. This is the first time the source-side theorem
is clearly implementation work rather than theorem-shape search.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idx0`
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idx1`
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idx2`

### What Would Unblock This
Continue the same transport pattern for:
`idx3`, `idx4`, `n-2`, and `n-1`, then assemble `p012source_step`.

### Key Parameters
Lean-side implementation only.

### Open Questions
Will `idx4` remain the only tracked case that needs a live extra parameter
(`c5`), or do the right-edge cases introduce another hidden dependency?

## Exploration 17

### Strategy
Continue the asymmetric source transport implementation by adding the first
interior tracked wrapper `idx3`.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out the idea that the first interior tracked case would force a return
to the discarded symmetric `P012` machinery. The asymmetric source
representation handles `idx3` cleanly.

### Surviving Structure
- `idx3` compiles in `P012SourceScratch`.
- The left-side tracked strip `0,1,2,3` now all compile.

### Reformulations
The remaining asymmetry is now sharper:

- left tracked strip is working
- right seam is excluded
- the remaining uncertainty is concentrated in
  `idx4`, `n-2`, and `n-1`

LOAD-BEARING ASSESSMENT: high. This narrows the remaining implementation
surface to the right edge and the single parameterized interior site.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idx3`

### What Would Unblock This
Finish the remaining three wrappers:
`idx4`, `n-2`, and `n-1`, then assemble the full one-step theorem.

### Key Parameters
Lean-side implementation only.

### Open Questions
Is it better to do `n-2`/`n-1` before `idx4` because they do not introduce a
new explicit parameter, or is `idx4` still the real bottleneck and should be
attacked immediately?

## Exploration 18

### Strategy
Finish the easy tracked wrappers before the parameterized `idx4` case by adding
the first interior wrapper `idx3` and the simple right-edge wrapper `n-1`.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out the worry that the right edge would introduce unexpected hidden
context immediately. The `n-1` case behaves like the simpler boundary wrappers.

### Surviving Structure
- `idx3` compiles.
- `n-1` compiles.
- The only tracked source-side cases still missing are now:
  `idx4` and `n-2`.

### Reformulations
The remaining source-side theorem work is now sharply split:

- `n-2` should be the final boundary-side case, using the exact projected
  `Pn2` side condition
- `idx4` is the only remaining parameterized interior case

LOAD-BEARING ASSESSMENT: high. The source-side theorem has become a two-case
residue rather than a broad implementation problem.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idx3`
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idxN1`

### What Would Unblock This
Add `p012source_sig_step_noninc_idxN2`, then attack the last parameterized case
`idx4`.

### Key Parameters
Lean-side implementation only.

### Open Questions
Will `n-2` be as straightforward as `n-1`, or does its exact side condition
interact with the right-frame invariants in a way that still needs one more
auxiliary lemma?

## Exploration 19

### Strategy
Finish the source-side boundary strip by adding the exact-side-condition
`n-2` wrapper.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out the concern that the projected `Pn2` side condition would still
need hidden deeper context in Lean. The boundary-side `n-2` case compiles with
the exact projected condition alone.

### Surviving Structure
- The source-side boundary strip is now complete:
  `idx0`, `idx1`, `idx2`, `n-2`, `n-1`.
- The only tracked wrapper still missing is the parameterized interior case
  `idx4`.

### Reformulations
The remaining source-side residue is now sharply concentrated:

- one parameterized tracked case: `idx4`
- one assembly theorem: `p012source_step`
- one reachable closure theorem: `p012source_tpReachable_bound`

LOAD-BEARING ASSESSMENT: high. The source-side theorem is now a small endgame,
not a broad transport problem.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idxN2`

### What Would Unblock This
Prove `p012source_sig_step_noninc_idx4`, then assemble the final source-side
step theorem.

### Key Parameters
Lean-side implementation only.

### Open Questions
Is `idx4` genuinely the only remaining source-side difficulty, or will the
assembly theorem still expose one more hidden off-window corner case?

## Exploration 20

### Strategy
Finish the last parameterized tracked wrapper, `idx4`, so the entire source-side
local transport layer is complete before assembling the one-step theorem.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out the possibility that `idx4` would force a return to theorem-shape
search. The parameterized interior case now fits the same transport framework
as the rest of the source-side wrappers.

### Surviving Structure
- All tracked source-side wrappers now compile:
  `idx0`, `idx1`, `idx2`, `idx3`, `idx4`, `n-2`, `n-1`.
- The remaining source-side work is theorem assembly:
  `p012source_step` and `p012source_tpReachable_bound`.

### Reformulations
The source-side residue is no longer “find the right local theorem.” It is now:

1. combine the tracked wrappers
2. combine the seam obstructions
3. combine the off-window preservation

This is finally ordinary Lean assembly work.

LOAD-BEARING ASSESSMENT: very high. The local theorem-search phase for the
source side is effectively complete.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_sig_step_noninc_idx4`

### What Would Unblock This
Write `p012source_step`, then lift it to `p012source_tpReachable_bound`, and
then wrap the final source-side TP cap theorem.

### Key Parameters
Lean-side implementation only.

### Open Questions
Will the source-side step theorem expose any new invariant-preservation wrinkle,
or is the remaining work now just careful case bookkeeping?

## Exploration 21

### Strategy
Try to simplify the final source-side assembly theorem by proving generic helper
lemmas that recover the exact projected `P1` and `Pn2` side conditions from
local privilege information.

### Outcome
FAILED

### Failure Constraint
Both helper statements are false. `native_decide` found counterexamples to:

- privileged `P1` implies `p012source_p1_live`
- nonnegative-rank privileged `Pn2` implies `cN2 = 0`

### What This Rules Out
Any final assembly strategy that tries to infer the exact projected side
conditions for `P1` and `Pn2` from local privilege alone.

### Surviving Structure
- All tracked wrappers still compile.
- The exact side predicates themselves remain correct and available; only the
  attempted shortcut from local privilege to those predicates failed.

### Reformulations
The final source-side step theorem must carry the `P1` and `Pn2` side
conditions explicitly in the relevant cases, rather than deriving them from
privilege on demand.

LOAD-BEARING ASSESSMENT: high. This prevents a misleading simplification and
keeps the final step theorem honest.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  generic helper
  “privileged `P1` implies `p012source_p1_live`” is false.
- STRUCTURAL RESULTS:
  generic helper
  “nonnegative-rank privileged `Pn2` implies `cN2 = 0`” is false.

### What Would Unblock This
Write `p012source_step` with explicit `P1` and `Pn2` branch assumptions instead
of trying to recover them from privilege.

### Key Parameters
Failure witnessed by finite `native_decide` on the asymmetric source
projection.

### Open Questions
Should the final step theorem split the `P1` and `Pn2` branches immediately, or
is it cleaner to postpone those splits to the reachable-bound theorem?

## Exploration 22

### Strategy
Finish the asymmetric source scratch by writing the honest assembly theorems:
first a generic one-step transport theorem, then a TP-reachable bound, both
parameterized by explicit `idx1`/`Pn2` side-condition providers.

### Outcome
SUCCEEDED

### Failure Constraint
None at the theorem-shape level. The only friction was Lean-side assembly:
wrapper argument order, `ReflTransGen` induction shape, and one off-window
arithmetic proof.

### What This Rules Out
It rules out continuing to intertwine the source-side induction with the
provider-lemma search. The induction can be built cleanly first, and the
remaining residue can be isolated to the two provider lemmas.

### Surviving Structure
- `P012SourceScratch.lean` now builds with:
  - `p012source_step`
  - `p012source_tpReachable_bound`
  - `p012source_tpReachable_fc_le_of_sideconds`
- The source-side rank/fc transport is now fully separated from the theorem
  search for the `idx1` and `Pn2` side-condition providers.
- The off-window branch is handled cleanly by deep-boundary preservation plus
  the existing `fc` nonincrease theorem.

### Reformulations
The remaining source-side problem is no longer “prove the whole cap theorem.”
It is:

1. prove reachable-`idx1` implies `p012source_p1_live`
2. prove reachable-`Pn2` implies `cN2 = 0`
3. feed those providers into the already-built transport theorem

LOAD-BEARING ASSESSMENT: very high. This turns the source residue into two
small theorem targets instead of one tangled assembly proof.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  build-clean theorem `p012source_step`
- STRUCTURAL RESULTS:
  build-clean theorem `p012source_tpReachable_bound`
- STRUCTURAL RESULTS:
  build-clean theorem `p012source_tpReachable_fc_le_of_sideconds`

### What Would Unblock This
Two provider lemmas for the exact source start:

- if a reachable state has a TP-bad step at `idx1`, then
  `p012source_p1_live (sigOfConfig d)`
- if a reachable state has a TP-bad step at `idxN2`, then
  `(d (cup2BoundaryIdxN2 ...)).1 = 0`

### Key Parameters
Lean-side implementation in `P012SourceScratch.lean`; no new mathematical
counterexamples found.

### Open Questions
Can the two provider lemmas be proved directly from reachable-state structure,
or should one of them be replaced by a sharper auxiliary invariant?

## Synthesis after exploration 22

The source-side work has crossed a real threshold. Earlier explorations kept
mixing three jobs:

1. finite-rank construction
2. one-step transport assembly
3. discovery of the hidden `idx1`/`Pn2` side conditions

Exploration 22 cleanly separates (1) and (2) from (3). That means the next
attempt should not touch the generic transport layer again unless the provider
lemmas expose a genuine contradiction in its interface. The residue is now
small enough that each provider can be investigated independently.

## Exploration 23

### Strategy
Audit the two provider failures inside the finite nonnegative-rank source
signature universe and encode the exact bad cores in Lean, so the remaining
provider search is stated in terms of explicit subcases rather than vague
missing side conditions.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out treating the missing providers as diffuse hidden-context failures.
Within the finite source signature universe, both failures collapse to tiny
explicit cores.

### Surviving Structure
- The `idx1` provider failure set is exactly the core
  `c1 = 2, c2 = 0, c3 = 0`.
- The `Pn2` provider failure set is exactly the core
  `cN2 = 1, cN1 = 1`.
- Both reductions are now recorded as build-clean Lean theorems in
  `P012SourceScratch.lean`.

### Reformulations
The provider lemmas no longer need to be attacked in full generality. The real
remaining subgoals are:

1. reachable TP-bad `idx1` step cannot occur from the
   `c1 = 2, c2 = 0, c3 = 0` core
2. reachable TP-bad `Pn2` step cannot occur from the
   `cN2 = 1, cN1 = 1` core

LOAD-BEARING ASSESSMENT: high. This converts the provider search into two
explicit forbidden-core theorems.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_p1_failure_core`
- STRUCTURAL RESULTS:
  `p012source_pn2_failure_core`
- COMPUTED EXAMPLES:
  on the nonnegative-rank signature universe:
  - `idx1` failures = 24 signatures, all in the single core
    `c1 = 2, c2 = 0, c3 = 0`
  - `Pn2` failures = 83 signatures, all in the single core
    `cN2 = 1, cN1 = 1`

### What Would Unblock This
Translate the two failure-core theorems from signature form to actual reachable
config form, then prove each core incompatible with a TP-bad step from the
exact source family.

### Key Parameters
Finite audit over the 305 nonnegative-rank source signatures.

### Open Questions
Which forbidden core is easier to kill first:
`idx1 : c1 = 2, c2 = 0, c3 = 0`, or
`Pn2 : cN2 = cN1 = 1`?

## Exploration 24 (probe)

### Strategy
Check what the raw `idx1` and `Pn2` successors do on the forbidden cores inside
the 305-state nonnegative-rank source universe, to see whether either provider
can be killed just by successor-rank exit.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  on the `Pn2` forbidden core `cN2 = cN1 = 1`, every raw `Pn2` successor has
  rank `-1`.
- COMPUTED EXAMPLES:
  on the `idx1` forbidden core `c1 = 2, c2 = 0, c3 = 0`, raw `idx1`
  successors have rank distribution:
  `-1 : 10`, `0 : 8`, `1 : 2`, `2 : 4`.
  So `idx1` still needs a sharper structural invariant, while `Pn2` looks much
  closer to a direct contradiction route.

## Exploration 25

### Strategy
Turn the clean `Pn2` forbidden-core probe into Lean theorems, so the `Pn2`
provider residue can be attacked as a direct negative-rank contradiction rather
than as a vague missing side condition.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out treating the `Pn2` provider residue as symmetric with the `idx1`
residue. `Pn2` is now strictly sharper: its failure core has a uniform negative
successor-rank theorem.

### Surviving Structure
- `p012source_pn2_core_succ_rank_neg`
- `p012source_pn2_failure_succ_rank_neg`
- `idx1` remains the mixed branch; no analogous uniform negative-rank theorem
  exists there.

### Reformulations
The `Pn2` provider target can now be restated as:

> a reachable TP-bad `Pn2` step cannot start from the failure core
> `cN2 = cN1 = 1`, because its signature successor would have rank `-1`.

This is materially different from the `idx1` provider target, which still
needs additional structure.

LOAD-BEARING ASSESSMENT: high. This cleanly separates the easier `Pn2`
provider route from the harder `idx1` route.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p012source_pn2_core_succ_rank_neg`
- STRUCTURAL RESULTS:
  `p012source_pn2_failure_succ_rank_neg`

### What Would Unblock This
An actual-config theorem that transfers the signature-level `Pn2` failure core
and negative successor rank into the reachable TP-bad-step setting.

### Key Parameters
Lean implementation in `P012SourceScratch.lean`.

### Open Questions
Can the `Pn2` contradiction be closed directly from the negative-rank
destination, or does it still need a path-level minimal-counterexample wrapper?

## Exploration 27

### Strategy
Lean-check whether the `Pn2` forbidden core survives the exact-source
reachability hypothesis by verifying an explicit TP-bad path from an exact
source start to the core state and its outgoing `idxN2` TP-bad step.

### Outcome
SUCCEEDED

### Failure Constraint
The old path-level `Pn2` provider target is false.

### What This Rules Out
Any source-side plan that expects the exact-source reachability hypothesis to
filter away `Pn2` by forcing `cN2 = 0`.

### Surviving Structure
- The parameterized transport theorem in `P012SourceScratch` is still valid.
- The `idx1` residue is still a provider-style target.
- `Pn2` must now be treated as a live branch, not as a side-condition failure
  to be filtered away.

### Reformulations
The source-side residue is no longer:

1. prove an `idx1` provider
2. prove a `Pn2` provider

It is now:

1. prove an `idx1` provider-style theorem
2. prove a direct theorem for the live reachable `Pn2` branch

LOAD-BEARING ASSESSMENT: very high. This changes the source-side theorem shape
again and invalidates a central assumption from explorations 9–25.

### Concrete Artifacts
- COMPUTED EXAMPLES:
  Lean-checked TP-bad path at `n = 9`:
  `(0,1,2,2,2,2,1,0,1)`
  `--idx0-->`
  `(1,1,2,2,2,2,1,0,1)`
  `--idx1-->`
  `(1,2,2,2,2,2,1,0,1)`
  `--idxN2-->`
  `(1,2,2,2,2,2,1,1,1)`
  `--idxN2-->`
  `(1,2,2,2,2,2,1,2,1)`.
- STRUCTURAL RESULTS:
  the exact-source path-level `Pn2` provider target is false.

### What Would Unblock This
A new direct theorem for the live reachable `Pn2` branch, or a stronger source
representation that makes the reachable `Pn2` dynamics finite and tractable.

### Key Parameters
Lean-native verification in temporary `Check.lean`, then removed.

### Open Questions
What is the smallest stronger source representation that makes the live
reachable `Pn2` branch local enough to prove directly?

## Exploration 28

### Strategy
Verify whether `P012ExactScratch.lean` already contains a buildable direct
exact-source theorem that can replace the provider-based `P012SourceScratch`
route for the `P1:(0,1,2)` source side.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out continuing to treat the provider-based source scratch as the only
viable route for `P1:(0,1,2)`. A direct exact-source theorem already exists.

### Surviving Structure
- `P012ExactScratch.lean` builds.
- The theorem
  `p1_012_exact_src_tpReachable_fc_le_core`
  is live and available.
- The provider-based `P012SourceScratch` work is still valuable as analysis,
  but it is no longer the critical path for the exact source branch.

### Reformulations
The source-side plan should now split:

1. reroute the `P1:(0,1,2)` exact source branch through
   `p1_012_exact_src_tpReachable_fc_le_core`
2. keep `P012SourceScratch` only as a residue-analysis tool, unless another
   direct theorem fails and forces us back there

LOAD-BEARING ASSESSMENT: very high. This is the cleanest route discovered so
far for the exact source branch.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  buildable theorem `p1_012_exact_src_tpReachable_fc_le_core`
- STRUCTURAL RESULTS:
  `lake build LeanMn.Convergence.P012ExactScratch` succeeds

### What Would Unblock This
Thread `p1_012_exact_src_tpReachable_fc_le_core` into the live `ConstLayerDAG`
strict-branch proof for the `P1:(0,1,2)` source side, and then reassess what
strict residue remains after that reroute.

### Key Parameters
Existing theorem in `P012ExactScratch.lean`; no new theorem discovery required
for the source cap itself.

### Open Questions
After rerouting `P1:(0,1,2)` through `P012ExactScratch`, how much of the last
strict residue is actually left?

## Exploration 29

### Strategy
Add the missing exact-destination theorem to `P012ExactScratch` so the
`P1:(0,1,2)` strict branch can be handled by an exact source/destination pair
rather than by the failed provider route.

### Outcome
SUCCEEDED

### Failure Constraint
None.

### What This Rules Out
It rules out the objection that `P012ExactScratch` only helps on the source
side. The exact destination side is now also packaged as a reusable theorem.

### Surviving Structure
- `p1_012_exact_src_tpReachable_fc_le_core`
- `p1_012_exact_dst_tpReachable_fc_le_core`
- `lake build LeanMn.Convergence.P012ExactScratch` succeeds

### Reformulations
The `P1:(0,1,2)` strict branch should now be viewed as an exact
source/destination theorem application problem, not as a provider theorem
problem.

LOAD-BEARING ASSESSMENT: very high. This is the first route that directly
matches the exact branch structure we now believe is true.

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p1_012_exact_dst_tpReachable_fc_le_core`

### What Would Unblock This
Thread the exact-source and exact-destination theorems into the live strict
branch in `ConstLayerDAG`, then see what residue remains after the
`P1:(0,1,2)` case is peeled off.

### Key Parameters
Lean implementation in `P012ExactScratch.lean`.

### Open Questions
Does the exact `P1:(0,1,2)` reroute remove only that bucket, or does it also
make other parts of the strict residue easier to classify?

## Exploration 30 (probe)

### Strategy
Test whether the full `n = 9` CPhi-style condition on the live
`P1:(0,1,2)` `idx1` branch forces the missing exact-source hypothesis
`c[n-4] = 2`, which would make the current `P012ExactScratch` source/destination
pair directly spliceable.

### Outcome
FAILED

### Failure Constraint
Even after imposing both `FutureFc` equality and `PhiFull` equality on the
actual `n = 9` `idx1` branch with source 6-boundary `(0,1,2,1,0,1)`,
the value `c[n-4]` still ranges over `0,1,2`.

### What This Rules Out
Any direct splice of the current `P012ExactScratch` theorems as a full solution
to the live `P1:(0,1,2)` branch. They only cover the `c[n-4] = 2` subcase.

### Surviving Structure
- The exact-source/destination pair is still valid and useful on the
  `c[n-4] = 2` slice.
- The broader live branch remains finite and highly structured; the obstruction
  is specifically the missing freedom in `c[n-4]`.

### Reformulations
The next viable exact-family route is no longer “use the current exact pair.”
It is “broaden the exact family so the live branch’s `c[n-4]` freedom is part
of the theorem,” or find a new invariant that collapses the `c[n-4] ≠ 2`
subcases separately.

LOAD-BEARING ASSESSMENT: very high. This invalidates the naive exact-theorem
splice and points toward a broader exact-family scratch as the next real route.

### Concrete Artifacts
- COMPUTED EXAMPLES:
  at `n = 9`, among bad `idx1` steps with source 6-boundary `(0,1,2,1,0,1)`
  and both `FutureFc` and `PhiFull` equality, `c[n-4]` counts are:
  `0 : 9`, `1 : 9`, `2 : 9`.

### What Would Unblock This
Either:
1. a broader exact-family theorem allowing `c[n-4] ∈ {0,1,2}`, or
2. a separate contradiction for the `c[n-4] ≠ 2` slices.

### Key Parameters
Exact brute-force scan at `n = 9` over the actual bad graph and TP graph.

### Open Questions
Is the right next object a broadened exact-family rank table, or a smaller
certificate that kills the `c[n-4] ≠ 2` slices directly?

## Exploration 31 (probe)

### Strategy
Probe the obvious broader exact-family route directly on the actual `n = 9`
TP-bad graph: keep the `P1:(0,1,2)` exact signature but free `c[n-4]`, and
measure the size/rank behavior of the resulting exact projected closure.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  the broadened exact-family closure at `n = 9` has:
  - `1442` actual states/signatures
  - no projected cycles
  - max projected rank `36`
- COMPUTED EXAMPLES:
  source and destination start ranks vary with `(c3,c4,cN4)` and are no longer
  tiny, but the family remains finite and acyclic.

### Load-Bearing Consequence
The natural next abstraction is now clear:

- not another micro case split
- not the too-small current `P012ExactScratch`
- but a **broader exact-family scratch with `c[n-4]` free**

So there is a real route out of the local branch soup. It is bigger, but still
finite and structured.

## Exploration 32 (probe)

### Strategy
Check whether the broadened exact-family source/destination starts have a
uniform rank gap, which would give the right theorem shape for a broader exact
scratch instead of an uncontrolled rank table.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  across all `27` broadened exact start pairs at `n = 9` (free `c3,c4,cN4`),
  the projected start-rank gap is uniformly:

  `rank(src) - rank(dst) = 4`

### Load-Bearing Consequence
This is the first strong evidence that the broadened exact-family route is not
just finite, but likely theorem-friendly. The right next theorem shape is no
longer mysterious:

- build a broader exact-family scratch with free `c[n-4]`
- prove step-nonincreasing on that projected graph
- use the uniform source/destination start-rank gap `4`

That is a much better target than continuing to peel off ad hoc subcases.

## Exploration 33 (probe)

### Strategy
Test the strongest non-sludge theorem candidate directly on the actual full
exact branch family:

- source starts: `c0=0, c1=1, c2=2, c[n-3]=1, c[n-2]=0, c[n-1]=1`
- destination starts: same but `c1=0`
- all other sites free

and ask whether the actual TP-bad closure has a uniform source/destination rank
gap.

### Outcome
SUCCEEDED

### Concrete Artifacts
- TOOLS:
  [p012_full_exact_gap_probe.py](./probes/p012_full_exact_gap_probe.py)
- COMPUTED EXAMPLES:
  on the actual full exact family:
  - `n = 10`: `4438` reachable states, acyclic, uniform gap `4` on all `81`
    start pairs
  - `n = 11`: `13455` reachable states, acyclic, uniform gap `4` on all `243`
    start pairs
  - `n = 12`: `40538` reachable states, acyclic, uniform gap `4` on all `729`
    start pairs
  - `n = 13`: `121822` reachable states, acyclic, uniform gap `4` on all
    `2187` start pairs

### Load-Bearing Consequence
This is now the strongest live theorem target:

> the full exact `P1:(0,1,2)` branch family has a uniform gap-`4` theorem
> under TP-bad reachability.

That is a much better abstraction than any branch-by-branch splice attempt or
any fixed finite window that breaks at larger `n`.

## Exploration 34 (probe)

### Strategy
Look for a decomposition invariant on the actual full exact family by checking
whether the free middle strip always contains a separator zero, and if not,
what the no-zero residue actually looks like.

### Outcome
PARTIAL SUCCESS

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the `n = 12` full exact family closure:
  - `37034` reachable states have at least one zero in the free middle strip
  - `3504` reachable states have no zero in that strip
- COMPUTED EXAMPLES:
  for the `n = 12` no-zero residue, the free middle strip realizes exactly
  all `2^6 = 64` binary `{1,2}` words.

### Load-Bearing Consequence
The full-family theorem may admit a structural split:

1. separator-zero regime
2. pure binary-strip regime

That is not yet a proof, but it is a real structural split rather than ad hoc
branch peeling.

## Exploration 35 (probe)

### Strategy
Check whether the `n = 13` no-zero residue of the full exact family still
collapses exactly to the binary `{1,2}` middle-strip language, to see whether
the separator-zero / binary-strip split survives larger `n`.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  in the `n = 13` full exact family closure:
  - `7031` reachable states have no zero in the free middle strip
  - the set of no-zero middle-strip patterns is exactly all `2^7 = 128`
    binary `{1,2}` words

### Load-Bearing Consequence
The binary-strip branch is not an `n = 12` accident. It persists at `n = 13`
with the obvious next word length, so it is now a serious candidate for one
half of an inductive proof split.

## Exploration 36 (probe)

### Strategy
Look for a cleaner factorization of the full exact gap by checking whether the
source/destination start-rank gap `4` splits through a short explicit lead-in
from the source start.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  for the full exact family at `n = 10,11,12`, if

  `mid = move idx1 (move idx0 src)`

  then uniformly:

  - `rank(src) - rank(mid) = 2`
  - `rank(mid) - rank(dst) = 2`

### Load-Bearing Consequence
The gap-`4` theorem appears to factor through the explicit intermediate family

```text
(c0,c1,c2) = (1,2,2),  (c[n-3],c[n-2],c[n-1]) = (1,0,1).
```

That is a much better theorem target than one giant opaque exact-family rank
proof. It suggests a proof program:

1. source family -> explicit two-step intermediate family gives gap `2`
2. intermediate family -> destination family gives gap `2`

## Exploration 37 (probe)

### Strategy
Check whether the empirical four-step rank factorization is backed by an actual
universal TP-bad step ladder on the full exact family, rather than by unrelated
rank coincidences.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  for the full exact family at `n = 10,11,12`, the following ladder is
  universally TP-bad:

  `012…101 --idx0--> 112…101 --idx1--> 122…101 --idx0--> 022…101 --idx1--> 002…101`

- COMPUTED EXAMPLES:
  the corresponding rank drops on actual reachable states are uniformly:
  `1 + 1 + 1 + 1`.

### Load-Bearing Consequence
The strongest current theorem shape is no longer an opaque gap-`4` statement.
It is:

> the full exact `P1:(0,1,2)` branch carries a universal TP-bad ladder of
> length `4`, and the global TP-bad rank drops by `1` on each rung.

That is a much more realistic proof target.

## Exploration 38

### Strategy
Add the stronger good-cycle obstructions suggested by the ladder route directly
to `ConstLayerDAG`, so the endpoint and intermediate ladder families have
usable off-cycle certificates in live Lean code.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `not_mem_goodCycle_of_cN2_zero_cN1_one_c0_one`
- STRUCTURAL RESULTS:
  `not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c2_two`
- VERIFICATION:
  `lake build LeanMn.Convergence.ConstLayerDAG` succeeds

### Load-Bearing Consequence
The ladder route is no longer just empirical.
It now has live Lean-side off-cycle support for:

- the intermediate/right-rung families with `cN2=0, cN1=1, c0=1`
- the endpoint/left-rung families with `cN2=0, cN1=1, c0=0, c2=2`

This is the first real Lean-native progress toward packaging the full-family
ladder.

## Exploration 39

### Strategy
Package the empirical full-family ladder as real `cup2TpBadStepFwd` artifacts in
`ConstLayerDAG`, rather than leaving it only in probes.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p1_012_idx0_tpStep`
- STRUCTURAL RESULTS:
  `p1_112_idx1_tpStep`
- STRUCTURAL RESULTS:
  `p1_122_idx0_tpStep`
- STRUCTURAL RESULTS:
  `p0_022_idx1_tpStep`
- STRUCTURAL RESULTS:
  public theorem
  `p1_full_exact_four_step_tpReachable`
- STRUCTURAL RESULTS:
  public theorem
  `p1_full_exact_four_step_fc_down_one`
- VERIFICATION:
  `lake build LeanMn.Convergence.ConstLayerDAG` succeeds

### Load-Bearing Consequence
The full-family ladder is now a real Lean object:

```text
012…101 --idx0--> 112…101 --idx1--> 122…101 --idx0--> 022…101 --idx1--> 002…101
```

packaged as a TP-reachable chain theorem rather than just a probe observation.

It also now has a corrected quantitative statement in live Lean:

- the full four-step ladder drops `fc` by exactly `1`

That means the next theorem step is no longer “does this ladder exist?”
It is “what measure/rank statement do we prove on top of this ladder?”

## Exploration 40

### Strategy
Correct the ladder-side `fc` bookkeeping and package the net quantitative
statement in Lean, so the full exact ladder has both reachability and a real
numeric consequence on top of it.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p1_full_exact_four_step_fc_down_one`
- VERIFICATION:
  `lake build LeanMn.Convergence.ConstLayerDAG` succeeds

### Load-Bearing Consequence
The full-family ladder now has two live Lean outputs:

1. an explicit TP-reachable chain
2. a net `fc` drop of exactly `1`

This is enough structure to support the next abstraction layer; we are no
longer working only from external probes.

## Exploration 41 (probe)

### Strategy
Lean-check the concrete 6-boundary pair

`012101 -> 002101`

directly against the 617 edge relation, to remove any remaining ambiguity about
the edge orientation or the Python parsing of `sixTupleEdgeVals`.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  Lean confirms
  `¬ sixTupleEdge (002101) (012101)`

### Load-Bearing Consequence
For the concrete candidate family, the unresolved question is now genuinely the
`FutureFc` / `PhiFull` side, not the 617 graph encoding.

## Exploration 42

### Strategy
Package the first universal right-hand rung out of the endpoint family
`002…101` directly in Lean, so the post-ladder continuation is not only a
probe-level observation.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p0_002_idxN1_tpStep`
- VERIFICATION:
  `lake build LeanMn.Convergence.ConstLayerDAG` succeeds

### Load-Bearing Consequence
The recursive right-hand continuation has started to become real Lean code.
The endpoint family is no longer a dead endpoint in the formalized picture.

## Exploration 43

### Strategy
Package the endpoint family’s first two-step right fork in Lean, carrying the
key boundary values out explicitly so it can be used as a real continuation
theorem rather than just a probe pattern.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p0_002_right_two_step_tpReachable`
- VERIFICATION:
  `lake build LeanMn.Convergence.ConstLayerDAG` succeeds

### Load-Bearing Consequence
The endpoint family `002…101` now has a formal two-step continuation to the
family

`102…100`

with the relevant boundary values carried out. So the right-hand side is no
longer just “there exists some continuation”; it is a concrete Lean theorem.

## Exploration 44

### Strategy
Try to formalize the next clean full-exact support layer in live Lean:

1. identify the direct `idx1` destination with the 4-step ladder endpoint
2. use that to transport `FutureFc` / `PhiFull` equalities along the ladder
3. get a destination-side `PhiFull` lower bound for the strict
   `P1:(0,1,2)` family without reopening local case sludge

### Outcome
FAILED

### Concrete Artifacts
- VERIFICATION:
  `lake build LeanMn.Convergence.ConstLayerDAG` succeeds after backing the
  attempted lemmas back out of the live path.

### Load-Bearing Consequence
This route failed for a substantive mathematical reason, not just Lean
plumbing:

- the probe-level identity

  `idx1(src) = idx1(idx0(idx1(idx0(src))))`

  on the full exact `012…101` family is still the right empirical picture
- but the first rung `012…101 --idx0--> 112…101` drops `fc` by `2`, not by `1`
- so the tempting plan

  “use the first rung’s `PhiFull` lower theorem to force
  `PhiFull(dst) ≥ fc(dst) + 1`”

  is false as a quantitative route

In other words: the ladder exists, but its early `fc` bookkeeping is too coarse
to give the missing contradiction by the naive transport argument.

The right next target is therefore **not** “formalize the ladder harder”. It is
either:

1. a sharper destination-side theorem for the exceptional `002…101` family, or
2. a different invariant that survives the 4-step identification without losing
   the extra unit in the first rung

## Exploration 45 (probe)

### Strategy
Probe the actual TP-bad closure of the **exceptional destination** family

`002…22101`

directly, instead of continuing to reason from the earlier 9-coordinate
overapproximation that gave the rank-`1` anomaly.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  for the starts
  `00222101`, `002222101`, `0022222101`, `00222222101`,
  the actual TP-bad closure has:
  - `n = 9`: size `82`
  - `n = 10`: size `111`
  - `n = 11`: size `144`
  - `n = 12`: size `181`
- COMPUTED EXAMPLES:
  across those closures, actual Lean `cup2Fc` ranges from `2` to `5`
  and the destination start has `cup2Fc = 5`
- COMPUTED EXAMPLES:
  the coarse boundary-style projection count stays exactly `36`
  for `n = 9,10,11,12`
- COMPUTED EXAMPLES:
  at `n = 12`, the reachable middle strips are **exactly**
  the words of the form

  `1^a 0^b 2^c`

  with `a + b + c = 6` and `c ≥ 1`
- COMPUTED EXAMPLES:
  the same language description survives unchanged for `n = 9,10,11`,
  with middle-strip counts `6, 10, 15` matching the exact
  `1^a 0^b 2^c` count at those lengths

### Load-Bearing Consequence
This is the first genuinely sharp structural description of the destination
exception.

The old “rank-1 exceptional destination” picture from the widened exact scratch
now looks like an overapproximation artifact. On the **actual** TP-bad closure:

- the exceptional destination family is small
- it appears to be closed under a simple regular language
- and actual Lean `cup2Fc` never rises above the starting value `5`

So the next honest theorem target is no longer vague:

> prove an exact destination-family theorem for the language
> `1^a 0^b 2^c` on the free middle strip of `002…22101`

If that theorem lands, it should give the missing destination cap for the last
strict `P1:(0,1,2)` residue.

## Exploration 46 (probe)

### Strategy
Check whether the exceptional destination family needs full-string tracking, or
whether its TP-bad dynamics actually collapse to a small automaton on the block
lengths `(a,b,c)` in the language `1^a 0^b 2^c`.

### Outcome
SUCCEEDED

### Concrete Artifacts
- NEW TOOLING:
  `probes/p002_exceptional_family_probe.py`
- COMPUTED EXAMPLES:
  at `n = 12`, after projecting each reachable middle strip to its block-length
  triple `(a,b,c)`, every TP-bad move falls into one of two types:
  - boundary moves leave `(a,b,c)` unchanged
  - interior moves update `(a,b,c)` by local block-length rewrites
- COMPUTED EXAMPLES:
  the projected `(a,b,c)` transitions are independent of the full raw middle
  strip; they only depend on the current triple

### Load-Bearing Consequence
The exceptional destination family really does look like a proper small
parameterized scratch target:

- one parameterized regular family `1^a 0^b 2^c`
- one finite boundary-state layer
- one small move automaton on `(a,b,c)`

So the next implementation step should be a dedicated destination-family scratch
module, not more unstructured probing in `ConstLayerDAG`.

## Exploration 47

### Strategy
Start the destination-family scratch in Lean with the smallest nontrivial piece:
the exact middle-strip language object for the exceptional `002…22101` family.

### Outcome
SUCCEEDED

### Concrete Artifacts
- NEW TOOLING:
  `LeanMn/Convergence/P002ExceptionalScratch.lean`
- STRUCTURAL RESULTS:
  `p002ExceptionalMidABC`
- STRUCTURAL RESULTS:
  `p002ExceptionalMidShape`
- STRUCTURAL RESULTS:
  `p002ExceptionalFamily`
- STRUCTURAL RESULTS:
  `p002Exceptional_allTwos_start_family`
- STRUCTURAL RESULTS:
  `p002ExceptionalFamily_cN3_one`
- STRUCTURAL RESULTS:
  `p002ExceptionalBoundaryForAB_c2_ne_two_of_prefix`
- STRUCTURAL RESULTS:
  `p002ExceptionalMidABC_last_two`
- STRUCTURAL RESULTS:
  `p002ExceptionalMidABC_idx3_ne_two_of_prefix`
- STRUCTURAL RESULTS:
  `p002ExceptionalFamily_frontier_at_n4`
- VERIFICATION:
  `lake build LeanMn.Convergence.P002ExceptionalScratch` succeeds

### Load-Bearing Consequence
The exceptional destination family is no longer just a note and a Python probe.
There is now a live Lean scratch target for its middle-strip language.

This is still not the closure theorem or the final `fc` cap, but the scratch
now has:

- the exact family predicate
- the canonical start witness
- boundary extraction lemmas
- the guaranteed frontier at `n-4`

That is enough structure to start a real `cup2Fc ≤ 5` proof on the family.

## Exploration 48 (probe)

### Strategy
Test whether corrected Lean `cup2Fc` on the exceptional family is controlled by
the finite boundary layer plus a tiny regime constant, rather than by the full
middle strip.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  across `n = 9,10,11,12`, the exact formula holds on the actual TP-bad
  closure:
  - `A0B0`: `cup2Fc = budgetA0B0 + 1`
  - `A0Bp`: `cup2Fc = budgetA0Bp + 2`
  - `APos, b = 0`: `cup2Fc = budgetAPos + 2`
  - `APos, b > 0`: `cup2Fc = budgetAPos + 3`
- COMPUTED EXAMPLES:
  the finite budget maxima are:
  - `budgetA0B0 ≤ 4`
  - `budgetA0Bp ≤ 3`
  - `budgetAPos ≤ 2`

### Load-Bearing Consequence
This is the first exact theorem shape for the family that plausibly closes the
destination cap:

1. prove the regime-specific `cup2Fc = budget + extra` formula in Lean
2. discharge the budgets by finite `native_decide`
3. conclude `cup2Fc ≤ 5`

That is now the right target, not a generic closure-first approach.

## Exploration 49

### Strategy
Stabilize `P002ExceptionalScratch` around the exact-family helper layer instead
of forcing the full `A0B0` formula in one theorem. The goal is to land the
middle-index API that the eventual regime proof actually needs.

### Outcome
SUCCEEDED

### Concrete Artifacts
- STRUCTURAL RESULTS:
  `p002ExceptionalMidIdx`
- STRUCTURAL RESULTS:
  `right_p002ExceptionalMidIdx`
- STRUCTURAL RESULTS:
  `p002ExceptionalA0B0_midIdx_eq_two`
- STRUCTURAL RESULTS:
  `p002ExceptionalA0B0_mid_frontier_zero`
- VERIFICATION:
  `lake build LeanMn.Convergence.P002ExceptionalScratch` succeeds

### Load-Bearing Consequence
The failed `A0B0` proof was missing an explicit index API for the middle strip.
That API now exists.

So the next proof pass should reintroduce the `A0B0` regime formula on top of
these helpers, rather than trying to prove it with raw `omega`-generated `Fin`
terms inline.

## Exploration 26 (probe)

### Strategy
Lean-check one concrete `n = 9` `Pn2`-core step to distinguish two possibilities:
either the `Pn2` forbidden core is already impossible at the local TP-bad-step
level, or the only valid `Pn2` provider must use the exact-source reachability
hypothesis.

### Outcome
SUCCEEDED

### Concrete Artifacts
- COMPUTED EXAMPLES:
  Lean-checked witness at `n = 9`:
  `src = (1,2,2,2,2,2,1,1,1)` and
  `dst = (1,2,2,2,2,2,1,2,1)`
  satisfy `cup2TpBadStepFwd 9 src dst`.
- STRUCTURAL RESULTS:
  any `Pn2` provider theorem stated only from the current state plus the
  TP-bad-step hypotheses is false.
- STRUCTURAL RESULTS:
  the surviving `Pn2` target must use path-level reachability from the exact
  source start.
