# Exploration Log

## Strategy Register

### Eliminated approach classes

- Exploration 1: Any information-theory approach that only refines witness-side decoder anatomy, without aiming at a necessary condition on all valid systems or a forbidden condition on subthreshold systems, is off the lower-bound critical path.

### Obstructions

- Exploration 1: Exact tiny codes, shallow decoders, and compact local recovery theorems are not lower-bound progress by themselves. They remain witness properties until they are upgraded into a universal valid-system condition or a forbidden subthreshold condition.
- Exploration 2: Explicit subthreshold forced-kernel obstruction scalars carry substantially larger width-`n-2` forbidden mass than the valid coarse `FutureFc` layer. Any lower-bound theorem in this direction must explain a real gap, not a tiny perturbation.
- Exploration 3: The obstruction-side floor candidate survives same-`n` comparison: at `n=5,6`, explicit forced-kernel residual families remain well above the valid witness coarse `FutureFc` forbidden fraction.
- Exploration 5: The broader explicit sweep-shadow obstruction class sits even higher: its shadow indicators have forbidden fractions around `0.146..0.222` at `n=5,6`, far above the valid same-`n` coarse `FutureFc` regime.
- Exploration 6: The explicit shadow-floor candidate persists at `n=7` with assignment-stable forbidden fractions around `0.141..0.173`, while valid `CUP-2(n=7)` coarse `FutureFc` is only `0.002573`.
- Exploration 7: The shadow-floor class can now be stated sharply: for the tested `n=5,6,7` 3-binary `{2,3}` sweep-shadow families, the shadow-indicator forbidden fraction is assignment-invariant within each binary-placement class and equals an explicit rational value. Across all tested classes it is always at least `71/504`.
- Exploration 8: The shadow-floor class now has a real symbolic core:
  coordinatewise relabeling preserves forbidden fraction, which is the correct
  analytic mechanism behind assignment-invariance inside a binary-placement
  class.
- Exploration 9: The right missing symbolic step is now explicit sweep/shadow equivariance under coordinatewise ternary relabeling. Once that is proved, assignment-invariance inside each binary-placement class is no longer a computation but a theorem.
- Exploration 10: The sweep/shadow equivariance statement now has a Lean-facing lemma chain tied directly to `construct_sweep_cycle`, `check_cycle_consistency`, and `find_shadow_cycle`.
- Exploration 11: The weaker global shadow-floor law is now packaged explicitly:
  through `n=7`, every tested 3-binary `{2,3}` sweep-shadow family has
  shadow-indicator forbidden fraction at least `71/504`, with a same-`n`
  separation from the valid coarse-layer regime.
- Exploration 12: The algorithmic sweep/shadow equivariance route has direct support:
  `shadow_equivariance_check.py` verified the transport of both the returned
  canonical sweep cycle and the returned shadow cycle on all tested classes
  through `n=7`, with `109` assignment comparisons and `0` failures.
- Exploration 13: The symbolic proof should not be centered on `find_shadow_cycle`
  itself. The correct proof object is the explicit shadow family from the paper
  formulas; the search routine should remain only a corroborative audit.
- Exploration 14: The current symbolic proof object is narrower than the tested
  computational class: the explicit shifted-waterfall formulas are proof-ready
  for a canonical binary placement, while the broader tested placement classes
  still need a normalization theorem or an explicit arbitrary-placement formula.
- Exploration 15: The strongest current normalization clue is the cyclic gap
  pattern between the three binary processors. It is clearly informative, but
  not yet a complete invariant for the class-value law.
- Exploration 16: The right normalization target is directed, not dihedral:
  the canonical sweep fixes an orientation, so cyclic rotation is a symmetry but
  reflection need not be. This resolves the misleading `n=6` discrepancy
  between reflection-related classes with different values.
- Exploration 17: The obstruction branch now has a stable result package:
  symbolic core, broader computational shell, weaker global floor theorem
  statement, and explicit remaining gaps.
- Exploration 18: Post-feedback course correction:
  the branch should prioritize universal witness extraction as the main line,
  with pure spectral transport treated as a fast feasibility sidecar rather
  than the default whole program.
- Exploration 19: The first naive EC witness confirms a key split: local
  overlap-count EC scalars are width-3 local and have zero width-`n-2`
  forbidden mass. So the EC track cannot simply reuse the shadow-side
  forbidden-mass observable unchanged.
- Exploration 20: The EC track now has its first explicit-family theorem
  package: on the canonical BAF family, the total overlap witness is exactly
  `E_conf = 2(n-3)`.
- Exploration 21: The EC package now has a first broader theorem candidate:
  for any BAF word with consecutive binary triple, the palindromic mechanism
  should yield `E_conf > 0`, with a candidate sharper count `>= n-4`.
- Exploration 22: The EC-side universality pattern strengthens computationally:
  on the tested non-sweep `fc=2` family through `n=9`, the total confusability
  witness appears rigidly `E_conf = 2(n-3)`.
- Exploration 23: The branch now has a real `review_packet_v2` that presents
  both tracks together and explicitly frames the universal target as a likely
  disjunctive EC-or-shadow witness theorem.
- Exploration 24: The reviewer’s key EC question has a positive answer on the
  first model case: a **derived global consequence** of EC, namely the
  conflict-state indicator, has substantial nonzero width-`n-2` forbidden mass
  through the tested range.
- Exploration 25: The derived global EC witness `chi_conf` remains spectrally
  visible across the whole tested non-sweep `fc=2` BAF family through `n=7`,
  not just the canonical word. This is the first serious sign of partial
  reunification between the EC and shadow tracks at the observable level.
- Exploration 26: The weak global EC bridge law persists through `n=8` on the
  tested BAF family, with floor at least `37/324 > 0.1141`.
- Exploration 29: The broader BAF family now has a clean support-geometry
  candidate for `chi_conf`: the conflict states appear to be exactly all
  good-cycle steps except the two turnaround steps and their immediate
  successors.
- Exploration 30: The broader BAF support-geometry formula for `chi_conf` has
  now been audited on every tested non-sweep `fc=2` BAF word through `n=9`,
  with zero failures.
- Exploration 32: The EC support formula now has a local arc-by-arc proof
  skeleton: on each directed arc between turnarounds, the conflict witness is
  carried by the mover processor at the arc start, by both current and previous
  processors in the middle, and by the previous processor at the arc end.
- Exploration 50: The broader EC support proof now has an explicit witness
  selection rule on each directed arc:
  interior mover steps are witnessed by the mover itself, while arc-terminal
  interior steps are witnessed by the immediately preceding interior processor.
- Exploration 33: The `chi_conf` support formula now survives one further size
  extension to `n=9`, strengthening it from a low-`n` pattern into a more
  credible general BAF theorem candidate.
- Exploration 34: The EC support theorem now has an explicit processorwise union
  formula:
  `ConfState = ⋃_{j=1}^{n-3} {j, j+1, 2n-2-j, 2n-1-j}`,
  which collapses directly to the complement-of-four-states formula.
- Exploration 35: The canonical support formula for `chi_conf` is now fully
  written as a theorem and proof, while the broader BAF support statement
  remains an audited extension candidate.
- Exploration 48: The broader BAF support theorem is now cleanly reduced to one
  arc-local lemma plus the four boundary exceptions.
- Exploration 36: The canonical EC bridge object now has a direct structural
  relation to the cycle indicator:
  `chi_conf = chi_good - chi_exc`,
  where `chi_exc` is the indicator of the four distinguished exceptional
  states.
- Exploration 37: The target-signature route on `chi_good` fails as a separator:
  the forbidden fraction of the good-cycle indicator lives on the same spectral
  scale for valid witnesses and explicit obstruction families.
- Exploration 38: The branch now has its first explicit disjunctive witness
  theorem candidate, combining the shadow-side weak floor and the EC-side weak
  bridge law under one common lower bound `37/324`.
- Exploration 39: The branch now has its first explicit **bridge theorem**
  candidate on one architecture class: on the tested consecutive-binary
  subthreshold family at `n=5`, every valid cycle is blocked by either EC or
  shadow, with no leftovers.
- Exploration 40: The explicit `n=5` bridge theorem candidate also comes with a
  simple tested case-split predicate: `any_overlap` separates the EC side from
  the shadow side on that architecture class.
- Exploration 42: The `n=5` bridge predicate strengthens further: every
  overlap-free cycle lies in a single dihedral orbit of one explicit
  shadow-producing mover word.
- Exploration 49: The branch now has a stable disjunctive bridge route note
  stating the next true target: prove a broader bridge theorem from the current
  EC-side and shadow-side weak floor laws.
- Exploration 43: The next bridge route is now packaged explicitly:
  `any_overlap` as the tested bridge predicate, plus overlap-free orbit
  rigidity on the first bridge class.
- Exploration 44: Extending the overlap-free orbit classification to the `n=7`
  consecutive-binary class crosses the cheap-probe boundary and is currently a
  computational stall, not yet a contradiction.
- Exploration 41: Extending the bridge predicate test to the `n=7`
  consecutive-binary class crosses the current cheap-probe boundary. This is a
  computational stall, not yet a mathematical failure of the predicate.
- Exploration 28: The canonical EC bridge object `chi_conf` now has a simple
  geometric description: on the canonical BAF family it is exactly the good
  cycle with four distinguished turnaround/endpoint states removed.
- Exploration 27: The `chi_conf` bridge now has a symbolic route note, but
  pushing the computational floor to `n=9` crosses the cheap-probe boundary.
  So the next work on this side should be proof refinement rather than more
  size-extension by default.

### Building Blocks

- Exploration 1: Forbidden width-`n-2` interaction suppression remains the strongest current candidate for a universal necessary condition.
- Exploration 1: The two-level decomposition
  `FutureFc` handles most suppression, slice-rank carries the residual
  remains the cleanest bridge from witness structure to a possible obstruction theorem.
- Exploration 1: The reduced-prefix coarse-code package may still matter as a bridge theorem if it can be universalized or shown to fail below threshold.
- Exploration 2: The obstruction-side forced-kernel scalars already give a concrete forbidden-mass floor candidate on explicit subthreshold families:
  - at `n=5`, actual forbidden fractions are about `0.068..0.097`,
  - at `n=6`, about `0.031..0.049`,
  compared to valid witness coarse-layer values near `10^{-4}` at `n=9`.
- Exploration 3: Same-`n` valid coarse-layer references:
  - `CUP-2(n=5)`: `FutureFc` forbidden fraction `0.026144`
  - `CUP-2(n=6)`: `FutureFc` forbidden fraction `0.008582`
  so the explicit subthreshold residual families already sit above the valid
  coarse witness regime by substantial margins at matching sizes.
- Exploration 4: Among the currently tested obstruction-side scalars, the
  simplest primary floor candidate is `kernel_indicator`: its same-`n` margins
  above valid coarse `FutureFc` are `0.042569` at `n=5` and `0.022750` at
  `n=6`.
- Exploration 5: The explicit 3-binary `{2,3}` sweep-shadow families give an
  even stronger floor candidate than the forced-kernel residual families:
  shadow-indicator forbidden mass is approximately
  `0.152778 .. 0.222222` at `n=5`,
  `0.146605 .. 0.194444` at `n=6`.
- Exploration 19: The lower-bound obstruction branch must explicitly bifurcate:
  one track for shadow witnesses, one track for EC witnesses. The current
  package only covers the shadow side.
- Exploration 6: The same sweep-shadow floor remains stable at `n=7` across all
  tested ternary assignments on the 5 rotation classes with 3 binary
  processors:
  `0.140873 .. 0.172619`.

### Known reformulations

- Exploration 1: Lower-bound triage lens. Every info-theory result must be classified as `keep`, `conditional`, or `shelve` according to whether it could become
  1. a necessary condition on all valid systems,
  2. a forbidden condition on subthreshold systems,
  3. or a bridge theorem to one of those.
  LOAD-BEARING: very high. This is the default representation for this obstruction-focused branch.
- Exploration 2: Subthreshold floor view. Instead of asking for an exact code obstruction immediately, ask for a positive lower bound on forbidden width-`n-2` mass for canonical subthreshold obstruction-side scalars. LOAD-BEARING: high. This is the first concrete forbidden-condition candidate on the redirected branch.
- Exploration 3: Same-`n` floor-gap view. The right first forbidden theorem is
  not cross-`n` qualitative separation but a same-size gap between explicit
  subthreshold obstruction scalars and the valid coarse `FutureFc` layer.
  LOAD-BEARING: high. This is the strongest theorem-shaped form currently
  supported by data.
- Exploration 4: Primary-floor-scalar view. Treat `kernel_indicator` as the
  first obstruction scalar to theoremize, with `peel_depth` as a backup/robustness
  scalar. LOAD-BEARING: medium-high. This focuses the next admissible theorem
  attempt.
- Exploration 5: Explicit shadow-floor view. Use shadow-cycle indicators on the
  canonical 3-binary `{2,3}` sweep families as the first broad explicit
  subthreshold class, rather than staying inside the narrower forced-kernel
  residual families. LOAD-BEARING: high. This is now the strongest explicit
  forbidden-condition candidate on the branch.
- Exploration 6: Assignment-stable shadow-floor law. The shadow-floor values are
  stable across all tested ternary assignments on the explicit sweep-shadow
  class, suggesting the floor depends mainly on the binary-placement class.
  LOAD-BEARING: high. This strengthens the case for theoremizing the shadow
  class first.
- Exploration 7: Explicit class-value law. The shadow-floor phenomenon can be
  stated class-by-class with exact rational values, not just numerically as a
  range. LOAD-BEARING: high. This is now a real explicit-family theorem
  candidate.
- Exploration 8: Relabeling-invariance proof package. The first paper-facing
  proof component is now in place: forbidden interaction fraction is invariant
  under coordinatewise relabeling, so the remaining symbolic work is to prove
  equivariance of the explicit sweep/shadow construction itself. LOAD-BEARING:
  high. This is the first real proof ingredient on the obstruction branch.
- Exploration 9: Sweep/shadow equivariance view. The assignment-stability of the
  shadow-floor class should be proved by transporting both the canonical sweep
  cycle and the induced shadow cycle under coordinatewise ternary `1 <-> 2`
  relabelings. LOAD-BEARING: high. This is the cleanest symbolic route from the
  current computational class table to an explicit-family theorem.
- Exploration 10: Construction-primitive equivariance. The symbolic proof should
  be decomposed into finite lemmas about:
  sweep construction, determined-entry transport, forced-move transport, and
  shadow-path transport. LOAD-BEARING: high. This is the first genuinely
  Lean-compatible proof breakdown for the explicit shadow-floor theorem.
- Exploration 11: Weaker global floor law. State the first paper-facing theorem
  as a lower bound `>= 71/504` on the tested explicit shadow class, rather than
  the stronger exact class-value law. LOAD-BEARING: high. This is the cleanest
  first obstruction theorem on the branch.
- Exploration 12: Algorithmic equivariance audit. The proof route via
  `construct_sweep_cycle` and `find_shadow_cycle` is not just plausible; it is
  computationally corroborated on the full tested class. LOAD-BEARING: high.
  This materially de-risks the symbolic route.
- Exploration 13: Explicit-shadow symbolic route. Replace the search-based proof
  target by the explicit shadow-family formulas from the paper proof. Use
  `find_shadow_cycle` only for discovery and audit. LOAD-BEARING: very high.
  This is the right proof-engineering move for both paper clarity and Lean
  compatibility.
- Exploration 14: Scope-split shadow theorem. Distinguish clearly between
  1. the canonical proof-ready explicit shadow family,
  2. the broader computational explicit-family class.
  LOAD-BEARING: very high. This prevents us from overstating what is currently
  symbolic.
- Exploration 15: Gap-pattern normalization clue. Track the broader placement
  classes by the normalized cyclic gap triple between binary processors.
  LOAD-BEARING: medium-high. This is the best current clue for the missing
  normalization theorem, but it is not yet sufficient.
- Exploration 16: Directed-sweep normalization. Normalize placement classes up
  to cyclic rotation only, not reflection, because the canonical sweep fixes a
  directed mover word. LOAD-BEARING: high. This makes the normalization problem
  sharper and more honest.
- Exploration 17: Obstruction result package. Separate the branch into:
  1. main preliminary theorem,
  2. symbolic core,
  3. broader computational shell,
  4. remaining open layers.
  LOAD-BEARING: high. This gives the branch a stable paper-facing shape.
- Exploration 19: EC/shadow split. The obstruction program should be phrased as
  a two-track witness program, possibly leading to a disjunctive theorem:
  every subthreshold system yields either an EC witness or a shadow witness
  with obstruction mass. LOAD-BEARING: very high. This keeps the branch aligned
  with the actual lower-bound mechanism split.
- Exploration 18: Witness-extraction main line. Use the current explicit
  shadow-floor theorem as model evidence for a canonical obstruction witness
  `Phi_S`, and treat pure transport as a kill-or-keep test rather than as the
  whole branch. LOAD-BEARING: very high. This aligns the branch directly with
  the feedback’s bridge-theorem demand.
- Exploration 19: Split-observable witness program. The likely universal
  theorem is now disjunctive not only in witness type (EC or shadow), but also
  in observable:
  shadow-side forbidden mass versus an EC-side zero-error/confusability
  quantity. LOAD-BEARING: very high. This is the first concrete sign that a
  single common spectral observable is probably too optimistic.
- Exploration 20: Canonical EC witness law. The EC side now has a clean model
  case theorem on the canonical BAF family, measured by a confusability
  observable rather than forbidden mass. LOAD-BEARING: very high. This is the
  first genuine EC-side theorem package on the branch.
- Exploration 21: General BAF EC witness. Recast the palindromic EC theorem as
  a witness theorem `E_conf > 0` for arbitrary BAF words, with `n-4` as a
  sharper count candidate. LOAD-BEARING: high. This is the first plausible
  bridge from the EC model case toward a broader EC theorem.
- Exploration 22: Tested BAF universality law. The EC-side branch now has a
  strong computational universality pattern: not just positivity, but exact
  linear growth `E_conf = 2(n-3)` on the tested non-sweep `fc=2` family.
  LOAD-BEARING: very high. This materially strengthens the EC track.
- Exploration 23: Two-track review framing. Package the obstruction branch for
  review as:
  1. shadow theorem package,
  2. EC theorem package,
  3. split-observable lesson,
  4. disjunctive bridge problem.
  LOAD-BEARING: high. This is the right review framing now.
- Exploration 24: Partial reunification clue. Raw EC overlap is spectrally
  invisible, but a derived global EC quantity may not be. LOAD-BEARING: very
  high. This is the first sign that the EC and shadow tracks might partially
  reunify at a deeper level.
- Exploration 25: EC-side forbidden-mass bridge. The conflict-state indicator
  stays uniformly positive on the tested broader BAF family, so the shadow-side
  forbidden-mass observable may extend to a meaningful derived EC witness after
  all. LOAD-BEARING: very high. This is the strongest bridge result on the EC
  track so far.
- Exploration 26: Weak global EC bridge law. The derived EC witness now has a
  stable tested floor through `n=8`, so it can be stated in the same theorem
  style as the weaker shadow-floor law. LOAD-BEARING: very high. This is the
  first EC-side theorem candidate that is directly parallel to the shadow-side
  weak floor theorem.
- Exploration 29: BAF conflict-state geometry. The EC bridge object `chi_conf`
  is now close to a true word-level theorem, not just a canonical-family
  definition. LOAD-BEARING: very high. This is the strongest symbolic advance
  on the EC bridge side so far.
- Exploration 30: Audited BAF support formula. The word-level support geometry
  of `chi_conf` is no longer a hand-checked pattern; it is audited across the
  full tested BAF family through `n=8`. LOAD-BEARING: very high. This is the
  cleanest current symbolic-looking theorem candidate on the EC side.
- Exploration 32: Arc-local support proof. The support formula is no longer only
  a word-level pattern; it now has a local witness mechanism organized by the
  two directed arcs of the BAF word. LOAD-BEARING: high. This is the right
  proof shape for a future symbolic argument.
- Exploration 50: Explicit witness selection on arcs. The arc-local proof is no
  longer existential; it now has a concrete witness rule. LOAD-BEARING: high.
  This should make the broader BAF support theorem much easier to formalize.
- Exploration 34: Processorwise union formula. The support theorem is now
  decomposed exactly as a union over interior processors of four explicit step
  indices. LOAD-BEARING: very high. This is the cleanest proof handle on the EC
  bridge object so far.
- Exploration 35: Canonical EC theorem closed. The EC branch now has one
  genuinely finished symbolic theorem: the canonical support formula for
  `chi_conf`. LOAD-BEARING: very high. This is the first fully written proof
  theorem on the EC bridge side.
- Exploration 48: Arc-local reduction for the broader BAF theorem. The broader
  support formula is no longer a vague extension; it reduces to a single
  word-generic arc statement. LOAD-BEARING: high. This makes the next proof
  task sharply defined.
- Exploration 36: Cycle-indicator reduction. The EC bridge object is now
  directly related to the good-cycle indicator itself, which ties the EC track
  much more closely to the original spectral target-signature program.
  LOAD-BEARING: very high. This is the strongest conceptual bridge on the EC
  side so far.
- Exploration 37: `chi_good` is not the target signature. The good-cycle
  indicator itself does not separate valid and explicit obstructed families by
  forbidden mass. LOAD-BEARING: very high. This sharply narrows the pure
  spectral program.
- Exploration 38: Explicit disjunctive theorem candidate. The two-track program
  now has a single theorem-shaped object rather than two disconnected packages:
  on the union of the tested explicit families, there exists a witness with
  forbidden mass at least `37/324`. LOAD-BEARING: very high. This is the first
  theorem matching the intended endgame shape.
- Exploration 39: Explicit bridge theorem candidate. The branch now has one
  architecture class on which the actual disjunction `EC or SHADOW` is observed
  cycle-by-cycle. LOAD-BEARING: very high. This is the first genuine bridge
  object on the branch.
- Exploration 40: First explicit bridge predicate. The disjunctive theorem is
  no longer just an existential partition on the tested class; it is governed
  by a concrete cycle-level predicate (`any_overlap`). LOAD-BEARING: very high.
  This is the first real bridge predicate on the branch.
- Exploration 42: Overlap-free orbit rigidity. On the first explicit bridge
  class, the shadow side is not just “everything else”; it collapses to one
  explicit mover-word orbit. LOAD-BEARING: very high. This is the strongest
  bridge-structure result on the branch so far.
- Exploration 49: Disjunctive bridge route. The branch now has a single note
  that packages the bridge endgame in theorem form rather than as scattered
  observations. LOAD-BEARING: high. This is the right target for the next proof
  sprint.
- Exploration 43: Bridge-predicate route. Package the bridge side as:
  tested predicate `any_overlap`,
  tested `n=5` disjunction,
  tested overlap-free orbit rigidity,
  and a future “if not overlap, then rigid shadow form” theorem direction.
  LOAD-BEARING: very high. This is the current best bridge program.
- Exploration 44: Bridge-classification stall. The `n=7` orbit-rigidity check is
  no longer a cheap probe. LOAD-BEARING: medium. This is a useful stop sign,
  not a mathematical setback.
- Exploration 41: Bridge-predicate scale check. The `n=7` extension of the
  explicit bridge predicate is now a nontrivial computation rather than a quick
  probe. LOAD-BEARING: medium-high. This does not weaken the theorem candidate,
  but it tells us not to depend on easy brute-force extension here.
- Exploration 28: Canonical conflict-state geometry. `chi_conf` is no longer
  just an algorithmically extracted set; it has a clean symbolic description on
  the canonical BAF family. LOAD-BEARING: high. This makes `chi_conf` a much
  more plausible EC-side bridge object.
- Exploration 27: EC bridge symbolic route. Treat `chi_conf` as the leading
  EC-side bridge object and refine its proof path; do not keep broadening its
  computational range unless a specific theorem question requires it. LOAD-BEARING:
  high. This keeps the EC track from turning into another open-ended sweep.

## Exploration 1

### Strategy

Start a separate obstruction-focused residue branch by writing an explicit admission rule for which information-theory results are allowed to remain on the lower-bound critical path.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing this branch as open-ended witness anatomy. From this point onward, witness-side exact code results only stay relevant if they are explicitly being converted into:

- a necessary condition on all valid systems,
- a forbidden condition on subthreshold systems,
- or a bridge theorem toward one of those.

### Surviving Structure

- The strongest live lower-bound-facing candidates are:
  - universal forbidden width-`n-2` suppression,
  - subthreshold forbidden-mass floor,
  - two-level `FutureFc + slice-rank` suppression as a bridge theorem.
- The strongest witness-side structures retained only conditionally are:
  - exact tiny `FutureFc` codes,
  - reduced-prefix recovery trees,
  - compact local `CUP-2` theorem.

### Reformulations

- Necessary-or-forbidden branch filter:
  the right question is no longer “what else is true of the witness?” but
  “can this be turned into a necessary valid-system condition or a forbidden subthreshold condition?”

LOAD-BEARING ASSESSMENT: very high. This is the branch discipline needed to prevent further drift.

### Concrete Artifacts

DOCS:

- `info_theory/lb_redirect_roadmap.md`
  records the strict triage, admissible theorem targets, and branch discipline.

STRUCTURAL RESULTS:

- Witness-side decoder polishing is no longer treated as lower-bound progress by default.
- The next admissible theorem attempts are restricted to:
  1. universal suppression theorem,
  2. subthreshold floor theorem,
  3. necessary reduced-prefix theorem,
  4. subthreshold code failure theorem.

REPRESENTATIONS:

- “Lower-bound triage lens” representation.

### What Would Unblock This

The next useful step is to formulate the strongest plausible universal coarse-layer suppression theorem and the strongest plausible subthreshold forbidden-mass floor theorem, then test only those.

### Key Parameters

- No new numerical sweep. This was a strategic redirect and branch setup.

### Open Questions

- Can forbidden width-`n-2` suppression be stated as a universal valid-system condition?
- Can any explicit subthreshold family be shown to violate a positive forbidden-mass floor?
- Which current witness-side theorem has the shortest route to becoming a genuine obstruction?

## Synthesis after exploration 1

- The branch now has a hard filter.
- The next admissible work is no longer decoder mining; it is obstruction formulation.

## Exploration 2

### Strategy

Formulate the first concrete forbidden-condition candidate by comparing the
strongest valid coarse-layer suppression signal against explicit subthreshold
obstruction-side scalars, using the forced-kernel residual families at
`n=5,6`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the hope that the valid witness suppression phenomenon is so tiny
that obstruction-side families might accidentally match it. The gap is large on
the explicit subthreshold residual families we can currently measure.

### Surviving Structure

- Valid witness coarse-layer forbidden fractions at width `n-2` are tiny:
  - `CUP-2(n=9)`: `FutureFc = 0.000255`
  - `Sol3(n=9)`: `FutureFc = 0.000170`
- Explicit subthreshold forced-kernel obstruction-side scalars are much larger.
  For the canonical residual families tested:
  - `n=5`, kernel-indicator forbidden fractions lie in
    `0.068713 .. 0.097222`
  - `n=5`, peel-depth forbidden fractions lie in
    `0.071082 .. 0.079303`
  - `n=6`, kernel-indicator forbidden fractions lie in
    `0.031332 .. 0.049383`
  - `n=6`, peel-depth forbidden fractions lie in
    `0.020846 .. 0.024903`
- These are still comfortably below their shuffled nulls, so the theorem target
  is not “subthreshold means no suppression at all.” The target is a **positive
  floor gap** separating valid witness-scale suppression from obstruction-scale
  suppression.

### Reformulations

- Subthreshold forbidden-mass floor view:
  the right lower-bound-facing question is not “can subthreshold families ever
  suppress forbidden mass?” but
  “how small can their forbidden mass possibly get, and is there a floor above
  the valid witness coarse-layer regime?”

LOAD-BEARING ASSESSMENT: high. This is the first concrete forbidden-condition
candidate supported by explicit obstruction-side computations.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `forced_kernel_spectrum.py --n 5`:
  8 full cycles on `ms=(2,2,2,3,3)`, with
  - kernel-indicator actual forbidden fractions
    `0.068713 .. 0.097222`
  - peel-depth actual forbidden fractions
    `0.071082 .. 0.079303`
- `forced_kernel_spectrum.py --n 6`:
  8 full cycles on `ms=(2,2,2,3,3,3)`, with
  - kernel-indicator actual forbidden fractions
    `0.031332 .. 0.049383`
  - peel-depth actual forbidden fractions
    `0.020846 .. 0.024903`
- Comparison point from valid witnesses:
  - `CUP-2(n=9)`: `FutureFc = 0.000255`
  - `Sol3(n=9)`: `FutureFc = 0.000170`

TOOLS:

- `info_theory/forced_kernel_spectrum.py`
  computes obstruction-side forbidden spectra on canonical subthreshold
  residual families.
- `info_theory/twolevel_spectrum.py`
  provides the valid coarse-layer comparison values.

STRUCTURAL RESULTS:

- There is a visible coarse-layer forbidden-mass gap between known valid
  witnesses and explicit subthreshold obstruction-side families.
- The candidate lower-bound theorem should target a **floor**, not total
  absence of suppression.

REPRESENTATIONS:

- “Subthreshold floor candidate” representation.

### What Would Unblock This

The next useful step is to turn this from an example bank into a theorem
candidate by deciding the strongest plausible quantitative form:

1. a universal positive lower bound for explicit subthreshold architecture
   classes,
2. or at least a theorem that subthreshold families cannot enter the witness
   coarse-layer regime `~10^{-4}`.

### Key Parameters

- Valid comparison data:
  `CUP-2(n=9)`, `Sol3(n=9)` coarse `FutureFc`.
- Subthreshold families:
  forced-kernel residual families at `n=5,6`.

### Open Questions

- What is the strongest quantitative floor statement that is still plausible?
- Can the same floor be measured on broader explicit subthreshold classes than
  the forced-kernel residual families?
- Is the right obstruction theorem about the coarse layer `FutureFc`, or about
  the full rank / slice residual?

## Synthesis after exploration 2

- The redirected branch now has its first genuine forbidden-condition candidate.
- The lower-bound-facing gap is large enough to matter.
- The next admissible move is to sharpen this floor candidate, not to return to
  witness decoder anatomy.

## Exploration 3

### Strategy

Sharpen the obstruction-side floor candidate into a same-`n` theorem form by
comparing the explicit forced-kernel residual families at `n=5,6` against the
valid witness coarse layer `FutureFc` at the same sizes.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the current floor candidate as merely a cross-`n`
phenomenon. The gap already exists at matching sizes between explicit
subthreshold residual families and valid coarse witnesses.

### Surviving Structure

- Valid same-`n` coarse-layer references:
  - `CUP-2(n=5)`: `FutureFc = 0.026144`
  - `CUP-2(n=6)`: `FutureFc = 0.008582`
- Explicit subthreshold forced-kernel families:
  - `n=5`:
    - kernel indicator `0.068713 .. 0.097222`
    - peel depth `0.071082 .. 0.079303`
  - `n=6`:
    - kernel indicator `0.031332 .. 0.049383`
    - peel depth `0.020846 .. 0.024903`
- So at matching sizes:
  - `n=5`, every tested obstruction scalar stays comfortably above valid
    coarse `FutureFc`,
  - `n=6`, every tested obstruction scalar also stays above valid coarse
    `FutureFc`.
- Full-rank references at matching sizes are even smaller:
  - `CUP-2(n=5)` full-rank extension `0.017567`
  - `CUP-2(n=6)` full-rank extension `0.004541`
  so the same families also clear a gap relative to the full valid rank.

### Reformulations

- Same-`n` floor-gap view:
  the first realistic obstruction theorem is a same-size lower bound on
  forbidden width-`n-2` mass for explicit subthreshold residual families,
  compared against the valid coarse `FutureFc` regime.

LOAD-BEARING ASSESSMENT: high. This gives the first theorem candidate that is
already quantitative and same-`n`, rather than a looser cross-`n` heuristic.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/theorem_candidates.md`
  records the current obstruction-side theorem candidates.

COMPUTED EXAMPLES:

- `twolevel_spectrum.py --family cup2 --n 5`:
  `FutureFc = 0.026144`
- `twolevel_spectrum.py --family cup2 --n 6`:
  `FutureFc = 0.008582`
- `anova_interaction_spectrum.py --family cup2 --n 5 --width 3`:
  full-rank forbidden fraction `0.017567`
- `anova_interaction_spectrum.py --family cup2 --n 6 --width 4`:
  full-rank forbidden fraction `0.004541`
- `forced_kernel_spectrum.py --n 5,6`:
  explicit subthreshold obstruction-side ranges as recorded above.

STRUCTURAL RESULTS:

- The subthreshold floor candidate survives same-`n` comparison.
- The candidate theorem should be stated first for explicit forced-kernel
  residual families, not yet for all subthreshold systems.

REPRESENTATIONS:

- “Same-`n` subthreshold floor gap” representation.

### What Would Unblock This

The next useful step is to convert this into the strongest plausible theorem
statement by deciding whether the right floor target is:

1. kernel indicator,
2. peel depth,
3. or “either canonical obstruction scalar”.

Then test whether the same floor extends to a broader explicit subthreshold
class.

### Key Parameters

- Valid references:
  `CUP-2(n=5,6)` coarse `FutureFc`, and full rank.
- Obstruction families:
  forced-kernel residual families at `n=5,6`.

### Open Questions

- What is the cleanest quantitative floor statement that remains plausible?
- Does peel depth give a more stable lower bound than kernel indicator?
- Can the same floor phenomenon be exhibited on broader explicit subthreshold
  classes than the forced-kernel residuals?

## Synthesis after exploration 3

- The obstruction branch now has its first same-`n` theorem candidate.
- The next admissible move is to sharpen that floor candidate, not to broaden
  back into witness-side code structure.

## Exploration 4

### Strategy

Choose the strongest current same-`n` obstruction scalar for a first explicit
floor theorem candidate, comparing `kernel_indicator` against `peel_depth` on
the forced-kernel residual families.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out keeping the first floor candidate underspecified. The branch now
has enough data to prioritize one primary scalar instead of carrying both
equally.

### Surviving Structure

- `kernel_indicator` gives the stronger uniform same-`n` margin over the valid
  coarse `FutureFc` layer:
  - `n=5`: min gap `0.042569`
  - `n=6`: min gap `0.022750`
- `peel_depth` remains useful as a backup/robustness scalar:
  - `n=5`: min gap `0.044938`
  - `n=6`: min gap `0.012264`
- So the cleanest next explicit theorem candidate is a floor theorem for the
  kernel indicator on the forced-kernel residual families.

### Reformulations

- Primary-floor-scalar view:
  the first obstruction theorem should target `kernel_indicator`, with
  `peel_depth` retained as corroborating evidence rather than as the main
  scalar.

LOAD-BEARING ASSESSMENT: medium-high. This narrows the next theorem attempt to
a single preferred scalar and avoids drifting into parallel scalar variants.

### Concrete Artifacts

DOCS:

- `lb_obstruction/theorem_candidates.md` now records `kernel_indicator` as the
  preferred primary floor candidate.

COMPUTED EXAMPLES:

- `n=5`:
  - valid coarse `FutureFc = 0.026144`
  - kernel-indicator floor candidate `>= 0.068713`
  - peel-depth floor candidate `>= 0.071082`
- `n=6`:
  - valid coarse `FutureFc = 0.008582`
  - kernel-indicator floor candidate `>= 0.031332`
  - peel-depth floor candidate `>= 0.020846`

STRUCTURAL RESULTS:

- The obstruction branch now has a preferred first scalar for a floor theorem.

REPRESENTATIONS:

- “Primary floor scalar” representation.

### What Would Unblock This

The next useful step is to state the strongest plausible theorem form for
`kernel_indicator` on the explicit forced-kernel residual families, then test
whether a broader explicit subthreshold class still clears the same floor
regime.

### Key Parameters

- Compared scalars:
  - `kernel_indicator`
  - `peel_depth`
- Same-`n` valid references:
  `CUP-2(n=5,6)` coarse `FutureFc`.

### Open Questions

- Can the kernel-indicator floor be proved directly from the forced-kernel
  elimination dynamics?
- Is there a broader explicit subthreshold class on which the same floor holds?
- Does the full-rank extension give an even cleaner obstruction theorem than the
  coarse `FutureFc` comparison?

## Synthesis after exploration 4

- The obstruction branch now has a preferred first theorem candidate.
- The next admissible move is to state and test a kernel-indicator floor
  theorem on broader explicit subthreshold classes.

## Exploration 5

### Strategy

Broaden the same-`n` floor candidate from forced-kernel residual families to a
larger explicit subthreshold class already present in the lower-bound machinery:
the 3-binary `{2,3}` sweep-shadow families at `n=5,6`, using shadow indicators
as obstruction scalars.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the concern that the current floor candidate is an artifact of the
narrow forced-kernel residual families. A broader explicit subthreshold class
already exhibits an even stronger same-`n` forbidden-mass floor.

### Surviving Structure

- For the explicit 3-binary `{2,3}` sweep-shadow families, the shadow indicator
  has very large width-`n-2` forbidden fraction:
  - `n=5`:
    - `(2,2,2,3,3)`: `0.152778`
    - `(2,2,3,2,3)`: `0.222222`
  - `n=6`:
    - `(2,2,2,3,3,3)`: `0.146605`
    - `(2,2,3,2,3,3)`: `0.152778`
    - `(2,2,3,3,2,3)`: `0.158951`
    - `(2,3,2,3,2,3)`: `0.194444`
- These values are stable across all tested ternary-value assignments for the
  canonical sweep cycles in each rotation class.
- Same-`n` valid coarse-layer references remain far below:
  - `CUP-2(n=5)`: `0.026144`
  - `CUP-2(n=6)`: `0.008582`
- So this explicit shadow class gives a much stronger same-`n`
  forbidden-mass floor candidate than the forced-kernel residual families.

### Reformulations

- Explicit shadow-floor view:
  the first strong obstruction theorem should probably be about shadow-cycle
  indicators on explicit 3-binary `{2,3}` families, not about the narrower
  forced-kernel residuals alone.

LOAD-BEARING ASSESSMENT: high. This is currently the strongest explicit
forbidden-condition candidate on the redirected branch.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/shadow_spectrum.py`
  computes forbidden spectra for canonical shadow-cycle indicators on explicit
  sweep-shadow families.

COMPUTED EXAMPLES:

- `n=5`, all ternary assignments on:
  - `(2,2,2,3,3)` give `0.152778`
  - `(2,2,3,2,3)` give `0.222222`
- `n=6`, all ternary assignments on:
  - `(2,2,2,3,3,3)` give `0.146605`
  - `(2,2,3,2,3,3)` give `0.152778`
  - `(2,2,3,3,2,3)` give `0.158951`
  - `(2,3,2,3,2,3)` give `0.194444`

STRUCTURAL RESULTS:

- The shadow-floor candidate is assignment-stable on the tested sweep-shadow
  families.
- The explicit shadow class is a broader and stronger obstruction class than
  the forced-kernel residual families.

REPRESENTATIONS:

- “Explicit shadow-floor theorem candidate” representation.

### What Would Unblock This

The next useful step is to decide whether the first obstruction theorem should
now be centered on:

1. the broader explicit shadow-floor class, or
2. the narrower forced-kernel class as a technically simpler first theorem.

Then formulate the strongest plausible explicit-family theorem statement.

### Key Parameters

- Tested classes:
  - all rotation classes with exactly 3 binary processors and ternary fill at
    `n=5,6`
- Obstruction scalar:
  shadow indicator of the canonical sweep-shadow cycle.

### Open Questions

- Is the shadow-floor class the right first theorem target, or is the
  forced-kernel class a better starting theorem despite the weaker floor?
- Can the assignment-invariance of the shadow indicator be proved directly?
- Does the same shadow-floor phenomenon continue at `n=7` on explicit sweep
  classes?

## Synthesis after exploration 5

- The obstruction branch now has a broader explicit forbidden-condition
  candidate than the original residual-family floor.
- The next admissible move is to choose which explicit class to theoremize
  first and state that theorem sharply.

## Exploration 6

### Strategy

Test whether the explicit shadow-floor candidate survives the next size `n=7`
on the same 3-binary `{2,3}` sweep-shadow class, and compare it against the
valid same-`n` coarse `FutureFc` layer.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the concern that the explicit shadow-floor class is only a small
`n=5,6` artifact. The same high forbidden-mass regime persists at `n=7`.

### Surviving Structure

- At `n=7`, all tested ternary assignments on the 5 rotation classes with
  exactly 3 binary processors and ternary fill produce assignment-stable shadow
  indicators with forbidden fractions:
  - `(2,2,2,3,3,3,3)`: `0.151896`
  - `(2,2,3,2,3,3,3)`: `0.154982`
  - `(2,2,3,3,2,3,3)`: `0.140873`
  - `(2,2,3,3,3,2,3)`: `0.154982`
  - `(2,3,2,3,2,3,3)`: `0.172619`
- The valid same-`n` coarse-layer reference is still tiny:
  - `CUP-2(n=7)`: `FutureFc = 0.002573`
- So the explicit shadow-floor gap now persists across `n=5,6,7`, with
  assignment-stable values on the tested shadow class.

### Reformulations

- Assignment-stable shadow-floor law:
  on the explicit 3-binary `{2,3}` sweep-shadow class, the shadow indicator’s
  forbidden mass appears to be controlled mainly by the binary-placement class,
  not by the ternary assignments.

LOAD-BEARING ASSESSMENT: high. This is the strongest explicit obstruction-side
result on the redirected branch so far.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `n=7` rotation classes with 3 binary processors and ternary fill:
  5 classes, each tested on all `2^4 = 16` ternary assignments.
- Exact forbidden fractions as listed above.
- Same-`n` valid reference:
  `twolevel_spectrum.py --family cup2 --n 7` gives `FutureFc = 0.002573`.

TOOLS:

- Reused `lb_obstruction/shadow_spectrum.py` for the `n=7` extension.

STRUCTURAL RESULTS:

- The explicit shadow-floor candidate persists at `n=7`.
- The assignment-stability strengthens the case that this is the right first
  explicit-family theorem to target.

REPRESENTATIONS:

- “Assignment-stable shadow-floor class” representation.

### What Would Unblock This

The next useful step is no longer more size-extension by default. It is to
write the strongest explicit-family theorem statement for the shadow-floor
class, now that it survives `n=5,6,7`.

### Key Parameters

- Tested explicit class:
  3 binary processors + ternary fill, canonical sweep-shadow cycle.
- Sizes tested: `n=5,6,7`.

### Open Questions

- Is the floor value determined purely by binary-placement type?
- Can the assignment-stability be proved directly from the shadow construction?
- Is it now better to theoremize the shadow-floor class first rather than the
  forced-kernel residual class?

## Synthesis after exploration 6

- The shadow-floor class has now overtaken the forced-kernel class as the
  strongest explicit obstruction candidate.
- The next admissible move is to state that theorem sharply rather than keep
  extending examples without need.

## Exploration 7

### Strategy

Promote the shadow-floor class from a numerical range statement to a sharp
explicit-family theorem candidate by recording exact class-by-class values and a
uniform tested floor through `n=7`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out describing the shadow-floor class only as “large forbidden mass.”
The phenomenon is now sharp enough to be stated by exact class values.

### Surviving Structure

- For the tested 3-binary `{2,3}` sweep-shadow families at `n=5,6,7`, the
  shadow-indicator forbidden fraction is invariant across all tested ternary
  assignments within a fixed binary-placement class.
- The resulting exact rational values are now tabulated in
  `theorem_candidates.md`.
- Across all tested classes and assignments:
  `forbidden_frac(shadow_indicator) >= 71/504`.
- The valid same-`n` coarse-layer references remain far below:
  - `CUP-2(n=5) = 0.026144`
  - `CUP-2(n=6) = 0.008582`
  - `CUP-2(n=7) = 0.002573`

### Reformulations

- Explicit class-value law:
  the first obstruction theorem candidate can now be stated as a class-by-class
  exact forbidden-mass law on a broad explicit subthreshold family, rather than
  only as a vague floor heuristic.

LOAD-BEARING ASSESSMENT: high. This is the sharpest explicit-family
obstruction statement on the branch so far.

### Concrete Artifacts

DOCS:

- `lb_obstruction/theorem_candidates.md` now includes exact rational values for
  the tested shadow-floor classes and the tested global floor `71/504`.

COMPUTED EXAMPLES:

- Exact values through `n=7` as listed in the theorem-candidate table.

STRUCTURAL RESULTS:

- The shadow-floor class is now an explicit-family theorem candidate rather
  than merely a computational trend.

REPRESENTATIONS:

- “Explicit class-value shadow-floor theorem” representation.

### What Would Unblock This

The next useful step is to decide whether to pursue:

1. a theorem for the explicit class-value law itself,
2. or a weaker but more portable theorem asserting only a positive floor (for
   example `>= 71/504`) on the whole tested shadow class.

### Key Parameters

- Tested sizes: `n=5,6,7`.
- Tested class: 3-binary `{2,3}` sweep-shadow families.

### Open Questions

- Is there a direct proof that the value is assignment-invariant within each
  binary-placement class?
- Is the class-value law or the global floor the better first theorem target?
- Does the same explicit class-value phenomenon continue at `n=8`?

## Synthesis after exploration 7

- The shadow-floor class is now theorem-shaped enough to write down cleanly.
- The next admissible choice is no longer “collect more examples” but
  “theoremize the explicit class-value law or the weaker global floor law.”

## Exploration 8

### Strategy

Package the shadow-floor class into a paper-facing theorem note, and isolate
the first real symbolic proof ingredient: assignment-invariance should come from
coordinatewise relabeling invariance of the forbidden interaction fraction.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the shadow-floor class as purely computational residue.
There is now a real symbolic core to build on.

### Surviving Structure

- Proposition-level symbolic fact:
  coordinatewise relabeling of state labels preserves width-`w` forbidden
  interaction fraction for any scalar on the full configuration space.
- This gives the right mechanism for assignment-invariance inside a fixed
  shadow-placement class: once the explicit sweep/shadow construction is proved
  equivariant under ternary `1 <-> 2` relabelings, the forbidden fraction
  follows automatically.
- The explicit shadow-floor package is now assembled in one place, including:
  - exact class values through `n=7`,
  - the tested floor `71/504`,
  - same-`n` valid coarse-layer comparisons,
  - and the remaining proof obligations.

### Reformulations

- Relabeling-equivariance view:
  the assignment-stability problem is no longer “why do dozens of runs agree?”
  but
  “prove the sweep/shadow construction commutes with coordinatewise ternary
  relabeling.”

LOAD-BEARING ASSESSMENT: high. This is the first real proof ingredient on the
obstruction branch and sharpens the remaining symbolic gap.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/shadow_floor_theorem.md`
  packages the explicit-family theorem candidate and the first symbolic
  invariance lemma.

STRUCTURAL RESULTS:

- The correct symbolic route to assignment-invariance is now explicit:
  relabeling invariance of forbidden fraction plus sweep/shadow equivariance.

REPRESENTATIONS:

- “Relabeling-equivariance shadow-floor theorem” representation.

### What Would Unblock This

The next useful step is now sharply defined:

1. prove that the canonical sweep/shadow construction is equivariant under
   independent ternary `1 <-> 2` relabelings,
2. then choose whether the paper theorem should state the stronger class-value
   law or just the weaker global floor `>= 71/504`.

### Key Parameters

- Tested explicit family:
  3-binary `{2,3}` sweep-shadow class through `n=7`.

### Open Questions

- Can the sweep/shadow equivariance be proved directly from the construction?
- Is the weaker global floor theorem the better first paper result?
- Does the shadow-floor class admit a useful same-`n` comparison against valid
  full-rank suppression, not just coarse `FutureFc`?

## Synthesis after exploration 8

- The obstruction branch now has a paper-facing theorem package with one real
  proof ingredient.
- The next admissible work is no longer more numeric broadening; it is proving
  the explicit sweep/shadow relabeling equivariance.

## Exploration 9

### Strategy

Take the next symbolic step in the shadow-floor package by writing the explicit
equivariance proposition for the canonical sweep cycle and induced shadow cycle
under coordinatewise ternary relabeling.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating assignment-invariance as a black-box computational
phenomenon. The correct proof path is now explicit.

### Surviving Structure

- The symbolic core of the shadow-floor package is now:
  1. coordinatewise relabeling preserves forbidden interaction fraction,
  2. canonical sweep/shadow construction should commute with ternary relabeling,
  3. therefore assignment-invariance follows.
- This reduces the class-value theorem to:
  - one representative computation per binary-placement class,
  - plus the relabeling-equivariance proof.

### Reformulations

- Sweep/shadow equivariance view:
  the right statement is not “all assignments happen to give the same value,”
  but
  “all assignments are coordinatewise relabelings of the same canonical
  sweep/shadow object.”

LOAD-BEARING ASSESSMENT: high. This is the cleanest symbolic route on the
obstruction branch so far.

### Concrete Artifacts

DOCS:

- `lb_obstruction/shadow_floor_theorem.md`
  now contains Proposition 3.1 (sweep/shadow equivariance under ternary
  relabeling) and Corollary 3.2 reducing assignment-invariance to one
  representative per class.

STRUCTURAL RESULTS:

- The assignment-invariance problem is now reduced to a concrete equivariance
  statement.

REPRESENTATIONS:

- “Sweep/shadow equivariance” representation.

### What Would Unblock This

The next useful step is to turn the proof sketch of sweep/shadow equivariance
into a more formal lemma list, with the `construct_sweep_cycle` and
`find_shadow_cycle` procedures unpacked into relabeling-stable primitives.

### Key Parameters

- Explicit class:
  3-binary `{2,3}` sweep-shadow families through `n=7`.

### Open Questions

- Can the `find_shadow_cycle` procedure be rewritten in a way that makes
  relabeling-equivariance completely tautological?
- Is the weaker global floor theorem now sufficiently justified to prioritize
  over the stronger class-value law?

## Synthesis after exploration 9

- The shadow-floor branch now has a concrete symbolic proof route.
- The next admissible work is to refine the equivariance proof into a formal
  lemma chain, not to gather more assignment data.

## Exploration 10

### Strategy

Refine the sweep/shadow equivariance proof sketch into a finite Lean-facing
lemma chain tied to the actual construction primitives
`construct_sweep_cycle`, `check_cycle_consistency`, and `find_shadow_cycle`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out leaving the shadow-floor symbolic step at the level of a global
proof sketch. We now have a decomposition into local transport lemmas that is
appropriate for formalization.

### Surviving Structure

- The symbolic route to assignment-invariance now factors into:
  1. relabeling preserves zero and chosen ternary sweep values,
  2. `construct_sweep_cycle` commutes with relabeling,
  3. `check_cycle_consistency` transports determined entries,
  4. forced privilege and forced successors commute with relabeling,
  5. the deterministic “first escaping forced move” rule in
     `find_shadow_cycle` is preserved,
  6. therefore the shadow path transports.
- This reduces assignment-invariance inside a binary-placement class to one
  representative computation plus an equivariance proof.

### Reformulations

- Construction-primitive equivariance view:
  do not prove assignment-invariance by arguing globally about the shadow set.
  Prove it by transporting the actual algorithms step-by-step.

LOAD-BEARING ASSESSMENT: high. This is the first genuinely Lean-compatible
proof breakdown on the obstruction branch.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/shadow_floor_equivariance_lemmas.md`
  records the full lemma chain and proof skeleton.

STRUCTURAL RESULTS:

- The sweep/shadow equivariance problem is now decomposed into local lemmas on
  deterministic construction primitives.

REPRESENTATIONS:

- “Construction-primitive equivariance” representation.

### What Would Unblock This

The next useful step is to decide whether to:

1. continue refining the paper-side proof of the shadow-floor theorem,
2. or start encoding the construction-primitive equivariance lemmas in a
   Lean-facing form immediately.

### Key Parameters

- No new numerical sweep. This was proof-structure refinement.

### Open Questions

- Which of the primitive transport lemmas is the true difficulty:
  determined-entry transport or shadow-path transport?
- Is it better to prove the weaker global floor theorem first and defer the
  full class-value law?

## Synthesis after exploration 10

- The obstruction branch now has both:
  1. an explicit-family theorem package,
  2. and a Lean-facing proof skeleton for its key symbolic step.
- The next move can now legitimately be proof work rather than exploration if
  we choose.

## Exploration 11

### Strategy

Turn the strongest current obstruction candidate into a paper-facing theorem by
writing the weaker global floor law first, rather than overcommitting to the
full class-value law.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out delaying theorem formulation until every stronger refinement is
symbolic. We now have a sufficiently sharp weaker theorem to write down
cleanly.

### Surviving Structure

- The explicit shadow-floor class now supports a clean theorem statement:
  for the tested 3-binary `{2,3}` sweep-shadow families through `n=7`,
  the shadow-indicator forbidden fraction is always at least `71/504`.
- This theorem still carries a strong same-`n` comparison against the valid
  coarse-layer `FutureFc` regime.
- The stronger exact class-value law is retained as a computational corollary,
  not the primary statement.

### Reformulations

- Weaker global floor law:
  use the explicit-family floor `>= 71/504` as the main obstruction theorem,
  and treat class-by-class exact values as refinement data.

LOAD-BEARING ASSESSMENT: high. This is the cleanest paper-facing theorem on the
obstruction branch so far.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/shadow_floor_global_theorem.md`
  states the weaker global floor theorem, proof skeleton, and status.

STRUCTURAL RESULTS:

- The first paper-facing obstruction theorem is now explicitly written down.

REPRESENTATIONS:

- “Weaker global shadow-floor theorem” representation.

### What Would Unblock This

The next useful step is to refine the symbolic half of the proof:

1. prove the sweep/shadow relabeling equivariance,
2. then reduce the theorem to one representative computation per binary-placement
   class.

### Key Parameters

- Tested explicit family:
  3-binary `{2,3}` sweep-shadow families through `n=7`.

### Open Questions

- Is the weaker global floor theorem now the right main obstruction theorem for
  the branch?
- How much of the representative-class verification can be made Lean-facing
  rather than left as certified computation?

## Synthesis after exploration 11

- The obstruction branch now has a real paper-facing theorem statement.
- The remaining work is clearly split:
  symbolic equivariance on one side,
  representative-class certification on the other.

## Exploration 12

### Strategy

De-risk the symbolic sweep/shadow equivariance route by checking directly that
the actual returned canonical sweep cycles and returned shadow cycles commute
with ternary relabeling on the full tested explicit shadow-floor class.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out a major hidden risk in the proof plan: that the abstract shadow
relation might be equivariant but the concrete algorithm `find_shadow_cycle`
would choose different returned cycles after relabeling.

### Surviving Structure

- For all tested explicit shadow-floor classes through `n=7`, the coordinatewise
  ternary relabeling transports:
  1. the returned canonical sweep cycle,
  2. the returned shadow cycle produced by `find_shadow_cycle`.
- Exhaustive check summary:
  - `n=5`: 2 classes
  - `n=6`: 4 classes
  - `n=7`: 5 classes
  - total assignment comparisons: `109`
  - failures: `0`

### Reformulations

- Algorithmic equivariance view:
  the symbolic route can legitimately reason about the actual construction
  procedures, not merely about a more abstract shadow existence statement.

LOAD-BEARING ASSESSMENT: high. This materially strengthens the credibility of
the current proof plan.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/shadow_equivariance_check.py`
  checks that ternary relabelings transport both the canonical sweep cycle and
  the returned shadow cycle on the tested explicit class.

DOCS:

- `shadow_floor_theorem.md` and `shadow_floor_equivariance_lemmas.md` now cite
  the equivariance audit.

STRUCTURAL RESULTS:

- The concrete `find_shadow_cycle` output behaves equivariantly on the full
  tested class, not just the abstract shadow relation.

REPRESENTATIONS:

- “Algorithmic sweep/shadow equivariance” representation.

### What Would Unblock This

The next useful step is now straightforward proof work:

1. formalize the relabeling transport lemmas for the construction primitives,
2. then cleanly separate the representative-class certification from the
   symbolic equivariance proof in the paper statement.

### Key Parameters

- Tested explicit class:
  3-binary `{2,3}` sweep-shadow families through `n=7`.

### Open Questions

- Can the `find_shadow_cycle` transport be proved directly from its
  “first escaping forced move” rule without further case splitting?
- Is the weaker global floor theorem now strong enough to serve as the main
  obstruction theorem for the branch?

## Synthesis after exploration 12

- The obstruction branch now has a numerically de-risked symbolic route.
- The next move can be genuine proof work on the equivariance lemmas.

## Exploration 13

### Strategy

Examine the current sweep/shadow equivariance route for proof-engineering
hazards and decide whether the symbolic theorem should be proved about the
search routine `find_shadow_cycle` or about the explicit shadow family used in
the paper proof.

### Outcome

SUCCEEDED

### Failure Constraint

A direct symbolic proof about the returned output of `find_shadow_cycle` is
awkward because the routine searches starting configurations in global product
order. Coordinatewise relabelings do not obviously preserve that outer search
order.

### What This Rules Out

It rules out centering the symbolic proof on the algorithmic statement

`map tau (find_shadow_cycle(...)) = find_shadow_cycle(...)`

as the main theorem. That is the wrong proof object.

### Surviving Structure

- The computational audit of algorithmic equivariance remains valuable.
- But the clean symbolic object is the explicit shadow family
  `S_{m,epsilon}` from the paper proof, defined by shifted waterfall formulas.
- On that explicit family, coordinatewise relabeling acts pointwise and the
  proof becomes local and formula-driven rather than search-order-driven.

### Reformulations

- Explicit-shadow symbolic route:
  prove the shadow-floor theorem for the explicit shadow family from the paper,
  and treat `find_shadow_cycle` only as a corroborative checker that rediscovers
  the same object on the tested classes.

LOAD-BEARING ASSESSMENT: very high. This is the right proof-engineering move
for both paper clarity and eventual Lean formalization.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/shadow_floor_symbolic_route.md`
  records the route correction and the revised proof architecture.

STRUCTURAL RESULTS:

- The symbolic theorem should be about the explicit shadow family, not the
  search procedure.
- The algorithmic audit remains useful but is no longer the central proof
  object.

REPRESENTATIONS:

- “Explicit shadow family, search only as audit” representation.

### What Would Unblock This

The next useful step is to restate the shadow-floor theorem package and the
equivariance lemma package in terms of the explicit shadow formulas from the
paper proof, then identify which parts remain computationally certified.

### Key Parameters

- No new numerical sweep. This was proof-route correction.

### Open Questions

- What is the smallest self-contained statement of the explicit shadow family
  needed for the obstruction theorem?
- How much of the current class-value package can be rephrased without
  referencing `find_shadow_cycle` at all?

## Synthesis after exploration 13

- The obstruction branch now has the right symbolic proof object.
- The next move is to rewrite the theorem package around the explicit shadow
  family formulas and separate paper proof from computational audit cleanly.

## Exploration 14

### Strategy

Clarify the exact scope of the current symbolic route by separating the
canonical explicit shadow-family formulas from the broader tested placement
classes, so we know what theorem is genuinely within reach now.

### Outcome

SUCCEEDED

### Failure Constraint

The current explicit shifted-waterfall formulas are proof-ready only for the
canonical binary placement used in the paper proof. The broader tested
3-binary `{2,3}` placement classes do not yet have the same symbolic
normalization.

### What This Rules Out

It rules out silently treating the whole tested explicit-family class as already
covered by the current symbolic formulas. That would overstate the proof
position.

### Surviving Structure

- We now have a clean scope split:
  1. canonical explicit shadow family: proof-ready symbolic object,
  2. broader tested placement classes: computationally certified only.
- The correct next symbolic target is therefore not “prove the whole broad class
  now,” but
  “prove a normalization theorem transporting the canonical shadow family to
  broader placement classes,”
  or else define an explicit arbitrary-placement shadow family.

### Reformulations

- Scope-split shadow theorem:
  separate
  - the canonical proof-ready theorem,
  - from the broader explicit-family computational package.

LOAD-BEARING ASSESSMENT: very high. This keeps the branch mathematically honest
and clarifies the next proof obligation.

### Concrete Artifacts

DOCS:

- `shadow_floor_theorem.md` now contains the canonical explicit shadow formulas
  and an explicit scope note.

STRUCTURAL RESULTS:

- The proof-ready symbolic route currently covers the canonical consecutive
  binary placement.
- The broader placement classes remain a normalization problem, not a proven
  symbolic theorem.

REPRESENTATIONS:

- “Canonical symbolic core + broader computational shell” representation.

### What Would Unblock This

The next useful step is to identify the right normalization statement:

1. cyclic rotation only,
2. binary-placement transport by an explicit permutation,
3. or a new explicit shadow-family formula for arbitrary placement.

### Key Parameters

- No new numerics. This was theorem-scope clarification.

### Open Questions

- What is the correct normalization theorem from the canonical shadow family to
  broader 3-binary placement classes?
- Is the weaker global floor theorem better stated first for the canonical
  class, with the broader class left computational?

## Synthesis after exploration 14

- The branch now knows exactly what part of the shadow-floor theorem is
  symbolic and what part is still computational.
- The next proof move is a normalization theorem, not more equivariance alone.

## Exploration 15

### Strategy

Look for the right normalization invariant for the broader tested shadow-floor
 classes by comparing the explicit class values against the cyclic gap pattern
 between the three binary processors.

### Outcome

SUCCEEDED

### Failure Constraint

The cyclic gap pattern is not yet a complete invariant for the class-value law.
It explains some equalities but not all differences.

### What This Rules Out

It rules out the simplest normalization guess:

- “the shadow-floor value depends only on the normalized gap triple.”

That is too optimistic in the current data.

### Surviving Structure

- The gap triple is still the strongest current clue:
  it organizes the placement classes much better than raw state vectors.
- Through `n=7`, equal normalized gap patterns can force equal values in some
  cases:
  - at `n=7`, the two classes with normalized gap pattern `(1,2,4)` both give
    `703/4536`.
- But the gap pattern does not yet fully determine the value:
  - at `n=6`, the two classes with normalized gap pattern `(1,2,3)` have
    different values `11/72` and `103/648`.

### Reformulations

- Gap-pattern normalization view:
  the missing normalization theorem, if it exists, is likely about the cyclic
  gap geometry of the three binary processors plus one additional datum, not
  about arbitrary placements directly.

LOAD-BEARING ASSESSMENT: medium-high. This is the best current clue for the
normalization problem, but it is not yet a theorem.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Normalized gap triples and values through `n=7`, recorded in the shadow-floor
  theorem note.

STRUCTURAL RESULTS:

- Gap pattern is informative but incomplete.

REPRESENTATIONS:

- “Gap-pattern normalization clue” representation.

### What Would Unblock This

The next useful step is to identify the extra datum beyond the gap triple that
separates the non-equal classes, especially the `n=6` pair with normalized gap
pattern `(1,2,3)`.

### Key Parameters

- Tested sizes: `n=5,6,7`.
- Tested explicit class: 3-binary `{2,3}` sweep-shadow families.

### Open Questions

- What is the smallest extra invariant beyond the gap triple?
- Is it enough to distinguish whether the length-1 binary gap is adjacent to the
  “front” of the sweep construction?

## Synthesis after exploration 15

- The branch now has the first concrete normalization clue, but not the
  normalization theorem itself.
- The next proof work remains focused: identify the extra placement datum beyond
  the gap pattern or stay with the canonical symbolic theorem plus broader
  computational shell.

## Exploration 16

### Strategy

Clarify the normalization problem by checking whether the shadow-floor value
should be invariant under full dihedral symmetry or only under cyclic rotation,
given that the canonical sweep construction fixes a direction.

### Outcome

SUCCEEDED

### Failure Constraint

Reflection is not a symmetry of the canonical sweep construction. It reverses
the mover order, so reflection-related placement classes need not share the
same shadow-floor value.

### What This Rules Out

It rules out phrasing the normalization problem in terms of gap patterns up to
rotation and reflection. That is too coarse for the directed sweep theorem.

### Surviving Structure

- Cyclic rotation remains the correct obvious symmetry.
- Reflection need not preserve the class value, because it changes the sweep
  orientation.
- The `n=6` discrepancy between
  `(2,2,3,2,3,3)` and `(2,2,3,3,2,3)` is therefore no longer paradoxical:
  they are reflection-related but not rotation-related.

### Reformulations

- Directed-sweep normalization view:
  the missing broader theorem should be formulated for directed placement
  classes, not dihedral placement classes.

LOAD-BEARING ASSESSMENT: high. This is a real clarification of the normalization
target and removes a false symmetry from the search space.

### Concrete Artifacts

DOCS:

- `shadow_floor_theorem.md` now states the directed-gap normalization clue
  explicitly.

STRUCTURAL RESULTS:

- The normalization problem is now correctly phrased as a directed one.

REPRESENTATIONS:

- “Directed sweep class” representation.

### What Would Unblock This

The next useful step is to identify the smallest extra directed placement datum
beyond cyclic rotation that controls the shadow-floor value.

### Key Parameters

- Key discrepancy resolved:
  `n=6` reflection-related classes with values `11/72` and `103/648`.

### Open Questions

- What is the smallest directed placement invariant beyond cyclic rotation?
- Is the weaker global floor theorem now already sufficient, making the broader
  normalization problem secondary for the paper?

## Synthesis after exploration 16

- The normalization problem is now cleaner.
- The branch no longer needs to explain false reflection symmetries.
- The next decision is whether to keep chasing broader directed normalization,
  or to stop with the canonical symbolic theorem plus explicit-family
  computational shell.

## Exploration 17

### Strategy

Package the current obstruction branch into a stable paper-facing result note
that cleanly separates the symbolic core from the broader computational shell,
so future work can proceed as proof refinement rather than repeated
re-summarization.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing to hold the branch together only by scattered notes and
log entries. The result package is now explicit enough that future work can be
measured against it.

### Surviving Structure

- The branch now has a single package note containing:
  - the main preliminary theorem statement,
  - the symbolic core,
  - the broader computational shell,
  - and the remaining open layers.
- This package makes explicit that the current best result is:
  - an explicit-family obstruction theorem package,
  - not yet a universal subthreshold theorem.

### Reformulations

- Obstruction result package view:
  future work should now be organized as refinement of this package, not as a
  new search for what the package even is.

LOAD-BEARING ASSESSMENT: high. This is the right stabilization step before more
proof work.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/obstruction_result_package.md`
  packages the current result in paper-facing form.

STRUCTURAL RESULTS:

- The branch now has a stable paper-facing baseline.

REPRESENTATIONS:

- “Stable obstruction package” representation.

### What Would Unblock This

The next useful step is straightforward:

1. refine the symbolic core,
2. or widen the explicit-family shell,
but always relative to the package.

### Key Parameters

- No new computation. This was branch stabilization and packaging.

### Open Questions

- Which open layer should be attacked next:
  canonical symbolic proof completion,
  directed normalization,
  or a first universal obstruction statement?

## Synthesis after exploration 17

- The obstruction branch now has a stable paper-facing baseline.
- Future work can now proceed as targeted proof refinement rather than further
  package discovery.

## Exploration 18

### Strategy

Use the external review feedback to reset the branch priority order and make the
obstruction program explicitly two-track: a shadow-witness track and an
entry-conflict witness track, instead of treating the current shadow package as
the whole lower-bound picture.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out silently allowing the shadow-side package to stand in for the full
lower-bound obstruction. The branch must now carry EC explicitly as a parallel
track.

### Surviving Structure

- The current explicit-family package remains strong, but is now explicitly
  tagged as **shadow-side only**.
- The next universal witness theorem should probably be framed as:
  - a single canonical witness if one emerges,
  - or a disjunctive EC-or-shadow witness theorem.

### Reformulations

- EC/shadow split:
  the right master framing is no longer “find one witness somehow,” but
  “stand up both the EC witness track and the shadow witness track, then ask
  whether they unify.”

LOAD-BEARING ASSESSMENT: very high. This is the key structural correction
needed to keep the branch honest.

### Concrete Artifacts

DOCS:

- `entry_conflict_witness_candidates.md`
  records the missing EC-side witness candidates and theorem shapes.
- `post_feedback_course.md`
  now prioritizes universal witness extraction as a two-track program.
- `obstruction_result_package.md`
  now explicitly states that it is shadow-side only.

STRUCTURAL RESULTS:

- The branch now mirrors the actual lower-bound mechanism split.

REPRESENTATIONS:

- “EC track + shadow track” representation.

### What Would Unblock This

The next useful step is to stand up the first actual EC witness candidate and
test it on explicit EC-killed families.

### Key Parameters

- No new computation. This was a branch-structure correction.

### Open Questions

- Which EC witness candidate is most spectral-friendly:
  overlap indicator, overlap count, confusability-edge count, or something
  derived from them?
- Can the explicit shadow witness be recognized as only one side of a larger
  universal witness program?

## Synthesis after exploration 18

- The obstruction branch is now structurally complete enough to proceed:
  one shadow track, one EC track.
- The next admissible move is to begin the EC witness track, not to keep
  refining shadow alone.

## Exploration 18

### Strategy

Use the two external feedback notes to reset the branch priority order and
explicitly choose between the two serious forward programs:

1. pure spectral transport,
2. universal witness extraction.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out drifting between two incompatible ambitions without choosing a main
line. The branch now has an explicit primary program and a sidecar program.

### Surviving Structure

- The current explicit shadow-floor theorem remains valuable, but only as:
  - model evidence,
  - and a test case for the universal witness program.
- The main line is now:
  **define and universalize a canonical obstruction witness `Phi_S` for
  arbitrary subthreshold systems.**
- The pure spectral transport program remains alive only as a fast feasibility
  test:
  if local updates move too much forbidden mass, we should discover that early
  and stop treating transport as the main route.

### Reformulations

- Main line:
  universal witness extraction.
- Sidecar:
  transport-feasibility test.

LOAD-BEARING ASSESSMENT: very high. This is the first real post-feedback course
decision.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/post_feedback_course.md`
  records the main line, sidecar, immediate tasks, and decision rules.

STRUCTURAL RESULTS:

- The explicit-family obstruction package is now reinterpreted as a model case,
  not as the endpoint.

REPRESENTATIONS:

- “Universal witness main line + transport sidecar” representation.

### What Would Unblock This

The next useful step is to start Step 1 of the new main line:

> propose a canonical candidate `Phi_S` for arbitrary subthreshold systems.

### Key Parameters

- No new numerical sweep. This was a course reset driven by review feedback.

### Open Questions

- What is the best candidate for `Phi_S`?
- Can the current shadow indicators be recognized as a special case of `Phi_S`?
- Does the transport sidecar die quickly, or does it show enough bite to keep?

## Synthesis after exploration 18

- The branch now has a real critical path again.
- The next admissible work is to define or test a canonical obstruction witness
  for arbitrary subthreshold systems.

## Exploration 19

### Strategy

Stand up the first explicit EC witness candidate and test whether it registers
in the same width-`n-2` forbidden-mass observable used on the shadow side.

### Outcome

SUCCEEDED

### Failure Constraint

The naive EC overlap witness is too local. When extended to the full
configuration space as a sum of processorwise overlap indicators, it is a
width-3 local scalar and therefore has zero width-`n-2` forbidden interaction
fraction.

### What This Rules Out

It rules out the simplest unification dream:

- “use the same forbidden-mass observable on a naive local EC witness and on
  the shadow witness.”

That is too naive.

### Surviving Structure

- On canonical BAF-style EC examples:
  - `ms = (2,2,2,3,3)`
  - `ms = (2,2,2,3,3,3)`
  the natural full-space EC scalar

  `total_overlap(c) = Σ_i 1[(c_{i-1}, c_i, c_{i+1}) in O_i]`

  has width-`n-2` forbidden fraction exactly `0`.
- This is not an accident but a structural fact:
  the scalar is a sum of width-3 local indicators.
- So the EC branch still needs a witness, but it likely needs either:
  - a nonlocal EC-derived witness,
  - or a different observable (zero-error / confusability style) than the
    shadow-side forbidden-mass quantity.

### Reformulations

- Split-observable witness view:
  the universal lower-bound program should now be treated as:
  - shadow witness measured by forbidden mass,
  - EC witness measured by a different complexity quantity unless a more
    nonlocal EC witness is found.

LOAD-BEARING ASSESSMENT: very high. This is the first concrete structural split
between the EC and shadow tracks.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_overlap_spectrum.py`
  probes the forbidden fraction of local EC overlap scalars on explicit EC
  examples.

COMPUTED EXAMPLES:

- `ms = (2,2,2,3,3)`:
  overlap processors `{1,2}`; `total_overlap` forbidden fraction `0.000000`.
- `ms = (2,2,2,3,3,3)`:
  overlap processors `{1,2,3}`; `total_overlap` forbidden fraction `0.000000`.

STRUCTURAL RESULTS:

- Naive EC overlap indicators are invisible to the current forbidden-mass
  observable.

REPRESENTATIONS:

- “EC track needs its own observable” representation.

### What Would Unblock This

The next useful step on the EC track is to decide between:

1. a nonlocal EC-derived witness,
2. or a zero-error/confusability quantity as the primary EC obstruction
   observable.

### Key Parameters

- Explicit EC examples:
  canonical BAF-style cycles on
  `(2,2,2,3,3)` and `(2,2,2,3,3,3)`.

### Open Questions

- What is the right nonlocal EC witness, if one exists?
- Is the confusability-edge count `E_conf` the right EC-side quantity?
- Can the final lower-bound theorem reasonably be disjunctive in both witness
  type and observable?

## Synthesis after exploration 19

- The branch now knows that EC and shadow are not just two obstruction types;
  they may require two different observables.
- The next admissible EC work is to test a zero-error/confusability quantity,
  not to keep forcing local overlap counts into the forbidden-mass framework.

## Exploration 57

### Strategy

Test whether the weak EC bridge theorem can now be reduced to the coarse
support geometry coming from the broader BAF support theorem.

Concretely:

1. group the simple two-turnaround BAF words by normalized turnaround-gap
   class,
2. check whether `ForbidFrac_{n-2}(chi_conf)` is already determined by that
   coarse geometry,
3. compare with the full valid-fiber minima on small `n`.

### Outcome

SUCCEEDED

### Failure Constraint

The coarse support geometry is too coarse.

Even inside the simple two-turnaround BAF family, the same normalized
turnaround-gap class can produce multiple distinct forbidden fractions for
`chi_conf`.

So the EC bridge theorem cannot be proved from the statement

> “`ConfState` is two long arcs of the good cycle with four exceptional states
> removed”

alone.

### What This Rules Out

It rules out the first naive version of Route A in `ec_bridge_theorem_route.md`:

- “prove a lower bound from support geometry alone.”

That is not enough data.

### Surviving Structure

- The broader BAF support theorem remains load-bearing.
- The missing datum is now much sharper:
  **turnaround placement geometry** relative to the anchored binary block and
  the induced good-cycle embedding.
- The weak EC bridge theorem should now be phrased as a
  **support-plus-placement** theorem, not a pure support theorem.

### Reformulations

- “support-plus-placement EC bridge law” representation.
- “turnaround-placement reduction” representation.

LOAD-BEARING ASSESSMENT: very high. This removes a false simplification and
sharpens the next proof target materially.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_bridge_geometry_probe.py`
  groups simple/two-turnaround BAF words by normalized turnaround-gap class and
  records the resulting forbidden-fraction variation.

UPDATED NOTES:

- `info_theory/lb_obstruction/ec_bridge_theorem_route.md`
- `info_theory/lb_obstruction/ec_obstruction_theorem.md`
- `info_theory/lb_obstruction/obstruction_result_package.md`

COMPUTED EXAMPLES:

- Full valid-fiber minima:
  - `n=5`, gap `(5,5)` gives distinct minima
    `0.115740740741`, `0.166666666667`
  - `n=6`, gap `(6,6)` gives distinct minima
    `0.129629629630`, `0.131944444444`, `0.148148148148`,
    `0.175925925926`
  - `n=7`, gap `(7,7)` gives distinct minima
    `0.129012345679`, `0.129629629630`, `0.137037037037`,
    `0.153086419753`
- Simple two-turnaround BAF realization:
  - `n=8`, gap `(8,8)` gives distinct minima
    `0.114197530864`, `0.118141289438`, `0.125857338820`,
    `0.126886145405`, `0.135802469136`
  - `n=9`, gap `(9,9)` gives distinct minima
    `0.101900842642`, `0.116696061141`, `0.118312757202`,
    `0.119145600627`, `0.122476974329`

STRUCTURAL RESULT:

- Same support cardinality and same normalized turnaround-gap class do not
  determine `ForbidFrac_{n-2}(chi_conf)`.

### What Would Unblock This

The next useful EC-side reduction is:

1. identify the smallest turnaround-placement invariant beyond the coarse gap
   class,
2. show that the weak EC bridge theorem depends only on that invariant,
3. reduce the bridge theorem to a finite placement-class analysis.

### Key Parameters

- Family:
  simple two-turnaround BAF words with consecutive binary triple `{0,1,2}`.
- Observable:
  `ForbidFrac_{n-2}(chi_conf)`.
- Coarse geometry:
  two equal arcs with four exceptional states removed.

### Open Questions

- What is the minimal turnaround-placement invariant controlling the EC bridge
  value?
- Does the full valid-fiber minimum occur on the simple realization?
- Is there a clean reduction from arbitrary BAF words to a finite list of
  anchored turnaround placements?

## Synthesis after exploration 57

- The broader BAF support theorem was a necessary step, but not the final
  bridge explanation.
- The EC bridge theorem is now clearly a support-plus-placement theorem.
- The next admissible proof work is to identify the right placement invariant,
  not to keep treating all two-turnaround words as one geometry class.

## Exploration 58

### Strategy

Try to identify the smallest turnaround-placement invariant that survives after
the route correction in Exploration 57.

Concretely:

1. inspect the simple two-turnaround BAF words through `n=9`,
2. record `ForbidFrac_{n-2}(chi_conf)` by turnaround position,
3. test whether those values collapse under a smaller anchored placement datum.

### Outcome

SUCCEEDED

### Failure Constraint

The bridge value is not controlled by the coarse gap class, but it does not
seem to require the full mover word either.

### Surviving Structure

There is now a strong placement-invariant candidate:

- on the simple two-turnaround BAF family through `n=9`,
- and on the full valid-fiber minima through `n=7`,

the value of `ForbidFrac_{n-2}(chi_conf)` appears to be constant once one fixes
the cyclic distance from the turnaround vertex to the middle binary processor
`1`.

So the smallest currently plausible EC bridge datum is:

> turnaround-distance-to-`1`.

### Reformulations

- “distance-to-middle-binary EC bridge law” representation.
- “anchored turnaround class” representation.

LOAD-BEARING ASSESSMENT: very high. This is the first nontrivial placement
invariant that survives the geometry correction.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_bridge_geometry_probe.py`
  now reports the turnaround vertex and its cyclic distance to processor `1`.

COMPUTED EXAMPLES:

Simple two-turnaround BAF family:

- `n=5`:
  - distance `0`: `0.166666666667`
  - distance `1`: `0.166666666667`
  - distance `2`: `0.115740740741`
- `n=6`:
  - distance `0`: `0.148148148148`
  - distance `1`: `0.175925925926`
  - distance `2`: `0.131944444444`
  - distance `3`: `0.129629629630`
- `n=7`:
  - distance `0`: `0.129629629630`
  - distance `1`: `0.153086419753`
  - distance `2`: `0.137037037037`
  - distance `3`: `0.129012345679`
- `n=8`:
  - distance `0`: `0.114197530864`
  - distance `1`: `0.135802469136`
  - distance `2`: `0.125857338820`
  - distance `3`: `0.126886145405`
  - distance `4`: `0.118141289438`
- `n=9`:
  - distance `0`: `0.101900842642`
  - distance `1`: `0.122476974329`
  - distance `2`: `0.118312757202`
  - distance `3`: `0.119145600627`
  - distance `4`: `0.116696061141`

Full valid-fiber minima:

- `n=5,6,7` obey the same collapse by distance-to-`1`.

STRUCTURAL RESULT:

- The full mover word is no longer the leading candidate for the missing EC
  bridge datum.
- The anchored distance from the turnaround vertex to processor `1` is now the
  best current placement invariant.

### What Would Unblock This

The next useful step is to explain symbolically why processor `1` is the
correct anchor:

1. derive the reflection / relabeling symmetries fixing the consecutive binary
   triple `{0,1,2}`,
2. show that these symmetries force equality within a fixed
   distance-to-`1` class,
3. reduce the weak EC bridge theorem to one representative per distance class.

### Key Parameters

- Anchored binary block: `{0,1,2}`.
- Candidate invariant:
  `d = dist_{C_n}(turnaround_vertex, 1)`.

### Open Questions

- Can the distance-to-`1` invariant be proved symbolically?
- Does the weak EC bridge minimum always occur at maximal distance from `1`?
- Does the full valid-fiber minimum always coincide with the simple
  realization?

## Synthesis after exploration 58

- The EC bridge theorem is now reduced from “some word-level placement datum”
  to a concrete candidate invariant.
- The next proof work should explain why distance-to-`1` is the right anchored
  class, then use that reduction in the weak bridge theorem.

## Exploration 59

### Strategy

Promote the distance-to-`1` pattern into a real symmetry reduction.

Concretely:

1. identify the ring reflection fixing the middle binary processor `1`,
2. show it preserves the anchored consecutive-binary family,
3. use it to reduce the simple two-turnaround BAF family to one representative
   per distance-to-`1` class.

### Outcome

SUCCEEDED

### Surviving Structure

The first genuine EC bridge reduction is now in place.

Let

`rho(i) = 2 - i (mod n)`.

Then:

- `rho` preserves the anchored binary block `{0,1,2}`,
- the induced coordinate permutation preserves `ForbidFrac_{n-2}`,
- and on the simple two-turnaround BAF family it sends the turnaround vertex
  `v` to `rho(v) = 2-v`.

Since the distance classes from processor `1` are exactly the reflection orbits,
this gives a full reduction to one representative per distance-to-`1` class.

### Reformulations

- “reflection reduction about the middle binary” representation.
- “one representative per distance class” representation.

LOAD-BEARING ASSESSMENT: very high. This is the first actual symmetry theorem
supporting the EC bridge route.

### Concrete Artifacts

NOTES:

- `info_theory/lb_obstruction/ec_distance_class_reduction.md`
  packages the reduction.

TOOLS:

- `info_theory/lb_obstruction/ec_turnaround_reflection_probe.py`
  audits reflection pairing.

AUDIT RESULTS:

- simple family:
  - `n=5`: 5 words, 0 failures
  - `n=6`: 6 words, 0 failures
  - `n=7`: 7 words, 0 failures
  - `n=8`: 8 words, 0 failures
  - `n=9`: 9 words, 0 failures
- full valid-fiber minima:
  - `n=5`: 5 words, 0 failures
  - `n=6`: 6 words, 0 failures
  - `n=7`: 7 words, 0 failures

STRUCTURAL RESULT:

- The distance-to-`1` classes are not just an empirical grouping; they are the
  reflection orbits of the anchored family.

### What Would Unblock This

The next useful step is to exploit the reduction rather than just record it:

1. choose one canonical representative for each distance class,
2. study how the forbidden fraction varies across those representatives,
3. prove a uniform lower bound over the distance classes.

### Key Parameters

- Reflection:
  `rho(i) = 2 - i (mod n)`.
- Anchor:
  middle binary processor `1`.
- Reduced classes:
  cyclic distance classes from `1`.

### Open Questions

- Can the canonical representative in each distance class be written in a clean
  closed form?
- Does the weak EC bridge minimum occur at maximal distance from `1` for all
  `n`?
- Can the reduced class analysis be done symbolically rather than by direct
  ANOVA computation?

## Synthesis after exploration 59

- The EC bridge route now has a real symmetry reduction.
- The next proof target is no longer “why do equal values appear in pairs?”
- It is “how do the distance-class representatives control the lower bound?”.

## Exploration 60

### Strategy

Check whether the new distance-class reduction is only a statement about the
simple model family, or whether it already captures the tested full valid-fiber
minima.

### Outcome

SUCCEEDED

### Surviving Structure

On the solved small range `n=5,6,7`, the full valid-fiber minimum in each
distance-to-`1` class already agrees exactly with the value of the simple
distance-class representative.

So the EC bridge reduction is stronger than expected:

- it is not just a simple-family symmetry,
- it already captures the tested class minima.

### Reformulations

- “simple representatives realize full small-fiber minima” representation.

LOAD-BEARING ASSESSMENT: very high. This is the first real reduction from the
full tested EC bridge class to a much smaller representative family.

### Concrete Artifacts

TOOL UPDATE:

- `info_theory/lb_obstruction/ec_turnaround_reflection_probe.py`
  now also compares simple and full class minima.

COMPUTED RESULTS:

- `n=5`: 3 distance classes, 0 simple-vs-full failures
- `n=6`: 4 distance classes, 0 simple-vs-full failures
- `n=7`: 4 distance classes, 0 simple-vs-full failures

UPDATED NOTE:

- `info_theory/lb_obstruction/ec_distance_class_reduction.md`

### What Would Unblock This

The next useful step is to stop asking about the whole tested family and start
asking about the class representatives directly:

1. choose canonical representatives `W_d`,
2. study the forbidden fraction as a function of `d`,
3. prove a uniform lower bound over `d`.

### Key Parameters

- Solved comparison range: `n=5,6,7`.
- Reduced parameter: `d = dist_{C_n}(turnaround_vertex, 1)`.

### Open Questions

- Does the simple representative realize the class minimum for all `n`?
- Can `ForbidFrac_{n-2}(chi_conf(W_d))` be described explicitly in terms of
  `n` and `d`?

## Synthesis after exploration 60

- The EC bridge branch now has a concrete finite-dimensional reduction.
- The next theorem work should be carried out on the canonical representatives
  `W_d`, not on arbitrary words or arbitrary valid fibers.

## Exploration 61

### Strategy

Make the distance-class reduction fully explicit by writing down one canonical
representative word for each class.

### Outcome

SUCCEEDED

### Surviving Structure

The EC bridge problem is now explicitly parameterized by:

- ring size `n`,
- distance class `d`.

For `d in {0,...,floor(n/2)}`, choose turnaround vertex

`v_d = 1 + d`,

and define

`W_v = [0,1,...,v, v-1,...,0, n-1,...,v, v+1,...,n-1]`,

then set

`W_d = W_{1+d}`.

By the reflection reduction, every simple two-turnaround BAF word is
reflection-equivalent to exactly one `W_d`.

### Reformulations

- “EC bridge as a function of `(n,d)`” representation.
- “canonical representative family `W_d`” representation.

LOAD-BEARING ASSESSMENT: high. This turns the EC bridge target into a concrete
finite family rather than an abstract quotient.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_distance_class_values.py`
  tabulates `ForbidFrac_{n-2}(chi_conf(W_d))`.

UPDATED NOTE:

- `info_theory/lb_obstruction/ec_distance_class_reduction.md`

REPRESENTATIVE VALUES THROUGH `n=9`:

- `n=8`:
  - `d=0`: `0.114197530864`
  - `d=1`: `0.135802469136`
  - `d=2`: `0.125857338820`
  - `d=3`: `0.126886145405`
  - `d=4`: `0.118141289438`
- `n=9`:
  - `d=0`: `0.101900842642`
  - `d=1`: `0.122476974329`
  - `d=2`: `0.118312757202`
  - `d=3`: `0.119145600627`
  - `d=4`: `0.116696061141`

### What Would Unblock This

The next useful step is to study these representative values as a function of
`d`:

1. search for a symbolic formula or monotonicity pattern in `d`,
2. or at least prove a uniform positive lower bound over the finite set
   `d = 0,...,floor(n/2)`.

### Key Parameters

- Canonical representatives:
  `W_d`.
- Reduced EC bridge values:
  `ForbidFrac_{n-2}(chi_conf(W_d))`.

### Open Questions

- Is there a closed-form expression for `ForbidFrac_{n-2}(chi_conf(W_d))`?
- What is the minimizing distance class as a function of `n`?

## Synthesis after exploration 61

- The EC bridge theorem is now reduced to an explicit representative family.
- The next theorem work is to control the value table in `d`, not to perform
  more family normalization.

## Exploration 62

### Strategy

Look for a coefficient-level proof route on the representative family `W_d`,
rather than trying to control the entire forbidden spectrum at once.

Concretely:

1. inspect the top forbidden masks on the representatives,
2. guess a tiny anchored mask family depending on `d`,
3. test whether one of those masks already has positive forbidden energy for
   every tested `W_d`.

### Outcome

SUCCEEDED

### Surviving Structure

The EC bridge route now has a first real coefficient-level theorem candidate.

On the tested representative range `n=5..9`, the following anchored mask family
always supplies a positive forbidden coefficient:

- `d=0`: complement `{1}`
- `d>0` even: complement `{1,d+1}`
- `d` odd: complement `{0,d+1}` or `{2,d+1}`

So one does not need to prove positivity of the whole forbidden spectrum
directly. It may be enough to prove that one tiny anchored forbidden mask
survives.

### Reformulations

- “single forbidden coefficient route” representation.
- “anchored mask family route” representation.

LOAD-BEARING ASSESSMENT: very high. This is the first EC bridge route that
looks genuinely theorem-shaped and Lean-compatible.

### Concrete Artifacts

NEW NOTE:

- `info_theory/lb_obstruction/ec_mask_family_route.md`

NEW TOOL:

- `info_theory/lb_obstruction/ec_mask_family_probe.py`

COMPUTED RESULTS THROUGH `n=9`:

- `n=8`
  - `d=0`: `{1}` energy `8.2558553e-05`
  - `d=1`: `{0,2}` energy `1.52415790e-04`
  - `d=2`: `{1,3}` energy `5.5039035e-05`
  - `d=3`: `{0,4}` and `{2,4}` energy `6.7740351e-05`
  - `d=4`: `{1,5}` energy `4.2337720e-05`
- `n=9`
  - `d=0`: `{1}` energy `2.0933650e-05`
  - `d=1`: `{0,2}` energy `3.5751852e-05`
  - `d=2`: `{1,3}` energy `1.2701316e-05`
  - `d=3`: `{0,4}` and `{2,4}` energy `1.5053411e-05`
  - `d=4`: `{1,5}` energy `8.4675440e-06`

STRUCTURAL RESULT:

- The weak EC bridge positivity may be provable by one forbidden coefficient per
  distance class, not by a full-spectrum argument.

### What Would Unblock This

The next useful theorem work is:

1. define the candidate mask family symbolically,
2. compute or characterize the corresponding ANOVA coefficient on `W_d`,
3. prove it is nonzero for each `d`.

### Key Parameters

- Representative family: `W_d`.
- Candidate anchored complements:
  `{1}`, `{1,d+1}`, `{0,d+1}`, `{2,d+1}` according to the parity rule above.

### Open Questions

- Why does the parity split in the mask family match the distance class?
- Can the chosen coefficient be written in closed form?

## Synthesis after exploration 62

- The EC bridge problem is now reduced twice:
  first to representatives `W_d`, then to one tiny forbidden mask per class.
- The next theorem attempt should target nonvanishing of those mask
  coefficients.

## Exploration 63

### Strategy

Check whether the old finite-range EC bridge constant is likely to survive
beyond the tested range, using the new representative family `W_d`.

### Outcome

SUCCEEDED

### Failure Constraint

The old constant

`37/324`

is not the right asymptotic EC bridge target.

On the representative family at `n=10`, the minimum class value is already

`0.091306584362`,

which lies below `37/324 ≈ 0.114198`.

### What This Rules Out

It rules out treating the old finite-range theorem candidate as the main
symbolic target for the EC branch.

### Surviving Structure

The EC side still has a strong theorem path, but its honest target is now:

- positivity of `ForbidFrac_{n-2}(chi_conf(W_d))`,
  or
- an explicit `n`-dependent lower bound,

not a universal constant in `n`.

### Reformulations

- “nonvanishing EC bridge theorem” representation.
- “`n`-dependent EC floor” representation.

LOAD-BEARING ASSESSMENT: very high. This prevents the branch from optimizing for
the wrong theorem.

### Concrete Artifacts

DATA:

- `n=10` representative values:
  - `d=0`: `0.091306584362`
  - `d=1`: `0.110368084134`
  - `d=2`: `0.110039437586`
  - `d=3`: `0.111825560128`
  - `d=4`: `0.108439071788`
  - `d=5`: `0.112354252401`

UPDATED NOTES:

- `info_theory/lb_obstruction/ec_bridge_theorem_route.md`
- `info_theory/lb_obstruction/ec_obstruction_theorem.md`
- `info_theory/lb_obstruction/obstruction_result_package.md`

### What Would Unblock This

The next useful step is not to chase a universal constant, but to prove one of:

1. nonvanishing of the candidate forbidden-mask coefficient on every `W_d`,
2. or an explicit lower bound on that coefficient as a function of `n` and `d`.

### Key Parameters

- Representative family: `W_d`.
- First out-of-range check: `n=10`.

### Open Questions

- Does the minimum always occur at `d=0` for large `n`?
- Is there a simple closed form for the `d=0` bridge value?

## Synthesis after exploration 63

- The EC branch now has the right asymptotic target.
- The next theorem work should be about nonvanishing or `n`-dependent bounds,
  not about preserving the old finite-range constant.

## Exploration 64

### Strategy

Sharpen the candidate-mask route to an explicit coefficient-nonvanishing route.

Concretely:

1. choose one explicit mean-zero product basis vector on the candidate support,
2. test its inner product with `chi_conf(W_d)`,
3. see whether that single coefficient is already nonzero across the
   representative range.

### Outcome

SUCCEEDED

### Surviving Structure

The strongest current EC theorem route is now:

> prove `<chi_conf(W_d), Psi_d> != 0`,

where

`Psi_d(x) = Π_{i in S_d} (1[x_i=0] - 1/m_i)`.

This is stronger than the old mask-energy statement, because nonvanishing of
this one explicit basis coefficient already implies positive forbidden energy on
the candidate support `S_d`.

### Reformulations

- “single basis-coefficient route” representation.
- “explicit product witness” representation.

LOAD-BEARING ASSESSMENT: extremely high. This is the most theorem-shaped and
Lean-compatible EC bridge target found so far.

### Concrete Artifacts

NEW NOTE:

- `info_theory/lb_obstruction/ec_basis_coefficient_route.md`

NEW TOOL:

- `info_theory/lb_obstruction/ec_basis_inner_probe.py`

TESTED NONVANISHING THROUGH `n=11`:

- `n=10`
  - `d=0`: ` 1.1107117775590859e-06`
  - `d=1`: ` 5.592760479944573e-06`
  - `d=2`: `-3.371336924826402e-06`
  - `d=3`: ` 4.233771952107575e-06`
  - `d=4`: `-2.1952891603520756e-06`
  - `d=5`: ` 3.763352846317844e-06`
- `n=11`
  - `d=0`: ` 2.482767502779134e-07`
  - `d=1`: ` 1.2370280189285505e-06`
  - `d=2`: `-7.40474518372724e-07`
  - `d=3`: ` 9.234152817353968e-07`
  - `d=4`: `-4.529961759456663e-07`
  - `d=5`: ` 7.666089131388202e-07`

SIGN PATTERN THROUGH THE TESTED RANGE:

- `d=0`: positive
- `d>0` odd: positive
- `d>0` even: negative

STRUCTURAL RESULT:

- The EC bridge route no longer needs the full forbidden spectrum.
- A single explicit coefficient already survives on every tested distance
  class.

### What Would Unblock This

The next useful theorem work is:

1. express `E_{C_d}(chi_conf(W_d))` on the kept coordinates as the weighted
   union of two monotone chains,
2. pair that projection formula with `Psi_d`,
3. compute the resulting alternating sum and show it is nonzero.

### Key Parameters

- Representative family: `W_d`
- Candidate support: `S_d`
- Product basis vector: `Psi_d`

### Open Questions

- Can the sign pattern be proved directly from the chain geometry?
- Is there a closed form for `<chi_conf(W_d), Psi_d>`?

## Synthesis after exploration 64

- The EC bridge target is now fully explicit.
- The next theorem attempt should be a direct computation of one basis
  coefficient from the projection-chain description.

## Exploration 65

### Strategy

Turn the explicit basis-coefficient route into an exact representative theorem.

Concretely:

1. write the projection-chain decomposition for the representative family
   `W_d`,
2. compute `<chi_conf(W_d), Psi_d>` exactly by geometric summation,
3. prove its sign and therefore nonvanishing.

### Outcome

SUCCEEDED

### Surviving Structure

The EC side now has a genuine exact representative theorem.

The new theorem package

- `info_theory/lb_obstruction/ec_basis_coefficient_theorem.md`

gives a closed-form formula for the coefficient

`I_{n,d} = <chi_conf(W_d), Psi_d>`

and proves:

- `I_{n,0} > 0`,
- `I_{n,d} > 0` for odd `d`,
- `I_{n,d} < 0` for even `d >= 2`.

Hence `I_{n,d} != 0` for every representative `W_d`, and the candidate
forbidden support already carries positive forbidden energy.

### Reformulations

- “exact coefficient theorem on representatives” representation.
- “sign theorem for `I_{n,d}`” representation.

LOAD-BEARING ASSESSMENT: extremely high. This is the first real exact theorem
on the EC bridge side beyond the canonical support law.

### Concrete Artifacts

NEW THEOREM NOTE:

- `info_theory/lb_obstruction/ec_basis_coefficient_theorem.md`

NEW AUDIT TOOL:

- `info_theory/lb_obstruction/ec_basis_formula_probe.py`

VERIFICATION:

- `ec_basis_formula_probe.py --n-from 5 --n-to 11`
  reports `0` failures at every tested `n`.

EXACT FORMULAS:

With `r = -1/2`:

- `d=0`:
  `I_{n,0} = A_{n,0} * (1-r^{n-2}) / (1-r)`
- `d=1`:
  `I_{n,1} = A_{n,1} * (2-r-r^{n-3}) / (1-r)`
- odd `d >= 3`:
  `I_{n,d} = A_n * (2-r^{d-2}-r^{n-d-2}) / (1-r)`
- even `d >= 2`:
  `I_{n,d} = -A_n * (1+r^{d-2}+r^{n-d-2}) / (1-r)`

where the positive prefactors `A_{n,0}, A_{n,1}, A_n` are defined in the note.

### What This Rules Out

It rules out the need to treat EC bridge positivity as merely a computational
theorem candidate on the representative family.

### What Would Unblock This

The next useful step is to connect the representative theorem back to the full
tested BAF class:

1. push the simple-vs-full reduction farther than `n=7`,
2. or prove the full class minima are realized by the representatives,
3. then restate the EC bridge theorem on the broader tested class.

### Key Parameters

- Representative family: `W_d`
- Product basis vector: `Psi_d`
- Exact coefficient: `I_{n,d}`

### Open Questions

- Can the representative theorem be lifted from `W_d` to the broader tested BAF
  family?
- Can one extract an explicit `n`-dependent lower bound from the exact formula?

## Synthesis after exploration 65

- The EC branch now has an exact theorem on the reduced representative family.
- The next bridge question is no longer “can we prove nonvanishing on `W_d`?”
- It is “how far can we lift this theorem from the representatives back to the
  broader BAF family?”.

## Exploration 66

### Strategy

Test the most optimistic lift of the new representative theorem:

> does the same explicit coefficient survive uniformly on the full tested BAF
> fibers?

### Outcome

PARTIAL

### Failure Constraint

The exact representative theorem does **not** lift coefficientwise verbatim.

On the small full-fiber checks:

- in some distance classes the same basis coefficient changes sign across valid
  goods,
- and at `n=6`, distance class `d=2`, no simple local product basis choice on
  the same support survives across all valid goods.

So the next lift theorem cannot be:

> “the same explicit coefficient is nonzero on every valid good cycle.”

That is false in the current simple basis family.

### Surviving Structure

- The representative theorem remains real and load-bearing.
- The distance-class reduction remains real and load-bearing.
- The likely next lift target is now:
  - support-level positive energy on the same support,
    or
  - a more flexible basis family depending on the good cycle.

### Reformulations

- “representative theorem but not rigid lift” representation.
- “support-level lift target” representation.

LOAD-BEARING ASSESSMENT: very high. This prevents us from overclaiming the
representative theorem and identifies the actual next bridge problem.

### Concrete Artifacts

FULL SMALL-FIBER CHECKS:

- `n=5`
  - `d=1`: coefficient values `{-1/108, +1/108}`
  - `d=2`: coefficient values `{-1/216, -1/864}`
- `n=6`
  - `d=1`: coefficient values `{-7/2916, +7/2916}`
  - `d=2`: candidate coefficient can be `0`
  - no simple local product basis choice on the same support survives across
    all valid goods in this class
- `n=7`
  - `d=1`: coefficient values `{-13/26244, +13/26244}`
  - `d=2`: multiple negative values
  - `d=3`: multiple positive values

UPDATED NOTES:

- `info_theory/lb_obstruction/ec_bridge_theorem_route.md`
- `info_theory/lb_obstruction/ec_obstruction_theorem.md`
- `info_theory/lb_obstruction/obstruction_result_package.md`

### What Would Unblock This

The next useful EC-side theorem attempt is one of:

1. prove positive energy on the same support `S_d` across the broader tested
   BAF class,
2. identify a slightly richer basis family that stays nonzero across the full
   class,
3. or prove that the class minimum is still realized by the representative
   theorem even when the coefficient itself is not rigid.

### Key Parameters

- Exact theorem object: `<chi_conf(W_d), Psi_d>`
- Failed rigid lift target:
  “same coefficient across full class”

### Open Questions

- Is the support-level energy on `S_d` the right robust lift target?
- Can the representative theorem still control the full-class minimum without
  coefficient rigidity?

## Synthesis after exploration 66

- The EC branch now has both:
  - a real exact theorem on the representatives,
  - and a sharp obstruction to the naive full-class lift.
- The next bridge work should be support-level.

## Exploration 67

### Strategy

Test the first support-level bridge replacement after the failure of the rigid
coefficient lift.

Concretely:

1. keep the same small-size support search space (complements of size `1` or
   `2`),
2. work inside the first genuinely problematic class for the coefficient lift,
3. ask whether some tiny forbidden support still has positive energy across the
   whole class.

### Outcome

SUCCEEDED

### Surviving Structure

The first concrete support-level lift clue is positive.

In the problematic class:

- `n=6`
- distance class `d=2`

the representative coefficient theorem does not lift rigidly, but there are
many tiny forbidden supports whose support-energy is positive and in fact
constant across all `16` valid goods in the class.

Examples:

- complement `{1}`:
  `0.000514403292`
- complement `{3}`:
  `0.000342935528`
- complement `{5}`:
  `0.000342935528`
- complement `{3,5}`:
  `0.000685871056`

So the right full-class bridge target is no longer hypothetical:
support-level rigidity is already visible in the first bad coefficient class.

### Reformulations

- “support-level lift after coefficient failure” representation.
- “tiny robust forbidden support” representation.

LOAD-BEARING ASSESSMENT: very high. This is the first direct evidence that the
EC bridge theorem may still lift on the right object even after the coefficient
route fails to lift rigidly.

### Concrete Artifacts

NEW TOOL:

- `info_theory/lb_obstruction/ec_support_lift_probe.py`

NEW NOTE:

- `info_theory/lb_obstruction/ec_support_lift_route.md`

COMPUTED EXAMPLE:

- `ec_support_lift_probe.py --n 6 --d 2 --max-comp-size 2`
  returns `13` tiny forbidden supports with positive energy across the whole
  class.

### What Would Unblock This

The next useful support-level work is:

1. scan the remaining small classes,
2. identify a class-stable support family,
3. and then try to prove a broader support-level EC bridge theorem.

### Key Parameters

- First bad coefficient class: `n=6, d=2`.
- Search space:
  complements of size at most `2`.

### Open Questions

- Is there one simple support family that works across all distance classes?
- Does support-level rigidity persist through the larger tested range?

## Synthesis after exploration 67

- The representative theorem still looks like the right structural core.
- The first lift beyond it now points to support-level rigidity, not
  coefficient rigidity.

## Exploration 68

### Strategy

Turn the support-level lift clue into the first actual full-class theorem on
the solved small range.

Concretely:

1. identify the class-stable tiny support in each solved distance class,
2. record the exact energy values,
3. package the result as a tested full-class support theorem through `n=7`.

### Outcome

SUCCEEDED

### Surviving Structure

The EC branch now has its first full-class lift theorem on the solved small
range.

New theorem note:

- `info_theory/lb_obstruction/ec_smallrange_support_lift_theorem.md`

Statement:

- on the full tested BAF class through `n=7`,
- if `d=0` or `d=2`, support complement `{1}` works,
- if `d=1`, support complement `{0,2}` works,
- if `d=3`, support complement `{0}` works, and by reflection so does `{2}`.

So the branch now has:

1. an exact representative theorem,
2. and a first nontrivial support-level lift theorem beyond the
   representatives.

### Reformulations

- “small-range full-class EC lift theorem” representation.

LOAD-BEARING ASSESSMENT: extremely high. This is the first actual theorem on the
broader tested BAF class, not just on the representatives.

### Concrete Artifacts

NEW THEOREM NOTE:

- `info_theory/lb_obstruction/ec_smallrange_support_lift_theorem.md`

CLASS-STABLE EXACT VALUES:

- `n=5`
  - `d=0`, `{1}`: `1/216`
  - `d=1`, `{0,2}`: `1/108`
  - `d=2`, `{1}`: `1/1296`
- `n=6`
  - `d=0`, `{1}`: `7/5832`
  - `d=1`, `{0,2}`: `2/729`
  - `d=2`, `{1}`: `1/1944`
  - `d=3`, `{0}` or `{2}`: `1/1458`
- `n=7`
  - `d=0`, `{1}`: `17/52488`
  - `d=1`, `{0,2}`: `4/6561`
  - `d=2`, `{1}`: `5/52488`
  - `d=3`, `{0}` or `{2}`: `1/8748`

UPDATED NOTES:

- `info_theory/lb_obstruction/ec_bridge_theorem_route.md`
- `info_theory/lb_obstruction/ec_obstruction_theorem.md`
- `info_theory/lb_obstruction/obstruction_result_package.md`

### What Would Unblock This

The next useful support-lift question is now:

1. does the same pattern persist beyond `n=7`?
2. if not exactly, what is the right stabilized support family?

### Key Parameters

- Solved lift range: `n=5,6,7`.
- Distance classes: `d`.

### Open Questions

- Does the pattern
  - even `d`: `{1}`,
  - `d=1`: `{0,2}`,
  - odd `d>=3`: `{0}` or `{2}`
  persist beyond the solved small range?

## Synthesis after exploration 68

- The EC branch now has a real bridge theorem beyond the representative family.
- The next support-lift work is to see whether this solved-range pattern
  stabilizes or changes at larger `n`.

## Exploration 69

### Strategy

Replace the old brute-force support scans with a cached class-pattern check that
tests the solved-range support family on larger `n` without recomputing the
same goods separately for each distance class.

### Outcome

PARTIAL

### Surviving Structure

The right dedicated extension probe now exists:

- `info_theory/lb_obstruction/ec_support_pattern_check.py`

This script computes all valid goods for a fixed `n` once, groups them by
distance class, and checks the candidate support pattern:

- `d=0`: `{1}`
- `d=1`: `{0,2}`
- even `d>=2`: `{1}`
- odd `d>=3`: `{0}` and `{2}`

The in-turn `n=8` run was still too expensive to finish cleanly, so there is no
new theorem yet. But the branch now has the correct extension tool instead of
the older redundant scans.

### Reformulations

- “cached pattern-extension probe” representation.

LOAD-BEARING ASSESSMENT: medium. No new theorem, but it sets up the next
support-lift extension step correctly.

### Concrete Artifacts

NEW TOOL:

- `info_theory/lb_obstruction/ec_support_pattern_check.py`

### What Would Unblock This

The next useful computation is now narrow and well-posed:

1. run `ec_support_pattern_check.py --n 8`,
2. decide whether the solved-range support family persists,
3. if it breaks, isolate the first changed class.

### Key Parameters

- First unresolved extension target: `n=8`.

### Open Questions

- Does the solved-range support pattern survive at `n=8`?
- If not, which distance class changes first?

## Synthesis after exploration 69

- The solved-range theorem remains the current boundary.
- The next step is now a single dedicated extension probe, not more ad hoc
  scanning.

## Exploration 70

### Strategy

Use the cached pattern-check probe to test the solved-range support family at
the first unresolved size `n=8`.

### Outcome

SUCCEEDED

### Surviving Structure

The solved-range support pattern survives intact through `n=8`.

So the small-range full-class support theorem now extends from

- `n=5,6,7`

to

- `n=5,6,7,8`.

The surviving pattern is:

- `d=0`: complement `{1}`
- `d=1`: complement `{0,2}`
- even `d>=2`: complement `{1}`
- odd `d>=3`: complement `{0}` and, by reflection, `{2}`

### Reformulations

- “support-lift theorem through `n=8`” representation.

LOAD-BEARING ASSESSMENT: extremely high. This is the first actual extension of
the full-class EC lift theorem beyond the original solved range.

### Concrete Artifacts

NEW TOOL:

- `info_theory/lb_obstruction/ec_support_pattern_check.py`

UPDATED THEOREM NOTE:

- `info_theory/lb_obstruction/ec_smallrange_support_lift_theorem.md`

COMPUTED `n=8` VALUES:

- `d=0`, `{1}`:
  `13/157464`
- `d=1`, `{0,2}`:
  `1/6561`
- `d=2`, `{1}`:
  `13/472392`
- `d=3`, `{0}` or `{2}`:
  `2/59049`
- `d=4`, `{1}`:
  `5/236196`

STRUCTURAL RESULT:

- The first full-class EC lift theorem is not a fragile `n<=7` accident.
- Its support-family pattern now survives the next size.

### What Would Unblock This

The next useful extension target is now:

1. run the same cached pattern check at `n=9`,
2. determine whether the pattern persists or where it first breaks.

### Key Parameters

- New solved support-lift range: `n=5..8`.

### Open Questions

- Does the same support family persist at `n=9`?
- If not, which distance class breaks first?

## Synthesis after exploration 70

- The EC branch now has a full-class support theorem through `n=8`.
- The next computation is singular: test the same support family at `n=9`.

## Exploration 71

### Strategy

Test the same support family at `n=9`, but do it on the direct two-turnaround
word family first so we can separate:

1. support-pattern persistence,
2. from the separate audit question “does direct family still equal the full
   tested class?”

### Outcome

SUCCEEDED

### Surviving Structure

The support pattern survives at `n=9` on the direct word family.

So the current EC support-lift boundary is now:

- full tested BAF class: theorem through `n=8`
- direct word family: same pattern verified through `n=9`

The surviving pattern remains:

- `d=0`: complement `{1}`
- `d=1`: complement `{0,2}`
- even `d>=2`: complement `{1}`
- odd `d>=3`: complement `{0}` and `{2}`

### Reformulations

- “full-class through `n=8`, direct-family through `n=9`” representation.

LOAD-BEARING ASSESSMENT: very high. This is the first successful extension
beyond the current full-class theorem boundary.

### Concrete Artifacts

UPDATED TOOLS:

- `info_theory/lb_obstruction/ec_support_lift_probe.py`
  now supports `--direct-family`
- `info_theory/lb_obstruction/ec_support_pattern_check.py`
  now supports `--direct-family` and uses the single-mask energy path
- `info_theory/lb_obstruction/single_mask_energy.py`

UPDATED NOTE:

- `info_theory/lb_obstruction/ec_smallrange_support_lift_theorem.md`

COMPUTED `n=9` DIRECT-FAMILY VALUES:

- `d=0`, `{1}`:
  approximately `2.093365e-05`
- `d=1`, `{0,2}`:
  exactly `19/531441`
- `d=2`, `{1}`:
  approximately `6.350658e-06`
- `d=3`, `{0}` or `{2}`:
  approximately `7.526706e-06`
- `d=4`, `{1}`:
  approximately `4.233772e-06`

### What Would Unblock This

The next useful step is now a single audit question:

1. does the direct word family still equal the full tested BAF class at `n=9`?

If yes, the support-lift theorem itself can be promoted from `n<=8` to `n<=9`
without changing form.

### Key Parameters

- New support-lift boundary:
  full class `n<=8`, direct family `n<=9`.

### Open Questions

- Does `ec_word_family_audit.py` still show exact equality at `n=9`?

## Synthesis after exploration 71

- The support family itself looks more stable than the current theorem
  statement.
- The next barrier is now an audit barrier, not a discovery barrier.

## Exploration 72

### Strategy

Clear the remaining audit barrier at `n=9`:

1. audit direct word family vs full tested class at `n=9`,
2. then promote the support-lift theorem if the same family still works on the
   full class.

### Outcome

SUCCEEDED

### Surviving Structure

The full tested BAF class and the direct word family still coincide at `n=9`.

`ec_word_family_audit.py --n-from 9 --n-to 9` reports:

- `tested=9`
- `direct=9`
- `missing=0`
- `extra=0`

So the support-lift theorem itself now extends from:

- `n=5..8`

to:

- `n=5..9`.

The support pattern remains unchanged:

- `d=0`: complement `{1}`
- `d=1`: complement `{0,2}`
- even `d>=2`: complement `{1}`
- odd `d>=3`: complement `{0}` and `{2}`

### Reformulations

- “full-class support-lift theorem through `n=9`” representation.

LOAD-BEARING ASSESSMENT: extremely high. This is the cleanest full-class EC
theorem currently on the branch.

### Concrete Artifacts

UPDATED THEOREM NOTE:

- `info_theory/lb_obstruction/ec_smallrange_support_lift_theorem.md`

AUDIT TOOL:

- `info_theory/lb_obstruction/ec_word_family_audit.py`

AUDIT RESULT:

- `n=9 tested=9 direct=9 missing=0 extra=0`

COMPUTED `n=9` CLASS-STABLE VALUES:

- `d=0`, `{1}`:
  approximately `2.093365e-05`
- `d=1`, `{0,2}`:
  exactly `19/531441`
- `d=2`, `{1}`:
  approximately `6.350658e-06`
- `d=3`, `{0}` or `{2}`:
  approximately `7.526706e-06`
- `d=4`, `{1}`:
  approximately `4.233772e-06`

### What Would Unblock This

The next useful extension question is now simply:

1. does the same support family persist at `n=10`?

At that point we will be testing a real pattern, not trying to discover one.

### Key Parameters

- New full-class support-lift range: `n=5..9`.

### Open Questions

- Does the same support family persist at `n=10`?
- Can the class-stable support values be written in exact closed form for all
  `n`?

## Synthesis after exploration 72

- The EC branch now has a genuine full-class support theorem through `n=9`.
- The next work can finally be about pattern extension or proof, not about
  whether the pattern exists.

## Exploration 73

### Strategy

Attempt the next direct-family extension test at `n=10` using the optimized
single-mask support-pattern checker.

### Outcome

PARTIAL

### Surviving Structure

The theorem boundary is now clean:

- full tested BAF class through `n=9`,
- direct-family extension to `n=10` still unresolved.

The `n=10` run is now an engineering/runtime issue, not a conceptual one:

- `ec_support_pattern_check.py --n 10 --direct-family`
  starts correctly and enters the `d=0` class,
- but does not complete cheaply enough for an in-turn check.

### Reformulations

- “next barrier is computational scale at `n=10`” representation.

LOAD-BEARING ASSESSMENT: medium. No new theorem, but it sharply localizes the
next extension cost.

### Concrete Artifacts

- no new theorem object
- optimized single-mask checker already in place:
  `info_theory/lb_obstruction/ec_support_pattern_check.py`
  with `single_mask_energy.py`

### What Would Unblock This

The next useful step is one of:

1. a dedicated long run of the `n=10` direct-family checker,
2. or a further optimization of the single-support energy computation on large
   classes.

### Key Parameters

- first unresolved extension size after the current theorem:
  `n=10`.

### Open Questions

- Does the same support family survive at `n=10`?

## Synthesis after exploration 73

- The current EC theorem boundary is stable and explicit.
- The next step is now a runtime problem, not a structural discovery problem.

## Exploration 74

### Strategy

Write a new review packet that reflects the actual current theorem boundary
rather than the older route-only state.

### Outcome

SUCCEEDED

### Surviving Structure

The new review artifact

- `info_theory/lb_obstruction/review_packet_v3.md`

now reflects:

- exact EC representative theorem,
- full-class EC support-lift theorem through `n=9`,
- shadow explicit-family theorem package,
- and the remaining universal bridge question.

### Reformulations

- “theorem-phase review packet” representation.

LOAD-BEARING ASSESSMENT: medium. This does not change the math, but it resets
the external presentation to match the true state of the branch.

### Concrete Artifacts

NEW REVIEW NOTE:

- `info_theory/lb_obstruction/review_packet_v3.md`

### What Would Unblock This

The next work after the packet is still mathematical:

1. extend the EC support-lift pattern to `n=10`,
2. or build a comparable lift theorem on the shadow side.

### Key Parameters

- current EC theorem boundary:
  full-class through `n=9`.

## Synthesis after exploration 74

- The branch now has a review packet aligned with its actual theorem boundary.

## Exploration 54

### Strategy

Promote the broader BAF support theorem from a proof architecture note to a
fully written theorem-and-proof package.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the broader EC support theorem as still merely an audited
candidate. It is now a full theorem statement with a complete proof in the
simple state-sequence realization.

### Surviving Structure

- The broader theorem now proves:
  - `ConfState = {all good-cycle states except g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`
  - and hence `|ConfState| = 2n-4`.
- The proof is processorwise:
  - each non-turnaround processor contributes
    `{u_j, u_j+1, v_j, v_j+1}`,
  - and the union of those sets simplifies to the complement of the four
    distinguished boundary steps.

### Reformulations

- Broader BAF theorem closed:
  the EC bridge side now has a full theorem-and-proof package beyond the
  canonical model case.

LOAD-BEARING ASSESSMENT: very high. This is the strongest symbolic theorem on
the EC side so far.

### Concrete Artifacts

DOCS:

- `ec_baf_support_theorem.md`
  now contains the full theorem and proof.

STRUCTURAL RESULTS:

- The broader EC support theorem is now closed in the simple realization.

REPRESENTATIONS:

- “Closed broader BAF support theorem” representation.

### What Would Unblock This

The next useful step is to feed this theorem back into the weak EC bridge law
and sharpen the bridge theorem package.

### Key Parameters

- Broader non-sweep `fc=2` BAF family.

### Open Questions

- Can the weak EC bridge law now be reproved in a more theorem-driven way from
  the support formula?

## Synthesis after exploration 54

- The EC side now has a broader symbolic theorem, not just a canonical one.
- The next best move is to use it to sharpen the bridge package.

## Exploration 55

### Strategy

Promote the broader BAF support statement from a theorem draft to a theorem
package by integrating its proof into the EC obstruction package itself.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing to describe the broader BAF support formula as merely a
candidate. It now has a theorem-and-proof package in its own right.

### Surviving Structure

- The broader BAF support formula is now treated as a theorem, with its proof
  delegated to `ec_baf_support_theorem.md`.
- The EC obstruction package now has:
  - canonical support theorem,
  - broader BAF support theorem,
  - weak global bridge theorem candidate,
  - and the subtraction formula `chi_conf = chi_good - chi_exc`.

### Reformulations

- Broader BAF theorem closed:
  the EC side now has one canonical theorem and one broader family theorem.

LOAD-BEARING ASSESSMENT: very high. This is the strongest stabilization of the
EC package so far.

### Concrete Artifacts

DOCS:

- `ec_obstruction_theorem.md`
  now treats the broader BAF support formula as a theorem with an explicit proof
  reference.
- `ec_baf_support_theorem.md`
  is now the dedicated broader theorem package.

STRUCTURAL RESULTS:

- The EC package is now theorem-complete enough to function as one side of the
  disjunctive bridge program.

REPRESENTATIONS:

- “Closed EC theorem package” representation.

### What Would Unblock This

The next useful step is to feed the closed broader BAF theorem back into the
weak EC bridge theorem and see whether that theorem can now be stated more
cleanly.

### Key Parameters

- Broader non-sweep `fc=2` BAF family.

### Open Questions

- Can the weak EC bridge theorem now be upgraded from a computational
  strengthening to a more theorem-driven corollary?

## Synthesis after exploration 55

- The EC side is now in a stable theorem package state.
- The next step is theorem strengthening, not theorem discovery.

## Exploration 56

### Strategy

Stabilize the next proof sprint by writing the bridge theorem route note for the
EC side, making explicit that the weak bridge theorem should be attacked as a
support-geometry theorem before trying the perturbative
`chi_good - chi_exc` route.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing to approach the EC bridge theorem as an amorphous
“make the numerics look nicer” task. The route is now explicit.

### Surviving Structure

- Route A:
  prove the weak bridge law directly from the support geometry of `ConfState`.
- Route B:
  use the subtraction formula `chi_conf = chi_good - chi_exc` as a secondary
  perturbative route.
- Current recommendation:
  Route A first.

### Reformulations

- EC bridge theorem as support-geometry theorem.

LOAD-BEARING ASSESSMENT: high. This is the right stabilization step before the
next proof sprint.

### Concrete Artifacts

DOCS:

- `ec_bridge_theorem_route.md`
  records the two possible proof routes and prioritizes the support-geometry
  route.

REPRESENTATIONS:

- “Support-geometry-first bridge route” representation.

### What Would Unblock This

The next useful step is to start proving a lower bound on the forbidden mass of
the support geometry itself.

### Key Parameters

- No new computation. This was theorem-route stabilization.

### Open Questions

- Can the support-geometry route actually yield a clean positive lower bound
  symbolically, or will it also need computation at the last step?

## Synthesis after exploration 56

- The next EC bridge proof sprint now has a clear route.
- Future work should attack the support-geometry lower bound directly.

## Exploration 53

### Strategy

Simplify the broader BAF support proof by switching from an arc-local proof
route to a processorwise proof route indexed by each non-turnaround
processor’s two firing times.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the broader EC support theorem must be proved in a
more awkward arc-by-arc language. The processorwise formulation is cleaner.

### Surviving Structure

- For each non-turnaround processor `j`, with firing times `u_j < v_j`,
  define

  `A_j = {u_j, u_j+1, v_j, v_j+1}`.

- Then:
  - processor `j` witnesses conflict exactly on the steps in `A_j`,
  - `ConfState = ⋃_j A_j`,
  - and the only uncovered steps are the two turnarounds and their immediate
    successors.

### Reformulations

- Processorwise proof route:
  the broader BAF support theorem is now a union-of-local-contributions
  theorem.

LOAD-BEARING ASSESSMENT: very high. This is the cleanest current proof route
for the broader EC support theorem.

### Concrete Artifacts

DOCS:

- `ec_baf_support_theorem.md`
  now presents the broader BAF theorem in processorwise form.

STRUCTURAL RESULTS:

- The proof route for the broader BAF theorem is now substantially cleaner.

REPRESENTATIONS:

- “Processorwise broader BAF support theorem” representation.

### What Would Unblock This

The next useful step is to turn the processorwise proof sketch into polished
proof prose and then use it to strengthen the weak global EC bridge theorem.

### Key Parameters

- Family: broader non-sweep `fc=2` BAF family.

### Open Questions

- Is the processorwise route now clean enough to promote the broader BAF
  support theorem from candidate to theorem?

## Synthesis after exploration 53

- The broader EC support theorem now has the right proof shape.
- The next move should be theorem promotion, not more structural tinkering.

## Exploration 52

### Strategy

Promote the broader BAF support theorem from a proof route into a more explicit
arc-local proof sketch with concrete witness selection on each directed arc.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the broader EC theorem as merely an audited statement with
no clear local proof path.

### Surviving Structure

- On each directed arc of a BAF word, the conflict witness is chosen by a
  simple local rule:
  - interior mover steps are witnessed by the mover processor itself,
  - the last interior step before a turnaround is witnessed by the immediately
    preceding interior processor.
- The only non-conflict steps are the two turnarounds and their immediate
  successors.

### Reformulations

- Explicit arc-local witness selection:
  the broader BAF support theorem is now a local geometric theorem, not a
  global pattern.

LOAD-BEARING ASSESSMENT: high. This is the strongest current non-computational
statement on the EC bridge side.

### Concrete Artifacts

DOCS:

- `ec_baf_support_theorem.md`
  now contains the explicit arc-local proof sketch with witness selection.

STRUCTURAL RESULTS:

- The broader EC support theorem now has a direct proof plan.

REPRESENTATIONS:

- “Explicit arc-local witness selection” representation.

### What Would Unblock This

The next useful step is to convert the arc-local proof sketch into a polished
theorem proof and then feed it back into the weak EC bridge theorem.

### Key Parameters

- Broader BAF support theorem.

### Open Questions

- Can the arc-local proof be written in a way that is independent of canonical
  indexing and only refers to the two turnarounds?

## Synthesis after exploration 52

- The broader EC support theorem is now as proof-ready as it is likely to get
  without actually writing the proof.
- The next work should be theorem polishing and bridge strengthening.

## Exploration 51

### Strategy

Stabilize the next EC-side proof target by writing the broader BAF support
theorem as its own theorem draft, rather than keeping it only as an audited
pattern inside larger notes.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing to treat the broader BAF support theorem as only a
supporting remark. It is now explicit enough to stand as the next theorem
object.

### Surviving Structure

- The broader BAF support theorem is now isolated as:
  - one arc-interior lemma,
  - one four-exception lemma,
  - and the resulting support formula.

### Reformulations

- Standalone broader BAF support theorem.

LOAD-BEARING ASSESSMENT: high. This is the right EC-side proof object now.

### Concrete Artifacts

DOCS:

- `ec_baf_support_theorem.md`
  packages the broader theorem statement and proof architecture in one place.

### What Would Unblock This

The next useful step is to actually prove the arc-interior lemma in final form.

## Synthesis after exploration 51

- The EC side now has a clean next theorem target.
- Future work should prove the broader support theorem rather than continue to
  rediscover its shape.

## Exploration 43

### Strategy

Stabilize the bridge side by writing the current bridge-predicate route
explicitly, so the branch can push on the theorem rather than repeatedly
rediscovering the bridge picture.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the bridge side as just a loose collection of EC/shadow
facts. There is now a coherent route note.

### Surviving Structure

- The current bridge route is:
  - `any_overlap` as the tested explicit predicate,
  - EC on the overlap side,
  - rigid shadow-producing orbit on the overlap-free side.

### Reformulations

- Bridge-predicate route:
  the right bridge theorem may be of the form
  “if not overlap, then rigid shadow form.”

LOAD-BEARING ASSESSMENT: very high. This is the clearest bridge program on the
branch so far.

### Concrete Artifacts

DOCS:

- `bridge_predicate_route.md`
  records the bridge-predicate route and the explicit next theorem target.

REPRESENTATIONS:

- “Stable bridge-predicate route” representation.

### What Would Unblock This

The next useful step is either:

1. prove the explicit `n=5` bridge predicate theorem cleanly,
2. or find a more efficient `n=7` classifier to test whether the route scales.

### Key Parameters

- Explicit bridge class:
  `n=5`, `ms=(2,2,2,3,3)`.

### Open Questions

- Is `any_overlap` the right stable bridge predicate?
- Does overlap-free orbit rigidity persist beyond `n=5`?

## Synthesis after exploration 43

- The bridge side now has a stable theorem route note.
- The next work should be proof on the `n=5` bridge theorem or a more efficient
  `n=7` classifier, not more unstructured classification.

## Exploration 44

### Strategy

Test whether the overlap-free orbit rigidity from the explicit `n=5` bridge
class persists to the `n=7` consecutive-binary class.

### Outcome

STALLED

### Failure Constraint

The `n=7` overlap-free orbit classification crosses the cheap-probe boundary in
the current environment. This is a computational stall, not a mathematical
refutation of the bridge route.

### What This Rules Out

It rules out treating the `n=7` bridge-rigidity check as a routine next probe.

### Surviving Structure

- The `n=5` bridge predicate theorem candidate remains intact.
- The `n=7` extension is unresolved, not contradicted.

### Reformulations

- Bridge-rigidity scale check:
  broadening the explicit bridge theorem is now a real computational task.

LOAD-BEARING ASSESSMENT: medium. This is a useful stall classification.

### Concrete Artifacts

TOOLS:

- `bridge_predicate_probe.py`
  isolates the bridge-predicate test for a single architecture class.

### What Would Unblock This

Either:

1. a more efficient targeted classifier for overlap-free cycles at `n=7`,
2. or a proof that overlap-free implies rigid shadow form without enumeration.

### Key Parameters

- Target class:
  `n=7`, `ms=(2,2,2,3,3,3,3)`.

### Open Questions

- Can the bridge route be proved at `n=5` first and only then generalized?

## Synthesis after exploration 44

- The bridge route remains promising, but its first nontrivial scale extension
  is computationally expensive.
- The next best move is likely proof on the explicit `n=5` bridge theorem.

## Exploration 45

### Strategy

Turn the tested bridge route into a more theorem-shaped object by finding a
derived global EC witness that reconnects to the shadow-side forbidden-mass
observable.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the stronger pessimistic conclusion that the EC side can never
reconnect to the forbidden-mass observable.

### Surviving Structure

- The derived global EC witness `chi_conf` has substantial forbidden mass on the
  canonical BAF family and remains uniformly positive on the tested broader BAF
  family through `n=8`.
- So the EC and shadow tracks may partially reunify at the level of derived
  global witnesses.

### Reformulations

- Derived-global-EC bridge:
  use `chi_conf`, not raw overlap, as the EC-side bridge object.

LOAD-BEARING ASSESSMENT: very high. This is the strongest bridge result on the
EC side so far.

### Concrete Artifacts

DOCS:

- `ec_bridge_symbolic_route.md`
  records the theorem ladder for `chi_conf`.
- `ec_obstruction_theorem.md`
  records the weak global bridge theorem candidate.

TOOLS:

- `ec_derived_spectrum.py`
- `ec_baf_conflict_state_probe.py`

### What Would Unblock This

The next useful step is to make `chi_conf` structurally explicit rather than a
black-box derived set.

## Synthesis after exploration 45

- The EC branch now has a serious bridge object.
- The next EC work should be structural, not just spectral.

## Exploration 46

### Strategy

Make the EC bridge object `chi_conf` structurally explicit on the canonical BAF
family.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating `chi_conf` as an opaque derived set on the canonical
family.

### Surviving Structure

- On the canonical BAF family,
  `chi_conf = chi_good - chi_exc`
  where `chi_exc` is the indicator of four exceptional states.
- The support of `chi_conf` is exactly
  `{g_1,...,g_{n-2},g_{n+1},...,g_{2n-2}}`.

### Reformulations

- `chi_conf` as trimmed `chi_good`.

LOAD-BEARING ASSESSMENT: very high. This is the cleanest conceptual bridge from
EC back to the cycle-signature side.

### Concrete Artifacts

DOCS:

- `ec_obstruction_theorem.md`
- `ec_support_formula_proof.md`

## Synthesis after exploration 46

- The EC bridge object is now structurally explicit on the canonical family.
- The next work is to generalize that support geometry beyond the canonical
  word.

## Exploration 47

### Strategy

Audit whether the support geometry of `chi_conf` extends from the canonical BAF
word to the broader non-sweep `fc=2` BAF family.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable through the tested range.

### What This Rules Out

It rules out the worry that the support formula is only a canonical-word
artifact.

### Surviving Structure

- Through the tested BAF family, `ConfState` is exactly the complement of the
  two turnaround steps and their immediate successors.
- This support formula has been audited through `n=9`.

### Reformulations

- Word-level conflict-state geometry.

LOAD-BEARING ASSESSMENT: very high. This is the cleanest symbolic-looking
theorem candidate on the EC side.

### Concrete Artifacts

DOCS:

- `ec_conflict_geometry_probe.py`
- `ec_support_formula_proof.md`

## Synthesis after exploration 47

- The EC bridge object now has a broader audited support formula.
- The next work should be proof, not more auditing.

## Exploration 48

### Strategy

Refine the broader BAF support theorem from a family-level audit into a sharply
defined proof target by reducing it to one arc-local lemma plus four explicit
boundary exceptions.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the broader BAF support theorem as too amorphous to prove.
It now has a clean reduction.

### Surviving Structure

- The broader theorem candidate reduces to:
  1. an arc-local lemma:
     every step in the open interior of a directed arc between the two
     turnarounds lies in `ConfState`,
  2. the boundary lemma:
     exactly the four steps `t_1, t_1+1, t_2, t_2+1` fail to lie in
     `ConfState`.
- Once these are proved, the support formula follows immediately.

### Reformulations

- Arc-local reduction:
  the broader BAF theorem is now a focused local proof task, not a vague global
  extension.

LOAD-BEARING ASSESSMENT: high. This is the correct proof decomposition for the
next EC-side theorem.

### Concrete Artifacts

DOCS:

- `ec_support_formula_proof.md` now states the broader theorem candidate in this
  reduced form.

STRUCTURAL RESULTS:

- The next EC-side proof target is sharply defined.

REPRESENTATIONS:

- “Arc-local reduction of broader BAF theorem” representation.

### What Would Unblock This

The next useful step is to write the arc-local lemma in exact index language and
prove it from the palindromic EC mechanism.

### Key Parameters

- Broader non-sweep `fc=2` BAF family.

### Open Questions

- Does the arc-local lemma admit a concise statement independent of the
  canonical indexing?

## Synthesis after exploration 48

- The broader EC support theorem is now proof-ready in shape.
- The next work should be the actual arc-local proof.

## Exploration 49

### Strategy

Stabilize the next universal target by writing the explicit disjunctive bridge
route as its own theorem note, rather than leaving the bridge theorem scattered
across shadow-side and EC-side packages.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing to talk about the bridge only informally. The branch now
has a theorem-shaped bridge target written down cleanly.

### Surviving Structure

- The branch now has:
  - shadow-side weak floor,
  - EC-side weak bridge law,
  - explicit disjunctive floor `37/324`,
  - and a bridge-predicate route.
- The next theorems worth proving are now explicitly prioritized inside one
  route note.

### Reformulations

- Disjunctive bridge route:
  the branch’s true target is no longer “more witness package polish” but a
  broader bridge theorem derived from the two weak witness floors.

LOAD-BEARING ASSESSMENT: high. This is the correct stabilization step before
the next theorem sprint.

### Concrete Artifacts

DOCS:

- `disjunctive_bridge_route.md`
  packages the next universal target and the immediate bridge tasks.

REPRESENTATIONS:

- “Stable disjunctive bridge route” representation.

### What Would Unblock This

The next useful step is to pick the next theorem sprint explicitly:

1. broader BAF support theorem,
2. weak global EC bridge theorem proof,
3. broader explicit bridge theorem beyond `n=5`,
4. or a first canonical shadow witness theorem beyond the explicit sweep class.

### Key Parameters

- No new numerics. This was bridge-target stabilization.

### Open Questions

- Which of the four bridge tasks should be attacked first?

## Synthesis after exploration 49

- The branch now has a stable next target.
- The next move should be a focused theorem sprint, not more route discovery.

## Exploration 33

### Strategy

Push the `chi_conf` support-geometry audit one size further to `n=9`, to test
whether the broader BAF-family support formula remains stable beyond the
low-`n` regime.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the concern that the broader support formula is only a through-`n=8`
accident. The same pattern survives at `n=9`.

### Surviving Structure

- `ec_conflict_geometry_probe.py --n-from 9 --n-to 9` reports:
  - `n=9`
  - `9` non-sweep words
  - `0` failures.
- So the support formula

  `ConfState = {all good-cycle steps except t_1, t_1+1, t_2, t_2+1}`

  now holds computationally on the tested BAF family through `n=9`.

### Reformulations

- Extended audited support formula:
  the word-level support geometry of `chi_conf` is now stable through a longer
  initial range and looks increasingly like a genuine theorem rather than a
  short-range pattern.

LOAD-BEARING ASSESSMENT: very high. This materially strengthens the case for
proof work on the support theorem.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `n=9`: 9 non-sweep BAF words, 0 support-formula failures.

STRUCTURAL RESULTS:

- The support formula for `chi_conf` now survives through `n=9`.

REPRESENTATIONS:

- “Extended audited BAF support theorem” representation.

### What Would Unblock This

The next useful step is no longer more auditing by default. It is to write the
general BAF support theorem in final form and prove it symbolically.

### Key Parameters

- Tested family: non-sweep `fc=2` BAF words.
- Tested sizes: `n=5..9`.

### Open Questions

- Is the symbolic proof now better attempted at the exact equality-support
  theorem level rather than via more local lemmas?

## Synthesis after exploration 33

- The EC support formula is now audited far enough that proof work should take
  priority over further extension.

## Exploration 34

### Strategy

Make the EC support theorem more canonical by expressing `ConfState` as an
explicit union over interior processors rather than only as a complement-of-four
exceptional states.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out presenting the support theorem only in the “all but four states”
form, which hides the local processorwise source of the conflicts.

### Surviving Structure

- For each interior processor `j`, the relevant conflict-step set is

  `A_j = {j, j+1, 2n-2-j, 2n-1-j}`.

- The full conflict-state set is exactly

  `ConfState = ⋃_{j=1}^{n-3} A_j`.

- Summing these step ranges immediately gives the simpler global description

  `ConfState = {1,...,n-2} ∪ {n+1,...,2n-2}`.

### Reformulations

- Processorwise union formula:
  the global EC bridge object is now visibly assembled from local palindromic
  conflict contributions.

LOAD-BEARING ASSESSMENT: very high. This is the cleanest proof handle on the EC
support theorem so far.

### Concrete Artifacts

DOCS:

- `ec_support_formula_proof.md` now includes Lemmas 4.5 and 4.6 for the union
  formula.
- `ec_obstruction_theorem.md` now records the processorwise union description.

STRUCTURAL RESULTS:

- The support theorem now has both a local and a global expression.

REPRESENTATIONS:

- “Processorwise union support theorem” representation.

### What Would Unblock This

The next useful step is to turn this union formula into a polished theorem
proof, then use it to sharpen the weak global EC bridge law.

### Key Parameters

- Family: canonical BAF and broader tested BAF family.

### Open Questions

- Can the processorwise union formula itself be generalized word-level beyond
  the canonical indexing without changing notation too much?

## Synthesis after exploration 34

- The EC bridge object now has a truly canonical support formula.
- The next work should be proof polishing and theorem promotion, not more
  structural discovery.

## Exploration 35

### Strategy

Promote the canonical EC support formula from a proof skeleton to a fully
written theorem, while keeping the broader BAF-family support statement
explicitly marked as a tested extension candidate.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out saying the EC branch still has only theorem candidates. It now has
at least one genuinely finished symbolic theorem.

### Surviving Structure

- The canonical support formula for `chi_conf` is now written as a theorem with
  proof:

  `ConfState = {g_1,...,g_{n-2}, g_{n+1},...,g_{2n-2}}`

  and equivalently

  `ConfState = ⋃_{j=1}^{n-3} {j, j+1, 2n-2-j, 2n-1-j}`.
- The broader BAF-family support formula remains a tested extension candidate.

### Reformulations

- Canonical EC theorem + broader audited shell:
  this is now the EC-side analogue of the branch structure already used on the
  shadow side.

LOAD-BEARING ASSESSMENT: very high. This is the first genuinely finished
symbolic theorem on the EC bridge side.

### Concrete Artifacts

DOCS:

- `ec_obstruction_theorem.md` now contains a fully written proof of the
  canonical support theorem.
- `ec_support_formula_proof.md` now explicitly separates the canonical theorem
  from the broader BAF extension candidate.

STRUCTURAL RESULTS:

- The EC branch now has a stable symbolic core theorem.

REPRESENTATIONS:

- “Canonical EC theorem + broader audited shell” representation.

### What Would Unblock This

The next useful step is to decide whether to:

1. push the broader BAF support theorem to a full proof,
2. or use the canonical theorem plus the broader audit to strengthen the weak
   EC bridge theorem first.

### Key Parameters

- Canonical BAF family.

### Open Questions

- Is the broader BAF support theorem close enough to prove now?
- Should the next proof effort target the broader support theorem or the weak
  EC bridge law?

## Synthesis after exploration 35

- The EC bridge side now has a real symbolic theorem, not just candidates.
- The branch is ready to choose between extending that theorem or using it as a
  stable base for the bridge theorem.

## Exploration 36

### Strategy

Relate the EC bridge object `chi_conf` directly to the good-cycle indicator
`chi_good`, so the EC branch no longer looks disconnected from the spectral
target-signature side of the program.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating `chi_conf` as an isolated ad hoc witness. On the
canonical BAF family it is directly obtained from the cycle indicator by
deleting four exceptional states.

### Surviving Structure

- On the canonical BAF family:

  `chi_conf = chi_good - chi_exc`,

  where `chi_exc` is the indicator of the four exceptional states
  `g_0, g_{n-1}, g_n, g_{2n-1}`.
- The resulting forbidden fractions show that `chi_conf` remains on the same
  spectral scale as `chi_good`, while `chi_exc` is even more nonlocal.

### Reformulations

- Cycle-indicator reduction:
  the EC bridge object is a trimmed good-cycle indicator, not a completely
  alien object.

LOAD-BEARING ASSESSMENT: very high. This is the strongest conceptual bridge
from the EC track back to the original spectral target-signature program.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Canonical BAF family:
  - `chi_good` forbidden fractions through `n=9`
  - `chi_conf` forbidden fractions through `n=9`
  - `chi_exc` forbidden fractions through `n=9`
  recorded in `ec_obstruction_theorem.md`.

DOCS:

- `ec_obstruction_theorem.md`, `review_packet_v2.md`, and
  `obstruction_result_package.md` now record the subtraction formula.

STRUCTURAL RESULTS:

- The EC bridge object is now directly tied to the cycle-spectrum side.

REPRESENTATIONS:

- “`chi_conf` as trimmed `chi_good`” representation.

### What Would Unblock This

The next useful step is to decide whether the branch should now return to the
reviewer’s “target signature lemma” question and study `chi_good` more
systematically on explicit obstruction families.

### Key Parameters

- Canonical BAF family through `n=9`.

### Open Questions

- Is there a clean target-signature theorem for `chi_good` itself on the EC
  side?
- Can the subtraction formula help prove the weak EC bridge law symbolically?

## Synthesis after exploration 36

- The EC and shadow sides are now closer conceptually than before.
- The next work can legitimately revisit the target-signature side with a much
  better EC bridge object in hand.

## Exploration 37

### Strategy

Test the reviewer’s target-signature question directly on the good-cycle
indicator `chi_good`, comparing valid witnesses against the explicit shadow and
EC obstruction families.

### Outcome

SUCCEEDED

### Failure Constraint

The good-cycle indicator `chi_good` is not a useful separator: its
width-`n-2` forbidden fraction sits on essentially the same scale for valid
witnesses and explicit obstruction families.

### What This Rules Out

It rules out using `chi_good` itself as Piece 1 of the pure spectral transport
program, at least in any naive form.

### Surviving Structure

- Valid witnesses:
  - `CUP-2(n=5..9)`: forbidden fractions `0.128385 .. 0.170450`
  - `Sol3(n=4..9)`: forbidden fractions `0.129630 .. 0.204115`
- Explicit obstruction families:
  - canonical shadow-side sweeps: `0.142618 .. 0.152778`
  - canonical EC-side BAF family: `0.108406 .. 0.136111`
- So `chi_good` lives on the same broad spectral scale on both sides.

### Reformulations

- Negative target-signature result:
  the right spectral target cannot simply be the good-cycle indicator.

LOAD-BEARING ASSESSMENT: very high. This sharply narrows the pure spectral
transport program and prevents wasted effort.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/good_indicator_spectrum.py`
  compares `chi_good` across valid witnesses and explicit obstruction families.

COMPUTED EXAMPLES:

- Valid `CUP-2` and `Sol3` ranges through the tested sizes,
- canonical shadow-side explicit families through `n=8`,
- canonical EC-side BAF family through `n=9`.

STRUCTURAL RESULTS:

- `chi_good` is not the target signature.

REPRESENTATIONS:

- “Negative `chi_good` target-signature result” representation.

### What Would Unblock This

The next useful step is to replace `chi_good` in the pure spectral program by a
different target signature, or else demote the pure transport route further.

### Key Parameters

- Valid families:
  `CUP-2`, `Sol3`.
- Explicit obstruction families:
  shadow-side canonical sweeps,
  canonical EC-side BAF family.

### Open Questions

- Is there any cycle-derived signature better than `chi_good`?
- Does the pure spectral transport route now depend entirely on a different
  scalar?

## Synthesis after exploration 37

- The branch now knows one important thing not to do.
- Future spectral work should not center on `chi_good`.

## Exploration 38

### Strategy

Package the two-track branch into a single theorem-shaped object by combining
the shadow-side weak floor and the EC-side weak bridge law into an explicit
disjunctive witness theorem candidate.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out saying the branch still has only two parallel packages and no
single theorem-shaped object. We now have one, albeit still on an explicit
family union.

### Surviving Structure

- Shadow side:
  `ForbidFrac_{n-2}(chi_shadow) >= 71/504` on the tested explicit shadow class.
- EC side:
  `ForbidFrac_{n-2}(chi_conf) >= 37/324` on the tested BAF family.
- Therefore on the union of these explicit obstruction classes there exists a
  canonically chosen witness `Phi` with

  `ForbidFrac_{n-2}(Phi) >= 37/324`.

### Reformulations

- Explicit disjunctive witness theorem:
  the branch now has the first theorem package that matches the eventual
  universal target in form, even if still only on an explicit family union.

LOAD-BEARING ASSESSMENT: very high. This is the first theorem-shaped object on
the branch that already has the disjunctive witness architecture.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/disjunctive_witness_theorem.md`
  records the explicit disjunctive theorem candidate.

STRUCTURAL RESULTS:

- The branch now has a single theorem object matching the two-track endgame
  shape.

REPRESENTATIONS:

- “Explicit disjunctive witness theorem” representation.

### What Would Unblock This

The next useful step is to decide whether to:

1. strengthen the explicit disjunctive theorem,
2. or attack the true bridge theorem that would make it universal.

### Key Parameters

- Shadow-side tested floor: `71/504`
- EC-side tested floor: `37/324`

### Open Questions

- What is the cleanest bridge theorem from arbitrary subthreshold systems to one
  of the two explicit witness-producing mechanisms?

## Synthesis after exploration 38

- The branch now has a theorem-shaped object that mirrors the intended final
  architecture.
- The next big step is no longer packaging but the universal bridge theorem.

## Exploration 39

### Strategy

Look for the first explicit architecture class on which the actual disjunctive
bridge statement

`EC or SHADOW`

holds cycle-by-cycle, not just as a union of two separate witness packages.

### Outcome

PARTIALLY SUCCEEDED

### Failure Constraint

The `n=7` extension of the same exhaustive bridge test did not finish promptly
in the current probe window, so the current bridge theorem candidate remains
anchored at `n=5`.

### What This Rules Out

It rules out saying we already have a broad bridge theorem. We do not. But we
now have a real architecture-class bridge theorem candidate.

### Surviving Structure

- On the explicit `n=5` consecutive-binary family `ms = (2,2,2,3,3)`,
  `binscc_shadow_universality.py` reports:
  - valid cycles: `6670`
  - blocked by conflict: `210`
  - blocked by shadow: `24`
  - blocked by overlap only: `0`
  - unblocked: `0`
- So on this architecture class, every tested valid cycle is blocked by one of
  the two obstruction mechanisms:
  `EC or SHADOW`.

### Reformulations

- Explicit bridge theorem candidate:
  the branch now has one architecture class on which the disjunctive witness
  theorem shape is already visible directly.

LOAD-BEARING ASSESSMENT: very high. This is the first genuine bridge object on
the branch.

### Concrete Artifacts

DOCS:

- `bridge_theorem_candidates.md`
  records the first explicit bridge theorem candidate.

COMPUTED EXAMPLES:

- `n=5`, `ms = (2,2,2,3,3)`:
  complete EC-or-shadow classification as listed above.

STRUCTURAL RESULTS:

- The branch now has one explicit architecture class where the bridge theorem
  shape is realized.

REPRESENTATIONS:

- “Explicit EC-or-shadow bridge theorem candidate” representation.

### What Would Unblock This

The next useful step is to either:

1. finish the `n=7` bridge sweep,
2. or extract the actual case-split predicate from the `n=5` classification,
   which would be more valuable than another raw extension.

### Key Parameters

- Consecutive-binary subthreshold class at `n=5`.

### Open Questions

- What property separates the 210 EC-blocked cycles from the 24 shadow-blocked
  cycles?
- Does the same architecture-class bridge statement persist at `n=7`?

## Synthesis after exploration 39

- The branch finally has a bridge theorem candidate in the right shape.
- The next smart move is probably to extract the case-split predicate, not just
  broaden the sweep blindly.

## Exploration 40

### Strategy

Extract the first concrete bridge predicate from the explicit `n=5`
consecutive-binary bridge class, rather than treating the EC-or-shadow split as
an unexplained partition.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested class.

### What This Rules Out

It rules out the worry that the explicit bridge theorem candidate is only an
observed disjunction with no identifiable case-split variable. On the tested
class there is already a simple candidate predicate.

### Surviving Structure

- On the explicit `n=5` consecutive-binary class:
  - cycles with `any_overlap = True` land on the EC side,
  - cycles with `any_overlap = False` land on the shadow side,
  - and there are no unblocked cycles.
- So the first explicit bridge predicate is:

  `P = "the cycle has some local overlap"`.

### Reformulations

- First explicit bridge predicate:
  the disjunction `EC or SHADOW` is now tied to a concrete cycle-level
  predicate on the tested architecture class.

LOAD-BEARING ASSESSMENT: very high. This is the first actual case-split
predicate on the branch.

### Concrete Artifacts

DOCS:

- `bridge_theorem_candidates.md` now records the explicit case-split predicate.

STRUCTURAL RESULTS:

- The branch now has an explicit bridge theorem candidate plus an explicit
  bridge predicate on one architecture class.

REPRESENTATIONS:

- “Explicit bridge predicate” representation.

### What Would Unblock This

The next useful step is to test whether `any_overlap` or a close refinement of
it remains the right predicate on a broader consecutive-binary class, or
whether the predicate needs to be made more structural.

### Key Parameters

- Explicit bridge class:
  `n=5`, `ms=(2,2,2,3,3)`.

### Open Questions

- Does the same predicate work at `n=7`?
- If not, what is the right refinement of `any_overlap`?

## Synthesis after exploration 40

- The branch now has a first bridge predicate, not just a bridge theorem
  candidate.
- The next big question is whether that predicate survives a larger explicit
  class.

## Exploration 42

### Strategy

Refine the first explicit bridge predicate by asking whether the overlap-free
side on the `n=5` consecutive-binary class has any internal rigidity, rather
than merely being “the shadow side.”

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested class.

### What This Rules Out

It rules out the worry that the overlap-free side of the bridge theorem is a
large heterogeneous zoo of shadow-producing cycles. On the tested class it is
much more rigid.

### Surviving Structure

- On the explicit `n=5` consecutive-binary class:
  - all overlap-free cycles are shadow-producing,
  - and in fact all `24` overlap-free cycles lie in a single dihedral orbit of
    the mover word

    `(0,1,2,3,4,0,1,2,3,4,3,4)`.

### Reformulations

- Overlap-free orbit rigidity:
  on the first bridge class, the bridge predicate is stronger than a raw
  partition. The shadow side already collapses to one explicit orbit.

LOAD-BEARING ASSESSMENT: very high. This is the strongest bridge-structure
result on the branch so far.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `n=5`, `ms=(2,2,2,3,3)`:
  all 24 overlap-free cycles fall into the single dihedral orbit above.

STRUCTURAL RESULTS:

- The `n=5` bridge class has strong rigidity on the shadow side.

REPRESENTATIONS:

- “Overlap-free orbit rigidity” representation.

### What Would Unblock This

The next useful step is to decide whether this rigidity is a low-`n`
coincidence or the first sign of a more general bridge theorem:
if no overlap, the mover word is forced into a small shadow-producing class.

### Key Parameters

- Explicit bridge class:
  `n=5`, `ms=(2,2,2,3,3)`.

### Open Questions

- Does any comparable rigidity hold at `n=7`?
- Is the right bridge theorem ultimately a rigidity theorem on overlap-free
  cycles?

## Synthesis after exploration 42

- The bridge branch now has a real structural hypothesis to chase:
  overlap-free may force a very small family of shadow-producing words.
- That is a better next target than more blind case extension.

## Exploration 41

### Strategy

Push the first explicit bridge predicate

`P = any_overlap`

from the `n=5` consecutive-binary class to the `n=7` consecutive-binary class.

### Outcome

STALLED

### Failure Constraint

The `n=7` bridge-predicate classification crosses the current cheap-probe
boundary in the present environment. This is a computational stall, not a
mathematical contradiction.

### What This Rules Out

It rules out treating the `n=7` bridge-predicate test as a quick confirmation
step. If we want it, it needs either:

1. a more efficient targeted classifier,
2. or a proof-level argument replacing brute-force classification.

### Surviving Structure

- The `n=5` explicit bridge predicate remains intact.
- The bridge predicate has not been falsified at `n=7`; it is simply not yet
  resolved computationally.

### Reformulations

- Bridge-predicate scale-check view:
  broadening the explicit bridge theorem is now a real computational task, not
  a trivial incremental probe.

LOAD-BEARING ASSESSMENT: medium-high. This is a useful stall classification and
prevents us from wasting cycles pretending this extension is cheap.

### Concrete Artifacts

TOOLS:

- `bridge_predicate_probe.py`
  isolates the bridge-predicate test for a single architecture class.

### What Would Unblock This

Either:

1. a better targeted classifier for the `n=7` cycle space,
2. or a proof of why overlap-free cycles must fall into the shadow regime
   without enumeration.

### Key Parameters

- Targeted class:
  `n=7`, consecutive-binary `ms=(2,2,2,3,3,3,3)`.

### Open Questions

- Is there a structural reason `any_overlap` should remain the right predicate
  at `n=7`?

## Synthesis after exploration 41

- The bridge branch now has a clear computational frontier.
- The next best move is probably proof on the existing `n=5` bridge class or a
  more efficient `n=7` classifier, not more blind waiting.

## Exploration 31

### Strategy

Turn the EC bridge object `chi_conf` into a more theorem-shaped object by
writing a proof-ready support formula for the canonical BAF family.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating `chi_conf` as merely a spectrally visible black-box
derived set. On the canonical BAF family, its support has an explicit simple
description.

### Surviving Structure

- On the canonical BAF family,
  `ConfState = {g_1, ..., g_{n-2}, g_{n+1}, ..., g_{2n-2}}`.
- Equivalently, the only non-conflict states are
  `g_0, g_{n-1}, g_n, g_{2n-1}`.
- Hence `|ConfState| = 2n - 4`.
- On the broader tested BAF family through `n=8`, the support formula appears
  to generalize word-level:
  if the turnarounds are `t_1, t_2`, the non-conflict states are exactly
  `{t_1, t_1+1, t_2, t_2+1}` modulo `2n`.

### Reformulations

- Word-level conflict-state geometry:
  `chi_conf` is the complement of four distinguished turnaround-neighborhood
  states inside the good cycle.

LOAD-BEARING ASSESSMENT: very high. This makes `chi_conf` a much more plausible
EC-side bridge object.

### Concrete Artifacts

DOCS:

- `ec_support_formula_proof.md`
  records the proof route for the support formula.
- `ec_obstruction_theorem.md`
  now includes Theorem candidate C' and C''.

TOOLS:

- `ec_conflict_geometry_probe.py`
  audits the broader support formula through `n=8`.

STRUCTURAL RESULTS:

- `chi_conf` now has a clean symbolic support formula on the canonical family.
- The broader BAF family shows the same support pattern on all tested words
  through `n=8`.

REPRESENTATIONS:

- “Proof-ready `chi_conf` support formula” representation.

### What Would Unblock This

The next useful step is to turn the support formula into a clean symbolic proof
for the broader BAF family and use it to justify the weak EC bridge theorem.

### Key Parameters

- Canonical BAF family, and broader tested non-sweep `fc=2` BAF family through
  `n=8`.

### Open Questions

- Can the word-level support formula be proved directly from the palindromic EC
  mechanism without any computation?
- Is `chi_conf` now canonical enough to be the main EC-side bridge object?

## Synthesis after exploration 31

- The EC bridge object is now structurally explicit.
- The next serious EC work is proof of the support formula, not more discovery.

## Exploration 32

### Strategy

Refine the support-formula proof candidate by identifying the local witness
mechanism step-by-step along the two directed arcs between the BAF turnarounds.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the support formula as a purely global pattern. The proof
can be organized locally along the two directed arcs of the BAF word.

### Surviving Structure

- On each directed arc between the two turnarounds:
  - the first interior step contributes a mover-based overlap witness,
  - interior middle steps contribute both a mover-based and previous-processor
    non-mover witness,
  - the last interior step contributes a previous-processor non-mover witness.
- Therefore every step away from the two turnaround neighborhoods lies in
  `ConfState`.
- The only exceptions are the two turnarounds and their immediate successors.

### Reformulations

- Arc-local support proof:
  the support theorem should be proved by local arc analysis, not by a single
  global combinatorial jump.

LOAD-BEARING ASSESSMENT: high. This is the right proof shape for the EC bridge
support formula.

### Concrete Artifacts

DOCS:

- `ec_support_formula_proof.md` now records the arc-local proof route.

STRUCTURAL RESULTS:

- The support formula has a natural local decomposition by arc position.

REPRESENTATIONS:

- “Arc-local `chi_conf` proof” representation.

### What Would Unblock This

The next useful step is to write the support theorem in terms of a generic BAF
word with turnarounds `t_1, t_2` and prove each of the four exceptional steps
separately.

### Key Parameters

- Family: non-sweep `fc=2` BAF words.

### Open Questions

- Can the same arc-local proof be made completely word-generic without hidden
  canonical assumptions?

## Synthesis after exploration 32

- The EC support theorem is now close to a formal proof plan.
- The next EC work should be a clean theorem statement and proof, not more
  probing.

## Exploration 30

### Strategy

Audit the broader BAF support-geometry formula for `chi_conf` on every tested
non-sweep `fc=2` BAF word through `n=8`, to see whether the canonical support
description really extends word-level.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested range.

### What This Rules Out

It rules out the worry that the support formula for `chi_conf` is a
canonical-word accident. The same formula survives the full tested BAF family.

### Surviving Structure

- For every tested non-sweep `fc=2` BAF word through `n=8`, if the two
  turnaround steps are `t_1, t_2`, then the non-conflict states are exactly:

  `{t_1, t_1+1, t_2, t_2+1}` mod `2n`.

- Equivalently, every other good-cycle step lies in `ConfState`.
- Hence on the tested family:

  `|ConfState| = 2n - 4`.

### Reformulations

- Word-level conflict-state geometry:
  `chi_conf` is now close to a theorem directly on mover words, not just on one
  canonical family instance.

LOAD-BEARING ASSESSMENT: very high. This is the cleanest symbolic-looking
theorem candidate on the EC side so far.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_conflict_geometry_probe.py`
  verifies the support formula across the full tested BAF family.

COMPUTED EXAMPLES:

- `n=5`: 5 non-sweep words, 0 failures
- `n=6`: 10 non-sweep words, 0 failures
- `n=7`: 7 non-sweep words, 0 failures
- `n=8`: 12 non-sweep words, 0 failures

STRUCTURAL RESULTS:

- The support geometry of `chi_conf` is word-level through the tested range.

REPRESENTATIONS:

- “Audited word-level `chi_conf` support formula” representation.

### What Would Unblock This

The next useful step is to turn this audited formula into a symbolic proof and
then use it to sharpen the weak global EC bridge law.

### Key Parameters

- Tested family:
  non-sweep `fc=2` BAF words through `n=8`.

### Open Questions

- Can the support formula be proved directly from the palindromic EC argument?
- Is there an equally clean word-level formula for the broader EC families
  outside the consecutive-binary BAF class?

## Synthesis after exploration 30

- The EC bridge object now has both a weak global bridge law and a clean
  word-level support formula on the tested BAF family.
- The next EC work should be proof of the support formula, not more auditing.

## Exploration 20

### Strategy

Stand up the first explicit-family EC theorem package by treating
confusability/overlap on the good cycle itself, rather than full-space spectral
mass, as the primary observable.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out delaying the EC branch until a universal witness is already in
hand. The branch now has a clean model case theorem, parallel to the shadow-side
model case.

### Surviving Structure

- On the canonical BAF family with binary at `{0,1,2}` and the simple state
  sequences `[0,1,0]`:
  - every interior processor `p in {1,...,n-3}` has overlap count `ov_p = 2`,
  - all other processors have overlap count `0`,
  - so the total confusability witness is
    `E_conf = 2(n-3)`.
- This has been checked through `n = 12`.

### Reformulations

- Canonical EC witness law:
  the EC-side branch should treat overlap / confusability on the good cycle as
  the primary observable, not as a full-space scalar.

LOAD-BEARING ASSESSMENT: very high. This is the first genuine EC-side theorem
package on the branch.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/ec_obstruction_theorem.md`
  packages the canonical EC model-case theorem.

TOOLS:

- `info_theory/lb_obstruction/ec_witness_probe.py`
  computes the processorwise overlap profile and total confusability witness.

COMPUTED EXAMPLES:

- `n=5`: conflict processors `{1,2}`, total overlap `4`
- `n=6`: conflict processors `{1,2,3}`, total overlap `6`
- ...
- `n=12`: conflict processors `{1,...,9}`, total overlap `18`

STRUCTURAL RESULTS:

- The canonical BAF EC witness grows linearly as `2(n-3)`.

REPRESENTATIONS:

- “Canonical EC witness law” representation.

### What Would Unblock This

The next useful step is to identify a canonical EC witness for broader
subthreshold systems, or else prove that the final theorem really needs a
disjunctive shadow-side / EC-side witness form.

### Key Parameters

- Explicit EC family:
  canonical BAF cycles with binary at `{0,1,2}`.
- Sizes tested:
  `n = 5..12`.

### Open Questions

- Can the canonical BAF witness be generalized beyond the consecutive-binary
  setting?
- Is `E_conf` the right EC-side quantity, or just the first model case?

## Synthesis after exploration 20

- The obstruction branch now really has two model cases:
  one shadow-side, one EC-side.
- The next universal-witness work should proceed with both tracks in view.

## Exploration 21

### Strategy

Strengthen the EC-side package from the canonical BAF model case toward a
broader theorem candidate by recasting the existing palindromic EC theorem as a
statement about the confusability witness `E_conf`.

### Outcome

SUCCEEDED

### Failure Constraint

The stronger quantitative count `E_conf >= n-4` is not yet written as a clean
symbolic proof; it remains a candidate refinement. The robust statement at
present is the weaker witness theorem `E_conf > 0`.

### What This Rules Out

It rules out treating the EC-side branch as stuck at one hand-built model case.
There is already a natural bridge theorem candidate to the broader BAF family.

### Surviving Structure

- The canonical BAF overlap law becomes the model case.
- The broader palindromic EC theorem naturally suggests:

  > For any BAF word with a consecutive binary triple, at least one processor
  > has mover/non-mover context overlap, hence `E_conf > 0`.

- A stronger count candidate is visible from the turnaround geometry:

  `# conflicting processors >= max(0,d-2) + max(0,n-d-2) = n-4`,

  but this should currently be treated as a refinement candidate rather than as
  the primary theorem.

### Reformulations

- General BAF EC witness view:
  the palindromic theorem is best restated as positivity of a confusability
  witness, not only as a contradiction argument.

LOAD-BEARING ASSESSMENT: high. This is the first real bridge from the EC model
case toward a broader theorem.

### Concrete Artifacts

DOCS:

- `ec_obstruction_theorem.md` now includes:
  - Theorem A: canonical BAF overlap law,
  - Theorem candidate B: general BAF overlap law.

STRUCTURAL RESULTS:

- The EC branch now has a model case and a broader theorem candidate.

REPRESENTATIONS:

- “General BAF EC witness theorem candidate” representation.

### What Would Unblock This

The next useful EC step is to decide whether to:

1. prove the weaker `E_conf > 0` theorem first,
2. or push the sharper `n-4` count claim into a full proof.

### Key Parameters

- Family under consideration:
  BAF words with consecutive binary triple.

### Open Questions

- Is the weaker positivity theorem already enough for the future disjunctive
  witness statement?
- How much extra work is really needed to turn the `n-4` count into a clean
  proof?

## Synthesis after exploration 21

- The EC-side branch has now crossed from model case to broader theorem
  candidate.
- The next work on this side should be proof refinement, not more package
  discovery.

## Exploration 22

### Strategy

Test how far the EC witness law already extends computationally beyond the
canonical BAF model case by measuring the total confusability witness on all
tested non-sweep `fc=2` words.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested range.

### What This Rules Out

It rules out the fear that the canonical BAF overlap law is a narrow artifact
of one specific mover word. The tested non-sweep `fc=2` family shows a much
stronger regularity.

### Surviving Structure

- On the tested range `n=5..9`, for every non-sweep `fc=2` word in the
  consecutive-binary family, the minimum total confusability witness is exactly
  `2(n-3)`.
- In the tested data, this is not merely a lower bound but an apparent rigid
  equality law.

### Reformulations

- Tested BAF universality law:
  the EC-side branch now points toward a theorem of the form
  `E_conf = 2(n-3)` for the whole non-sweep `fc=2` family, not just
  `E_conf > 0`.

LOAD-BEARING ASSESSMENT: very high. This is the strongest EC-side result on the
branch so far.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_baf_universality_probe.py`
  probes the minimum `E_conf` across all tested non-sweep `fc=2` words.

COMPUTED EXAMPLES:

- `n=5`: minima `{4: 5}`
- `n=6`: minima `{6: 6}`
- `n=7`: minima `{8: 7}`
- `n=8`: minima `{10: 8}`
- `n=9`: minima `{12: 9}`

STRUCTURAL RESULTS:

- The EC-side branch now has a strong tested universality pattern with exact
  linear growth.

REPRESENTATIONS:

- “Tested BAF universality law” representation.

### What Would Unblock This

The next useful EC move is to decide whether to:

1. prove the stronger equality theorem `E_conf = 2(n-3)`,
2. or first prove the weaker positivity theorem `E_conf > 0` and keep the
   equality as computational strengthening.

### Key Parameters

- Tested family:
  all non-sweep `fc=2` words with consecutive binary triple.
- Tested sizes:
  `n=5..9`.

### Open Questions

- Is the equality law symbolically accessible with moderate effort, or should
  the branch bank the weaker positivity theorem first?
- Does the same exact law extend beyond `n=9`?

## Synthesis after exploration 22

- The EC-side branch is now significantly stronger than before.
- The next serious decision is whether to push for the exact equality law or to
  stabilize at the weaker positivity theorem first.

## Exploration 23

### Strategy

Produce the actual `review_packet_v2` reflecting the corrected branch state:
two obstruction tracks, two likely observables, and a disjunctive universal
target.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing to share a shadow-heavy packet that underrepresents the
EC side and the split-observable lesson.

### Surviving Structure

- The branch can now be presented cleanly as:
  - shadow-side package,
  - EC-side package,
  - split-observable lesson,
  - likely disjunctive universal target.
- The universal target is now framed explicitly as:

  > every subthreshold system yields either
  > an EC witness or a shadow witness.

### Reformulations

- Two-track review framing:
  the package is no longer “one obstruction plus caveats,” but a structured
  two-track obstruction program.

LOAD-BEARING ASSESSMENT: high. This is the right form for external review at
the current stage.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/review_packet_v2.md`
  presents both obstruction tracks and the disjunctive bridge problem in one
  self-contained note.

STRUCTURAL RESULTS:

- The branch now has a review document aligned with its actual internal
  structure.

REPRESENTATIONS:

- “Two-track review packet” representation.

### What Would Unblock This

The next useful step is no longer package assembly. It is to make progress on
the universal bridge problem itself.

### Key Parameters

- No new computation. This was package synthesis.

### Open Questions

- Which bridge route should now get the next proof sprint:
  universal witness extraction, reduction, or direct disjunction?

## Synthesis after exploration 23

- The branch now has a reviewable two-track package.
- Future work should focus on the bridge theorem, not on more packaging.

## Exploration 24

### Strategy

Test the reviewer’s highest-value EC question directly: whether a **global
consequence** of entry conflict, rather than the raw local overlap count, has
nonzero width-`n-2` forbidden mass.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the stronger pessimistic conclusion:

- “the EC track can never reconnect to the forbidden-mass observable.”

That is false for at least the first derived global EC quantity tested.

### Surviving Structure

- The raw local EC overlap scalar remains width-3 local and spectrally
  invisible.
- But the derived global EC quantity

  `chi_conf = 1[configuration is a good-cycle state participating in an EC overlap]`

  has substantial nonzero width-`n-2` forbidden mass on the canonical BAF
  family:
  - `n=5`: `0.115741`
  - `n=6`: `0.131944`
  - `n=7`: `0.137037`
  - `n=8`: `0.125857`
- Same-`n` valid coarse-layer references remain much smaller:
  - `CUP-2(n=5)`: `0.026144`
  - `CUP-2(n=6)`: `0.008582`
  - `CUP-2(n=7)`: `0.002573`
  - `CUP-2(n=8)`: `0.000814`

### Reformulations

- Partial reunification view:
  the EC and shadow tracks may still share the forbidden-mass observable at the
  level of **derived global witnesses**, even though they do not share it at the
  level of raw local witnesses.

LOAD-BEARING ASSESSMENT: very high. This is the first serious sign that the
two-track split may not be final at the observable level.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_derived_spectrum.py`
  computes forbidden fractions of the conflict-state indicator.

COMPUTED EXAMPLES:

- Canonical BAF conflict-state indicator through `n=8`, values listed above.

STRUCTURAL RESULTS:

- Raw local EC witness: spectrally invisible.
- Derived global EC witness: spectrally visible and large.

REPRESENTATIONS:

- “Derived global EC witness” representation.

### What Would Unblock This

The next useful step is to decide whether `chi_conf` is the right EC-side
derived witness to pursue, or whether there is an even more canonical global EC
quantity.

### Key Parameters

- Explicit EC family:
  canonical BAF family with consecutive binary triple.
- Tested sizes:
  `n=5..8`.

### Open Questions

- Does the nonzero forbidden-mass phenomenon extend from canonical BAF to the
  broader BAF family?
- Is `chi_conf` canonical enough for the eventual disjunctive witness theorem?

## Synthesis after exploration 24

- The branch now has its first indication that the EC and shadow tracks may
  reconnect at the level of derived global witnesses.
- The next serious decision is whether to push `chi_conf` as the EC-side bridge
  object or keep searching for a better one.

## Exploration 25

### Strategy

Test whether the derived global EC witness `chi_conf` remains spectrally visible
on the broader non-sweep `fc=2` BAF family, rather than only on the single
canonical BAF word.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested range.

### What This Rules Out

It rules out the concern that the nonzero forbidden-mass phenomenon for
`chi_conf` is a one-word artifact. The effect persists across the tested BAF
family.

### Surviving Structure

- On the tested non-sweep `fc=2` BAF family through `n=7`, the conflict-state
  indicator `chi_conf` has uniformly positive width-`n-2` forbidden mass:
  - `n=5`: minima `0.115741 .. 0.166667`
  - `n=6`: minima `0.129630 .. 0.175926`
  - `n=7`: minima `0.129012 .. 0.153086`
- So the EC-side forbidden-mass bridge is not confined to the canonical BAF
  family.
- Same-`n` valid coarse-layer references remain much smaller throughout this
  range.

### Reformulations

- EC-side forbidden-mass bridge:
  the right EC-side bridge object may be a derived global witness like
  `chi_conf`, not the raw local overlap count and not a completely separate
  observable.

LOAD-BEARING ASSESSMENT: very high. This is the strongest bridge result on the
EC track so far.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_derived_spectrum.py`
  probes the conflict-state indicator on the canonical BAF family.
- `info_theory/lb_obstruction/ec_baf_conflict_state_probe.py`
  extends the same quantity across the broader non-sweep `fc=2` family.

COMPUTED EXAMPLES:

- `n=5` non-sweep `fc=2` family:
  minima in `{0.115741, 0.166667}`.
- `n=6`:
  minima in `{0.129630, 0.131944, 0.148148, 0.175926}`.
- `n=7`:
  minima in `{0.129012, 0.129630, 0.137037, 0.153086}`.

STRUCTURAL RESULTS:

- Derived global EC witnesses can have substantial forbidden mass.
- The split-observable lesson still holds for raw local EC witnesses, but the
  two tracks may partially reunify at the level of derived global witnesses.

REPRESENTATIONS:

- “Derived global EC bridge” representation.

### What Would Unblock This

The next useful step is to decide whether `chi_conf` should become the main EC
bridge object, or whether an even more canonical derived global EC witness
exists.

### Key Parameters

- Tested family:
  non-sweep `fc=2` BAF family through `n=7`.

### Open Questions

- Is `chi_conf` canonical enough for the future disjunctive witness theorem?
- Does the same spectral visibility persist at `n=8` and beyond?

## Synthesis after exploration 25

- The EC-side bridge problem is now substantially clearer.
- The current best EC bridge object is `chi_conf`.

## Exploration 26

### Strategy

Push the weak global EC bridge law one step further to `n=8`, to see whether
the uniformly positive forbidden-mass floor for `chi_conf` survives beyond the
initial tested BAF range.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested range.

### What This Rules Out

It rules out the concern that the weak EC bridge law might collapse immediately
after `n=7`. The floor remains positive at `n=8`.

### Surviving Structure

- On the tested non-sweep `fc=2` BAF family at `n=8`, the conflict-state
  indicator minima lie in
  `0.114198 .. 0.135802`.
- Therefore the weak EC bridge theorem candidate strengthens to:

  `ForbidFrac_{n-2}(chi_conf) >= 37/324 > 0.1141`

  on the tested BAF family through `n=8`.

### Reformulations

- Weak global EC bridge law:
  the EC side now has a bridge theorem candidate directly parallel in form to
  the weaker shadow-floor theorem.

LOAD-BEARING ASSESSMENT: very high. This is the first EC-side theorem candidate
with a stable tested floor through a nontrivial range.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `n=8` tested non-sweep `fc=2` BAF family:
  minima include `37/324`, `367/2916`, `185/1458`, `689/5832`, `11/81`.

DOCS:

- `ec_obstruction_theorem.md`, `obstruction_result_package.md`, and
  `review_packet_v2.md` updated to use the strengthened floor
  `37/324`.

STRUCTURAL RESULTS:

- The EC bridge law now persists through `n=8`.

REPRESENTATIONS:

- “Weak global EC bridge theorem” representation.

### What Would Unblock This

The next useful step is to decide whether the branch should now elevate
`chi_conf` to the main EC-side bridge object, or still search for a more
canonical derived global EC witness.

### Key Parameters

- Tested family:
  non-sweep `fc=2` BAF family.
- Tested sizes:
  `n=5..8`.

### Open Questions

- Does the weak EC bridge law continue at `n=9` and beyond?
- Is `chi_conf` canonical enough, or should the branch still search for a more
  intrinsic EC bridge object?

## Synthesis after exploration 26

- The EC-side branch now has a proper weak bridge theorem candidate.
- The next strategic question is no longer “is there an EC bridge?” but “is
  `chi_conf` the right EC bridge object to bet on?”

## Exploration 28

### Strategy

Make the canonical EC bridge object more theorem-shaped by identifying a simple
intrinsic description of its support on the canonical BAF family.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating `chi_conf` as merely an algorithmically extracted derived
set. On the canonical BAF family, it has a simple direct description.

### Surviving Structure

- On the canonical BAF family, the conflict-state set is exactly:

  `{g_1, ..., g_{n-2}, g_{n+1}, ..., g_{2n-2}}`,

  i.e. all good-cycle states except the four distinguished states
  `g_0, g_{n-1}, g_n, g_{2n-1}`.
- Therefore

  `|ConfState| = 2n - 4`.

### Reformulations

- Canonical conflict-state geometry:
  the EC bridge object `chi_conf` can be defined geometrically from the BAF
  cycle itself, not only by searching for overlap states.

LOAD-BEARING ASSESSMENT: high. This makes `chi_conf` a much more plausible
symbolic bridge object.

### Concrete Artifacts

DOCS:

- `ec_obstruction_theorem.md` now includes Theorem candidate C' giving the
  exact support geometry of `chi_conf`.

STRUCTURAL RESULTS:

- The canonical EC bridge object now has a simple support description.

REPRESENTATIONS:

- “Canonical conflict-state geometry” representation.

### What Would Unblock This

The next useful step is to see whether the broader BAF-family `chi_conf`
objects admit an equally simple word-level description, or whether this clean
geometry is special to the canonical word.

### Key Parameters

- Family: canonical BAF.

### Open Questions

- Is there a word-level description of `ConfState` for general BAF words?
- Does that word-level description explain the observed weak global bridge law?

## Synthesis after exploration 28

- `chi_conf` is now a cleaner bridge object than before.
- The next EC bridge work should target its geometry on the broader BAF family.

## Exploration 29

### Strategy

Ask for a direct word-level description of the conflict-state set on the
broader non-sweep `fc=2` BAF family, instead of treating `chi_conf` as a
black-box derived set.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested range.

### What This Rules Out

It rules out the concern that the support geometry of `chi_conf` is a quirk of
the single canonical BAF word. The same pattern appears to hold on the broader
tested BAF family.

### Surviving Structure

- For all tested non-sweep `fc=2` BAF words through `n=8`, if the two
  turnaround steps are `t_1` and `t_2`, then the non-conflict steps are exactly

  `{t_1, t_1+1, t_2, t_2+1}`  (mod `2n`),

  and every other good-cycle step lies in `ConfState`.
- Hence the tested support size is uniformly

  `|ConfState| = 2n - 4`.

### Reformulations

- General BAF conflict-state geometry:
  the EC bridge object `chi_conf` appears to have a direct mover-word
  description, independent of the specific state-sequence realization.

LOAD-BEARING ASSESSMENT: very high. This is the strongest symbolic advance on
the EC bridge side so far.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Through `n=8`, every tested non-sweep `fc=2` BAF word matches the same
  support formula:
  non-conflict steps are exactly the two turnarounds and their successors.

STRUCTURAL RESULTS:

- The support geometry of `chi_conf` appears to be determined by the BAF word
  itself.

REPRESENTATIONS:

- “Word-level conflict-state geometry” representation.

### What Would Unblock This

The next useful step is to turn this from a tested pattern into a symbolic
proof, then use it to prove the weak global EC bridge law more cleanly.

### Key Parameters

- Tested family:
  non-sweep `fc=2` BAF family through `n=8`.

### Open Questions

- Can the support formula be proved directly from the palindromic EC argument?
- Does the same word-level support geometry hold at `n=9` and beyond?

## Synthesis after exploration 29

- The EC bridge object is now much closer to a theorem than before.
- The next step is straightforward proof work on the word-level support
  formula.

## Exploration 27

### Strategy

Stabilize the EC bridge branch around `chi_conf`: write the symbolic route note
for the derived global EC witness, and test whether pushing the weak bridge law
one size further remains a cheap probe.

### Outcome

PARTIALLY SUCCEEDED

### Failure Constraint

The `n=9` extension of the full BAF-family `chi_conf` sweep crossed the current
cheap-probe boundary before returning. This is a computational stall, not a
mathematical contradiction.

### What This Rules Out

It rules out treating `n=9` extension of the full EC bridge sweep as a routine
next probe in the current environment. From here on, size-extension should only
be done when it answers a sharp theorem question.

### Surviving Structure

- `chi_conf` is still the leading EC-side bridge object.
- The EC bridge route is now written down explicitly:
  local overlap → conflict-state extraction → global witness `chi_conf`.
- The branch has enough tested range through `n=8` to proceed with proof
  refinement without waiting on `n=9`.

### Reformulations

- EC bridge symbolic route:
  the right next work is on the witness definition and proof chain, not on
  more size-extension unless necessary.

LOAD-BEARING ASSESSMENT: high. This is the right stabilization step on the EC
bridge side.

### Concrete Artifacts

DOCS:

- `info_theory/lb_obstruction/ec_bridge_symbolic_route.md`
  records the symbolic theorem ladder for `chi_conf`.

STRUCTURAL RESULTS:

- The EC bridge side now has a stable proof route note.
- `n=9` extension is reclassified as computationally nontrivial.

REPRESENTATIONS:

- “Stable `chi_conf` bridge route” representation.

### What Would Unblock This

The next useful step is to refine the symbolic treatment of `chi_conf`, or to
ask a narrower `n=9` computational question than the full family sweep.

### Key Parameters

- Tested BAF bridge law through `n=8`.
- Attempted but stalled extension: full `n=9` family sweep.

### Open Questions

- Is `chi_conf` canonical enough to become the EC-side bridge theorem?
- What is the right narrowly scoped `n=9` question if more computation becomes
  necessary?

## Synthesis after exploration 27

- The EC bridge branch is now stabilized around `chi_conf`.
- The next work should be proof refinement, not blind size extension.

## Exploration 19

### Strategy

Stand up the first explicit EC witness candidate and test whether it registers
in the same width-`n-2` forbidden-mass observable used on the shadow side.

### Outcome

SUCCEEDED

### Failure Constraint

The naive EC overlap witness is too local. When extended to the full
configuration space as a sum of processorwise overlap indicators, it is a
width-3 local scalar and therefore has zero width-`n-2` forbidden interaction
fraction.

### What This Rules Out

It rules out the simplest unification dream:

- “use the same forbidden-mass observable on a naive local EC witness and on
  the shadow witness.”

That is too naive.

### Surviving Structure

- On canonical BAF-style EC examples:
  - `ms = (2,2,2,3,3)`
  - `ms = (2,2,2,3,3,3)`
  the natural full-space EC scalar

  `total_overlap(c) = Σ_i 1[(c_{i-1}, c_i, c_{i+1}) in O_i]`

  has width-`n-2` forbidden fraction exactly `0`.
- This is not an accident but a structural fact:
  the scalar is a sum of width-3 local indicators.
- So the EC branch still needs a witness, but it likely needs either:
  - a nonlocal EC-derived witness,
  - or a different observable (zero-error / confusability style) than the
    shadow-side forbidden-mass quantity.

### Reformulations

- Split-observable witness view:
  the universal lower-bound program should now be treated as:
  - shadow witness measured by forbidden mass,
  - EC witness measured by a different complexity quantity unless a more
    nonlocal EC witness is found.

LOAD-BEARING ASSESSMENT: very high. This is the first concrete structural split
between the EC and shadow tracks.

### Concrete Artifacts

TOOLS:

- `info_theory/lb_obstruction/ec_overlap_spectrum.py`
  probes the forbidden fraction of local EC overlap scalars on explicit EC
  examples.

COMPUTED EXAMPLES:

- `ms = (2,2,2,3,3)`:
  overlap processors `{1,2}`; `total_overlap` forbidden fraction `0.000000`.
- `ms = (2,2,2,3,3,3)`:
  overlap processors `{1,2,3}`; `total_overlap` forbidden fraction `0.000000`.

STRUCTURAL RESULTS:

- Naive EC overlap indicators are invisible to the current forbidden-mass
  observable.

REPRESENTATIONS:

- “EC track needs its own observable” representation.

### What Would Unblock This

The next useful step on the EC track is to decide between:

1. a nonlocal EC-derived witness,
2. or a zero-error/confusability quantity as the primary EC obstruction
   observable.

### Key Parameters

- Explicit EC examples:
  canonical BAF-style cycles on
  `(2,2,2,3,3)` and `(2,2,2,3,3,3)`.

### Open Questions

- What is the right nonlocal EC witness, if one exists?
- Is the confusability-edge count `E_conf` the right EC-side quantity?
- Can the final lower-bound theorem reasonably be disjunctive in both witness
  type and observable?

## Synthesis after exploration 19

- The branch now knows that EC and shadow are not just two obstruction types;
  they may require two different observables.
- The next admissible EC work is to test a zero-error/confusability quantity,
  not to keep forcing local overlap counts into the forbidden-mass framework.
