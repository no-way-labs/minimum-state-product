# UB Exploration Log

This file is the long-horizon exploration log for the upper-bound proof of the
endpoint-binary CUP-2 witness family.

It is intended to play the same role for the UB pursuit that the residue logs
play elsewhere: preserve failed ideas, proven substructure, and the exact shape
of the remaining gap so later sessions do not re-derive old dead ends.

---

## Strategy Register

### Eliminated Approach Classes

- **B1-B4 / anomalous-entry table-chase as main Lean route** — eliminated at
  exploration 1. The proof architecture exploded into ~14,855 lines of dead
  infrastructure and false decomposition hypotheses. See
  `ub_convergence_retro.md`.

- **Raw mixed-step staircase assembly** — eliminated at exploration 6. Any
  route that needs a one-step well-founded rank for the coupled mixed interval
  runs into symmetric boundary/interior coupling. See
  `ub_staircase_mixed_obstruction.md`.

- **Deterministic macro quotient / per-step rerouting after normalization** —
  eliminated at exploration 7. The rerouting lemma is false: normalization can
  disable the boundary step that existed pre-normalization.

- **Finite local quotients of BasinMacroStep by obvious signatures** —
  eliminated at exploration 8. Thickened annulus quotients and halo-signature
  quotients all reintroduced cycles even when they determined edge sets.

- **Boundary determination of Φ_full** — eliminated at exploration 9. False
  under exact semantics: same boundary six-tuple can yield different Φ_full,
  even with the same TP triple.

- **Uniform per-config +1 shift for Φ_full under adding a deep interior site** —
  eliminated at exploration 9. False / overkill as a main theorem target.

- **Local theorem “all TP-preserving T_mid moves are fc-nonincreasing”** —
  eliminated at exploration 9. False at `P2`: `(2,1,1) -> 0` can preserve TP
  while increasing `fc`.

### Obstructions

- **`cphi_bridge` is the old-route bottleneck.** The old `Φ_full / CΦ / 617-edge`
  route is complete except for one global transport/locality theorem in
  `ConstLayerDAG.lean`.

- **Mixed interval coupling obstruction.** The pure-mid rank depends on
  interface state and the interface rank depends on pure-mid boundary cells, so
  no simple lex / weighted energy order closes `mixed_step_wf`.

- **Rerouting obstruction.** For macro staircase, normalizing the source can
  change a boundary-adjacent interior cell and make a previously available
  boundary move no longer privileged.

- **Quotient-cycle obstruction.** `BasinMacroStep` on full CoreNormal states may
  be acyclic, but all tested finite quotients by annulus or halo data had
  cycles.

- **`Exp2Weight` reindexing is global under deletion.** It is affine enough to
  analyze exactly, but deletion transport must account for side counts or
  weighted side distributions, not just local windows.

### Building Blocks

- **Executable `Φ_full` at `n = 9`** with `bridge_class9`: exact exhaustive
  classification of boundary-changing TP-preserving bad steps into 617-edge or
  `Φ`-drop.

- **Reachability infrastructure**: `Reachable.lean` and computable
  `cup2TpReachable` / `cup2PhiFull`.

- **ConstLayerDAG cleanup**: 6 easy sorrys closed; only `cphi_bridge` remains.

- **Staircase pure-mid theorem**: explicit rank-based acyclicity for the
  unbounded pure-mid core.

- **Staircase Normalize API**: `interior_step_wf`, relation-valued
  normalization, same-fiber preservation.

- **`BasinMacroStep`**: corrected replacement for the false rerouting-based
  `MacroStep` bridge object.

- **Deletion machinery**: `liftIdx`, `deleteConfig`, and partial transport
  lemmas in `CPhiDelete.lean`.

### Known Reformulations

1. **One-site no-drop transport** — LOAD-BEARING.
   Instead of proving full locality of `Φ_full`, try to show that every non-617
   no-drop witness at size `n` deletes to one at size `n-1`, preserving the
   same boundary pair. This is currently the best theorem shape.

2. **Equality-witness focus for `cphi_bridge`** — LOAD-BEARING.
   `Φ_full` is monotone along TP-preserving bad reachability. The only true
   obstruction is equality, not increase. This cuts the target from global
   classification to “no-drop witness” transport.

3. **Staircase as negative guidance, not active route** — LOAD-BEARING.
   The staircase detour is now best treated as a source of proved local assets
   and obstructions, not the main closure path.

4. **Boundary-locality or exact `+1` shift for all configs** — NOT LOAD-BEARING.
   Both are now judged too strong and, in their naive forms, false.

---

## Exploration 1

### Strategy
Follow the AP’s B1-B4 anomalous-entry table-chase proof architecture in Lean.

### Outcome
FAILED

### Failure Constraint
The AP architecture required large endpoint-refined certificate systems and
false decomposition hypotheses. The Lean code grew to ~14,855 lines without
closing the main convergence argument.

### What This Rules Out
Any UB route whose primary machine-proof object is a forced-sequence anomalous
entry chase with bespoke certificate layers.

### Surviving Structure
- A clearer sense that the real proof should be much shorter.
- The eventual realization that the AP and the best computational proof route
  had diverged.

### Reformulations
The proof should be centered on a global monotone quantity plus a finite inner
graph, not per-entry sequence analysis.

### Concrete Artifacts
- `ub_convergence_retro.md`
- the large deleted convergence infrastructure recorded there

### What Would Unblock This
Nothing. This route is not worth repairing.

### Key Parameters
- Full `n ≥ 9` upper-bound convergence proof.

### Open Questions
- What is the shortest honest replacement architecture?

---

## Exploration 2

### Strategy
Adopt the discovered old-route architecture:
`Φ_full` + constant-`Φ_full` 6-tuple graph + interior hop potential.

### Outcome
SUCCEEDED (except one hard bridge theorem)

### Failure Constraint
Only one hard theorem remained: `cphi_bridge`, the transport/locality step
showing that a boundary-changing CΦ step must lie in the 617-edge graph.

### What This Rules Out
It rules out treating the whole old route as fundamentally broken. The route is
sound except for one global theorem.

### Surviving Structure
- `PhiFull.lean`
- `PhiFullTP.lean`
- `ConstLayerDAG.lean`
- `Main.lean`
- the two-level potential proof architecture

### Reformulations
The UB problem is reduced to understanding boundary-changing TP-preserving bad
steps at constant `Φ_full`.

### Concrete Artifacts
- the reduced convergence codebase
- the 617-edge / 324-state boundary graph

### What Would Unblock This
An n-independent transport/locality theorem for `cphi_bridge`.

### Key Parameters
- boundary-changing CΦ steps for all `n ≥ 9`

### Open Questions
- can `cphi_bridge` be reduced to a finite executable check plus transport?

---

## Exploration 3

### Strategy
Make `cup2PhiFull` executable and close `cphi_bridge` via an exhaustive `n = 9`
classification plus a transport theorem.

### Outcome
STALLED

### Failure Constraint
The exact `n = 9` classification became executable and proved, but the
transport theorem did not crystallize. `Φ_full` is a max over TP-preserving
bad-reachable states, so naive compression/extension changes the reachable set
globally.

### What This Rules Out
Naive “compress to `n = 9`” or “embed `n = 9` into arbitrary `n`” arguments
that ignore reachable-set changes.

### Surviving Structure
- `Reachable.lean`
- computable `cup2TpReachable`, `cup2PhiFull`
- `PhiFull9.lean`
- `bridge_class9`
- 6 easy `ConstLayerDAG` sorrys closed

### Reformulations
The real last gap is not “compute Φ_full.” It is “transport the `n = 9`
boundary classification to all `n ≥ 9`.”

### Concrete Artifacts
- `ub_cphi_bridge_plan.md`
- `ub_cphi_bridge_session_results.md`

### What Would Unblock This
A weakest true locality/compression theorem for no-drop witnesses, not for
all of `Φ_full`.

### Key Parameters
- exact `n = 9` classification solved
- arbitrary `n ≥ 9` transport open

### Open Questions
- is full finite-signature locality true, or is a weaker one-sided theorem enough?

---

## Exploration 4

### Strategy
Search for a staircase proof route: Phase 1 bad-pattern predicate, support
freezing, active intervals, and a local pure-mid core.

### Outcome
SUCCEEDED (as local structure discovery)

### Failure Constraint
None at this stage. The staircase route looked more local than `cphi_bridge`
and was worth serious pursuit.

### What This Rules Out
It rules out dismissing staircase as mere speculation. The Phase 1 predicate
and pure-mid core are real.

### Surviving Structure
- fixed Phase 1 predicate
- support freezing
- active interval decomposition
- pure-mid local theorem target

### Reformulations
Same-score positive-score dynamics can be studied by frozen bad support plus
independent active intervals.

### Concrete Artifacts
- `ub_staircase_research.md`
- `ub_staircase_lean_plan.md`
- cold-start answer family `oans4/oans5/...`

### What Would Unblock This
Formal pure-mid acyclicity and then a post-pure-mid global assembly theorem.

### Key Parameters
- Phase 1 predicate on exact CUP-2 tables

### Open Questions
- does the post-pure-mid route admit a bounded quotient?

---

## Exploration 5

### Strategy
Prove the pure-mid core theorem directly by an explicit rank
`ρ = (N21, N01, N20, N02, μ)`.

### Outcome
SUCCEEDED

### Failure Constraint
None for the pure-mid core itself.

### What This Rules Out
It rules out the concern that the unbounded pure-mid interval was the main
mathematical gap.

### Surviving Structure
- `PureMid.lean` complete
- rank-drop theorem for the 13 legal pure-mid rewrites
- interval acyclicity and well-foundedness

### Reformulations
The unbounded heart of the staircase route is now a solved rank problem, not an
open graph problem.

### Concrete Artifacts
- `PureMid.lean`
- `ub_puremid_proof.md`
- `ub_staircase_pure_mid_package.md`

### What Would Unblock This
A way to expose the pure-mid theorem through a correct global assembly API.

### Key Parameters
- all boundary pairs
- all pure-mid lengths

### Open Questions
- what is the right cross-section/quotient above the pure-mid core?

---

## Exploration 6

### Strategy
Use pure-mid acyclicity plus interface DAG to prove a mixed-step well-founded
theorem for the full staircase active interval.

### Outcome
FAILED

### Failure Constraint
The pure-mid rank depends on interface boundary values, while the interface
rank depends on pure-mid boundary cells. Each move changes the “other”
component’s rank. No lex order, weighted energy, or corrected boundary energy
worked.

### What This Rules Out
Any one-step rank on the raw coupled mixed interval that treats pure-mid and
interface parts as almost independent.

### Surviving Structure
- proved 108-state interface DAG
- a complete catalog of the 4 hard obstruction rewrites

### Reformulations
The right place for the hard endpoint-adjacent T_mid rewrites is inside a
contracted pure-mid block, not inside a raw one-step mixed theorem.

### Concrete Artifacts
- `ub_staircase_mixed_obstruction.md`
- `Gadget.lean` partial results

### What Would Unblock This
Not another weighted rank. The raw mixed-step theorem is the wrong object.

### Key Parameters
- boundary-adjacent T_mid rewrites
- left/right extension lengths

### Open Questions
- can same-score pure-mid motion be contracted instead of ranked stepwise?

---

## Exploration 7

### Strategy
Switch to the macro staircase route: define `CoreNormal`, relational
normalization, and macro steps as boundary move plus normalization.

### Outcome
PARTIAL SUCCESS / FAILED at the original proof sketch

### Failure Constraint
The per-step rerouting lemma is false. Normalizing the source can change a
boundary-adjacent interior cell and remove the boundary privilege needed to
simulate the original step.

### What This Rules Out
Any proof that projects same-score cycles by normalizing each boundary source
first and then replaying the same boundary step.

### Surviving Structure
- `Normalize.lean`
- `interior_step_wf`
- same-fiber normalization existence

### Reformulations
Normalization is relation-valued and nonunique. The bridge theorem must be
SCC/cycle-style, not deterministic quotient-style.

### Concrete Artifacts
- `Normalize.lean`
- false rerouting counterexample recorded in `Macro.lean`

### What Would Unblock This
A corrected bridge relation that lets the boundary step happen somewhere in the
normalization basin.

### Key Parameters
- positive-score same-score cycles

### Open Questions
- can a repaired basin relation admit an acyclic finite quotient?

---

## Exploration 8

### Strategy
Use `BasinMacroStep`, then search for a finite acyclic quotient by six-tuple
data, thickened annuli, or finite halo signatures.

### Outcome
FAILED

### Failure Constraint
`BasinMacroStep` itself may be acyclic on full states, but every obvious finite
local quotient introduced cycles. The old six-tuple `(fc, ψ)` rank did not
control basin edges, the annulus quotient cycled, and halo-signature quotients
cycled even when they determined edge sets.

### What This Rules Out
Finite bounded-interface quotients of the obvious local type as a remaining
high-ROI staircase proof object.

### Surviving Structure
- `BasinMacroStep`
- preservation lemmas
- strong negative knowledge about false quotient shapes

### Reformulations
The staircase route is now better viewed as a source of local assets and
obstructions than as the main closure path.

### Concrete Artifacts
- `Macro.lean`
- annulus and halo computational tests
- `ub_post_staircase_pivot_log.md`

### What Would Unblock This
Either a fundamentally different full-state argument for `BasinMacroStep`, or a
return to the old route.

### Key Parameters
- positive-score fibers
- boundary-visible summaries of depth 1–3

### Open Questions
- is there any high-ROI staircase compression idea left? Current answer: likely no.

---

## Exploration 9

### Strategy
Interrogate the old-route `cphi_bridge` gap with new cold-start prompts.

### Outcome
PARTIAL SUCCESS

### Failure Constraint
Broad locality theorems were repeatedly too strong. Several candidate theorems
were outright false.

### What This Rules Out
- full boundary determination of `Φ_full`
- exact per-config `+1` shift of `Φ_full`
- blanket local `Δfc ≤ 0` for all TP-preserving T_mid steps

### Surviving Structure
- best theorem shape from `oans6/oans8a`: one-site no-drop transport
- exact `Exp2Weight` deletion defect analysis from `oans6` revision 3

### Reformulations
The real target is not locality of all of `Φ_full`, but transport of
**non-617 no-drop witnesses**:

```text
E_n \ G617 ⊆ E_{n-1}
```

### Concrete Artifacts
- `oans6.md`
- `oans7.md`
- `oans8a.md`
- `oans8b.md`
- `ans6` rejected by explicit counterexample

### What Would Unblock This
Formalize the deletion theorem in Lean and force the exact remaining hard lemma
to surface.

### Key Parameters
- no-drop equality witnesses
- deletable deep interior sites

### Open Questions
- can every non-617 no-drop witness delete to one at size `n-1`?

---

## Exploration 10

### Strategy
Implement the deletion route in Lean via `CPhiDelete.lean` and push until the
real obstruction appears.

### Outcome
STALLED (constructively)

### Failure Constraint
The session first chased two over-strong axiom candidates
(`phiFull_boundary_determined`, `phiFull_shift_plus_one`), then pivoted back to
deletion transport. The current concrete remaining gap is a `Φ_full`-gap
preservation lemma under deletion.

### What This Rules Out
It further rules out returning to the axiom route as the main active theorem.

### Surviving Structure
- deletion map `δ_k`
- boundary-six preservation machinery (partially proved)
- exact `Exp2Weight` correction formulas (partially set up)
- TP-preserving deep-interior T_mid triples copy a neighbor
- local `fc` nonincrease for the relevant divergent triples

### Reformulations
The best Lean-facing theorem now is:

```text
for every non-617 no-drop witness at size n ≥ 10,
there exists k ∈ {3,...,n-4} such that deleting k yields
a non-617 no-drop witness at size n-1 with the same β
```

### Concrete Artifacts
- `CPhiDelete.lean`
- `ub_cphi_delete_session.md`

### What Would Unblock This
An exact lemma of the form:

```text
if c and d agree in a neighborhood of k and Φ_n(c) = Φ_n(d),
then Φ_{n-1}(δ_k c) = Φ_{n-1}(δ_k d)
```

or a stronger witness-path transport lemma implying it.

### Key Parameters
- deep interior deletion sites `k ∈ {3,...,n-4}`
- source/target witness transport

### Open Questions
- is the true wall source-side lifting, target-side compression, or
  existence of a deletable site?

---

## Synthesis after exploration 10

The UB search is no longer broad.

The current situation is:

- old route: one genuine theorem gap (`cphi_bridge`)
- staircase: valuable local assets, but no remaining high-ROI quotient route
- current best theorem shape: deletion transport of no-drop non-617 witnesses

The search should now proceed by repeatedly sharpening the deletion theorem:

1. prove every structural deletion fact possible
2. isolate the exact remaining `Φ_full` transport lemma
3. if that lemma fails, extract the smallest counterexample shape

That is the current default representation of the UB problem.

---

## Exploration 11

### Strategy
Refactor the deletion route inside `CPhiDelete.lean` into passive and active
branches, and push the passive/no-copy branch to the smallest finite object.

### Outcome
PARTIAL SUCCESS

### Failure Constraint
The route did not close outright, but the passive branch compressed much
further than expected. The remaining obstacle is no longer broad locality of
`Φ_full`; it is one exact n-independence theorem for frozen no-copy strips.

### What This Rules Out
It further rules out treating the deletion route as one monolithic hard lemma.
The route is now sharply split:

- passive/no-copy branch
- active/copy-pair branch

Any future work should preserve this split.

### Surviving Structure
- `source_transport` is engineering rather than the main mathematical wall
- target transport decomposes into:
  - active case
  - passive + copy-pair case
  - passive + no-copy impossibility
- `passive_uniform_defect` is proved and gives exact control of deletion defect
  when a frozen strip agrees near the deletion site
- a finite passive object `H_nocopy` emerged:
  the set of boundary six-tuple pairs arising from passive/no-copy no-drop
  witnesses

### Reformulations
The passive branch now has the following exact factorization:

```text
isNoCopyEdge / H_nocopy
        |
        +-- H_nocopy_subset_G617
        +-- passive_noCopy_mem_H
        |
        v
passive_noCopy_impossible
```

This is a major compression of the search space.

LOAD-BEARING ASSESSMENT:
Yes. This changes the effective search space. The passive branch is no longer a
vague global theorem; it is a finite classification plus one n-independence
claim.

### Concrete Artifacts

COMPUTED EXAMPLES:
- No-copy no-drop witnesses were checked at `n = 10, 11` under exact semantics.
- The passive/no-copy no-drop boundary pairs stabilize to a finite subset
  `H_nocopy`.
- Current cleaned summary:
  `H_nocopy` has cardinality 335 under exact CΦ semantics and is a subset of
  `G617`.

STRUCTURAL RESULTS:
- passive/no-copy no-drop witnesses depend only on the boundary six-tuple pair
  `β`, not on strip endpoints
- `passive_noCopy_impossible` is now sorry-free *modulo*
  `passive_noCopy_mem_H` and `H_nocopy_subset_G617`

TOOLS:
- `CPhiDelete.lean` now contains the passive/active branch split explicitly

REPRESENTATIONS:
- `H_nocopy` as a finite predicate on `SixState × SixState`
- passive/no-copy branch as a finite edge-membership problem, not a path problem

### What Would Unblock This

Passive branch:
- encode `H_nocopy` exactly in Lean
- prove `H_nocopy_subset_G617` by finite check
- prove `passive_noCopy_mem_H`, i.e. the n-independence theorem for frozen
  no-copy strips

Active branch:
- after passive branch closes, isolate the remaining path-analysis theorem
  for a deletable active site

### Key Parameters
- passive/no-copy strip
- exact boundary pair `β`
- `n = 10, 11` used as stabilization checks

### Open Questions
- what is the weakest exact statement of `passive_noCopy_mem_H`?
- once passive branch closes, is the active branch really just one path lemma?

---

## Synthesis after exploration 11

The UB pursuit is now in a two-branch endgame:

1. **Passive branch**
   - finite object `H_nocopy`
   - one n-independent membership theorem
   - then `passive_noCopy_impossible` closes

2. **Active branch**
   - one deletable active-site / path-projection theorem

This is the most compressed state the UB search has reached so far.

Practical conclusion:
- finish the passive branch first
- do not let the active branch distract from closing a finite-classification
  subproblem that is now clearly separated

---

## Exploration 12

### Strategy
Internalize the passive branch base case in Lean (`PhiFull10.lean`), then build
generic deletion/path transport infrastructure reusable across passive and
active branches.

### Outcome
PARTIAL SUCCESS

### Failure Constraint
Several generic theorems turned out to be false, forcing branch-specific
refinements:

- generic `deleteConfig_bad_preserved`
- generic right-seam no-copy step projection
- exact per-config scalar shortcuts for `Φ_full`

### What This Rules Out
It rules out proving the passive branch by one global deletion theorem or by a
single scalar formula for `Φ_full`.

### Surviving Structure
- `PhiFull10.lean` built internally in Lean, with passive base checks proved
- generic path frameworks:
  - `TpPathProjection`
  - `TpPathBiProjection`
  - `tpPathProjection_reachable`
  - `tpBiProjection_phiFull_eq`
  - `tpBiProjection_comparison`
- deletion arithmetic:
  - `liftIdx` commutation
  - `fc_deletion_formula`
- projected-step plumbing:
  - `projected_triple_eq`
  - `projected_position_type_eq`
  - `projected_privileged`
  - `projected_tpPreserving`

### Reformulations
The proof now has the correct layered shape:

```text
shared deletion/path infrastructure
        + branch-specific local simulation/pruning
```

LOAD-BEARING ASSESSMENT:
Yes. This is the correct proof-engineering decomposition going forward.

### Concrete Artifacts

TOOLS:
- `PhiFull10.lean`
- deletion transport infrastructure in `CPhiDelete.lean`

STRUCTURAL RESULTS:
- `H_nocopy_subset_G617` proved by native finite check
- no-copy deep steps always copy LEFT
- no-copy deep steps strictly decrease `fc`
- generic badness preservation under deletion is false

### What Would Unblock This
- a correct passive-specific badness theorem
- branch-specific no-copy seam handling
- a branch-specific pruning theorem replacing false generic projection

### Key Parameters
- no-copy period-2 and period-3 strips
- deep deletion sites `k`
- seam-adjacent vs non-seam movers

### Open Questions
- can the passive branch close independently with a finite key?
- where does the shared path transport infrastructure stop helping and branch-specific arguments begin?

---

## Exploration 13

### Strategy
Refine the passive no-copy branch into period-2 and period-3 cases, replace
false generic theorems by branch-specific local theorems, and isolate seam
pruning.

### Outcome
PARTIAL SUCCESS

### Failure Constraint
The passive branch still resists closure, but the remaining obstacles are now
small and explicit:

- period-2 comparison/pruning theorem
- period-3 far-seam pruning theorem

The false right-boundary edge case `k = n - 5` was isolated and removed from the
general theorem, with `n = 10` handled by the base case.

### What This Rules Out
It rules out:
- generic seam step projection for no-copy deletion
- generic seam pruning including the right-boundary edge case
- the idea that passive closure reduces to a single one-line induction

### Surviving Structure
- `goodCycle_has_deep_copyPair`
- `noDeepCopyPair_implies_not_goodCycle`
- `period2_deletion_creates_copyPair`
- `cycling_deletion_preserves_noCopy`
- `seamAvoidingReachable` and seam-avoiding transport infrastructure
- `seam_pruning_period3` reduced to the hard direction `seam_pruning_le`
- later, `seam_pruning_le` further reduced to:
  - `seam_pruning_le_far`
  - false edge case documented and excluded

### Reformulations
The passive branch is now correctly represented as:

```text
period-2 no-copy comparison transfer
period-3 no-copy far-seam pruning
base case at n = 10
recombination
```

LOAD-BEARING ASSESSMENT:
Yes. This is the correct endgame form of the passive branch.

### Concrete Artifacts

COMPUTED EXAMPLES:
- false edge case `k = n - 5` produced 80 counterexamples at `n = 10`
- far-seam period-3 case remained empirically valid

STRUCTURAL RESULTS:
- no-copy deep steps copy LEFT
- right-seam no-copy local simulation is false
- seam-avoiding projection is the right replacement

TOOLS:
- branch-specific seam-avoiding step/path projection lemmas

### What Would Unblock This
- period-2 comparison/pruning theorem
- period-3 far-seam pruning theorem
- later, the active/copy-pair transport branch

### Key Parameters
- far-seam condition `k + 6 ≤ n`
- period-2 versus period-3 strip type
- base case `n = 10`

### Open Questions
- can period-2 be proved by pairwise comparison transfer rather than absolute pruning?
- can far-seam period-3 pruning be reduced to a bounded local window theorem?

---

## Synthesis after exploration 13

The UB pursuit has now stabilized around:

1. **Shared deletion/path infrastructure**
   largely built and reused

2. **Passive branch**
   split into two theorem-sized problems:
   - period-2 comparison/pruning
   - period-3 far-seam pruning

3. **Active branch**
   still expected to be the longer final road

This is not endless case-bashing. Each false generic theorem has been replaced
by a smaller, more accurate local theorem, and the remaining branches are now
theorem-sized rather than architecture-sized.

---

## Exploration 14

### Strategy
Push the passive period-3 branch through a seam-pruning theorem, first via
global reset/replay invariants, then via local seam-step pruning, then via
strong induction / path pruning.

### Outcome
FAILED (current theorem shape), with substantial structural gains

### Failure Constraint
Several increasingly plausible pruning strategies were shown false or inadequate:

- global `resetSeam` dominance is false
- direct one-step seam deletion / replay is false
- boundary-only replay is false
- full non-seam replay is false
- SCC-free / reachable-set-size induction is false because seam edges occur
  inside nontrivial SCCs in the far period-3 no-copy TP graph

The remaining true theorem is no longer a path-pruning statement in the naive
sense. It appears to require an SCC-level or max-attainment theorem.

### What This Rules Out
It rules out the whole family of proofs that try to remove seam steps from a TP
path by deterministic replay or prefix surgery.

More specifically, it rules out:

- proving `seam_pruning_le_far` by deleting or resetting seam steps directly
- proving it by induction on path length or reachable-set size
- assuming seam steps lie outside SCCs

### Surviving Structure
- period-3 passive branch is still computationally true at tested sizes
- the far-seam restriction `k + 6 ≤ n` is the correct theorem domain
- seam steps have bounded local effect
- no-copy deep steps always copy LEFT
- seam-step cascade length is 1
- all generic deletion/path transport plumbing is much better than before

### Reformulations
The period-3 passive theorem must now be viewed as an **SCC-max theorem** or a
max-attainment theorem, not as a path-pruning theorem.

Best current formulation candidate:

```text
For every SCC in the far period-3 no-copy TP graph,
the maximum `fc` on that SCC is attained at a seam-avoiding state.
```

If true, this would imply the desired seam-pruning comparison theorem.

LOAD-BEARING ASSESSMENT:
Yes. This is a genuine theorem-shape pivot, not a local proof repair.

### Concrete Artifacts

COMPUTED EXAMPLES:
- 13,992 violations to `resetSeam_fc_ge`
- all 8 no-copy right-seam local windows falsify the generic seam projection
  theorem
- 26,000+ within-SCC seam edges at `n = 11` in the far period-3 no-copy TP
  graph
- computational evidence still supports the overall far-seam theorem at
  `n = 10, 11, 12`

STRUCTURAL RESULTS:
- `deleteConfig_bad_preserved` is false generically
- passive badness must come from branch-specific no-copy incompatibility with the
  good cycle
- `seam_pruning_period3` / `seam_pruning_le` were restructured several times
  until the real failure mode (SCC seam edges) was exposed

TOOLS:
- seam-avoiding transport infrastructure
- `PhiFull10` base object
- local seam-window computational checks

### What Would Unblock This
- either an SCC-max theorem for the far period-3 no-copy TP graph
- or a new local replacement theorem at the level of SCCs / seam blocks rather
  than seam steps

### Key Parameters
- far-seam regime `k + 6 ≤ n`
- no-copy period-3 strip
- SCC structure of the TP graph

### Open Questions
- does every SCC in the far period-3 no-copy TP graph contain an SA state of
  maximal `fc`?
- if yes, can that be proved structurally rather than by finite check?

---

## Synthesis after exploration 14

The UB pursuit is still converging, but the nature of the remaining work has
shifted again.

Previously the passive branch looked like it might collapse to local path
pruning. That is now false. The remaining period-3 theorem is more global than
expected: seam steps live inside SCCs, so max-attainment rather than simple path
rewriting is the likely correct proof language.

Current picture:

1. **Shared transport infrastructure**
   largely built

2. **Passive branch**
   - period-2 comparison/pruning theorem still open
   - period-3 far-seam branch likely needs an SCC-max theorem

3. **Active branch**
   still waiting, likely still the longest road

This is the first point in the UB search where real concern is warranted.
The proof is not lost, but one passive branch theorem has become more global
than expected. Future progress should be judged by whether that theorem can be
recast into a sharp SCC-max statement, not by raw sorry count.

---

## Exploration 15

### Strategy
Continue refining the passive period-3 theorem, first by trying SCC-max
attainment, then by discovering a simpler “all-distinct constructive route,” and
finally by formalizing seam pruning around local reset/replay and seam-avoiding
paths.

### Outcome
FAILED (current passive period-3 theorem shape), with strong residue

### Failure Constraint
The passive period-3 branch did not just resist proof; its current theorem shape
was shown false.

Concrete failure:

- `seam_pruning_period3` as stated is false on genuine no-copy/cycling examples
  near the right boundary
- the edge case `k = n - 5` is not a proof nuisance but a real mathematical
  obstruction
- later, even the far-seam route became unstable because the current
  path-pruning / all-distinct / seam-reset proof shapes were not the right ones

In particular:

- `hallInterior` was not cheaply derivable and was not the right simplification
- `resetSeam`-based dominance was false
- deterministic replay (boundary-only or full non-seam) was false
- seam pruning by local step deletion was false
- SCC-max theorem was itself false: some SCC maxima are achieved only at non-SA
  states
- the surviving empirical fact is weaker:
  **there exists at least one SA-reachable global maximizer**, but not one in
  every SCC

### What This Rules Out
This rules out the whole family of passive-period3 theorem shapes based on:

- seam-pruning as currently stated
- SCC-wise SA-max attainment
- all-distinct constructive closure under the current hypotheses
- adding `hallInterior` as a supposedly cheap hypothesis

More generally, it rules out assuming the passive branch is merely an easier
version of the active branch.

### Surviving Structure
- `PhiFull10` base object is fully internalized in Lean
- `H_nocopy` finite object (size 335 under exact CΦ semantics) is sound
- deletion/path arithmetic and projection infrastructure remain valuable
- many local no-copy facts are proved:
  - deep no-copy T_mid steps copy LEFT
  - deep no-copy T_mid steps strictly decrease `fc`
  - seam-step cascade length is 1
- the passive branch has a large amount of true local residue even though its
  current global theorem shape failed

### Reformulations
The main reformulation from this exploration is negative:

```text
The passive branch is not "almost done with one more local theorem."
It needs a theorem-shape replan.
```

LOAD-BEARING ASSESSMENT:
Yes. This is a major correction to the UB endgame map.

### Concrete Artifacts

COMPUTED EXAMPLES:
- counterexample to the current passive period-3 seam-pruning statement:
  `dst = (0,0,0,1,0,2,0,1,0,1,1)` at `n = 11`
- 91% of relevant configs fail `hallInterior`
- every global `Φ`-achiever still has at least one SA-reachable achiever at
  tested sizes, but this no longer yields a usable local proof route under the
  current formulations

STRUCTURAL RESULTS:
- `deleteConfig_bad_preserved` is false
- generic right-seam projection is false
- seam-pruning period-3 is false in the edge case regime
- SCC-max theorem is false

TOOLS:
- `PhiFull10.lean`
- `CPhiDelete.lean`
- passive finite objects and many local no-copy lemmas remain available

### What Would Unblock This
- a corrected theorem shape for the passive branch
- or a decision to abandon the passive/active split and reunify the proof under
  the shared transport problem

### Key Parameters
- `n = 10` base
- no-copy period-2 vs period-3
- right-boundary edge regime `k = n - 5`
- SCC structure of the TP graph

### Open Questions
- what is the smallest corrected passive theorem that survives the counterexample?
- is the passive branch still meaningfully simpler than the active branch?
- should the proof abandon the passive/active split and return to a single
  shared transport theorem?

---

## Synthesis after exploration 15

The UB pursuit is still alive, but one important belief should be retired:

```text
The passive branch is not simply "one theorem away."
```

That was true for several local lemmas, but false at the theorem-shape level.

Current sober picture:

1. **Shared transport/deletion infrastructure**
   has been built to a useful level and is not wasted

2. **Passive branch**
   has strong local residue and a finite base, but its current global theorem
   shape has failed and needs a theorem-shape replan

3. **Active branch**
   remains unclosed and may ultimately be the cleaner main road again

This is the first point where the project should prefer a deliberate theorem
replan over continued local patching. Progress from here should be measured by
whether a corrected passive theorem shape emerges, or whether the passive branch
is intentionally abandoned in favor of a unified transport problem.

---

## Latest active structural finding

This is now load-bearing knowledge for the UB route:

```text
For broad active boundary-changing TP-preserving steps:
  non-617  =>  PhiFull strictly drops

But the drop is NOT explained by immediate TP-component change.
```

What was checked:

- bucket scans at `n = 10..15` showed:
  - broad active theorem: false
  - no-drop-filtered active theorem: true
- boundary-successor analysis at `n = 11` showed:
  - many abstract non-617 boundary successor buckets exist
  - realized active non-617 buckets always carry strictly positive `PhiFull` drop
- decomposition of those broad active non-617 steps showed:
  - `ΔExp2Count = 0`
  - `ΔInt21 = 0`
  - `ΔExp2Weight = 0`
  - immediate `Δfc` varies over `{-2,-1,0,+1}`
  - nevertheless `PhiFull(src) - PhiFull(dst) ∈ {1,2,3,4}`

Interpretation:

1. The active non-617 bridge is NOT a local TP-invariant argument.
2. It is NOT a simple immediate-`fc` monotonicity argument either.
3. The mechanism is a future-reachability statement:
   non-617 active boundary steps land in states with strictly worse future
   TP-reachable `fc` maxima.

Consequence:

- any successful structural proof of the active bridge must reason about the
  future TP graph (or an equivalent finite summary of it)
- trying to prove the active bridge from boundary data or immediate TP deltas
  alone is the wrong theorem shape
- this explains why the purely boundary finite-bucket route stalled even after
  the bucket classification was identified

---

## Assessment of `active_farProjectedMaximizer_exists_raw`

Current statement:

- choose one maximizing terminal `u`
- choose one deep site `k`
- require:
  - `u` has a deep copy-pair at `k`
  - the path `w0.dst →* u` is delete-projectable at `k`
  - the deleted start `deleteConfig ... w0.dst` is still bad
  - and `k` is far enough (`k + 5 ≤ n`) to avoid the known right-seam blocker

Assessment:

```text
This is still a real theorem-shape / discovery theorem, not just proof engineering.
```

Why:

1. It asks for simultaneous existence of:
   - a maximizer
   - a safe deep site
   - a delete-projectable maximizing path

2. Broad nearby variants are already known false:
   - arbitrary fixed-site transport: false
   - broad active existential transport: false

3. The theorem is therefore using the exact witness-class hypotheses in a
   delicate way, not just repackaging already-proved infrastructure.

What *is* already engineering:

- `cup2PhiFull_attained`
- packaging into `ActiveSafeProjectedMaximizer`
- downstream target/source transport consequences once the raw theorem exists

Bottom line:

- `active_farProjectedMaximizer_exists_raw` is not the next bottom-up closure
  target while local theorem holes remain
- it should stay parked until the lower local obligations are either closed or
  intentionally bypassed by a base-window argument

---

## Session summary: computational base abort, active structural diagnosis, local closure status

### 1. What was tried

This session explored three main directions:

1. **Computational finite base via `native_decide`**
   - `BridgeTest` / `cphi_bridge_n9_full`
   - `PhiFull10` active base theorem
   - minimal encoded `PhiFull11` feasibility file

2. **Structural active bridge**
   - broad active boundary theorem
   - then no-drop-filtered active theorem
   - bucket classification by:
     - boundary mover
     - deep copy-pair site / site class
     - seam-local value

3. **Local transport closure**
   - `source_transport_step_lift_offsite`
   - `source_transport_step_lift_seam`
   - passive branch of `noDropTransport`

### 2. What failed

#### Computational route

- `BridgeTest` became unusable as an active dependency:
  the `n = 9` `native_decide` build path ran for many hours without verifying
  in-session
- `PhiFull10` / `PhiFull11` active computational builds did not verify quickly
  enough to justify committing the whole finite base to that route
- conclusion:
  raw per-`n` `native_decide` is not a reliable closure plan at the current
  size scale

#### Broad active structural theorems

- the broad active theorem is false
- the broad purely boundary theorem is false
- a pure boundary-state decidable predicate cannot capture `hnodrop`, because
  `PhiFull` is not boundary-determined

### 3. What was discovered

#### A. No-drop active buckets are uniformly in `617`

Bucket scans established:

- `n = 10`: no-drop active buckets ⊂ `617`
- `n = 11..15`: no-drop active buckets ⊂ `617`

This strongly suggests an `n`-independent active theorem shape is true.

#### B. Broad active non-617 steps always drop `PhiFull`

For broad active boundary-changing TP-preserving bad steps:

```text
non-617  =>  PhiFull strictly drops
```

This was observed uniformly in the discovery scripts.

#### C. The `PhiFull` drop is a future-reachability effect

Decomposition of broad active non-617 steps showed:

- `ΔExp2Count = 0`
- `ΔInt21 = 0`
- `ΔExp2Weight = 0`
- immediate `Δfc ∈ {-2,-1,0,+1}`
- but `PhiFull(src) - PhiFull(dst) ∈ {1,2,3,4}`

So the drop is **not** explained by the immediate TP components.
It is a future TP-reachability / future-max-`fc` phenomenon.

#### D. Seam mismatch is repaired by copy-pair orientation

Exact computational check:

- left seam (`p' = k - 1`) matches the obvious one-step lift iff `c[k] = c[k+1]`
- right seam (`p' = k`) matches the obvious one-step lift iff `c[k] = c[k-1]`

So the seam issue is not generic chaos: it is controlled by copy-pair
orientation.

#### E. But the source-side architectural gap remains

The active chosen deletion site `k` is chosen because the **terminal maximizer**
has a copy-pair there, not because the **source** does.

Therefore:

- seam repair by copy orientation does **not** automatically close generic
  `source_transport_step_lift_seam`
- the current `source_transport` call chain still has a real architectural gap
  at the source side

### 4. Current `CPhiDelete.lean` sorry inventory

Current declaration-level picture:

1. `source_transport_step_lift_seam`
   - lowest local open theorem
   - only two branch holes remain
   - offsite theorem is fully written

2. `period2_noCopy_nIndep_core`
   - still a whole-theorem sorry
   - known hard from earlier explorations

3. `period3_noCopy_nIndep_transfer_core`
   - still a whole-theorem sorry
   - known hard / theorem-shape sensitive

4. `active_noDrop_subset_G617`
   - theorem statement written
   - `n = 10` slice closed
   - `n > 10` split into 18 mover/site branches
   - compressed finite carrier defined
   - but no canonical finite realizability theorem yet, so the branches are not
     decidable in Lean yet

5. `active_farProjectedMaximizer_exists_raw`
   - theorem-shape / discovery theorem
   - intentionally parked

6. active branch of `noDropTransport`
   - downstream witness assembly still open

7. `no_noDropWitness_9`
   - temporarily re-parked after removing the `BridgeTest` import

8. `no_noDropWitness_10_15`
   - still open
   - computational route not yet validated enough to close it

Raw `grep -n sorry` count is much larger because:

- `active_noDrop_subset_G617` is explicitly split into its 18 local branches

### 5. Recommended approach for the next session

#### A. Do not return to the abandoned routes

- do **not** resurrect `BridgeTest` as a live dependency
- do **not** try a purely boundary-only decision theorem for active no-drop
- do **not** reopen the passive period-2 / period-3 theorem-shape route unless
  there is an explicit new theorem shape

#### B. Closest genuinely local closure target

- `source_transport_step_lift_seam`

This is still the only bottom-level local theorem with a plausible direct
mechanism (copy-orientation or a specialized two-step lift), even though the
current generic source-side architecture prevents an immediate active reuse.

#### C. Most important theorem-shape fact

- `active_farProjectedMaximizer_exists_raw` is still discovery, not engineering

It should stay parked while lower local obligations remain.

#### D. Best high-level working view

The project is now split clearly:

1. **Local closure / plumbing**
   - offsite transport: essentially done
   - seam transport: real local gap
   - passive branch of `noDropTransport`: done

2. **Future-structure bridge**
   - active non-617 implies `PhiFull` drop
   - mechanism is future TP reachability, not local TP delta
   - any final proof has to reflect that

This should be treated as the new baseline context for future sessions.

---

## Theorem-shape reassessment for `active_noDrop_subset_G617`

The current theorem

```lean
active_noDrop_subset_G617 :
  bad + TP-preserving + boundary-changing + no-drop + active -> sixTupleEdge
```

is probably not the cleanest final shape.

Reason:

- the actual discovered mechanism is:

```text
broad active boundary-changing TP-preserving step
  ∧ not-617
  => PhiFull strictly drops
```

- the no-drop theorem is then just the immediate corollary:

```text
if PhiFull does not drop, the step must be in 617
```

So the structurally natural active theorem shape is the **contrapositive bridge**
statement:

```lean
theorem active_boundary_bridge
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n) (hn10 : 10 ≤ n)
    {src dst : Config (cup2Spec n hn4)}
    (hbad : cup2BadStepFwd n hn4 src dst)
    (htp : cup2TpInvariant n hn4 dst = cup2TpInvariant n hn4 src)
    (hbdry : cup2BoundaryState n hn4 hn9 dst ≠ cup2BoundaryState n hn4 hn9 src)
    (hactive : ¬ noDeepCopyPair n hn4 hn10 dst) :
    sixTupleEdge (cup2BoundaryState n hn4 hn9 dst)
                 (cup2BoundaryState n hn4 hn9 src) ∨
    cup2PhiFull n hn4 dst < cup2PhiFull n hn4 src
```

Then:

```lean
active_noDrop_subset_G617
```

should be derived from it by contradiction with `hnodrop`.

Why this shape is cleaner:

1. It matches the actual empirical separation.
2. It removes the awkward burden of proving a no-drop theorem directly.
3. It aligns with the original `cphi_bridge` semantics:
   boundary change implies `617` or `PhiFull` drop.
4. It avoids making the active theorem look more special than it really is.

Recommended refactor:

- keep the bucket classification/compression theorem as a separate local tool
- stop trying to prove `active_noDrop_subset_G617` directly from the bucket
  branches
- instead aim the 18 active branches at the stronger bridge theorem above
- recover `active_noDrop_subset_G617` as the downstream corollary

### Active bridge wall: approaches tried and ruled out

The following approaches were explicitly explored and should be treated as
ruled out unless a genuinely new idea appears:

1. **Broad active theorem**
   - false

2. **Pure boundary-state decidable theorem**
   - false in shape
   - `PhiFull` / no-drop is not boundary-determined

3. **Exact bucket-local Phi drop**
   - false
   - even the full active bucket key does not determine the exact drop amount

4. **Immediate local measure proof**
   - fails
   - for broad active non-617 steps:
     - `ΔExp2Count = 0`
     - `ΔInt21 = 0`
     - `ΔExp2Weight = 0`
     - immediate `Δfc` is mixed
     - condensation-rank / SCC-subrank are also mixed

5. **Seam repaired by choosing source copy-pair site**
   - false
   - there are no-drop active steps where `dst` has a deep copy-pair but `src`
     does not

6. **Use `ConstLayerDAG.cphi_bridge` infrastructure directly**
   - circular
   - the 617-edge DAG/rank machinery consumes the bridge theorem; it does not
     prove the bridge theorem for free

Current best understanding:

- the remaining active theorem is fundamentally a future-reachability / future
  max-`fc` statement
- any successful proof must encode that future structure somewhere, either:
  - directly, or
  - via a finite summary that is rich enough to recover strict positivity of
    the `PhiFull` drop

---

## Session-end leaf inventory (structural state)

After the cleanup / refactor passes, the genuinely mathematical leaves are:

1. `deleteConfig_cycleConfig_eq`
2. `converse_tpPreserving_offsite`
3. `source_transport_step_lift_seam_left`
4. `source_transport_step_lift_seam_right`
5. `period2_noCopy_nIndep_core`
6. `period3_noCopy_nIndep_transfer_core`
7. `active_bridge_alternative`
8. `active_farProjectedMaximizer_exists_raw`

Downstream theorems such as:

- `source_transport`
- `active_safeProjectedMaximizer_exists_of_raw`
- `noDropTransport_active_nonempty`
- `no_noDropWitness_9`
- `no_noDropWitness_11_15`

are not the real mathematical wall. They are consequences or packaging around
the eight leaves above.

### 1. `deleteConfig_cycleConfig_eq`

Mathematical content:

- explicit statement that deleting a deep site from a good-cycle config yields
  another good-cycle config at size `n - 1` after reindexing cycle time

What was tried:

- full extensional equality proof by case split on `j < k`
- arithmetic cleanup with `split_ifs` / `omega`

What failed:

- the tactic-heavy proof became fragile and caused build errors

Honest next step:

- prove the weaker existential cycle-config image first
- or give a shorter direct proof specialized to membership in the good cycle
  rather than exact time reindexing

### 2. `converse_tpPreserving_offsite`

Mathematical content:

- deleted offsite TP-preservation at size `n - 1`
  implies original offsite TP-preservation at size `n`

What was tried:

- restore the original proof shape from `projected_triple_eq`
- fully prove `Exp2` and `Int21`
- attempt the `Exp2Weight` branch by rewriting the deleted weight equality
  back to the original system

What failed:

- the `Exp2Weight` branch still had rewrite/type mismatches
- restoring the partial proof broke the build again

Honest next step:

- reprove it from scratch with only:
  - triple equality
  - output equality
  - the local `Exp2Weight` formula
- keep the proof short and avoid carrying the old partial proof text

### 3–4. `source_transport_step_lift_seam_left/right`

Mathematical content:

- lift a deleted seam TP step back to size `n`

What was tried:

- direct one-step lift (fails in general)
- computational seam-copy analysis

What was discovered:

- left seam works iff `c[k] = c[k+1]`
- right seam works iff `c[k] = c[k-1]`

What failed:

- the current generic source-side theorem does not know the required copy
  orientation at the chosen `k`
- choosing `k` as a source copy-pair site is false in general

Honest next step:

- either redesign source-side transport around a site chosen from the source
- or prove a two-step seam lift
- do not expect the current generic seam statement to fall by local rewriting
  alone

### 5. `period2_noCopy_nIndep_core`

Mathematical content:

- no-copy, period-2, no-drop comparison is boundary-determined / in `H_nocopy`

What was tried:

- boundary mover localization
- explicit period-2 strip equality
- explicit shared-deep-strip argument

What failed:

- the actual comparison transfer to size `10` remained the whole theorem
- this was already known hard from earlier explorations

Honest next step:

- do not reopen without a theorem-shape replan
- if revisited, aim directly at a compressed finite comparison theorem

### 6. `period3_noCopy_nIndep_transfer_core`

Mathematical content:

- no-copy, period-3, no-drop comparison transfer

What was tried:

- wrapper narrowing
- transfer-core isolation

What failed:

- same theorem-shape wall as before; the core remained unresolved

Honest next step:

- parked until a new theorem shape exists
- not a near-term local cleanup target

### 7. `active_bridge_alternative`

Mathematical content:

```text
active + boundary-changing + TP-preserving
  -> sixTupleEdge OR PhiFull strictly drops
```

What was tried:

- broad active theorem
- no-drop direct theorem
- boundary-only finite bucket proof
- exact bucket-local `PhiFull` drop
- local measure explanations (`Δfc`, TP triple, boundary rank)

What failed:

- broad active theorem is false
- boundary-only theorem is false
- exact drop is not bucket-determined
- no local measure explains the drop

What was discovered:

- non-617 active steps always drop `PhiFull`
- the drop is a future-reachability / future max-`fc` effect

Honest next step:

- this is the real active bridge theorem
- any proof must encode future TP structure, not just local boundary data

### 8. `active_farProjectedMaximizer_exists_raw`

Mathematical content:

- choose one maximizing terminal `u`
- choose one safe deep site `k`
- choose one delete-projectable maximizing path at that same `k`

What was tried:

- sharpening and packaging
- isolating downstream uses

What failed:

- nearby stronger variants are false
- the theorem remains a real existence/discovery statement

Honest next step:

- keep parked until lower local transport leaves are resolved or bypassed
- do not mistake it for proof engineering

## Cascade map

The main dependency cascades are:

- `deleteConfig_cycleConfig_eq`
  -> `deleteConfig_mem_goodCycle_of_mem_goodCycle`
  -> source-side deleted badness arguments

- `converse_tpPreserving_offsite`
  -> `source_transport_step_lift_offsite`
  -> `source_transport`

- `source_transport_step_lift_seam_left/right`
  -> `source_transport_step_lift_seam`
  -> `source_transport_step_lift`
  -> `source_transport_lift`
  -> `source_transport`

- `active_bridge_alternative`
  -> `active_noDrop_subset_G617`
  -> any active finite-base contradiction using no-drop

- `active_farProjectedMaximizer_exists_raw`
  -> `active_safeProjectedMaximizer_exists_of_raw`
  -> `active_safeProjectedMaximizer_exists`
  -> `noDropTransport_activeCase`
  -> `noDropTransport_eq_of_activeWitness`

## Anti-patterns now known

1. **`native_decide` at these sizes is a trap**
   - BridgeTest-style monoliths are infeasible
   - even split computational files are unreliable enough to avoid as core plan

2. **Boundary-only `PhiFull` arguments are false**
   - no-drop is not boundary-determined

3. **Exact bucket-local `PhiFull` drop is false**
   - only strict positivity appears bucket-local

4. **Immediate local measures do not explain active non-617**
   - TP triple unchanged
   - immediate `fc` mixed
   - boundary-rank data mixed

5. **The source-side seam problem is architectural**
   - not a missing local lemma around the current chosen `k`

## Session Update: Offsite TP Refactor

Verified state:

- `lake build LeanMn.Convergence.CPhiDelete` passes
- `converse_exp2_offsite` is proved
- `converse_int21_offsite` is proved
- `converse_tpPreserving_offsite` is now a sorry-free assembly theorem
- only `converse_weight_offsite` remains open in that block

What was changed:

- the old monolithic `converse_tpPreserving_offsite` proof was refactored into:
  - `converse_exp2_offsite`
  - `converse_int21_offsite`
  - `converse_weight_offsite`
  - plus a thin assembly theorem

This was a real improvement even though the weight component is still open, because:

- Exp2 and Int21 are now isolated and closed
- the remaining TP-converse blockage is exactly one local weight lemma

### Exact residual from `converse_weight_offsite`

The `p < k`, `p = 0` branch was reopened with a `convert` experiment.
The first residual subgoal was:

```lean
⊢ (if 2 ≤ n - 1 ∧ n - 1 + 2 < n ∧ ↑(c (left p)) = 2 ∧
        ¬ cup2OutVal n p ↑(c (left p)) ↑(c p) ↑(c (right p)) = 2
    then n - 1 else 0)
  =
  (if 2 ≤ n - 1 ∧ n - 1 + 2 < n ∧ ↑(c (left p)) = 2 ∧
        ¬ cup2OutVal n p ↑(c (left p)) ↑(c p) ↑(c (right p)) = 2
    then n - 1 - 1 else 0)
```

Interpretation:

- this is exactly the top-index mismatch in the `p = 0` case
- the only difference is `n - 1` vs `n - 2`
- the guard contains `n - 1 + 2 < n`, which is impossible

What was tried on that residual:

- `have h_imp : ¬ (n - 1 + 2 < n) := by omega`
- `simp only [h_imp, and_false, if_false]`
- `split_ifs`

What failed:

- after `convert`, Lean still leaves a second residual subgoal
- at that point the goal is no longer literally an `if`, so `split_ifs` does not apply
- the second residual was only partially extracted from the build log; the build showed:
  - one unsolved goal at the residual above
  - one further branch where `simp` made no progress

Honest next step:

- re-open only `converse_weight_offsite`
- keep the three local branches split:
  - `p < k, p = 0`
  - `p < k, p > 0`
  - `p > k`
- close the `p = 0` branch by proving both sides are `0` directly, not by `convert`
- for `p > 0`, use `localExp2Weight_congr`
- for `p > k`, use the already-proved `converse_exp2_offsite` count equality plus coefficient arithmetic

### Current Lean wall: `converse_weight_offsite`

Status:

- `converse_exp2_offsite`: proved
- `converse_int21_offsite`: proved
- `converse_tpPreserving_offsite`: sorry-free assembly
- only `converse_weight_offsite` remains open

What was tried after the factorization:

- direct projected-weight proof with:
  - `projected_triple_eq`
  - `projected_position_type_eq`
  - `exp2BitVal_proj`
  - `converse_exp2_offsite` for the local count equality
- `convert` on the `p < k, p = 0` branch
- explicit impossible-guard lemma
- `split_ifs`

Exact residual seen in the `p = 0` branch:

```lean
⊢ (if 2 ≤ n - 1 ∧ n - 1 + 2 < n ∧ ↑(c (left p)) = 2 ∧
        ¬ cup2OutVal n p ↑(c (left p)) ↑(c p) ↑(c (right p)) = 2
    then n - 1 else 0)
  =
  (if 2 ≤ n - 1 ∧ n - 1 + 2 < n ∧ ↑(c (left p)) = 2 ∧
        ¬ cup2OutVal n p ↑(c (left p)) ↑(c p) ↑(c (right p)) = 2
    then n - 1 - 1 else 0)
```

What failed:

- `have h_imp : ¬ (n - 1 + 2 < n) := by omega`
- `simp only [h_imp, and_false, if_false]`
- `split_ifs`

Reason:

- after `convert`, Lean still leaves a second residual subgoal
- at that point the residual is no longer literally an `if`, so `split_ifs` does not apply

## Current Lean wall: `deleteCycleVal_eq_phase1`

Mathematical target:

- under `t < n`,
  prove

```lean
cup2CycleVal n t (if j < k then j else j + 1)
=
cup2CycleVal (n - 1) (deleteCycleTime n k t) j
```

using the phase-1 formula

```lean
cup2CycleVal n t j = if j < t then 1 else 0
```

What was tried:

- direct proof with:
  - `rw [cup2CycleVal_phase1 ...]` on both sides
  - split on `t ≤ k`
  - split on `j < k`
  - `omega` on the resulting arithmetic branches

What failed:

- all 4 arithmetic branches remained open
- the concrete failing lines in the attempted restore were around:
  - `585`
  - `589`
  - `592`
  - `596`

Shape of the remaining goals:

- branchwise comparisons of

```lean
if (if j < k then j else j + 1) < t then 1 else 0
```

against

```lean
if j < deleteCycleTime n k t then 1 else 0
```

with the corresponding branch hypotheses (`t ≤ k` / `¬ t ≤ k`, `j < k` / `¬ j < k`)

Honest next step:

- do not reopen the full cycle theorem
- isolate one branch at a time and prove the resulting `if`-comparison by
  explicit `split_ifs` or direct monotonicity lemmas, not `omega` alone

## Comprehensive Session Handoff

Verified end state:

- `lake build LeanMn.Convergence.CPhiDelete` passes
- the current worktree is back in a clean buildable state
- `BridgeTest` / `PhiFull10` computational routes remain out of the critical path

### Closures achieved in this session

1. `active_safeProjectedMaximizer_exists_of_raw`

- status: proved
- file: `CPhiDelete.lean`
- proof shape:
  - unpack `active_farProjectedMaximizer_exists_raw`
  - obtain deleted witness-step compatibility via
    `deletedWitnessStepCompatible_of_farDeepSite`
  - package everything with `activeSafeProjectedMaximizer_of_raw`

2. `converse_exp2_offsite`

- status: proved
- file: `CPhiDelete.lean`
- proof shape:
  - take `hexp2'` from `cup2TpPreserving_local_eqs`
  - rewrite the deleted local equality to the original `c`-values using
    `projected_triple_eq`
  - transport the output value using `projected_position_type_eq`
  - compose with `localExp2After_proj` / `localExp2Before_proj`

3. `converse_int21_offsite`

- status: proved
- file: `CPhiDelete.lean`
- proof shape is exactly parallel to `converse_exp2_offsite`

4. `converse_tpPreserving_offsite`

- status: proved as an assembly theorem
- file: `CPhiDelete.lean`
- now just combines:
  - `converse_exp2_offsite`
  - `converse_int21_offsite`
  - `converse_weight_offsite`

### Major theorem-shape improvement

The old monolithic offsite TP converse theorem is no longer one opaque wall.
It is now factored into three local components:

- `converse_exp2_offsite`
- `converse_int21_offsite`
- `converse_weight_offsite`

This was an important structural win even though the weight component remains open.

## What was tried and failed

### A. `converse_weight_offsite`

This was the main local proof target after factoring the TP converse theorem.

Approaches tried:

1. Monolithic rewrite style
- direct `rw [hL, hS, hR, hout] at hweight'`
- failed repeatedly on term matching / projected mover proof-term consistency

2. Exact `(by omega)` proof-term alignment
- rewrote the theorem to use the exact same `projMover n k (by omega) p hpk`
  term everywhere
- fixed some mismatches, but the weight branch still did not close

3. `calc` / transitivity style
- successfully used for `Exp2` and `Int21`
- for weight, still reduced to index/coefficient mismatch

4. Direct projected-weight proof with coefficient shift
- used:
  - `projected_triple_eq`
  - `projected_position_type_eq`
  - `exp2BitVal_proj`
  - `converse_exp2_offsite` as the count equality
- mathematically correct, but Lean got stuck in local arithmetic normalization

5. `convert` on the `p < k`, `p = 0` branch
- this exposed the residual clearly
- but the residual was not discharged by either:
  - `have h_imp : ¬ (n - 1 + 2 < n) := by omega; simp only [...]`
  - or `split_ifs`

6. `split_ifs`
- after `convert`, the residual was no longer literally an `if`
- `split_ifs` therefore failed at that stage

7. Attempted split into below/above sub-lemmas
- tried splitting `converse_weight_offsite` into:
  - a `p < k` lemma
  - a `p > k` lemma
- the refactor itself was not worth keeping once it stopped compiling cleanly

Current exact residual captured:

```lean
⊢ (if 2 ≤ n - 1 ∧ n - 1 + 2 < n ∧ ↑(c (left p)) = 2 ∧
        ¬ cup2OutVal n p ↑(c (left p)) ↑(c p) ↑(c (right p)) = 2
    then n - 1 else 0)
  =
  (if 2 ≤ n - 1 ∧ n - 1 + 2 < n ∧ ↑(c (left p)) = 2 ∧
        ¬ cup2OutVal n p ↑(c (left p)) ↑(c p) ↑(c (right p)) = 2
    then n - 1 - 1 else 0)
```

Interpretation:

- this is the `p < k`, `p = 0` top-index case
- the mismatch is exactly `n - 1` versus `n - 2`
- the guard contains `n - 1 + 2 < n`, which is impossible

But:

- after `convert`, Lean still produced another residual subgoal
- one branch specifically reported: `simp made no progress`

Conclusion:

- the mathematics is local and correct
- the remaining issue is Lean normalization in the weight branch, not theorem shape

### B. `deleteConfig_cycleConfig_eq`

This remains the main cycle-deletion leaf.

Approaches tried:

1. Full extensional proof with branch-by-branch arithmetic
- `funext j`
- split on `j < k`
- unfold `deleteCycleTime` / `cup2CycleVal`
- repeatedly broke on arithmetic proof state / elaboration

2. Four phase helper theorems
- `deleteCycleVal_eq_phase1`
- `deleteCycleVal_eq_phase2`
- `deleteCycleVal_eq_phase3_boundary`
- `deleteCycleVal_eq_phase3`
- good theorem shape, but repeated `omega` failures in the current file context

3. Direct one-shot proof
- witness:
  `t' := deleteCycleTime n k t.1`
- then:
  `funext j; simp [deleteConfig, cup2CycleConfig, cup2CycleVal, deleteCycleTime, liftIdx]; omega`
- failed on:
  - witness-bound arithmetic
  - 4 remaining direct arithmetic branches

4. Direct phase-1-only proof
- rewrote both sides with `cup2CycleVal_phase1`
- split on `t ≤ k`
- split on `j < k`
- still left 4 arithmetic goals that `omega` did not close

The exact shape of the remaining phase-1 goals is:

```lean
if (if j < k then j else j + 1) < t then 1 else 0
```

versus

```lean
if j < deleteCycleTime n k t then 1 else 0
```

under the corresponding branch hypotheses.

Conclusion:

- the phase split is the right math
- but the branch arithmetic must be proved more explicitly than `omega`

### C. Scratch-file experiment for weight

Tried:

- create `/tmp/weight_scratch.lean`
- import `LeanMn.Convergence.CPhiDelete`
- `#check` the helper lemmas needed for the weight proof

Result:

- the helpers are not visible outside the file because they are `private`
- specifically inaccessible from the scratch file:
  - `converse_exp2_offsite`
  - `projected_triple_eq`
  - `projected_position_type_eq`
  - `exp2BitVal_proj`
  - `localExp2Weight_congr`

Conclusion:

- the scratch-file route is blocked unless the needed helpers are made non-`private`
- this confirms that isolation is not currently available without refactoring exports

## Remaining theorem-level `sorry` inventory from the green build

Current actual theorem-level `sorry`s:

- `deleteCycleVal_eq_phase1`
- `deleteCycleVal_eq_phase2`
- `deleteCycleVal_eq_phase3_boundary`
- `deleteCycleVal_eq_phase3`
- `deleteConfig_cycleConfig_eq`
- `source_transport_step_lift_offsite`
- `source_transport_step_lift_seam`
- `source_transport_step_lift_seam_left`
- `source_transport_step_lift_seam_right`
- `converse_weight_offsite`
- `period2_noCopy_nIndep_core`
- `period3_noCopy_nIndep_transfer_core`
- `active_bridge_alternative`
- `active_farProjectedMaximizer_exists_raw`
- `deletedWitnessStepCompatible_of_farDeepSite`
- `noDropTransport_active_nonempty`
- `no_noDropWitness_9`
- `no_noDropWitness_11_15`

Verified current counts:

- raw `grep -c sorry CPhiDelete.lean`: `21`
- theorem-level `sorry`s: `18`

## Honest next steps

Best local next steps:

1. `converse_weight_offsite`
- continue only there until it is closed
- the three natural subcases are:
  - `p < k`, `p = 0`
  - `p < k`, `p > 0`
  - `p > k`

2. `deleteCycleVal_eq_phase1`
- do not reopen the full cycle theorem
- isolate one arithmetic branch at a time and prove it explicitly
- do not expect `omega` alone to finish the branchwise `if`-comparison

Best downstream packaging opportunities:

- none obvious remain besides the ones already closed
- `noDropTransport_active_nonempty` still needs a full deleted witness, so it is
  not mere plumbing

## Latest update: weight normalization helper

Added and verified:

- `projMover_left_val_above`

This helper captures exactly the modular-left normalization needed in the
`p > k` branch of `converse_weight_offsite`:

```lean
(left (projMover ... p)).1 = p.1 - 2
```

using the actual deep-site regime (`hk3 : 3 ≤ k`).

Then retried the `p > k` branch with the full intended arithmetic chain:

1. normalize indices with:
   - `projMover_val_above`
   - `projMover_left_val_above`
2. rewrite projected weight to the `(p-2, p-1)` coefficients
3. use `converse_exp2_offsite` to get the local count equality
4. prove:

```lean
original_weight = projected_weight + count
```

What remained:

- one `omega` failure in the first calc step even after adding:
  - `hp4 : 4 ≤ p`
  - `zify; omega`
- one later rewrite failure in the calc chain

So the current `p > k` branch is already reduced to the mathematically correct
coefficient-shift identity, and the only remaining obstruction is Lean closing
that final arithmetic/normalization pair.
