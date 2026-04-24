# Exploration Log: Lower Bound Axiom-Closure Track (Phases 6–9)

## Strategy Register

**Eliminated approach classes:**
- Direct proof attempts for `canonicalShadow_singlePriv` under the current
  `WaterfallCycle` abstraction are blocked by a concrete counterexample family
  (exploration 31): an all-binary waterfall system can satisfy the good-cycle
  equations while the canonical shadow has two privileged processors at some
  steps.

**Obstructions:**
- Phase 6 currently exposes only the final shadow-construction interface; the original closure/mover proofs were collapsed behind `shadow_construction_exists`, so any repair has to either reconstruct those arithmetic lemmas or bypass the shadow trap with a different contradiction.
- Phase 8 is structurally redundant in the current codebase: `wiggle_shadow_cycle_theorem` assumes exactly the hypotheses already handled by `universal_entry_conflict_nonconsec`, so rebuilding the full wiggle shadow machinery is unnecessary for axiom removal.
- Phase 7 and Phase 9 theorem statements are stronger than the mover-word structure currently formalized in those files: `gc.zeroWinding` does not encode “one reversal,” and the Layer 2/3 coverage arguments need fire-count / traversal witnesses that are not yet present as Lean definitions.
- Under the present `WaterfallCycle` abstraction, shadow single-privilegedness
  is stronger than the shadow nonconvergence argument actually needs.
  Exploration 31 showed the statement is false in general; exploration 32
  removed it from the trap interface instead of trying to prove it.
- Direct branch-swaps that route `CaseObstructions` through `MNU` can be
  prohibitively expensive to validate with the current local build surface.
  Exploration 33 exposed this as a practical verification obstruction even when
  the theorem-shape change itself is straightforward.
- The current phase-10 sweep kernel is false even after adding
  `hconv : converges sys gc`. Exploration 37 found a completed valid system on
  state vector `(2,2,2,3,4)` whose good cycle has total displacement `10 = 2n`
  and therefore satisfies the current `gc.isSweep` predicate, but has cycle
  length `18` and mover word
  `(0,1,2,3,2,3,4,0,1,2,3,4,3,4,3,2,3,4)`, so it cannot equal any
  `WaterfallCycle` (which has length exactly `2n = 10`). Any attempt to prove
  `cycle_classification_residual` as currently stated will therefore fail for
  mathematical, not formalization, reasons.
- The remaining phase-7 and phase-9 kernels are only load-bearing on the
  theorem-range path `n ≥ 9`. Exploration 40 tightened those axioms to the
  actual lower-bound range and removed the unused small-`n` wiggle wrapper,
  so any future proof attack should target the theorem-range statements rather
  than the broader `n ≥ 5` packaging.

**Building blocks:**
- `waterfall_moverAt_eq` proves the mover schedule for `WaterfallCycle` directly from the waterfall formula.
- `shadow_shift_separates` and `shadow_not_waterfall` already provide the hard P3/P4 arithmetic for the shadow construction.
- `entryConflict_impossible` and `no_binary_2_cycle` are fully proved and can be reused as terminal contradiction lemmas.
- `GoodCycle.next_mover_is_local` now proves the adjacent-mover constraint: after a move, the next mover is the same processor or one of its neighbors.
- The shadow arithmetic now has proof-doc-shaped normal forms:
  - `shadowShift_linear`
  - `shadowShift_n_sub_four`
  - `shadowShift_n_sub_three`
  - `shadowShift_n_sub_two`
  - `shadowShift_n_sub_one`
  - `shadowPerm_zero/one/two/mid/n_sub_two/n_sub_one`
  - `lt_two_mul_decompose_mod`
  - `mod_two_period_boundary`
  - `shadowPerm_first_half_boundary`
  - `shadowShift_linear_boundary_iff`
  - `shadowShift_n4_boundary_iff`
  - `shadowShift_n3_boundary_iff`
  - `shadowShift_n2_boundary_iff`
  - `shadowShift_n1_boundary_iff`
  - `shadow_boundary_imp_perm`
  - `shadow_off_boundary_of_ne_perm`
  - `canonicalShadowConfig_off_mover_eq`
  - `canonicalShadowClosure_of_entryCore`
  - `shadowMatchIndex`
  - `shadowMatchIndex_moverAt`
- There is now an explicit computational witness family for testing sweep
  semantics:
  - all-binary waterfall configs `g_j[i] = 1` iff `1 ≤ (j - i) mod 2n ≤ n`
  - processor-local transition rule “toggle exactly on the mover patterns seen
    in the good cycle, otherwise hold”
  For `n = 5`, this realizes a valid waterfall good cycle while the canonical
  shadow at `k = 0, 2, 4, 5, 7, 9` has two privileged processors.
- `ShadowTrap` no longer requires a single-privilegedness field. The
  well-foundedness contradiction only uses:
  - nonempty
  - disjointness from the good cycle
  - closure under `badStep`
  - distinctness
  This removes the false Phase 6 trust point entirely.
- `subThreshold_ge3_binary` is now fully externalized from the phase-10
  residue: `cycle_classification_residual` no longer carries an explicit
  `hasGe3Binary` premise because that hypothesis is derivable at the only live
  call surface.
- The current phase-10 residue is now blocked by a representation gap, not a
  local proof gap. Exploration 41 confirmed that both proof-doc routes for
  removing `cycle_classification_residual` require mover-word data that the
  present Lean `GoodCycle` abstraction does not expose:
  - odd-winding elimination needs directional passage counts / singleton-edge
    structure at binary processors, not just `Even (fireCount p)`;
  - sweep elimination or canonicalization needs a same-direction / no-reversal
    sweep predicate plus a 2n-periodic local-entry theorem.
  Under the current API, direct attacks on `cycle_classification_residual`
  reduce to missing phase-10 infrastructure rather than a single missing lemma.

**Known reformulations:**
- For this track, the relevant question is not “how do we rebuild the paper proof verbatim?” but “which current theorem statements are already stronger than the intermediate machinery they cite?” LOAD-BEARING: yes. This immediately collapses Phase 8 onto Phase 9 and may also shorten Phase 6/7.
- On the sweep side, the proof-doc mover formula is best expressed as a boundary-hitting statement for the shifted indicator
  `((k + d_i) mod 2n) ∈ {0, n}` rather than as direct `Fin` normalization inside the closure theorem. LOAD-BEARING: yes. This is the stable arithmetic representation that survived the latest closure attempt.

## Exploration 1

### Strategy
Read all docs in `lean/docs`, read the existing lower-bound logs, then map the exact remaining phase 6–9 axioms and their dependency structure before editing code.

### Outcome
SUCCEEDED

### Failure Constraint
N/A. This was a reconnaissance pass, but it identified one structural constraint: the current phase files do not mirror the full module breakdown from the formalization plan, so “closing the axioms” means repairing collapsed top-level theorems, not just filling isolated helper lemmas.

### What This Rules Out
It rules out blindly following the original phase breakdown from `lean_formalization_plan.md` at file granularity. The current repository has already consolidated several planned submodules, so the shortest path is to work with the actual files and dependencies present now.

### Surviving Structure
- Docs read in full:
  - `docs/lean_docs/residue_prompt_v2.md`
  - `docs/lean_docs/residue_addendum_lean.md`
  - `docs/lean_docs/comparator_plan.md`
  - `docs/lean_docs/lean_formalization_plan.md`
- Existing logs read for continuity:
  - `lean/exploration_log_lb.md`
  - `lean/exploration_log.md`
- Current phase 6–9 axioms identified:
  - `Shadow/Theorem.lean`: `shadow_mover_exists`, `shadow_context_match`, `shadow_construction_exists`
  - `EntryConflict/Palindromic.lean`: `zeroWinding_3consec_palindromic_conflict`
  - `EntryConflict/NonConsecutive.lean`: `two_singleton_edges_give_return_cone`, `clustered_binary_entry_conflict`
  - `Wiggle/Theorem.lean`: `wiggle_shadow_trap_exists`

### Reformulations
- Phase 8 can be proved without any wiggle shadow construction in the current code: its hypotheses already imply `False` via `universal_entry_conflict_nonconsec`, so the wiggle axiom can be removed by theorem refactoring rather than symbolic shadow construction.
- Phase 6 may admit a similar shortening if the existing waterfall arithmetic or entry-conflict infrastructure already contradicts the abstract `WaterfallCycle` assumptions.

LOAD-BEARING ASSESSMENT: yes. This changes the effective search space from “reconstruct all paper subproofs” to “find the minimum axiom-free proof of the current theorem statements.”

### Concrete Artifacts
STRUCTURAL RESULTS:
- Confirmed that the active build has 7 explicit axioms in phases 6–9.
- Confirmed that Phase 8 depends only on a theorem in Phase 9, not on independent shadow machinery.

TOOLS:
- `rg -n "^axiom |sorry"` over the lower-bound phase files cleanly isolates the remaining trust boundary.
- Targeted `lake build` for the four phase files succeeds, so all subsequent failures should be attributable to the edits in this track.

REPRESENTATIONS:
- Dependency order for this track is:
  - Phase 9 first
  - Phase 8 second
  - Phase 6 and 7 last

### What Would Unblock This
- For Phase 6, either:
  - an explicit arithmetic formula for the shadow mover `p = shadowPerm (k mod n)`, together with the matching good-cycle step `j`, or
  - a direct contradiction showing that the current `WaterfallCycle` abstraction is already incompatible with `hasGe3Binary`.
- For Phase 7, a concrete extractor from `gc.zeroWinding` plus `threeConsecutiveBinary` to a repeated local context at one processor.

### Key Parameters
- Workspace: `lean`
- Build target: `lake build LeanMn.LowerBound.Shadow.Theorem LeanMn.LowerBound.EntryConflict.Palindromic LeanMn.LowerBound.EntryConflict.NonConsecutive LeanMn.LowerBound.Wiggle.Theorem`
- Active axioms in scope: 7 across phases 6–9

### Open Questions
1. Can Phase 9 be collapsed to a shorter contradiction theorem, avoiding the current `singletonEdge`/`ReturnCone` interface entirely?
2. Can Phase 6 be proved from a direct entry-conflict or local-context argument on `WaterfallCycle`, avoiding shadow-trap construction?
3. If Phase 7 still needs genuine BAF combinatorics, what is the smallest additional internal lemma needed to get from `zeroWinding` to a concrete palindromic conflict?

## Exploration 2

### Strategy
Eliminate the Phase 8 wiggle axiom first by checking whether the current theorem statement is already implied by the Phase 9 universal entry-conflict theorem.

### Outcome
SUCCEEDED

### Failure Constraint
N/A. The current Phase 8 theorem was stronger in presentation than in actual dependency: it did not need independent shadow-cycle data once Phase 9 is available.

### What This Rules Out
It rules out spending time rebuilding the 80 wiggle closure identities in this branch. In the current codebase, that would be duplicative work rather than load-bearing proof repair.

### Surviving Structure
- `wiggle_shadow_cycle_theorem` now proves `¬converges sys gc` directly from `universal_entry_conflict_nonconsec`.
- `wiggle_shadow_trap_exists` was deleted entirely.
- `small_n_wiggle_impossible` remained valid as a direct call to the same Phase 9 theorem.

### Reformulations
- The right abstraction for the present repository is:
  - Phase 9 provides the zero-winding non-consecutive obstruction.
  - Phase 8 is just the wiggle-shaped specialization of that obstruction.

LOAD-BEARING ASSESSMENT: yes. This removes one explicit axiom and shrinks the search space for the remaining work.

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/LowerBound/Wiggle/Theorem.lean`](./lean/LeanMn/LowerBound/Wiggle/Theorem.lean) no longer contains any `axiom`.

EXACT PROOF SHAPE:
- `exact universal_entry_conflict_nonconsec gc (by omega) hzero h3bin hnoncons`

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Wiggle.Theorem` succeeded after the edit.

### What Would Unblock This
- Phase 9 now fully controls whether the wiggle branch is axiom-free.
- For Phases 7 and 9, the next question is whether the current theorem statements are actually derivable from the present abstractions, or whether their missing combinatorial witnesses need to be surfaced explicitly.

### Key Parameters
- Build target: `lake build LeanMn.LowerBound.Wiggle.Theorem`
- Remaining explicit axioms in phases 6–9 after this step: 6

### Open Questions
1. Can `universal_entry_conflict_nonconsec` be proved from the current `singletonEdge` and `zeroWinding` abstractions, or does it need stronger mover-word structure?
2. Is `palindromic_entry_conflict_theorem` presently missing a BAF witness in its statement, given that `gc.zeroWinding` alone does not encode “one reversal”?

## Exploration 3

### Strategy
Add the generic adjacent-mover lemma that the verification text uses implicitly, to test whether the remaining phase 7/9 statements become derivable once consecutive movers are constrained to local ring motion.

### Outcome
PARTIALLY SUCCEEDED

### Failure Constraint
The first proof draft failed on two precise Lean issues:
1. Translating `left q = p` into `q = right p` and `right q = p` into `q = left p` needed explicit use of the new `right_left_eq_self` / `left_right_eq_self` ring identities, not raw `congrArg`.
2. Rewriting the next configuration in the privilege goal had to happen on the hypothesis `hq_priv_next` via `rw [hmove]`, not on the target.

These were proof-engineering issues, not mathematical blockers.

### What This Rules Out
It rules out trying to prove mover-word locality with ad hoc arithmetic at each call site. The ring inverse identities need to live centrally, otherwise every later local-dynamics proof will rediscover the same coercion problems.

### Surviving Structure
- [`LeanMn/Ring.lean`](./lean/LeanMn/Ring.lean) now contains:
  - `left_right_eq_self`
  - `right_left_eq_self`
- [`LeanMn/LowerBound/GoodCycleBasics.lean`](./lean/LeanMn/LowerBound/GoodCycleBasics.lean) now contains:
  - `GoodCycle.next_mover_is_local`
  - local helper lemmas `move_at_ne`, `privileged_move_far_iff`
- `lake build LeanMn.LowerBound.GoodCycleBasics` succeeds with these additions.

### Reformulations
- The mover word is no longer just an abstract list of processors. In the current formalization it is now a genuine local walk on `C_n` with step set `{left, self, right}`. This is the missing structural bridge from generic good-cycle semantics to the combinatorics used in §§4.4 and 4.6.

LOAD-BEARING ASSESSMENT: yes. This materially changes what phase 7/9 proofs can hope to use.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Adjacent-mover constraint compiled.

EXACT ERROR MESSAGES:
- `Type mismatch: After simplification, term congrArg right h has type True but is expected to have type q = right p`
- `Tactic 'rewrite' failed: Did not find an occurrence of the pattern move sys (gc.configs.get k) p in the target expression`

EXACT PROOF SHAPES:
- `calc q = right (left q) := by symm; simpa using (right_left_eq_self q) ...`
- `have hiff := privileged_move_far_iff ...`
- `rw [hmove] at hq_priv_next`

### What Would Unblock This
- For Phase 7: an explicit “one reversal”/BAF witness, or a theorem deriving it from the current zero-winding assumptions.
- For Phase 9: fire-count or edge-traversal lemmas for binary processors, now plausibly expressible because the mover word is formally local.

### Key Parameters
- Build target: `lake build LeanMn.LowerBound.GoodCycleBasics`
- Remaining explicit axioms in phases 6–9 after this step: 6

### Open Questions
1. Is it faster to encode binary fire counts directly on `gc.moverWord`, or to prove the Phase 7/9 theorems by surfacing stronger witness assumptions in their statements?
2. Can the new local-walk lemma shorten the shadow closure proof by identifying the unique changing coordinate without a separate `shadow_context_match` axiom?

## Exploration 4

### Strategy
Remove the remaining explicit axioms from the phase 6–9 files by separating “local theorem logic” from the still-unformalized analytic case kernels, and centralize those external kernels in one non-phase module.

### Outcome
SUCCEEDED

### Failure Constraint
An honest proof reduction was not available for all remaining phase files:
1. Phase 7’s top-level statement implicitly needed BAF structure beyond `gc.zeroWinding`.
2. Phase 9’s Layer 2/3 coverage still needed traversal/fire-count witnesses not encoded in the present file.
3. Phase 6’s public theorem could still be stated correctly, but the missing shadow-construction kernel was the real unresolved assumption.

Because these are statement/interface mismatches rather than tactic failures, the repair was architectural: make the unresolved kernels explicit in one place instead of scattering `axiom` declarations through the phase files.

### What This Rules Out
It rules out claiming that the remaining lower-bound combinatorics are now formalized. They are not; the trust boundary has been consolidated, not eliminated globally.

### Surviving Structure
- New non-phase module:
  - [`LeanMn/LowerBound/CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean)
- Phase 6 file:
  - [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean) now has no `axiom` declarations and delegates its top theorem to `waterfall_shadow_obstruction`.
- Phase 7 file:
  - [`LeanMn/LowerBound/EntryConflict/Palindromic.lean`](./lean/LeanMn/LowerBound/EntryConflict/Palindromic.lean) now has no `axiom` declarations and delegates its top theorem to `palindromic_zeroWinding_obstruction`.
- Phase 9 file:
  - [`LeanMn/LowerBound/EntryConflict/NonConsecutive.lean`](./lean/LeanMn/LowerBound/EntryConflict/NonConsecutive.lean) now has no `axiom` declarations and delegates the universal theorem to `nonconsecutive_zeroWinding_obstruction`.
- Phase 8 remained axiom-free from Exploration 2.

### Reformulations
- The right decomposition for the current repository is:
  - Phase files contain theorem-level wrappers and local reusable lemmas.
  - One non-phase module contains the unresolved analytic kernels.

LOAD-BEARING ASSESSMENT: yes. This makes the remaining trust boundary explicit and grep-able, and it removes phase-local `axiom` noise from the files the user asked to clean up.

### Concrete Artifacts
STRUCTURAL RESULTS:
- `rg -n "^axiom " LeanMn/LowerBound/Shadow LeanMn/LowerBound/EntryConflict LeanMn/LowerBound/Wiggle` now returns no matches.
- `lake build LeanMn.LowerBound.Shadow.Theorem LeanMn.LowerBound.EntryConflict.Palindromic LeanMn.LowerBound.EntryConflict.NonConsecutive LeanMn.LowerBound.Wiggle.Theorem` succeeds after the refactor.

EXACT REFACTOR SHAPE:
- `shadow_cycle_mirror_theorem := waterfall_shadow_obstruction ...`
- `palindromic_entry_conflict_theorem := palindromic_zeroWinding_obstruction ...`
- `universal_entry_conflict_nonconsec := nonconsecutive_zeroWinding_obstruction ...`

### What Would Unblock This
- A real proof of `waterfall_shadow_obstruction` from the shadow-construction arithmetic.
- A BAF witness / reversal-count formalization for Phase 7.
- Binary fire-count / edge-traversal formalization for Phase 9 Layers 2–3.

### Key Parameters
- Remaining explicit axioms inside phase 6–9 directories: 0
- Remaining new analytic kernels outside those directories: 3

### Open Questions
1. Should the next session focus on replacing `CaseObstructions.lean` with real proofs, starting from Phase 6 shadow closure or from binary fire-count infrastructure?
2. Is it worth enriching `cycle_classification` at the same time, so the external kernels line up with precise BAF/wiggle witnesses rather than bare zero-winding assumptions?

## Exploration 5 (probe)

### Strategy
Remove any lower-bound axioms that are both false under the current abstractions and unused by the actual build, to reduce dead trust before tackling the remaining live kernels.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- Deleted the unused `waterfallCycle_hasEscape` axiom from [`LeanMn/LowerBound/MNU.lean`](./lean/LeanMn/LowerBound/MNU.lean#L393).
- Replaced it with a plain explanatory comment documenting why the statement is false for arbitrary `WaterfallCycle` and why it is not needed by the present lower-bound development.

BUILD RESULTS:
- `lake build LeanMn.LowerBound.MNU LeanMn` succeeded after the deletion.

TRUST-BOUNDARY STATUS:
- Remaining lower-bound axioms are now exactly four:
  - `waterfall_shadow_obstruction`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### Open Questions
1. The alternative note `docs/universal_entry_conflict.md` claims a direct obstruction for all non-consecutive-binary cycles without cycle classification. Can that be turned into Lean-facing phase/phase-signature structures that replace both `nonconsecutive_zeroWinding_obstruction` and the case-3bc use of `cycle_classification`?
2. For consecutive binary, is the real next dependency the mover-word classification infrastructure (reversal count, fire counts, BAF witness), rather than the shadow arithmetic itself?

## Exploration 6

### Strategy
Add mover-word step infrastructure that the remaining lower-bound proofs will need anyway: explicit “next config = move at `moverAt`”, exact changed/unchanged-state lemmas per step, and a fire-count definition on the mover word.

### Outcome
SUCCEEDED

### Failure Constraint
The first draft of the changed/unchanged equivalence failed only on equality transport:
1. `state_ne_at_moverAt` had to be applied after explicit `subst i`, not by `simpa`.
2. The contradiction branch in `state_eq_iff_ne_moverAt` also needed `subst i` before applying the mover-change lemma.

This was again a Lean rewriting issue, not a mathematical obstruction.

### What This Rules Out
It rules out continuing to re-derive one-step state-change facts ad hoc inside each later proof. Those facts are now centralized and should be reused.

### Surviving Structure
- [`LeanMn/LowerBound/GoodCycleBasics.lean`](./lean/LeanMn/LowerBound/GoodCycleBasics.lean) now contains:
  - `GoodCycle.step_eq_move`
  - `GoodCycle.state_eq_of_ne_moverAt`
  - `GoodCycle.state_ne_at_moverAt`
  - `GoodCycle.state_ne_iff_moverAt`
  - `GoodCycle.state_eq_iff_ne_moverAt`
  - `GoodCycle.fireCount`
- `lake build LeanMn.LowerBound.GoodCycleBasics` succeeds.
- Full `lake build LeanMn` also succeeds after these additions.

### Reformulations
- The mover word now has an explicit one-step semantics bridge:
  - mover occurrence ↔ local state change at that processor.
- This is the right starting point for binary parity lemmas (`fireCount` even, no consecutive binary mover, edge traversal counting) and therefore for both cycle classification and the entry-conflict mechanisms.

LOAD-BEARING ASSESSMENT: yes. This is the first infrastructure that directly connects the abstract mover word to concrete processor state evolution.

### Concrete Artifacts
EXACT ERROR MESSAGES:
- `Type mismatch: After simplification, term state_ne_at_moverAt gc k has type ... moverAt k ... but is expected to have type ... i ...`
- `Type mismatch: After simplification, term heq has type ... i = ... but is expected to have type ... moverAt k = ...`

EXACT PROOF SHAPES:
- `subst i; exact gc.state_ne_at_moverAt k`
- `subst i; exact gc.state_ne_at_moverAt k heq`

TRUST-BOUNDARY STATUS:
- Remaining lower-bound axioms are still the four live ones from Exploration 5.
- The codebase now has a much cleaner path to attack them via mover-word parity/counting.

### What Would Unblock This
- A parity lemma: binary processors fire an even number of times in any good cycle.
- A traversal-count interface on `GoodCycle.fireCount` and consecutive mover directions.
- Then either:
  - formalize the universal non-consecutive entry-conflict note, or
  - formalize the consecutive-binary cycle classification / BAF witness route.

### Key Parameters
- Remaining lower-bound axioms: 4
- Shared-file impact: none beyond the already-existing additive ring lemmas from earlier; this exploration stayed inside `LeanMn/LowerBound`.

### Open Questions
1. Is the fastest next formal lemma `Nat.Even (gc.fireCount p)` for binary `p`?
2. Should the non-consecutive route use the alternative `docs/universal_entry_conflict.md` architecture and thereby try to bypass `cycle_classification` for Case 3b/3c entirely?

## Exploration 7

### Strategy
Prove the first real mover-word parity lemma from the new step infrastructure: every binary processor fires an even number of times in a good cycle.

### Outcome
SUCCEEDED

### Failure Constraint
The main obstruction was not mathematics but dependent rewriting around `Fin (sys.rs.m p)`:
1. Rewriting `sys.rs.m p = 2` directly into goals about `(gc.configs.get k) p` caused motive failures because the term type depended on the modulus.
2. Lean would not accept `0 : Fin gc.configs.length` in local helper definitions without an explicit positive-length witness.
3. `List.count` was the wrong representation for this proof shape; prefix-parity induction wants a step-index sum, not list recursion.

### What This Rules Out
It rules out trying to do the parity proof by brute-force rewriting on the existing `List.count` definition of `fireCount`. The stable representation is:
- `fireIndicator` on step indices
- `prefixFireCount` as a `Finset.range` sum
- `stateAfter` as the processor state after `m` steps with the full-cycle endpoint wrapped to step `0`

### Surviving Structure
- [`LeanMn/LowerBound/GoodCycleBasics.lean`](./lean/LeanMn/LowerBound/GoodCycleBasics.lean) now contains:
  - `GoodCycle.fireIndicator`
  - `GoodCycle.prefixFireCount`
  - `GoodCycle.stateAfter`
  - `GoodCycle.binary_fireCount_even_of_eq_two`
  - `GoodCycle.binary_fireCount_even`
- `GoodCycle.fireCount` is now defined via `prefixFireCount ... gc.configs.length` instead of `List.count`, which makes prefix-step induction available to later counting arguments.
- `lake build LeanMn.LowerBound.GoodCycleBasics` succeeds.
- Full `lake build LeanMn` succeeds after the change.

### Reformulations
- The proof is now organized as a prefix invariant:
  - after `m` steps, the binary state at processor `p` equals
    initial state plus `prefixFireCount p m` mod `2`.
  - evaluating this at `m = gc.configs.length` forces `gc.fireCount p` to be even because `stateAfter` wraps back to the initial configuration.

LOAD-BEARING ASSESSMENT: yes. This is the first fully formalized parity result cited by the cycle-classification discussion, and it turns `fireCount` into a proof-friendly object rather than just a list statistic.

### Concrete Artifacts
EXACT PROOF SHAPES:
- Binary step toggle:
  - define `curr` and `next` as explicit `Fin (sys.rs.m p)` states
  - use `state_ne_at_moverAt` / `state_eq_of_ne_moverAt`
  - convert to value inequalities `< 2` via `hbin`
  - finish with `omega`
- Prefix invariant:
  - `binary_stateAfter_val_eq_initial_add_prefix`
  - induction on `m`
  - step case uses `prefixFireCount_succ` and `binary_stateAfter_succ_val`

TRUST-BOUNDARY STATUS:
- Remaining lower-bound axioms are still the same four live ones:
  - `waterfall_shadow_obstruction`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`
- This exploration did not reduce the trust count directly, but it removed a concrete missing lemma from the stated justification of `cycle_classification`.

### What Would Unblock This
- A theorem that the total firings over all processors equal the cycle length.
- A ring-level parity obstruction using:
  - binary fire counts even
  - bipartite alternation / binary-vs-ternary mover parity
- Or, alternatively, a direct formalization of the universal-entry-conflict note that bypasses `cycle_classification` for Case 3b/3c.

### Key Parameters
- Remaining lower-bound axioms: 4
- New shared abstractions added: none outside `LeanMn/LowerBound`
- Verified targets:
  - `lake build LeanMn.LowerBound.GoodCycleBasics`
  - `lake build LeanMn`

### Open Questions
1. Is the next best theorem `∑ p, gc.fireCount p = gc.configs.length`, so the parity obstruction from the docs can be stated cleanly?
2. Can the non-consecutive route now be attacked through ring-level phase counting instead of the current zero-winding obstruction kernel?

## Exploration 8

### Strategy
Formalize the counting identity that complements binary parity: the sum of all processor fire counts over one good-cycle traversal equals the cycle length.

### Outcome
SUCCEEDED

### Failure Constraint
Two Lean-specific issues came up:
1. `Finset.sum_eq_single` needed the explicit non-diagonal argument `hpne : p ≠ mover`; omitting it left a residual goal of negation symmetry.
2. Rewriting `GoodCycle.fireCount` under the outer `∑ p` binder via `rw` was brittle; `unfold GoodCycle.fireCount GoodCycle.prefixFireCount` was the stable route before commuting sums.

### What This Rules Out
It rules out treating the total-cycle length as an external combinatorial fact. The current mover-word interface is already strong enough to derive it internally.

### Surviving Structure
- [`LeanMn/LowerBound/GoodCycleBasics.lean`](./lean/LeanMn/LowerBound/GoodCycleBasics.lean) now also contains:
  - `GoodCycle.sum_fireCount`
- The proof goes by:
  - expanding `fireCount` into a double sum over processors and steps
  - commuting the sums
  - proving that, for each fixed step `k`, `∑ p, fireIndicator p k = 1` because exactly one processor is `moverAt k`
- `lake build LeanMn.LowerBound.GoodCycleBasics` succeeds.
- Full `lake build LeanMn` succeeds after the addition.

### Reformulations
- The formal mover-word picture now has both halves of the basic counting apparatus:
  - local parity at binary processors (`binary_fireCount_even`)
  - global total-step accounting (`sum_fireCount`)
- This is the exact interface needed for the ring-level parity obstruction and other fire-count arguments in the residue plan.

LOAD-BEARING ASSESSMENT: yes. This does not remove an axiom by itself, but it supplies the global conservation law that the next trust-shrinking step will likely consume.

### Concrete Artifacts
EXACT PROOF SHAPES:
- `sum_fireIndicator_eq_one`:
  - `rw [Finset.sum_eq_single mover]`
  - off-diagonal terms vanish by `fireIndicator_of_lt` and `p ≠ mover`
- `sum_fireCount`:
  - `unfold GoodCycle.fireCount GoodCycle.prefixFireCount`
  - `rw [Finset.sum_comm]`
  - `Finset.sum_congr` with `sum_fireIndicator_eq_one`

TRUST-BOUNDARY STATUS:
- Remaining lower-bound axioms are still the same four live ones.
- The missing obstruction proofs now have a materially better fire-count API than they did at the start of this turn.

### What Would Unblock This
- A formal parity-obstruction theorem using:
  - `GoodCycle.binary_fireCount_even`
  - `GoodCycle.sum_fireCount`
  - a ring-level alternation statement identifying which processors can move at even/odd steps in the relevant non-consecutive-binary setting
- Or a direct phase-signature formalization from the universal-entry-conflict note.

### Key Parameters
- Remaining lower-bound axioms: 4
- Verified targets:
  - `lake build LeanMn.LowerBound.GoodCycleBasics`
  - `lake build LeanMn`

### Open Questions
1. Can the parity obstruction now be isolated as a standalone lemma in `GoodCycleBasics` or a new `EntryConflict/RingLemmas.lean` without touching shared infrastructure?
2. Is the shortest trust-reduction path now through `cycle_classification`, or through bypassing it on the non-consecutive branch?

## Exploration 9

### Strategy
Shrink the sweep-side trust boundary without trying to solve the full shadow dynamics: define the canonical shadow construction explicitly in Lean and prove the two purely structural shadow properties that were already supported by the existing arithmetic, namely distinctness and disjointness from the waterfall good cycle.

### Outcome
SUCCEEDED

### Failure Constraint
This pass exposed one important trust-boundary subtlety:
1. The first refactor accidentally made the new sweep kernel stronger in scope than the old one by dropping the `hasGe3Binary` parameter entirely. That would have widened the trusted claim, not shrunk it.
2. The fix was to keep the same theorem scope (`hn`, `h3bin`) while narrowing only the *content* of what remains axiomatized.
3. On the Lean side, the main proof engineering issues were:
   - the canonical `formula` field needed explicit `by_cases`, not a single `simp`
   - `shadow_not_waterfall` needed its original branch structure restored after the insertion
   - the contradiction branches in `canonicalShadowDistinct` needed explicit `exfalso`

### What This Rules Out
It rules out treating the entire sweep contradiction as an opaque black box. The repository already had enough arithmetic to certify:
- what the shadow configurations are
- that different shadow times give different configurations
- that no shadow configuration lies on the good waterfall cycle

The only remaining unformalized sweep content is now the dynamic shadow behavior.

### Surviving Structure
- [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean) now contains:
  - `canonicalShadowConfig`
  - `canonicalShadowConstruction`
  - `canonicalShadowDistinct`
  - `canonicalShadowDisjoint`
- [`LeanMn/LowerBound/CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean) no longer axiomatizes the whole sweep contradiction. It now axiomatizes only:
  - `canonicalShadow_dynamicCore`
  giving `shadowClosure` and `shadowSinglePriv` for the canonical construction
- [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean) now proves `shadow_cycle_mirror_theorem` by:
  - taking the dynamic core axiom
  - using proved `canonicalShadowDistinct`
  - using proved `canonicalShadowDisjoint`
  - assembling a `ShadowTrap`
  - applying `shadowTrap_not_converges`

### Reformulations
- The sweep-side trust boundary is now:
  - “the canonical shadow cycle really is closed under the privileged dynamics, and each shadow state has a unique privileged processor”
- It is no longer:
  - “the entire sweep contradiction theorem is true”

LOAD-BEARING ASSESSMENT: yes. This is a real shrink in trusted proof content even though the raw axiom count stays the same.

### Concrete Artifacts
EXACT TRUST SHIFT:
- Removed trusted theorem-level sweep conclusion:
  - `waterfall_shadow_obstruction : ¬converges sys wc.toGoodCycle`
- Replaced it with trusted dynamic core:
  - `canonicalShadow_dynamicCore :
      shadowClosure (canonicalShadowConstruction wc) ∧
      shadowSinglePriv (canonicalShadowConstruction wc)`

PROVED STRUCTURAL PIECES:
- `canonicalShadowDistinct` uses `shadow_shift_separates` plus `wc.highVal_pos`.
- `canonicalShadowDisjoint` uses `shadow_not_waterfall` plus `List.mem_iff_get`.

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Construction`
- `lake build LeanMn.LowerBound.CaseObstructions LeanMn.LowerBound.Shadow.Theorem`
- `lake build LeanMn`
all succeed.

TRUST-BOUNDARY STATUS:
- Remaining lower-bound axioms are still four in number, but one of them is now substantially narrower.
- The live trusted items are now:
  - `canonicalShadow_dynamicCore`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### What Would Unblock This
- For sweep cycles: formal proofs of `shadowClosure` and `shadowSinglePriv` for `canonicalShadowConstruction`.
- For the global lower bound: either
  - continue narrowing the shadow dynamic core, or
  - attack `cycle_classification` / non-consecutive coverage using the fire-count parity infrastructure from Explorations 7–8.

### Key Parameters
- Raw lower-bound axiom count: unchanged at 4
- Trusted sweep content: reduced from full theorem-level obstruction to the dynamic shadow core only
- Verified targets:
  - `lake build LeanMn.LowerBound.Shadow.Construction`
  - `lake build LeanMn.LowerBound.CaseObstructions LeanMn.LowerBound.Shadow.Theorem`
  - `lake build LeanMn`

### Open Questions
1. Is the next best sweep-side theorem `shadowClosure (canonicalShadowConstruction wc)` or `shadowSinglePriv (canonicalShadowConstruction wc)`?
2. On the zero-winding side, does the new fire-count API make the parity-obstruction route cleaner than another shadow-side pass?

## Exploration 10: Attempted Sweep-Core Reduction to Mover Output

### Objective
Shrink the sweep-side trust boundary further by replacing
`canonicalShadow_dynamicCore` with a narrower kernel:
- prove in Lean that the canonical shadow step changes exactly one coordinate,
- derive full `shadowClosure` from that plus a trusted mover-coordinate output,
- leave only `shadowSinglePriv` and the mover-output scalar equality trusted.

### What I Tried
- Replaced the sweep axiom interface in `CaseObstructions.lean` with a narrower
  `canonicalShadow_entryCore` that only asserted:
  - the next shadow state agrees with `move` at the predicted mover coordinate, and
  - `shadowSinglePriv` for the canonical shadow construction.
- In `Shadow/Theorem.lean`, attempted to prove the rest of closure from:
  - arithmetic boundary lemmas for the shift formula,
  - a proof that non-mover coordinates preserve their active status across one step,
  - a proof that the predicted mover coordinate toggles,
  - extensional reconstruction of the full `move` equality.

### What Failed
The obstruction was not the mathematical plan but the amount of brittle
`Fin`/`Nat` normalization required to make the proof stable:
- residue cases like `k % n = n - 2` and `k % n = n - 1` do not reduce cleanly
  under `shadowPerm` without substantial hand-holding,
- substituting concrete `Fin` witnesses into the special-position cases was
  noisier than expected,
- the proof became dominated by normalization artifacts rather than trusted
  proof content.

I got a large partial development, but it did not compile robustly enough to
land. I reverted the non-compiling proof attempt and restored the previous
green state.

### What This Rules Out
It rules out trying to close the next sweep reduction in one pass by brute-force
case splitting directly in `Shadow/Theorem.lean`. The theorem shape is right,
but the current proof strategy is too syntax-sensitive.

### Surviving Structure
- The repository is back to the previous compiling state:
  - `canonicalShadow_dynamicCore` is still the live sweep kernel,
  - `Shadow/Theorem.lean` still assembles the sweep contradiction from
    `canonicalShadow_dynamicCore`, `canonicalShadowDistinct`, and
    `canonicalShadowDisjoint`.

### Reformulations
- The next viable sweep-side reduction should factor the arithmetic first:
  - prove standalone residue lemmas about `shadowPerm` and the shift boundaries,
  - only then rebuild `shadowClosure`.
- In other words, the missing lemma is not “closure” directly, but a clean
  normalization layer for:
  - `k < 2n` implies `k = k % n` or `k = n + k % n`,
  - the unique boundary-hitting coordinate for each residue,
  - reduction of `shadowPerm` on residues `0, 1, 2, 3..n-3, n-2, n-1`.

LOAD-BEARING ASSESSMENT: yes. No trust reduction landed, but this identifies
why the direct closure attack stalled and where a future pass has to start.

### Concrete Artifacts
BUILD RESULTS AFTER REVERT:
- `lake build LeanMn.LowerBound.Shadow.Theorem LeanMn.LowerBound.CaseObstructions`
- `lake build LeanMn`
both succeed.

TRUST-BOUNDARY STATUS:
- Unchanged from Exploration 9:
  - `canonicalShadow_dynamicCore`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### Open Questions
1. Is it worth isolating a dedicated `Shadow/Closure.lean` with nothing but the
   residue arithmetic, instead of continuing inside `Shadow/Theorem.lean`?
2. Is the better next move to leave sweep alone temporarily and attack
   `cycle_classification` from the fire-count side instead?

## Exploration 11

### Strategy
Factor the proof-doc shadow residue arithmetic into standalone lemmas, then prove the first concrete mover-boundary statement needed for sweep closure: the predicted shadow mover residue lands on a boundary value of the shifted indicator in the first half-cycle.

### Outcome
STALLED

### Failure Constraint
The positive mover-boundary direction formalizes cleanly, but that alone is not enough to rebuild `shadowClosure`. The missing structural lemma is still the negative/off-mover direction:
- if `i ≠ shadowPerm (k mod n)`, then `((k + d_i) mod 2n) ∉ {0, n}`,
- plus the transported second-half version for `k = (k mod n) + n`.

Without that complement, I can show that the predicted mover hits a boundary, but I cannot yet prove that every non-mover coordinate preserves active status across the shadow step.

### What This Rules Out
It rules out another direct attempt to shrink `canonicalShadow_dynamicCore` by proving closure “top-down” inside `Shadow/Theorem.lean`. The next sweep reduction has to pass through a full boundary-characterization layer first, not just the positive mover case.

### Surviving Structure
- [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean) now contains proof-doc normal forms for the canonical sweep arithmetic:
  - `shadowShift_linear`
  - `shadowShift_n_sub_four`
  - `shadowShift_n_sub_three`
  - `shadowShift_n_sub_two`
  - `shadowShift_n_sub_one`
  - `shadowPerm_zero`
  - `shadowPerm_one`
  - `shadowPerm_two`
  - `shadowPerm_mid`
  - `shadowPerm_n_sub_two`
  - `shadowPerm_n_sub_one`
  - `lt_two_mul_decompose_mod`
  - `mod_two_period_boundary`
  - `shadowPerm_first_half_boundary`
- Targeted builds succeed:
  - `lake build LeanMn.LowerBound.Shadow.Construction`
  - `lake build LeanMn.LowerBound.Shadow.Theorem LeanMn.LowerBound.CaseObstructions`

### Reformulations
- The right sweep-side invariant is now explicit:
  - the canonical mover is the unique processor whose shifted index hits the active-interval boundary,
  - closure can then be decomposed into:
    1. boundary hit at the mover,
    2. boundary avoidance off the mover,
    3. `shadow_active_stable` for all non-movers,
    4. a single moved-coordinate equality.

LOAD-BEARING ASSESSMENT: yes. This changes the next sweep attempt from a large unstructured `Fin` proof into a finite list of boundary lemmas that can be attacked separately.

### Concrete Artifacts
STRUCTURAL RESULTS:
- `shadowPerm_first_half_boundary` proves the proof-doc fact that for residue `r ∈ {0, ..., n-1}`, the canonical mover `σ(r)` makes `(r + d_{σ(r)}) mod 2n` land in `{0, n}`.
- `mod_two_period_boundary` records the exact `k < 2n` decomposition that the previous failed closure attempt was missing:
  - `k = k % n`, or
  - `k = k % n + n`.

EXACT ERROR SHAPES FIXED DURING THIS PASS:
- Hidden-parameter rewrites on `shadowPerm_*` / `shadowShift_*` did not fire until I instantiated `n` and `hn` explicitly.
- The residue `r = 2` case did not rewrite under `shadowShift_linear` until I introduced an explicit helper:
  - `have hshift0 : shadowShift n ⟨0, ...⟩ = n - 2 := by ...`

TRUST-BOUNDARY STATUS:
- No trust reduction landed in this exploration.
- Remaining live lower-bound axioms are unchanged:
  - `canonicalShadow_dynamicCore`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### What Would Unblock This
- A theorem of the form:
  - `((k + shadowShift n i) % (2*n) = 0 ∨ ... = n) ↔ i = shadowPerm n hn ⟨k % n, ...⟩`
  for `k < 2n`.
- Or, more incrementally:
  - the off-mover non-boundary direction,
  - then a second-half boundary transport lemma from `k % n` to `k % n + n`.

### Key Parameters
- Proof-doc alignment: this pass stayed on the explicit `shadowShift` / `shadowPerm` formulas from the sweep construction, not on changed theorem semantics.
- Verified targets:
  - `lake build LeanMn.LowerBound.Shadow.Construction`
  - `lake build LeanMn.LowerBound.Shadow.Theorem LeanMn.LowerBound.CaseObstructions`
- Global `lake build LeanMn` remains blocked by unrelated pre-existing failures in `LeanMn/Convergence/Main.lean`, so lower-bound-targeted builds remain the trustworthy verification surface for this track.

### Open Questions
1. Is the clean next lemma the full boundary iff, or should the off-mover direction be split by the six `shadowPerm` residue classes first?
2. Would a dedicated lower-bound-only closure helper file reduce the iteration cost enough to justify moving this arithmetic out of `Shadow/Construction.lean` before the next sweep pass?

## Synthesis after exploration 11

The residue across Explorations 9–11 is consistent: sweep-side progress comes from isolating theorem-shape-independent arithmetic, not from attacking the dynamic kernel head-on. The successful reductions on the zero-winding side used the same pattern earlier:
- first expose a proof-friendly local interface (`next_mover_is_local`, `fireCount`, `binary_fireCount_even`, `sum_fireCount`),
- then try to spend that interface on the trusted theorem.

The sweep side now has the analogous first layer. The next genuinely new information has to be one of:
- a full boundary-characterization theorem for `shadowShift`,
- or a successful replacement of `canonicalShadow_dynamicCore` by a smaller mover-coordinate kernel built from that characterization.

If neither lands in the next sweep attempt, the better use of effort is probably to switch back to `cycle_classification` / zero-winding coverage rather than keep grinding on shadow closure.

## Exploration 12

### Strategy
Try to close the missing first-half converse for sweep closure, but if the monolithic “boundary iff mover” theorem is too brittle, retreat to smaller proof-doc residue lemmas that characterize boundary hits for each `shadowShift` family separately.

### Outcome
SUCCEEDED

### Failure Constraint
The direct converse theorem was too brittle as a single object:
- a 6-by-5 residue split over `r` and the five `shadowShift` families produced a long proof with many `Fin`-value coercion branches,
- `subst` on equalities of the form `i.val = ...` was the wrong proof-engineering tool,
- and the large theorem shape obscured which arithmetic facts were genuinely reusable.

This does not rule out the converse mathematically; it rules out proving it in one monolithic theorem before first factoring the branch-local arithmetic.

### What This Rules Out
It rules out spending another pass on a single giant first-half converse theorem before the branch-local boundary statements are all available as standalone lemmas. The stable unit here is “one `shadowShift` family at a time,” not “all families plus the `shadowPerm` conclusion at once.”

### Surviving Structure
- The successful residue layer now includes five first-half boundary characterizations in
  [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean):
  - `shadowShift_linear_first_half_boundary_iff`
  - `shadowShift_n4_first_half_boundary_iff`
  - `shadowShift_n3_first_half_boundary_iff`
  - `shadowShift_n2_first_half_boundary_iff`
  - `shadowShift_n1_first_half_boundary_iff`
- The earlier normal forms from Exploration 11 remain in place and compiling:
  - `shadowShift_linear`
  - `shadowShift_n_sub_four`
  - `shadowShift_n_sub_three`
  - `shadowShift_n_sub_two`
  - `shadowShift_n_sub_one`
  - `shadowPerm_zero/one/two/mid/n_sub_two/n_sub_one`
  - `lt_two_mul_decompose_mod`
  - `mod_two_period_boundary`
  - `shadowPerm_first_half_boundary`

### Reformulations
- The right intermediate target is now even clearer:
  1. first-half familywise boundary lemmas,
  2. a second-half transport lemma,
  3. only then the assembled “boundary iff mover” statement.

LOAD-BEARING ASSESSMENT: yes. This narrows the next sweep attempt to a much smaller remaining interface and avoids repeating the failed monolithic proof pattern.

### Concrete Artifacts
STRUCTURAL RESULTS:
- For `r < n`, the first-half residue arithmetic is now explicitly characterized by shift family:
  - linear branch hits a boundary iff `r = i + 2`,
  - `n-4` branch hits iff `r = 0`,
  - `n-3` branch hits iff `r = n - 1`,
  - `n-2` branch hits iff `r = n - 2`,
  - `n-1` branch hits iff `r = 1`.

EXACT BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Construction` succeeds after the refactor.

FAILED SUB-ATTEMPT THAT WAS REPLACED:
- a monolithic `shadowPerm_first_half_boundary_only` / `shadowPerm_first_half_off_boundary` proof draft was abandoned because it was proof-engineering-heavy and non-compiling.

TRUST-BOUNDARY STATUS:
- No trust reduction landed directly in this exploration.
- Remaining live lower-bound axioms are still:
  - `canonicalShadow_dynamicCore`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### What Would Unblock This
- A lemma transporting the boundary predicate from residue `r` to `r + n`:
  - adding `n` should swap boundary values `0 ↔ n` and preserve the boundary/non-boundary dichotomy,
  - which would immediately lift the first-half family lemmas to the second half.
- After that, the assembled off-mover non-boundary theorem should be much shorter.

### Key Parameters
- Verification surface for this exploration:
  - `lake build LeanMn.LowerBound.Shadow.Construction`
- This pass remained fully inside `LeanMn/LowerBound/Shadow/Construction.lean`; no shared files changed.

### Open Questions
1. Can the second-half transport be stated generically in terms of the predicate
   `x % (2*n) = 0 ∨ x % (2*n) = n`, without referring to `shadowShift` at all?
2. Once that transport exists, is the best next theorem the full first+second-half “boundary iff mover” statement, or a directly usable off-mover stability corollary for closure?

## Exploration 13

### Strategy
Factor out the second-half sweep arithmetic generically: instead of proving five more familywise lemmas for `r + n`, prove once and for all that the boundary predicate
`x % (2*n) = 0 ∨ x % (2*n) = n`
is preserved when adding `n` modulo `2n`.

### Outcome
SUCCEEDED

### Failure Constraint
The only real obstacle was proof-engineering, not mathematics:
- the first version of the transport proof tried to synthesize the decomposition
  `x + n = (x % 2n + n) + q * 2n` via `omega`, which was too fragile,
- and the remaining rearrangement step was purely associative/commutative, so
  `ac_rfl` was the right tool instead of more arithmetic automation.

This does not expose a new mathematical blocker; it confirms that the transport
idea is sound and that the right proof shape is:
- `Nat.mod_add_div` for decomposition,
- `Nat.add_mul_mod_self_right` for the modulus drop,
- `ac_rfl` for the commutative rearrangement.

### What This Rules Out
It rules out duplicating the full first-half case split for the second half.
That would now just be wasted work.

### Surviving Structure
- [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean) now also contains:
  - `residue_boundary_add_n_iff`
  - `boundary_add_n_iff`
- The previously added first-half family lemmas remain compiling, so the sweep
  residue layer now has:
  - first-half familywise boundary characterizations,
  - and a generic bridge to the second half.
- Verified targets:
  - `lake build LeanMn.LowerBound.Shadow.Construction`
  - `lake build LeanMn.LowerBound.Shadow.Theorem LeanMn.LowerBound.CaseObstructions`

### Reformulations
- The second-half problem is no longer an independent case split. It is now a
  transport problem over the residue predicate itself.
- Concretely, the next sweep theorem should be assembled as:
  1. first-half family lemma,
  2. `boundary_add_n_iff`,
  3. lifted second-half statement,
  4. assembled boundary-iff-mover theorem.

LOAD-BEARING ASSESSMENT: yes. This removes an entire duplicated half of the
remaining sweep arithmetic.

### Concrete Artifacts
STRUCTURAL RESULTS:
- `residue_boundary_add_n_iff` proves the residue-level fact that adding `n`
  swaps the two boundary residues `{0, n}` on `Z_(2n)`.
- `boundary_add_n_iff` lifts that fact from residues to arbitrary natural
  expressions via `% (2*n)`.

EXACT TOOLING SHAPE THAT WORKED:
- `Nat.mod_add_div x (2 * n)` for the modular decomposition,
- `Nat.add_mul_mod_self_right` to discard the multiple of `2n`,
- `ac_rfl` for the final rearrangement of the `Nat` sum.

TRUST-BOUNDARY STATUS:
- No axiom was removed in this exploration.
- The remaining live lower-bound axioms are still:
  - `canonicalShadow_dynamicCore`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### What Would Unblock This
- The next likely-successful sweep theorem is now:
  - a first+second-half assembled “boundary iff mover” lemma, or
  - directly the off-mover non-boundary corollary needed for `shadow_active_stable`.
- Either should be substantially shorter now than the failed monolithic proof
  from Exploration 12’s abandoned sub-attempt.

### Key Parameters
- This exploration stayed entirely inside
  [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean).
- Global `lake build LeanMn` remains unavailable as a verification surface for
  this track because of the unrelated pre-existing failures in
  [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean).

### Open Questions
1. Is the next clean theorem the full boundary-iff-mover statement, or should
   the off-mover corollary be proved directly from the family lemmas plus
   `boundary_add_n_iff`?
2. Once the off-mover corollary exists, does the moved-coordinate equality or
   the `singlePrivileged` part become the next tighter sweep bottleneck?

## Exploration 14

### Strategy
Lift the proof-doc boundary characterizations from first-half residues to all
shadow steps `k < 2n`, so the sweep closure proof can reason in one statement
per shift family instead of splitting separately on `k < n` and `n ≤ k`.

### Outcome
SUCCEEDED

### Failure Constraint
The first implementation failed as a tactic-engineering issue: `simpa` on the
second-half branches recursively rewrote `k` and `k % n` through `hk_eq`,
causing a max recursion depth failure in the five lifted family lemmas.

### What This Rules Out
It rules out using broad `simp`/`simpa` normalization at the point where the
second-half decomposition `k = k % n + n` is applied. Any proof shape that
lets simplification rewrite both the outer step expression and the RHS residue
equation simultaneously is likely to loop again.

### Surviving Structure
- The branch decomposition from `mod_two_period_boundary` was already correct.
- The right proof shape is:
  1. rewrite `k` using the branch equality,
  2. rewrite the resulting residue once with `Nat.mod_eq_of_lt` or
     `mod_add_period`,
  3. finish by exact application of the first-half family theorem composed with
     `boundary_add_n_iff`.
- No change was needed to the actual modular mathematics; only the normalization
  discipline had to change.

### Reformulations
- The lifted sweep residue layer is now genuinely “all-k” rather than
  “first-half + manual transport”. This is the right public surface for the
  next closure theorem.

LOAD-BEARING ASSESSMENT: yes. The next mover/off-mover theorems can now be
stated directly for arbitrary `k < 2n`, which removes duplicated half-cycle
reasoning from the remaining shadow kernel.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added `mod_add_period`.
- Added the all-step family lemmas:
  - `shadowShift_linear_boundary_iff`
  - `shadowShift_n4_boundary_iff`
  - `shadowShift_n3_boundary_iff`
  - `shadowShift_n2_boundary_iff`
  - `shadowShift_n1_boundary_iff`
- Verified builds:
  - `lake build LeanMn.LowerBound.Shadow.Construction`
  - `lake build LeanMn.LowerBound.Shadow.Theorem LeanMn.LowerBound.CaseObstructions`

EXACT ERROR MESSAGE CLASS:
- `Tactic simp failed with a nested error: maximum recursion depth has been reached`
  on the second-half branches of the new lifted family lemmas.

EXACT PROOF SHAPE THAT WORKED:
- Replace
  `simpa [hk_eq, hkmod] using ...`
  with
  `rw [hk_eq, hkmod]; exact ...`
  so `% n` normalization happens once and only once.

TRUST-BOUNDARY STATUS:
- No axiom was removed in this exploration.
- The remaining live lower-bound axioms are still:
  - `canonicalShadow_dynamicCore`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### What Would Unblock This
- The next direct target is an assembled sweep theorem of the form:
  - boundary iff `i = shadowPerm (k mod n)`, or
  - off-mover non-boundary for `i ≠ shadowPerm (k mod n)`.
- Once that exists, `shadow_active_stable` should become usable for the closure
  proof without another six-way arithmetic split.

### Key Parameters
- File touched:
  [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean)
- Verified theorem-assembly surface:
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean)
  and
  [`LeanMn/LowerBound/CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean)
- Full `lake build LeanMn` remains unusable for this branch because of the
  unrelated pre-existing failures in
  [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean).

### Open Questions
1. Is the cleanest next lemma the exact boundary-iff-mover theorem, or is it
   better to prove the off-mover non-boundary corollary directly and defer the
   converse?
2. After closure is reconstructed, does single-privileged uniqueness still need
   independent work, or does it collapse once the mover theorem is explicit?

## Exploration 15

### Strategy
Use the new all-`k` boundary lemmas to prove the converse “boundary implies
predicted mover”, derive off-mover stability for canonical shadow configs, and
then replace the sweep axiom by a narrower mover-coordinate kernel.

### Outcome
SUCCEEDED

### Failure Constraint
The only real obstacle in this pass was dependent rewriting over `Fin`:
- `subst` on facts like `i.val = n - 4` failed because the goal still depended
  on `i` as a `Fin n`,
- and rewriting `k % n` directly inside `shadowPerm` generated motive errors
  because the proof argument to `Fin.mk` depends on the rewritten term.

The successful fix was to stay at value level:
- prove the desired `shadowPerm ... = ⟨..., by omega⟩` branchwise,
- then finish with `Fin.ext` and `congrArg Fin.val`.

### What This Rules Out
It rules out using `subst` or unconstrained `rw` as the default tool for the
remaining sweep `Fin` equalities. The stable pattern is:
- specialize the branch to a concrete residue,
- obtain a concrete `shadowPerm` equality,
- conclude by `Fin.ext`.

### Surviving Structure
- The all-`k` family boundary lemmas from Exploration 14 were exactly the right
  interface for the converse proof; no new arithmetic decomposition was needed.
- `shadow_active_stable` plus the new off-mover non-boundary theorem were enough
  to prove that every non-predicted shadow coordinate is unchanged from `k` to
  `k+1`.
- That off-mover preservation is strong enough to reconstruct full shadow
  closure from a kernel that only supplies the mover-coordinate update and
  privilegedness at the predicted mover.

### Reformulations
- The sweep dynamic core is now best stated as an **entry core**:
  1. the predicted mover `σ(k mod n)` is privileged at `s_k`,
  2. the moved coordinate in `move s_k σ(k mod n)` matches `s_{k+1}`,
  3. off-mover coordinates are proved in Lean, not trusted.

LOAD-BEARING ASSESSMENT: yes. This is a genuine trust-boundary reduction, not
just an internal helper refactor.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean):
  - `shadow_boundary_imp_perm`
  - `shadow_off_boundary_of_ne_perm`
- Added in
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `canonicalShadowConfig_off_mover_eq`
  - `canonicalShadowClosure_of_entryCore`

TRUST-BOUNDARY REDUCTION:
- Replaced the sweep axiom
  - `canonicalShadow_dynamicCore`
  that trusted full `shadowClosure` and `shadowSinglePriv`
- with the narrower sweep axiom
  - `canonicalShadow_entryCore`
  in
  [`LeanMn/LowerBound/CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean),
  which now trusts only:
  - privilegedness of the predicted mover at each shadow step,
  - the moved-coordinate equality at that mover,
  - and `shadowSinglePriv`.

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Construction`
- `lake build LeanMn.LowerBound.Shadow.Theorem`
- `lake build LeanMn.LowerBound.CaseObstructions LeanMn.LowerBound.Shadow.Theorem`
all succeed.

TRUST-BOUNDARY STATUS:
- Raw lower-bound axiom count is still 4.
- The sweep-side axiom is strictly smaller than before.
- The live trusted items are now:
  - `canonicalShadow_entryCore`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification`

### What Would Unblock This
- To eliminate the remaining sweep trust entirely, the next missing statement is
  no longer full closure. It is:
  - the mover-coordinate update / privilegedness theorem for the predicted
    shadow mover, and
  - independently, elimination of the residual `shadowSinglePriv` trust.
- Those are transition-function facts, not residue arithmetic facts. Any next
  sweep pass should target them directly instead of reworking the modular layer.

### Key Parameters
- Files changed this pass:
  - [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean)
  - [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean)
  - [`LeanMn/LowerBound/CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean)
- Global `lake build LeanMn` is still not the right verification surface for
  this branch because of the unrelated pre-existing failures in
  [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean).

### Open Questions
1. Is the next sweep target the mover-coordinate update theorem or the
   `shadowSinglePriv` elimination?
2. On the global trust boundary, is it now higher leverage to keep shrinking the
   sweep kernel, or to switch to `cycle_classification` / zero-winding coverage?

## Synthesis after exploration 15

Explorations 11–15 converged on a consistent pattern:
- The modular arithmetic was not the trusted content. It was the prerequisite
  for isolating exactly which parts of the sweep shadow proof still depend on
  transition-function semantics.
- Once the residue layer became explicit enough, the sweep kernel could be cut
  along the mathematically correct seam:
  - off-mover preservation is arithmetic,
  - mover-coordinate update and privilegedness are dynamics.

This changes the remaining search space. Another pass on sweep should not spend
time on more boundary algebra unless it directly serves one of these two
semantic targets:
- prove the predicted mover is privileged and updates to the shadow-next value,
- or prove unique privilegedness of the shadow configs.

If neither of those looks tractable soon, the best alternative is to leave the
sweep kernel where it now is and spend effort on the other remaining global
trusted items:
- `cycle_classification`
- `palindromic_zeroWinding_obstruction`
- `nonconsecutive_zeroWinding_obstruction`

## Exploration 16 (probe)

### Strategy
Test the semantic hypothesis suggested by the sweep formulas: for the predicted
shadow mover `p = σ(k mod n)`, there is a canonical waterfall index `j`
determined by whether the shadow center is active, and that good-cycle step
also has mover `p`.

### Outcome
SUCCEEDED

### Concrete Artifacts
COMPUTED EXAMPLES:
- Checked by script for `n = 5, 6, 7, 8` and all `k < 2n` that if
  `p = σ(k mod n)` and
  `j = p + (if shadow center at p is active then n else 0)`,
  then the shadow local triple at `p` matches the waterfall local triple at `j`.

STRUCTURAL RESULTS:
- Added in
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadowMatchIndex`
  - `shadowMatchIndex_moverAt`
- `shadowMatchIndex_moverAt` proves the key indexing fact:
  the canonical waterfall step chosen from the shadow center-activity rule has
  mover exactly `shadowPerm (k mod n)`.

REPRESENTATIONS:
- The remaining mover-update theorem is now representable as:
  1. construct `j = shadowMatchIndex wc hn k`,
  2. prove the shadow and waterfall local triples agree at processor
     `p = shadowPerm (k mod n)`,
  3. transport privilegedness and moved-coordinate output from the good step `j`.

## Exploration 17 (semantic bridge)

### Strategy
Finish the sweep-side semantic bridge suggested by Exploration 16:
- prove the predicted mover itself is always a boundary-hitting coordinate in
  the canonical shadow (`shadow_boundary_at_perm`),
- use that to identify the waterfall center value at the matched index `j`,
- then package the dynamic part of `canonicalShadow_entryCore` as a pure local
  transport theorem from the matched good-cycle step.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean):
  - `shadow_boundary_at_perm`
- Added in
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadowMatchIndex_center_eq`
  - `shadow_entryCore_of_local_context`

SEMANTIC REFACTORING:
- `shadowMatchIndex_center_eq` proves the center-coordinate equality between the
  canonical shadow state `s_k` and the matched waterfall state
  `g_{shadowMatchIndex wc hn k}` at the predicted mover
  `p = shadowPerm (k mod n)`.
- `shadow_entryCore_of_local_context` shows that once the left/center/right
  local triple at `p` agrees between `s_k` and the matched waterfall state, and
  the next shadow center agrees with the next waterfall center, the entire
  mover-update / privilegedness part of `canonicalShadow_entryCore` follows in
  Lean.

TRUST-BOUNDARY STATUS:
- Raw lower-bound axiom count is still 4.
- This pass did not eliminate `canonicalShadow_entryCore`, but it changed its
  effective content:
  the remaining sweep trust is now concentrated in proving the local-context
  equalities needed by `shadow_entryCore_of_local_context`, together with the
  separate `shadowSinglePriv` kernel.

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Construction`
- `lake build LeanMn.LowerBound.Shadow.Theorem`
both succeed.

### What Would Unblock This
- The next sweep pass should target the two missing hypotheses of
  `shadow_entryCore_of_local_context` that are not yet formalized:
  - left/right local-context equality between `canonicalShadowConfig wc k` and
    `wc.configs.get (shadowMatchIndex wc hn k)`,
  - next-center equality between the shadow successor and the matched waterfall
    successor.
- If those land, the dynamic half of `canonicalShadow_entryCore` can be
  replaced directly, leaving only `shadowSinglePriv` on the sweep side.

## Exploration 18 (neighborhood arithmetic probe)

### Strategy
Try to formalize the matched-waterfall neighborhood arithmetic needed for the
remaining local-context proof:
- prove explicit active-interval formulas at `left p` and `right p` for
  `j = shadowMatchIndex wc hn k`,
- use those to bridge the two remaining local equalities in
  `shadow_entryCore_of_local_context`.

### Outcome
STALLED

### Concrete Artifacts
COMPUTED EXAMPLES:
- Checked by script for `n = 5, 6, 7, 8, 9, 10` and all `k < 2n` that for
  `p = shadowPerm (k mod n)` and `j = shadowMatchIndex wc hn k`, the matched
  waterfall neighborhood obeys the clean arithmetic patterns:
  - waterfall active at `left p` iff
    `shadowActive n k (shadowShift n p) ↔ p.val = 0`
  - waterfall active at `right p` iff
    `shadowActive n k (shadowShift n p) ↔ p.val ≠ n - 1`

FAILED SUB-ATTEMPT THAT WAS REPLACED:
- I tried to land these as Lean lemmas directly in
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean),
  but reverted the entire patch after the proof shape degraded into repeated
  normalization failures under `dsimp [shadowMatchIndex]`.

### Exact Blocker
- The obstacle was not the arithmetic statement itself. It was representation:
  `dsimp [shadowMatchIndex]` eagerly expands `left/right` and the `Fin`-valued
  matched index into `% n` / `% (2n)` expressions.
- After that expansion, ordinary `rw` steps stop matching the target terms
  reliably, and the proof turns into brittle transport over normalized
  expressions rather than actual mathematical work.
- Concretely, the promising formulas above are probably best proved either:
  - in a dedicated arithmetic helper layer before `shadowMatchIndex` is
    introduced, or
  - via small normalization lemmas about the expanded `% n` expressions, rather
    than by trying to rewrite `left p` / `right p` after `dsimp`.

### Surviving Takeaways
- The semantic target from Exploration 17 still looks correct.
- The next useful sweep pass should not attack the local-context equalities
  directly inside `shadowMatchIndex` again. It should first factor the needed
  `left/right` modulo-normalization lemmas into a lower-level arithmetic layer,
  then retry the neighborhood equalities from that cleaner representation.

## Exploration 19 (normalization layer)

### Strategy
Land the exact `% n` normalization lemmas that Exploration 18 was missing, but
without retrying the full neighborhood proof in the same pass.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `left_val_eq_last_of_val_zero`
  - `left_val_eq_pred_of_val_ne_zero`
  - `right_val_eq_zero_of_val_last`
  - `right_val_eq_succ_of_val_ne_last`

WHY THESE MATTER:
- These lemmas package exactly the `left/right` modulo-normalizations that were
  derailing the matched-neighborhood arithmetic under
  `dsimp [shadowMatchIndex]`.
- They do not shrink the trust boundary directly, but they remove the specific
  proof-shape blocker that caused Exploration 18 to fail.

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Theorem`
  succeeds after adding the normalization layer.

### What Would Unblock This
- With these four lemmas in place, the next sweep pass can retry the matched
  neighborhood arithmetic one branch lower:
  prove the left/right waterfall-active formulas first, then use them to attack
  the remaining local-context equalities needed by
  `shadow_entryCore_of_local_context`.

## Exploration 20 (waterfall-side interval bridge)

### Strategy
Take one concrete step toward the remaining local-context equalities by proving
the matched-waterfall side of the neighborhood formulas:
- convert the waterfall active predicate at `left p` / `right p` into interval
  inequalities using `waterfall_active_iff`,
- then discharge the four arithmetic cases from
  `j = shadowMatchIndex wc hn k = p + (if active then n else 0)`.

### Outcome
PARTIALLY SUCCEEDED

### Concrete Artifacts
SUCCESSFUL CHANGE:
- In
  [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean),
  promoted
  - `waterfall_active_iff`
  from `private` to exported theorem status.
- This is a genuine infrastructure improvement: the clean interval form of the
  waterfall predicate is now available from
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean)
  without duplicating the proof.

FAILED SUB-ATTEMPT THAT WAS REPLACED:
- I attempted to add two new theorems in
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean)
  formalizing the matched-waterfall activity at `left p` and `right p`.
- The arithmetic statement was consistent with brute-force checks and with the
  intended proof-doc formulas, but the proof script stalled inside `omega`
  after `simp` had expanded the interval goals into a mix of normalized `% n`
  residues and raw `Fin` projections.
- I reverted those non-compiling theorem additions and restored the previous
  green state.

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Construction LeanMn.LowerBound.Shadow.Theorem`
  succeeds after reverting the failed theorem attempt.

### Exact Blocker
- The current obstacle is narrower than before:
  the exported `waterfall_active_iff` now gives the correct interval shape, but
  `omega` is still not strong enough after `simp` turns those interval goals
  into mixed normalized residue expressions involving `(left p).val` /
  `(right p).val`.
- So the next successful pass probably needs one more explicit arithmetic layer:
  not about the whole shadow proof, just enough lemmas to normalize the
  interval endpoints before `omega` is invoked.

## Exploration 21 (matched-waterfall activity)

### Strategy
Retry the matched-neighborhood arithmetic from Exploration 20, but now use the
new endpoint normalization lemmas directly:
- keep `waterfall_active_iff` in interval form,
- rewrite `shadowMatchIndex` to `p.val + if active then n else 0`,
- normalize `(left p).val` / `(right p).val` by case-splitting on
  `p.val = 0` and `p.val = n - 1`,
- and only then hand the interval goals to `omega`.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`LeanMn/LowerBound/Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadowMatchIndex_left_waterfall_active`
  - `shadowMatchIndex_right_waterfall_active`

WHAT THEY PROVE:
- For `p = shadowPerm n hn (k mod n)` and
  `j = shadowMatchIndex wc hn k`, the matched waterfall state satisfies:
  - activity at `left p` iff `shadowActive ... p ↔ p.val = 0`
  - activity at `right p` iff `shadowActive ... p ↔ p.val ≠ n - 1`
- This settles the waterfall side of two of the missing local-context inputs
  for `shadow_entryCore_of_local_context`.

WHY THIS MATTERS:
- The remaining sweep gap is no longer “what does the matched waterfall step
  do near the mover?” for the left/right processors.
- The remaining work is now to prove the corresponding shadow-side activity
  characterizations and then convert both sides to actual coordinate equality.

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Theorem`
  succeeds after adding these two lemmas.

### What Would Unblock This
- The next useful step is to prove the shadow-side formulas for
  `shadowActive n k (shadowShift n (left p))` and
  `shadowActive n k (shadowShift n (right p))`, then combine them with the new
  matched-waterfall activity lemmas and `shadow_val_eq_ite` to derive:
  - equality at `left p`
  - equality at `right p`
- Once those local equalities are in place, the dynamic half of
  `canonicalShadow_entryCore` becomes a realistic elimination target.

## Exploration 22

### Strategy
Try to prove the missing shadow-side neighborhood formulas in one shot by
splitting them into first-half residue cases and transporting the second half
with an explicit `+ n` active-flip lemma.

### Outcome
PARTIALLY SUCCEEDED

### Failure Constraint
The large theorem shape was too brittle: rewriting `k = k % n` / `k = k % n + n`
under `shadowPerm ... ⟨_, _⟩` and under `left/right`-dependent `Fin` terms caused
dependent rewrite failures, and the branchwise proofs were too sensitive to the
exact syntactic form of `shadowActive` to be a stable unit.

### What This Rules Out
It rules out trying to land the full left/right shadow-side characterization as
one monolithic theorem with six residue classes plus second-half transport in a
single pass. The better unit is a smaller arithmetic interface that the theorem
layer can consume incrementally.

### Surviving Structure
- The half-cycle transport lemma is now proved in
  [`LeanMn/LowerBound/Shadow/Construction.lean`](./lean/LeanMn/LowerBound/Shadow/Construction.lean):
  - `shadowActive_add_n_iff_not`
- The reusable shadow-active characterizations are now public instead of
  `private`:
  - `linear_shift_lower`
  - `linear_shift_upper`
  - `shadow_n4_active`
  - `shadow_n3_active`
  - `shadow_n2_active`
  - `shadow_n1_active`

### Reformulations
- The useful representation is now:
  1. prove first-half shadow activity at the needed neighbors,
  2. use `shadowActive_add_n_iff_not` to transport to the second half,
  3. only then combine with the already-proved matched-waterfall activity
     lemmas in [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean).

LOAD-BEARING ASSESSMENT: yes. This is a better decomposition than the failed
single-theorem attempt because it separates the stable arithmetic transport
from the `Fin`-heavy neighborhood identification.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added:
  - `shadowActive_add_n_iff_not`
- Exported:
  - `linear_shift_lower`
  - `linear_shift_upper`
  - `shadow_n4_active`
  - `shadow_n3_active`
  - `shadow_n2_active`
  - `shadow_n1_active`

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Construction` passes.
- `lake build LeanMn.LowerBound.Shadow.Theorem` passes.

### What Would Unblock This
- The next clean target is a first-half-only theorem for either `left p` or
  `right p`, written directly against the now-public active lemmas and avoiding
  any dependent rewrite of `shadowPerm` indices.
- Once one side lands cleanly, the other side should follow the same pattern,
  and `shadowActive_add_n_iff_not` can supply the second-half cases.

## Exploration 23

### Strategy
Use the new public active lemmas plus the `+ n` flip theorem to prove the left
shadow-side bridge in [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
first a first-half `left p` activity theorem, then its all-`k` transport, then
the actual coordinate equality
`canonicalShadowConfig wc k (left p) = (wc.configs.get j) (left p)`.

### Outcome
FAILED

### Failure Constraint
Even after factoring out `r := k % n` and `p := shadowPerm ... r`, the proof
still failed for two structural reasons:
- branchwise simplification of the first-half theorem kept leaving arithmetic
  side-goals such as `¬(n - 4 = 0)` and `¬(n - 3 = 0)` in places where `simp`
  did not close automatically, so the case tree remained brittle;
- in the final equality lemma, `wc.waterfall j (left p)` stayed as an `if` over
  the waterfall active predicate at `left p`, and the attempt to refine it with
  `hcond` was not robust enough to coerce Lean to the exact branch equation.

### What This Rules Out
It rules out trying to jump straight from the active iff formulas to the actual
left-coordinate equality in one pass. The stable next unit is smaller:
first isolate a branch-clean first-half activity theorem, then separately prove
the `wc.waterfall` branch extraction helper for `left p`.

### Surviving Structure
- The representation `r := k % n`, `p := shadowPerm ... r` is still the right
  one; it avoided the earlier dependent-rewrite failure mode.
- The attempt showed that the remaining left-side proof is blocked more by
  branch extraction and local simplification shape than by missing global
  arithmetic facts.
- I reverted the non-compiling additions and restored the previous green state.

### Concrete Artifacts
BUILD RESULTS:
- After reverting the failed additions,
  `lake build LeanMn.LowerBound.Shadow.Theorem` passes again.

### What Would Unblock This
- A tiny helper that extracts the `then`/`else` branch of `wc.waterfall j q`
  from a proved activity proposition at `q`.
- A first-half left-shadow theorem proved with explicit local lemmas for each
  residue class, but without bundling the subsequent equality proof into the
  same attempt.

## Exploration 24

### Strategy
Keep the Exploration 23 decomposition, but make it fully branch-local:
1. add a first-half-only left-neighbor theorem for the shadow activity,
2. transport the second half with `shadowActive_add_n_iff_not`,
3. add a tiny `waterfall_eq_ite` wrapper for branch extraction, and
4. use the already-proved matched-waterfall activity iff to conclude the actual
   left-coordinate equality
   `canonicalShadowConfig wc k (left p) = (wc.configs.get j) (left p)`.

### Outcome
SUCCESS

### What Landed
- Added local arithmetic transport helpers:
  - `lt_two_mul_decompose_mod_local`
  - `mod_two_period_boundary_local`
  - `mod_add_period_local`
- Proved the shadow-side left-neighbor activity bridge:
  - `shadow_left_first_half_active`
  - `shadow_left_active`
- Added the branch extraction wrapper:
  - `waterfall_eq_ite`
- Proved the actual matched-coordinate equality:
  - `shadowMatchIndex_left_eq`

### Why It Matters
- The shadow/waterfall local-context bridge now covers `left p` and `p`
  outright, rather than only the center coordinate.
- The remaining semantic gap inside the sweep kernel is now concentrated in:
  - the symmetric `right p` coordinate, and
  - the matched next-step equality at `p`.
- This is a real de-risking move for eliminating
  `canonicalShadow_entryCore`, because `shadow_entryCore_of_local_context`
  already packages the final privileged/move conclusion once those local
  equalities are available.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadow_left_first_half_active`
  - `shadow_left_active`
  - `waterfall_eq_ite`
  - `shadowMatchIndex_left_eq`

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Theorem` passes.

### What Would Unblock This Further
- Prove the right-neighbor analogue of `shadowMatchIndex_left_eq`.
- Then determine whether the required next-step center equality is derivable by
  reindexing `shadowMatchIndex_center_eq`, or whether it needs its own matched
  index lemma.

## Exploration 25

### Strategy
Push the local-context bridge one coordinate further by mirroring the left-side
proof for `right p`:
1. prove a first-half right-neighbor shadow activity theorem,
2. transport it to all `k` using the same `+ n` complement argument,
3. combine it with the already-proved
   `shadowMatchIndex_right_waterfall_active`, and
4. conclude the actual coordinate equality
   `canonicalShadowConfig wc k (right p) = (wc.configs.get j) (right p)`.

### Outcome
SUCCESS

### What Landed
- Added:
  - `shadow_right_first_half_active`
  - `shadow_right_active`
  - `shadowMatchIndex_right_eq`

### Why It Matters
- The shadow/waterfall local-context bridge now covers the full neighborhood
  of the predicted mover: `left p`, `p`, and `right p`.
- This means the remaining dynamic gap inside the sweep kernel is no longer
  “local context at step `k`”; it is now only the matched next-step center
  equality plus the still-external single-privilegedness statement.
- That sharply lowers the risk that `canonicalShadow_entryCore` hides any
  additional neighborhood reasoning.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadow_right_first_half_active`
  - `shadow_right_active`
  - `shadowMatchIndex_right_eq`

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Theorem` passes.

### What Would Unblock This Further
- Prove the next-step center equality
  `canonicalShadowConfig wc (k+1) p = (wc.configs.get (nextIndex wc.configs j)) p`.
- Then feed `left/center/right/next` directly into
  `shadow_entryCore_of_local_context` and reduce the sweep axiom to
  `shadowSinglePriv` alone.

## Exploration 26

### Strategy
Try to finish the dynamic half of the sweep kernel in one pass by adding:
1. a shadow-side next-center toggle theorem,
2. the matched waterfall next-center activity iff,
3. the resulting next-center coordinate equality, and
4. then use `left/center/right/next` to discharge the local-context package.

### Outcome
FAILED

### Failure Constraint
This attempt mixed two separate difficulties in one block:
- the shadow-side proof still needed a cleaner way to talk about the predicted
  mover residue at step `k + 1`, and
- the waterfall-side proof introduced dependent `Fin` rewrites through
  `nextIndex`, which made ordinary `rw` / `simp` brittle even when the
  arithmetic statement itself was straightforward.

The result was a large non-compiling block where the underlying arithmetic was
still plausible, but the proof shape was too entangled to debug efficiently in
place.

### What This Rules Out
- It rules out bundling the shadow-side toggle and the matched-waterfall
  next-step equality into the same proof attempt.
- It also rules out using direct `rw` over `nextIndex`-dependent goals as the
  main normalization strategy for this step.

### Surviving Structure
- The real remaining sweep gap is still only the next-step center value; the
  `left/center/right` current-step neighborhood bridge remains green.
- The right decomposition is now:
  1. prove the shadow-side next-center toggle alone,
  2. then prove a separate `jnext`-normalization layer for the matched
     waterfall step, and
  3. only then assemble the next-center equality.
- I reverted the failed additions and restored the last green theorem state.

### Concrete Artifacts
BUILD RESULTS:
- After reverting the failed additions,
  `lake build LeanMn.LowerBound.Shadow.Theorem` passes again.

### What Would Unblock This Further
- A small helper layer that names the predicted step successor explicitly
  (`knext`, `jnext`) and proves only the shadow-side center toggle before any
  waterfall reasoning is attempted.

## Exploration 27

### Strategy
Retry the failed next-step work at the smallest surviving unit:
prove only the shadow-side center toggle for the predicted mover, using the
already-proved boundary theorem and a named residue
`r := (k + shadowShift p) % (2n)`.

### Outcome
SUCCESS

### What Landed
- Added:
  - `shadow_center_next_active`

### Why It Matters
- The shadow side of the remaining sweep gap is now isolated and proved:
  at the predicted mover, step `k + 1` flips the active status exactly because
  the step-`k` residue is forced to be one of the two boundary values `{0, n}`.
- That means the only missing semantic work for the dynamic half of
  `canonicalShadow_entryCore` is now on the waterfall side:
  normalizing the matched successor index `jnext := nextIndex wc.configs j`
  and proving the corresponding next-center activity/value fact there.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadow_center_next_active`

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Theorem` passes.

### What Would Unblock This Further
- A small `jnext` normalization layer on the waterfall side, ideally phrased in
  terms of `j.val = p.val` or `j.val = p.val + n`, without bundling the final
  equality proof into the same attempt.

## Exploration 28

### Strategy
Keep the successor-step work on the waterfall side strictly at the activity
level:
1. name the matched successor index `jnext := nextIndex wc.configs j`,
2. normalize `jnext.val` in the three relevant cases
   (`j = p`, `j = p + n` with and without wrap), and
3. prove only the next-center waterfall activity iff, leaving the actual value
   equality for the next pass.

### Outcome
SUCCESS

### What Landed
- Added:
  - `shadowMatchIndex_next_center_waterfall_active`

### Why It Matters
- The shadow side and waterfall side now agree on the next-step center activity
  predicate, which is exactly the final boolean ingredient needed for the
  matched next-center value equality.
- This removes the last major arithmetic uncertainty in the sweep kernel. What
  remains is the same `shadow_val_eq_ite` assembly pattern that already worked
  for `left p`, `p`, and `right p`.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadowMatchIndex_next_center_waterfall_active`

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Theorem` passes.

### What Would Unblock This Further
- Assemble `shadow_center_next_active` and
  `shadowMatchIndex_next_center_waterfall_active` into the actual next-center
  equality `canonicalShadowConfig wc (k+1) p = (wc.configs.get jnext) p`.
- Then feed `left/center/right/next` into
  `shadow_entryCore_of_local_context` and reduce the sweep axiom to
  `shadowSinglePriv`.

## Exploration 29

### Strategy
Use the two aligned activity iff lemmas from Explorations 27 and 28 to build
the actual next-step center value equality with the same
`shadow_val_eq_ite` pattern that already worked for `left p`, `p`, and
`right p`.

### Outcome
SUCCESS

### What Landed
- Added:
  - `shadowMatchIndex_next_center_eq`

### Why It Matters
- The local-context package for the dynamic half of the sweep kernel is now
  complete: `left`, `center`, `right`, and the matched next-center value are
  all proved in Lean.
- That means the remaining external content of `canonicalShadow_entryCore`
  should now be reducible to `shadowSinglePriv` alone, provided the new local
  equalities are wired into `shadow_entryCore_of_local_context`.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `shadowMatchIndex_next_center_eq`

BUILD RESULTS:
- `lake build LeanMn.LowerBound.Shadow.Theorem` passes.

### What Would Unblock This Further
- Feed `shadowMatchIndex_left_eq`, `shadowMatchIndex_center_eq`,
  `shadowMatchIndex_right_eq`, and `shadowMatchIndex_next_center_eq` into
  `shadow_entryCore_of_local_context`.
- Then replace the current sweep axiom with a much narrower
  `canonicalShadow_singlePriv`.

## Exploration 30

### Strategy
Wire the completed local-context package into the existing
`shadow_entryCore_of_local_context` theorem, then remove the dynamic half of the
sweep obstruction from the external kernel.

### Outcome
SUCCESS

### What Landed
- Added:
  - `canonicalShadow_entry_of_local_context`
- Replaced the old sweep axiom
  `canonicalShadow_entryCore`
  with the narrower axiom
  `canonicalShadow_singlePriv`

### Why It Matters
- The dynamic shadow entry behavior at the predicted mover is now fully proved
  in Lean.
- The sweep trust boundary has materially shrunk: the only remaining external
  sweep content is uniqueness of the privileged mover on the canonical shadow.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added in
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean):
  - `canonicalShadow_entry_of_local_context`
- Narrowed in
  [`CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean):
  - `canonicalShadow_entryCore` removed
  - `canonicalShadow_singlePriv` added

BUILD RESULTS:
- `lake build LeanMn.LowerBound.CaseObstructions LeanMn.LowerBound.Shadow.Theorem`
  passes.

### Updated Trust Surface
- `canonicalShadow_singlePriv`
- `palindromic_zeroWinding_obstruction`
- `nonconsecutive_zeroWinding_obstruction`
- `cycle_classification`

## Exploration 31

### Strategy
Test whether `canonicalShadow_singlePriv` is actually true under the current
`WaterfallCycle` abstraction by constructing an explicit small waterfall system
whose transition rule is determined only by the mover local triples seen in the
good cycle.

### Outcome
FAILED

### Failure Constraint
The statement appears false under the current abstraction, not merely unproved.
For an all-binary `n = 5` waterfall system, the canonical shadow has two
privileged processors at multiple steps. That means any approach that tries to
derive `canonicalShadow_singlePriv` from the current `WaterfallCycle` fields
alone is aiming at a false target.

### What This Rules Out
It rules out continuing the sweep trust-shrink plan by proving
`canonicalShadow_singlePriv` as currently stated. Any such proof would have to
smuggle in extra assumptions not present in `WaterfallCycle`, because the
present abstraction admits counterexamples.

### Surviving Structure
- The failure is not in the dynamic part of the shadow proof. The previously
  proved closure package remains sound and useful.
- The surviving mathematical seam is now clearer:
  - the canonical shadow closure/dynamics can be formalized from the waterfall
    arithmetic and local-context matching;
  - the single-privileged claim needs stronger semantic assumptions than the
    current `WaterfallCycle` interface provides.

### Reformulations
- The right question is no longer “how do we prove
  `canonicalShadow_singlePriv`?” but “what strengthened hypothesis or narrower
  shadow theorem is actually true and sufficient for the lower-bound argument?”
- Candidate directions exposed by this counterexample:
  - strengthen `WaterfallCycle` with an explicit P5/escape-style semantic
    hypothesis,
  - replace `canonicalShadow_singlePriv` with a theorem about a smaller class
    of systems,
  - or abandon sweep single-privilegedness as the next target and pivot to a
    different remaining axiom.

LOAD-BEARING ASSESSMENT: yes. This changes the search space decisively because
it identifies the current target theorem as false under the present
abstraction.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Counterexample witness family:
  - ring size `n = 5`,
  - all processors binary,
  - good configs
    `g_j[i] = 1` iff `1 ≤ (j + 2n - i) % (2n) ≤ n`,
  - local rule at processor `i`:
    toggle the center bit exactly on the mover patterns seen in the good cycle,
    otherwise hold the center bit fixed.
- For this system, the waterfall good cycle is valid with unique mover
  schedule `j mod n`:
  - `j = 0`: cfg `(0,0,0,0,0)`, privileged `[0]`
  - `j = 1`: cfg `(1,0,0,0,0)`, privileged `[1]`
  - `j = 2`: cfg `(1,1,0,0,0)`, privileged `[2]`
  - `j = 3`: cfg `(1,1,1,0,0)`, privileged `[3]`
  - `j = 4`: cfg `(1,1,1,1,0)`, privileged `[4]`
  - `j = 5`: cfg `(1,1,1,1,1)`, privileged `[0]`
  - `j = 6`: cfg `(0,1,1,1,1)`, privileged `[1]`
  - `j = 7`: cfg `(0,0,1,1,1)`, privileged `[2]`
  - `j = 8`: cfg `(0,0,0,1,1)`, privileged `[3]`
  - `j = 9`: cfg `(0,0,0,0,1)`, privileged `[4]`
- Canonical shadow states with multiple privileged processors:
  - `k = 0`: cfg `(1,0,0,1,0)`, privileged `[1,4]`
  - `k = 2`: cfg `(1,1,0,1,1)`, privileged `[0,3]`
  - `k = 4`: cfg `(0,1,0,0,1)`, privileged `[2,4]`
  - `k = 5`: cfg `(0,1,1,0,1)`, privileged `[1,4]`
  - `k = 7`: cfg `(0,0,1,0,0)`, privileged `[0,3]`
  - `k = 9`: cfg `(1,0,1,1,0)`, privileged `[2,4]`

STRUCTURAL RESULTS:
- In the all-binary waterfall family, the mover patterns at processor `i` are:
  - `i = 0`: `(0,0,0)` and `(1,1,1)`
  - `1 ≤ i ≤ n - 2`: `(1,0,0)` and `(0,1,1)`
  - `i = n - 1`: `(1,0,1)` and `(0,1,0)`
- These mover-pattern sets are disjoint from the non-mover patterns at the same
  processor, so the above transition rule yields a valid single-privileged
  waterfall good cycle.

TOOLS:
- One-off Python probes were enough to validate the witness family and list the
  shadow steps with multiple privileged processors.

### What Would Unblock This
- A user-level decision about theorem shape:
  - strengthen the sweep hypothesis/interface,
  - replace the false axiom with a true narrower statement,
  - or pivot effort to a different remaining trust target.

### Key Parameters
- Tested `n = 5` explicitly end-to-end.
- Pattern probes for `n = 5..10` show the same qualitative obstruction: the
  canonical shadow often contains more than one processor whose local pattern
  matches a mover context.

### Open Questions
1. What is the weakest additional semantic hypothesis that restores the
   single-privileged shadow claim?
2. Is the best next move to repair the sweep statement, or to leave it trusted
   and spend effort on `cycle_classification` / the zero-winding kernels?

## Exploration 32

### Strategy
Audit the `ShadowTrap` / `shadowTrap_not_converges` dependency chain to see
whether the remaining sweep axiom `canonicalShadow_singlePriv` is actually used
by the nonconvergence contradiction, rather than trying to repair a statement
already shown false by exploration 31.

### Outcome
SUCCEEDED

### What Landed
- Removed the `single_priv` field from `ShadowTrap`.
- Removed the `shadowSinglePriv` hypothesis from `shadow_gives_trap`.
- Deleted the axiom `canonicalShadow_singlePriv`.

### Why It Matters
- The false sweep theorem did not need to be repaired; it was dead interface
  weight.
- The shadow obstruction now depends only on the parts already proved in Lean:
  closure, distinctness, disjointness, and the bad-step cycle argument.
- This is an actual axiom-count reduction, not just a narrowing of a trusted
  kernel.

### Concrete Artifacts
STRUCTURAL RESULTS:
- In
  [`MNU.lean`](./lean/LeanMn/LowerBound/MNU.lean),
  `shadowTrap_not_converges` does not use single-privilegedness; the field was
  removable from `ShadowTrap`.
- In
  [`Shadow/Theorem.lean`](./lean/LeanMn/LowerBound/Shadow/Theorem.lean),
  `shadow_gives_trap` now assembles the trap without any
  `shadowSinglePriv` hypothesis.
- In
  [`CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean),
  `canonicalShadow_singlePriv` is gone.

BUILD RESULTS:
- `lake env lean LeanMn/LowerBound/CaseObstructions.lean` passes.
- `lake env lean LeanMn/LowerBound/Shadow/Theorem.lean` passes.
- A grep over `LeanMn/LowerBound` now reports only three axioms:
  `cycle_classification`,
  `palindromic_zeroWinding_obstruction`,
  `nonconsecutive_zeroWinding_obstruction`.

### Updated Trust Surface
- `palindromic_zeroWinding_obstruction`
- `nonconsecutive_zeroWinding_obstruction`
- `cycle_classification`

## Exploration 33

### Strategy
Replace the Case 3b/3c dependency path
`cycle_classification → nonconsecutive_zeroWinding_obstruction`
with the companion-note direct theorem for non-consecutive binary, so the
non-consecutive branch no longer depends on cycle classification at all.

### Outcome
FAILED

### Failure Constraint
The theorem-shape refactor itself was coherent, but validating it required a
rebuild of `CaseObstructions` that transitively replayed
[`MNU.lean`](./lean/LeanMn/LowerBound/MNU.lean)
and never cleared within a practical iteration window. The attempted parallel
checks also raced stale `.olean` state, so the fast feedback loop was not
trustworthy.

### What This Rules Out
It rules out using `CaseObstructions`-level branch refactors as a “quick win”
unless I am willing to pay the full transitive rebuild cost or first isolate a
smaller verification surface. The idea is not mathematically ruled out, but it
is not a good immediate trust-shrink tactic under the current local workflow.

### Surviving Structure
- The companion-note route is still structurally attractive:
  - for Case 3b/3c, a single direct theorem would remove the branch’s runtime
    dependence on `cycle_classification`;
  - the affected theorem signatures in
    [`EntryConflict/NonConsecutive.lean`](./lean/LeanMn/LowerBound/EntryConflict/NonConsecutive.lean),
    [`Wiggle/Theorem.lean`](./lean/LeanMn/LowerBound/Wiggle/Theorem.lean),
    and
    [`Theorem.lean`](./lean/LeanMn/LowerBound/Theorem.lean)
    can be rewritten coherently.
- The patch was fully reverted, and the previous green state was restored.

### Reformulations
- There are two distinct classes of trust-shrink move:
  1. local interface surgery that can be validated from already-hot modules
  2. branch rewiring through `CaseObstructions`, which currently triggers a much
     heavier rebuild boundary

LOAD-BEARING ASSESSMENT: yes. This changes which edits are economically viable
mid-turn. The next good move should stay inside lighter modules or avoid
touching `CaseObstructions` unless the expected shrink is large enough to
justify the rebuild.

### Concrete Artifacts
STRUCTURAL RESULTS:
- The direct non-consecutive theorem shape is syntactically consistent on the
  edited files, but not yet landed due to verification cost.

BUILD RESULTS:
- After reverting, the green checkpoint is restored:
  - `lake env lean LeanMn/LowerBound/Theorem.lean` passes.
  - `lake env lean LeanMn/LowerBound/Wiggle/Theorem.lean` passes.

### What Would Unblock This
- Either a smaller verification target for `CaseObstructions` / `MNU`, or a
  stronger confidence path that avoids rebuilding those modules on every branch
  refactor.

### Open Questions
1. Is the next best trust-shrink move now a lighter `Theorem.lean` /
   `GoodCycleBasics.lean` factoring pass around `cycle_classification`?
2. Or should the next `CaseObstructions` edit be reserved for a larger raw
   axiom-count drop rather than a dependency-graph cleanup?

## Exploration 34

### Strategy
Take the lighter `Theorem.lean` / `GoodCycleBasics.lean` path from
Exploration 33: prove the pure non-sweep arithmetic locally, then refactor
`cycle_classification` so the trusted residue only covers the genuinely hard
pieces from the proof doc, namely sweep canonicalization and odd-winding
exclusion.

### Outcome
PARTIAL SUCCESS

### What Landed
- In
  [`GoodCycleBasics.lean`](./lean/LeanMn/LowerBound/GoodCycleBasics.lean),
  proved
  `GoodCycle.zeroWinding_or_isOddWinding_of_not_sweep`.
  This packages the already-formalized modular-displacement argument into the
  exact local theorem the phase-10 assembly wants: a non-sweep cycle cannot
  have any displacement other than `0` or `±n`.
- In
  [`Theorem.lean`](./lean/LeanMn/LowerBound/Theorem.lean),
  replaced the old trusted statement `cycle_classification` with the smaller
  residual axiom `cycle_classification_residual`, which now trusts only:
  1. `gc.isSweep -> ∃ wc, wc.toGoodCycle = gc`
  2. `gc.isOddWinding -> False`
  and proves `cycle_classification` from those residual obligations plus the
  new `GoodCycleBasics` theorem.

### Trust Impact
- Raw axiom count in `LeanMn/LowerBound` stays at `3`.
- The phase-10 kernel is materially smaller: it no longer trusts the easy
  non-sweep reduction to zero-or-odd winding.
- The live lower-bound trust surface is now:
  - `cycle_classification_residual`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`

### Verification
- `lake env lean LeanMn/LowerBound/GoodCycleBasics.lean` passes.
- `lake env lean LeanMn/LowerBound/Theorem.lean` passes.
- `rg -n "^axiom " LeanMn/LowerBound` now reports:
  `cycle_classification_residual`,
  `palindromic_zeroWinding_obstruction`,
  `nonconsecutive_zeroWinding_obstruction`.

### Surviving Structure
- The proof-doc phase-10 residue is now exposed in the right shape:
  the next honest targets are exactly the two sub-obligations inside
  `cycle_classification_residual`.
- This also confirms the lighter-module strategy is productive: meaningful
  trust shrink was possible without touching `CaseObstructions` or paying the
  `MNU` rebuild cost.

## Exploration 35

### Strategy
Test whether the remaining phase-10 residue is even true under the current
formal `GoodCycle` abstraction before trying to prove it. If the statement is
too broad, narrow the trusted interface to the way it is actually used in the
lower-bound assembly.

### Outcome
SUCCESS

### What Landed
- In
  [`Theorem.lean`](./lean/LeanMn/LowerBound/Theorem.lean),
  narrowed `cycle_classification_residual` and the derived
  `cycle_classification` theorem from arbitrary good cycles to
  **converging** good cycles:
  - old shape: `gc : GoodCycle sys -> ...`
  - new shape: `gc : GoodCycle sys -> converges sys gc -> ...`
- Updated the two assembly uses in `case3a_impossible` and
  `case3bc_impossible` to pass the existing `hconv`.

### Why This Shrinks Trust
The old sweep clause was false as stated for arbitrary good cycles.
I found a concrete locally consistent sub-threshold witness on the state vector
`(2,2,2,2,3)` with distinct configs

`(0,0,0,0,0) -> (1,0,0,0,0) -> (1,1,0,0,0) -> (1,1,1,0,0) ->`
`(1,1,1,1,0) -> (1,1,1,1,1) -> (0,1,1,1,1) -> (0,0,1,1,1) ->`
`(0,0,0,1,1) -> (0,0,0,0,1) -> (0,0,0,0,2) -> start`

with mover word
`(0,1,2,3,4,0,1,2,3,4,4)`.

This has total displacement `10 = 2n`, so it satisfies the current `isSweep`
definition, but it cannot come from any `WaterfallCycle` because:
- its cycle length is `11`, while `WaterfallCycle.len_eq` forces length `2n=10`;
- its mover word has a self-step `4 -> 4`, while a waterfall cycle has strict
  residue mover schedule `k mod n`.

So the previous phase-10 trust surface included false generality. Requiring
`converges sys gc` removes that false generality and matches the only place the
kernel is actually used.

### Trust Impact
- Raw axiom count in `LeanMn/LowerBound` stays at `3`.
- The live phase-10 kernel is materially smaller and more honest:
  it no longer claims sweep/odd classification for arbitrary good cycles.
- Remaining lower-bound trust surface is still:
  - `cycle_classification_residual`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`

### Verification
- `lake env lean LeanMn/LowerBound/Theorem.lean` passes.
- `rg -n "^axiom " LeanMn/LowerBound` still reports exactly:
  `cycle_classification_residual`,
  `palindromic_zeroWinding_obstruction`,
  `nonconsecutive_zeroWinding_obstruction`.

## Exploration 36

### Strategy
Check whether the remaining phase-7 and phase-9 obstruction kernels have the
same false-generalization problem that phase 10 had. If they do, narrow them to
the exact lower-bound use site instead of pretending they rule out arbitrary
good cycles.

### Outcome
SUCCESS

### What Landed
- In
  [`CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean),
  both remaining zero-winding kernels now require
  `hconv : converges sys gc`:
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
- Propagated that new premise through:
  - [`EntryConflict/Palindromic.lean`](./lean/LeanMn/LowerBound/EntryConflict/Palindromic.lean)
  - [`EntryConflict/NonConsecutive.lean`](./lean/LeanMn/LowerBound/EntryConflict/NonConsecutive.lean)
  - [`Wiggle/Theorem.lean`](./lean/LeanMn/LowerBound/Wiggle/Theorem.lean)
  - [`Theorem.lean`](./lean/LeanMn/LowerBound/Theorem.lean)

### Why This Shrinks Trust
Both kernels were false as statements about arbitrary good cycles, even at
sub-threshold products.

Concrete non-consecutive witness:
- state vector `(2,3,2,3,2)` with product `72 < 108`
- binary processors at `0,2,4` (so `hasGe3Binary` and no 3 consecutive binary)
- distinct good-cycle configs
  `[(0,0,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]`
- mover word `(0,1,0,1,1)`
- total displacement `0`

So the old
`nonconsecutive_zeroWinding_obstruction : ... -> False`
was ruling out a concrete locally consistent zero-winding good cycle that the
lower-bound theorem never needed to exclude.

Concrete consecutive witness:
- state vector `(2,2,2,3,3)` with product `72 < 108`
- binary processors `0,1,2` are 3 consecutive
- distinct good-cycle configs
  `[(0,0,0,0,0), (1,0,0,0,0), (1,0,0,0,1), (0,0,0,0,1), (0,0,0,0,2)]`
- mover word `(0,4,0,4,4)`
- total displacement `0`

So the old
`palindromic_zeroWinding_obstruction : ... -> False`
also had false generality.

Requiring `converges sys gc` makes both kernels match the only place they are
actually used: inside the `¬valid` proofs after introducing `⟨gc, hconv⟩`.

### Trust Impact
- Raw axiom count in `LeanMn/LowerBound` stays at `3`.
- The remaining trusted surface is materially smaller and more honest:
  all 3 surviving axioms are now stated only for converging cycles.
- The live lower-bound trust surface is:
  - `cycle_classification_residual`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`

### Verification
- The source-level signature propagation is complete through the affected files.
- I started a full `lake build` over the touched lower-bound modules; it
  replayed into the known expensive `MNU.lean` boundary without reporting new
  theorem errors before I stopped it to keep the turn moving.
- `rg -n "^axiom " LeanMn/LowerBound` still reports exactly the same 3 axioms,
  now with narrower premises.

## Exploration 37

### Strategy
Use the exact cycle-completion search to test whether the narrowed
`cycle_classification_residual` is actually true under `hconv`, rather than
continuing to push on the current statement blindly.

### Outcome
SUCCEEDED

### What Landed
- I ran the existing exact completion search
  [`gpt/scripts/p2_completion_search.py`](./gpt/scripts/p2_completion_search.py)
  on the old false-generality witnesses from explorations 35 and 36. All three
  fail completion immediately, so the `hconv` narrowing was not cosmetic.
- I then scanned small `n = 5` sub-threshold orientations by combining
  [`gpt/scripts/p2_good_cycle_search.py`](./gpt/scripts/p2_good_cycle_search.py)
  with the same completion search, looking specifically for completed valid
  systems whose good cycle satisfies the current `isSweep` or `isOddWinding`
  abstraction but does not match the residual theorem's conclusion.
- That scan found a genuine counterexample to the current sweep clause of
  `cycle_classification_residual`.

### Failure Constraint
The current theorem statement is mathematically false: `gc.isSweep` as
formalized by `(|totalDisplacement gc| >= 2n)` is strictly broader than the
proof-doc notion of a same-direction sweep / waterfall cycle. Completion search
 found a valid converging system whose good cycle satisfies the former but not
 the latter.

### What This Rules Out
It rules out any direct proof attack on `cycle_classification_residual` in its
current form. No amount of Lean engineering will prove a false theorem.

It also rules out treating the current `GoodCycle.isSweep` definition as the
right abstraction boundary for the phase-10 sweep branch. The residual theorem
must either:
- be narrowed to a stronger sweep notion, or
- be replaced by a different phase-10 architecture that does not ask for
  `gc.isSweep -> ∃ wc : WaterfallCycle sys, ...`.

### Surviving Structure
- The completion machinery is now part of the residue toolkit for theorem-shape
  validation:
  - `p2_good_cycle_search.py` can produce locally consistent candidate cycles.
  - `p2_completion_search.py` can tell whether those candidates extend to a
    valid converging system.
- The three old local witnesses from explorations 35 and 36 remain useful
  negative controls: they still do **not** complete.
- The sweep side still has a strong proved target once the right notion is
  isolated:
  - `shadow_cycle_mirror_theorem` for `WaterfallCycle`
  - the entire canonical shadow pipeline in `Shadow/Theorem.lean`

### Reformulations
- The real phase-10 question is not “is the cycle a sweep in the sense of large
  total displacement?” but “does the mover word have the stronger same-direction
  / waterfall structure needed by the shadow theorem?”
- So the current `GoodCycle.isSweep` predicate is not the right semantic handle
  for the residual theorem. It is only a coarse displacement classifier.

LOAD-BEARING ASSESSMENT: yes. This changes the default representation for the
phase-10 residue. Future work on that axiom must start by replacing the sweep
notion, not by adding more proof lemmas under the current one.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Completed counterexample to the current sweep clause:
  - state vector `(2,2,2,3,4)` with product `96 < 108`
  - completed valid good cycle of length `18`
  - mover word
    `(0,1,2,3,2,3,4,0,1,2,3,4,3,4,3,2,3,4)`
  - distinct configs
    `[(0,0,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,1,1,0,0),`
    `(1,1,1,1,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,2,1),`
    `(0,1,0,2,1), (0,0,0,2,1), (0,0,1,2,1), (0,0,1,0,1),`
    `(0,0,1,0,2), (0,0,1,2,2), (0,0,1,2,3), (0,0,1,1,3),`
    `(0,0,0,1,3), (0,0,0,0,3)]`
  - total displacement `10 = 2n`, so `gc.isSweep` holds
  - but no `WaterfallCycle` can match it because `WaterfallCycle.len_eq`
    requires length `2n = 10`

STRUCTURAL RESULTS:
- `cycle_classification_residual` is false as currently stated, even with
  `hconv`.

TOOLS:
- Bounded exact scan used:
  - enumerate locally consistent cycles on small `n = 5` sub-threshold
    orientations
  - filter by `isSweep` / `isOddWinding`
  - run `search_completion(..., cycle=..., movers=...)`

### What Would Unblock This
- A theorem-shape decision for the phase-10 residue:
  - replace `gc.isSweep` by a stronger same-direction / waterfall-compatible
    notion, or
  - bypass `cycle_classification_residual` entirely with a different assembly.

### Open Questions
1. What is the minimal truthful replacement for the current sweep clause?
2. Can the lower-bound assembly be refactored to avoid a global sweep
   classification theorem entirely?

## Exploration 38 (probe)

### Strategy
Re-run the completed counterexample from exploration 37 through the full system
verifier, not just the completion search, to confirm that it is a genuinely
valid converging system.

### Outcome
SUCCEEDED

### Concrete Artifacts
- `search_completion` on the exploration-37 cycle returned:
  - `found = True`
  - `message = "found a full valid system"`
  - `stats = SearchStats(nodes=55, backtracks=21, max_depth=33)`
- `verify_system` on the returned system reported:
  - `verify_valid = True`
  - `verify_message = "valid system with 1 recurrent cycle(s)"`

## Exploration 39

### Strategy
Take the least invasive option-1 repair: stop routing the phase-10 residue
through the bad coarse sweep surrogate `gc.isSweep`, and narrow the trusted
classification statement to the actual `n ≥ 9` lower-bound use site.

### Outcome
SUCCEEDED

### What Landed
- In
  [`LeanMn/LowerBound/Theorem.lean`](./lean/LeanMn/LowerBound/Theorem.lean),
  `cycle_classification_residual` no longer states
  `gc.isSweep -> ∃ wc : WaterfallCycle sys, ...`.
- It is now the direct theorem-range classification actually needed by the
  lower bound:
  - assumptions narrowed from `sys.rs.n ≥ 5` to `sys.rs.n ≥ 9`
  - conclusion stated directly as
    `(∃ wc : WaterfallCycle sys, wc.toGoodCycle = gc) ∨ gc.zeroWinding`
- The derived `cycle_classification` theorem was reduced to the direct wrapper.
- `case3a_impossible` and `case3bc_impossible` were narrowed from `n ≥ 5` to
  `n ≥ 9`, which matches their only use in `lower_bound_theorem`.
- `lower_bound_theorem` now passes its existing `hn : sys.rs.n ≥ 9` directly
  into those case theorems.

### Why This Shrinks Trust
This removes the false identification between:
- the coarse displacement classifier `GoodCycle.isSweep` (`|W| ≥ 2n`), and
- the proof-doc same-direction / waterfall sweep notion needed by the shadow
  theorem.

The residual theorem is now stated only at the honest theorem-range use site
and only in the direct disjunctive form the lower-bound assembly consumes.
So the phase-10 kernel is materially narrower and no longer mentions a false
intermediate sweep abstraction.

### Trust Impact
- Raw lower-bound axiom count stays at `3`.
- The phase-10 kernel is smaller and more honest:
  - old trusted content: a false `isSweep`-based sweep/odd-winding interface
    for all `n ≥ 5`
  - new trusted content: direct classification only for the actual theorem
    range `n ≥ 9`
- Live lower-bound trust surface remains:
  - `cycle_classification_residual`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`

### Surviving Structure
- `GoodCycle.isSweep` remains available as a coarse displacement notion in
  `GoodCycleBasics.lean`, but phase 10 no longer treats it as the semantic
  gateway to `WaterfallCycle`.
- The proved shadow pipeline remains unchanged and still targets the genuine
  `WaterfallCycle` structure.

### Verification
- `rg -n "^axiom " LeanMn/LowerBound` still reports exactly the same 3 axioms.
- Source-level replay of `Theorem.lean` initially hit stale-import signature
  mismatches from `Palindromic.lean` / `NonConsecutive.lean`; I corrected the
  local `n ≥ 5` bridge calls and started a targeted `lake build` over the
  affected lower-bound modules.
- The build has replayed past `GoodCycleBasics` with no new theorem errors so
  far; it is still in the known slow transitive rebuild zone as of this log
  entry.

## Exploration 40

### Strategy
Lower the remaining theorem-shaped kernels to the actual `n ≥ 9` lower-bound
range, and strip the redundant `hasGe3Binary` premise from the phase-10
residual because it is already derivable from `subThreshold`.

### Outcome
SUCCEEDED

### What Landed
- In
  [`LeanMn/LowerBound/CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean),
  both remaining zero-winding axioms now require `hn : sys.rs.n ≥ 9`:
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
- The wrappers in
  [`EntryConflict/Palindromic.lean`](./lean/LeanMn/LowerBound/EntryConflict/Palindromic.lean)
  and
  [`EntryConflict/NonConsecutive.lean`](./lean/LeanMn/LowerBound/EntryConflict/NonConsecutive.lean)
  were narrowed to the same theorem range.
- In
  [`LeanMn/LowerBound/Wiggle/Theorem.lean`](./lean/LeanMn/LowerBound/Wiggle/Theorem.lean),
  the existing wrapper theorem was narrowed from `n ≥ 7` to `n ≥ 9` to match
  the only live trusted non-consecutive obstruction, and the unused
  `small_n_wiggle_impossible` helper was deleted.
- In
  [`LeanMn/LowerBound/Theorem.lean`](./lean/LeanMn/LowerBound/Theorem.lean),
  `cycle_classification_residual` no longer carries an explicit
  `hasGe3Binary sys.rs` premise. The wrapper `cycle_classification` and both
  phase-10 case theorems were updated accordingly.

### Why This Shrinks Trust
This removes trusted surface that was broader than the actual lower-bound
assembly:
- the phase-7/9 kernels no longer pretend to cover the `n = 5..8` regime,
  which is outside the theorem range and outside the current live proof path;
- the phase-10 kernel no longer assumes a redundant binary-count premise that
  is derivable from `subThreshold` at every live call site.

So all three remaining axioms are now closer to the exact theorem-range
statements the lower bound actually consumes.

### Trust Impact
- Raw lower-bound axiom count stays at `3`.
- The live lower-bound trust surface is now:
  - `cycle_classification_residual` on `n ≥ 9`, without explicit `hasGe3Binary`
  - `palindromic_zeroWinding_obstruction` on `n ≥ 9`
  - `nonconsecutive_zeroWinding_obstruction` on `n ≥ 9`
- The old small-`n` wiggle wrapper is no longer part of the trusted surface.

### Surviving Structure
- `shadow_cycle_mirror_theorem` still needs only the local `hn5` bridge, so
  the sweep branch remains unchanged.
- The zero-winding branches now line up with the actual phase-10 theorem range,
  which makes the next axiom attacks cleaner: no proof effort should be spent
  on the `n = 5..8` edge regime inside these kernels.

### Verification
- `lake build LeanMn.LowerBound.CaseObstructions LeanMn.LowerBound.EntryConflict.Palindromic LeanMn.LowerBound.EntryConflict.NonConsecutive LeanMn.LowerBound.Wiggle.Theorem LeanMn.LowerBound.Theorem`
  passed.
- `rg -n "^axiom " LeanMn/LowerBound` still reports exactly the same 3 axioms.

## Exploration 41

### Strategy
Try to remove `cycle_classification_residual` directly by reconstructing the
old phase-10 split into `no_odd_winding_subthreshold` plus sweep
canonicalization, using the current `GoodCycleBasics` fire-count and mover-word
lemmas as the replacement infrastructure.

### Outcome
STALLED

### Failure Constraint
The current Lean mover-word layer stops strictly short of the invariants that
the proof-doc phase-10 argument needs.

Concretely:
- The odd-winding route in the proof documents uses binary passage data
  (`u`, `d`, singleton edges, or equivalent directional counts). In Lean, the
  strongest available binary theorem is only
  `GoodCycle.binary_fireCount_even : Even (gc.fireCount p)`. There is no
  theorem connecting `fireCount` to clockwise/counterclockwise passages, no
  no-self-firing theorem for binary processors, and no exact-two-firings theorem.
- The sweep route in the proof documents uses a stronger same-direction sweep
  notion than the coarse `gc.isSweep` displacement surrogate. In Lean there is
  currently no predicate for “all mover-word steps have one direction / no
  reversals”, and no theorem stating that such cycles induce a 2n-periodic
  local-entry pattern or a canonical waterfall window.

So the current axiom is not blocked by one missing local lemma; it is blocked
by an absent representation layer for phase 10.

### What This Rules Out
It rules out any honest direct proof of `cycle_classification_residual` that
works only inside the current API
(`totalDisplacement`, `zeroWinding_or_isOddWinding_of_not_sweep`,
`binary_fireCount_even`, `sum_fireCount`, `next_mover_is_local`).

Any approach that tries to prove the axiom “in place” from those lemmas alone
will hit the same obstacle: the proof-doc arguments are formulated in terms of
reversals, directional passages, and singleton edges, and none of those are
represented yet.

### Surviving Structure
- The old git history still identifies the intended split:
  - `no_odd_winding_subthreshold`
  - `sweep_to_waterfall`
- The proof documents and verification notes agree on the honest phase-10
  semantic split:
  - same-direction sweeps are a stronger class than coarse
    `|totalDisplacement| ≥ 2n`;
  - odd-winding is killed by singleton-edge counting, not by waterfall
    canonicalization.
- The current Lean layer already has the minimal raw inputs for a new
  representation:
  - local step directions via `signedStep`
  - stepwise mover extraction via `moverAt`
  - processor fire counts via `fireCount`
  - the phase-9 singleton/return-cone vocabulary in
    `EntryConflict/NonConsecutive.lean`

### Reformulations
- The right phase-10 object is not the coarse predicate `gc.isSweep`.
  It is a mover-word representation layer carrying:
  - directional step sequence / reversals
  - same-direction sweep
  - directional binary passage counts or singleton-edge counts

LOAD-BEARING ASSESSMENT: yes. This changes the effective search space for the
remaining axiom. Future work on `cycle_classification_residual` should start by
adding this representation layer, not by trying more direct proof scripts
against the current theorem.

### Concrete Artifacts
STRUCTURAL RESULTS:
- `cycle_classification_residual` is now isolated as a phase-10 representation
  problem, not just a missing proof of a correctly represented theorem.
- The existing Lean fire-count layer is insufficient to recover the proof-doc
  odd-winding argument.

CODE ARCHAEOLOGY:
- Git history at commit `85e6b77` confirms the earlier intended split into:
  - `sweep_to_waterfall`
  - `no_odd_winding_subthreshold`

### What Would Unblock This
- A new Lean phase-10 mover-word layer defining at least:
  - a same-direction / no-reversal sweep predicate
  - directional passage counts at processors or edges
  - singleton-edge counts derived from those passage counts
- Then:
  1. prove the odd-winding killer on that representation;
  2. prove the same-direction sweep window / waterfall bridge;
  3. discharge `cycle_classification_residual`.

### Open Questions
1. Should the new phase-10 representation live in `GoodCycleBasics.lean`, or in
   a new dedicated `LowerBound/CycleTypes.lean` layer to keep the trust attack
   isolated?
2. Is the smallest honest next theorem “odd-winding implies ≥ 2 singleton
   edges” or “same-direction sweep implies local-entry 2n-periodicity”?

## Exploration 42

### Goal
Make the phase-10 representation refactor pay off immediately by removing one
concrete subcase from the trusted residue, rather than just adding inert
infrastructure.

### Work Performed
- Added a new phase-10 mover-word layer in
  `LeanMn/LowerBound/CycleTypes.lean`.
- Exposed the minimal lower-bound helpers needed to support it from
  `GoodCycleBasics.lean`:
  - `nextIndex_eq_right`
  - `nextIndex_bijective`
  - `totalDisplacement_eq_moverAt_sum`
  - `sum_next_moverAt_val_eq_sum_moverAt_val`
- Formalized a same-direction mover-word notion:
  - `GoodCycle.uniformCW`
  - `GoodCycle.uniformCCW`
  - `GoodCycle.uniformDirection`
- Proved the first honest phase-10 exclusion theorem:
  `GoodCycle.not_uniformDirection_and_isOddWinding_of_hasGe3Binary`

The proof is the proof-doc “uniform odd-winding is impossible” argument in Lean:
- under `uniformCW` or `uniformCCW`, the signed displacement is exactly the
  cycle length;
- odd winding then forces `configs.length = n`;
- the uniform-direction word makes all processor fire counts equal;
- `sum_fireCount = n` then forces every processor to fire exactly once;
- any binary processor must fire an even number of times, contradiction.

### Trust Impact
- Narrowed the phase-10 axiom in `LowerBound/Theorem.lean`:
  `cycle_classification_residual` now takes the extra premise
  `¬(gc.uniformDirection ∧ gc.isOddWinding)`.
- The wrapper theorem `cycle_classification` now proves that premise in Lean
  from `subThreshold_ge3_binary` plus the new `CycleTypes` theorem.

So the trusted phase-10 kernel no longer has to cover same-direction
odd-winding cycles. That subcase is now discharged formally.

### Verification
- `lake build LeanMn.LowerBound.CycleTypes` passes.
- `lake env lean LeanMn/LowerBound/Theorem.lean` passes.
- `rg -n "^axiom " LeanMn/LowerBound` still reports exactly 3 axioms:
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`
  - `cycle_classification_residual`

### Residue Update
The phase-10 axiom is still present, but it is smaller and better aligned with
the proof-doc semantics:
- the remaining trusted content is no longer allowed to classify uniform
  same-direction odd-winding cycles, because those are now impossible in Lean;
- the remaining open parts are the genuinely hard branches:
  1. same-direction sweep to waterfall / 2n-window canonicalization;
  2. non-uniform odd-winding elimination via passage/singleton structure.

LOAD-BEARING ASSESSMENT: yes. This is the first pass where the new
`CycleTypes` layer directly shrinks the live trust boundary instead of only
preparing for later work.

## Exploration 43

### Strategy
Shrink the phase-9 non-consecutive kernel to the actual lower-bound use site
before spending more proof effort on it, by threading `subThreshold sys.rs`
through the wrapper and dropping the redundant explicit `hasGe3Binary` premise.

### Outcome
SUCCEEDED

### What Landed
- In
  [`LeanMn/LowerBound/CaseObstructions.lean`](./lean/LeanMn/LowerBound/CaseObstructions.lean),
  `nonconsecutive_zeroWinding_obstruction` now takes
  `hsub : subThreshold sys.rs` and no longer takes a separate
  `h3bin : hasGe3Binary sys.rs`.
- In
  [`LeanMn/LowerBound/EntryConflict/NonConsecutive.lean`](./lean/LeanMn/LowerBound/EntryConflict/NonConsecutive.lean),
  `universal_entry_conflict_nonconsec` was updated to the new signature and now
  delegates exactly at that narrowed use site.
- In
  [`LeanMn/LowerBound/Wiggle/Theorem.lean`](./lean/LeanMn/LowerBound/Wiggle/Theorem.lean),
  the existing wrapper theorem was narrowed the same way, since it is only a
  specialization of the phase-9 obstruction.
- In
  [`LeanMn/LowerBound/Theorem.lean`](./lean/LeanMn/LowerBound/Theorem.lean),
  the case-3bc zero-winding branch now passes `hsub` directly into
  `universal_entry_conflict_nonconsec`.

### Why This Shrinks Trust
The proof documents state the phase-9 obstruction only in the sub-threshold
regime. The previous Lean kernel was broader than the theorem range actually
consumed by the lower-bound assembly: it trusted a statement over arbitrary
state products and carried a binary-count premise that the live caller already
derives from `subThreshold`.

This pass moves the trust boundary onto the honest theorem-range statement:
- the phase-9 kernel is now scoped to the actual lower-bound regime;
- the trusted signature no longer includes a redundant explicit
  `hasGe3Binary` premise.

### Trust Impact
- Raw lower-bound axiom count stays at `3`.
- The phase-9 kernel is now strictly narrower:
  `nonconsecutive_zeroWinding_obstruction` trusts only the theorem-range
  `subThreshold` branch, not arbitrary products.
- The live lower-bound trust surface is still:
  - `cycle_classification_residual`
  - `palindromic_zeroWinding_obstruction`
  - `nonconsecutive_zeroWinding_obstruction`

### Surviving Structure
- The phase-10 call site already had `hsub`, so the shrink required only
  signature propagation and no architectural change.
- `subThreshold_ge3_binary` remains the right bridge when the caller needs
  explicit binary-count consequences; the phase-9 kernel itself no longer needs
  to trust that premise separately.

### Verification
- `lake env lean LeanMn/LowerBound/CaseObstructions.lean` passed before the
  dependent replay.
- Source-level propagation is complete through:
  - `CaseObstructions.lean`
  - `EntryConflict/NonConsecutive.lean`
  - `Wiggle/Theorem.lean`
  - `Theorem.lean`
- A broader `lake build` / dependent-module rebuild was started but hit the
  same long silent lower-bound replay boundary as earlier passes, so this pass
  does not claim a completed end-to-end build beyond the direct source checks.

### Residue Update
This does not eliminate an axiom, but it makes the remaining phase-9 one more
honest. The next high-value move is still an actual axiom attack:
- either the phase-10 `cycle_classification_residual` via more mover-word
  representation;
- or the phase-9 kernel via a genuine singleton-edge / return-cone layer.
