# Lean Exploration Log

## Strategy Register

**Eliminated approach classes:**
- Direct reuse of older CUP-2 scripts as authoritative table sources — ruled out at exploration 1 because several local scripts still encode the obsolete `T_mid(2,1,1)→0` variant, while `verification_claims_v2.md` fixes this to `T_mid(2,1,1)→2`.

**Obstructions:**
- Lake dependency bootstrapping without a complete local manifest is brittle in this workspace: `mathlib`'s transitive packages must be mirrored, or `lake build` fails before checking any Lean code (exploration 1).
- The naive global sum of per-site hop budgets cannot be a descent measure for deep-interior TP-preserving zero-`Δfc` moves: the hop cases shift budget mass to the right, and `(1,0,0) -> 1` can increase the next-site budget by `2` (exploration 23).

**Building blocks:**
- Source of truth fixed: `docs/verification_claims_v2.md` governs the CUP-2 tables and Phase 1 classification claims.
- CUP-2 prior work establishes that `T_mid(2,1,1)→2` is the intended 4-anomalous variant; older `→0` scripts are obsolete for this formalization.
- Working Lean project scaffold under `lean` with Lean 4.27.0 and local cached `mathlib` dependencies.
- Nat-valued table kernels (`TBotVal`, `TLowVal`, `TMidVal`, `THighVal`, `TTopVal`) plus typed wrappers are a workable Phase 1 representation: they preserve the published tables while making the heterogeneous system constructor manageable.
- `cup2Trans` can be built without pervasive `Fin.cast` by branching on processor class and proving output bounds for raw Nat table values.
- The deep-interior TP-preserving zero-`Δfc` relation now has a compiled global well-founded measure: a base-`3` right-to-left weighted sum of the local hop budgets strictly decreases on every such move (exploration 23).

**Known reformulations:**
- Convergence is to be formalized as well-foundedness of the non-good transition relation rather than scheduler traces.
- For CUP-2 formalization, the right representation is:
  raw Nat table kernels for computation
  typed `Fin` wrappers for table statements
  a branch-local proof that `cup2OutVal < cup2M`.
  LOAD-BEARING: yes. This avoids cast-heavy dependent code and compiled cleanly in exploration 1.
- The analytical “boundary-fixed hop impossibility” step can be reframed as a global weighted-potential descent problem on TP-preserving deep-interior zero-`Δfc` moves, not only as a position-by-position induction. LOAD-BEARING: yes. The local hop cases already compile into a single well-founded relation in exploration 23.

## Session Start
No prior explorations in `lean`. Phase 1 will start from the semantics, CUP-2 tables, and the arbitrary-`n` system constructor.

## Exploration 1

### Strategy
Bootstrap the Lean project and implement the full Phase 1 scaffold in the simplest compiling representation: generic semantics plus raw Nat CUP-2 tables with typed wrappers and a branchwise `cup2System` constructor.

### Outcome
SUCCEEDED

### Failure Constraint
N/A. The attempt completed, but it exposed two concrete encoding constraints:
1. `lake` needed the full local `mathlib` dependency graph, not just the top-level package.
2. Early simplification inside `cup2Trans` destroyed the useful `Fin` bound hypotheses; the bounds had to be derived before simplification.

### What This Rules Out
Any Phase 1 implementation that tries to copy old CUP-2 scripts verbatim, or that simplifies the dependent target of `cup2Trans` before extracting branch-local bounds, will recreate the same errors.

### Surviving Structure
- `RingSpec`, `Config`, `left`, `right`, `TransFn`, `System`, `stateProduct` compile.
- `privileged`, `move`, `step`, `singlePrivileged`, `GoodCycle`, `badStep`, `converges`, `valid` compile.
- All five published CUP-2 tables compile from `verification_claims_v2.md`.
- The finite Phase 1 checks compile:
  `allEntries_length = 87`
  `claim_3_1_1 : allEntriesWellFormed = true`
  `claim_3_3_1_privileged_count : privilegedEntries.length = 45`
  `claim_3_3_1_copyNeighbor_count : copyNeighborEntries.length = 41`
  `claim_3_3_1_anomalous_count : anomalousEntries.length = 4`
  `anomalous_signatures = [(.bot,0,0,0,1), (.bot,1,1,2,0), (.high,1,1,1,2), (.top,2,0,0,1)]`
- `cup2Spec`, `cup2OutVal`, `cup2Trans`, and `cup2System` compile for all `n ≥ 4`.

### Reformulations
The key representation shift was:
- Do not build CUP-2 by casting typed table inputs around dependent equalities.
- Instead, define raw Nat table kernels, prove finite bound lemmas with `interval_cases`, wrap them as typed tables, and use the raw kernels in `cup2Trans`.

LOAD-BEARING ASSESSMENT: yes. This changes the effective search space for the formalization. The dependent-type pain moves from every call site into a small number of branchwise bound proofs, which made Phase 1 compile.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Lean project files added: `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, `LeanMn.lean`.
- Phase 1 modules added: `LeanMn/Basic.lean`, `LeanMn/Ring.lean`, `LeanMn/Dijkstra.lean`, `LeanMn/Tables.lean`, `LeanMn/System.lean`, `LeanMn/Main.lean`.

TOOLS:
- Local package reuse works: symlinked `.lake/packages/*` from `./_external/Github/blind-tab/lean/.lake/packages/` into this workspace, avoiding networked `lake update`.

REPRESENTATIONS:
- Raw table kernel example:
  `def TMidVal : Nat → Nat → Nat → Nat := ...`
- Typed wrapper example:
  `def T_mid (L : Fin 3) (S : Fin 3) (R : Fin 3) : Fin 3 := ⟨TMidVal L.1 S.1 R.1, ...⟩`
- System constructor representation:
  `cup2OutVal` branches on processor class, and `cup2Trans` proves the output bound branchwise.

EXACT ERROR MESSAGES:
- `error: dependency 'plausible' of 'mathlib' not in manifest; this suggests that the manifest is corrupt`
- `error: LeanMn/Tables.lean:193:13: Invalid field 'bind': The environment does not contain 'List.bind'`
- `error: LeanMn/System.lean:132:8: Tactic 'rewrite' failed: Did not find an occurrence of the pattern if ↑i = 0 then ...`

EXACT TACTIC SCRIPTS / PROOF SHAPES:
- `rw [Nat.zero_add, Nat.mod_eq_of_lt] <;> omega`
- `simpa [cup2Spec, cup2M_left_bot hn h0] using L.2`
- `simpa [cup2OutVal, h0] using TBotVal_lt hL hS hR`
- `rw [hself]; simpa [cup2OutVal, h0, h1, htop, hhigh] using TMidVal_lt hL hS hR`

MATHLIB LEMMA NAMES:
- `Nat.mod_lt`
- `Nat.mod_eq_of_lt`
- `Nat.add_mod_left`

TOOLCHAIN / MATHLIB:
- Lean toolchain: `leanprover/lean4:v4.27.0`
- Mathlib input revision: `v4.27.0`
- Mathlib manifest revision: `a3a10db0e9d66acbebf76c5e6a135066525ac900`

### What Would Unblock This
- Phase 2 needs the closed-form good-cycle encoding from Claim 3.2.2 and a clean representation of cyclic indexed configs over `List` or `Fin (3*n-2)`.
- It would also help to strengthen `claim_3_1_1` from a boolean finite check to a propositional statement if downstream proofs want to rewrite with it directly.

### Key Parameters
- Workspace: `lean`
- Lean build target: `lake build LeanMn`
- Phase 1 source document: `docs/verification_claims_v2.md`

### Open Questions
- Should the cycle in Phase 2 be represented as `Fin (3*n-2) → Config` first, with the `List` view derived later?
- Is it worth refactoring the Phase 1 finite checks to expose more proposition-level theorems now, or should that wait until a Phase 2/3 proof needs them?

## Synthesis after exploration 1

### Cross-artifact pattern
The successful pattern is consistent across the whole scaffold:
- Generic semantics can stay dependent.
- Finite table data should stay computational.
- The bridge between them should be local bound proofs, not global casts.

### Implication for the next exploration
Phase 2 should reuse the same split:
- closed-form cycle data in a computation-friendly representation
- small local lookup lemmas for the 39 table checks
- only then package the result into `GoodCycle`.

## Exploration 2

### Strategy
Close the remaining Phase 1 gap by proving the CUP-2 state-space product formula directly as a raw finite product, then lift it back to `stateProduct (cup2Spec n hn)` only at the final theorem.

### Outcome
SUCCEEDED

### Failure Constraint
Two seemingly reasonable proof shapes failed before the final successful version:
1. Rewriting `stateProduct (cup2Spec n hn)` directly with `rw` on `n = (n - 2) + 2` failed because the motive depended on the proof field `hn : 4 ≤ n`.
2. A broader `simpa`/`convert` approach on the final theorem either looped (`maximum recursion depth has been reached`) or generated unusable arithmetic goals over whole products.

### What This Rules Out
For later phases, avoid doing arithmetic rewrites through dependent structures when the theorem only needs their computational fields. Rewrite the computational term first, then reconnect it to the structured object at the boundary.

### Surviving Structure
- `cup2_stateProduct_aux (m)` now proves
  `∏ i : Fin (m + 2), cup2M (m + 2) i = 4 * 3 ^ m`.
- `cup2_stateProduct (n) (hn)` now proves
  `stateProduct (cup2Spec n hn) = 4 * 3 ^ (n - 2)`.
- `cup2_phase1_summary` compiles, so the finite table checks and arbitrary-`n` state-product claim are packaged together.
- `lake build LeanMn` succeeds after these additions.

### Reformulations
The load-bearing proof reformulation was:
- prove the product theorem on the raw term
  `fun k => ∏ i : Fin k, cup2M k i`
- then transport along `n = (n - 2) + 2` using
  `congrArg (fun k => ∏ i : Fin k, cup2M k i)`.

LOAD-BEARING ASSESSMENT: yes. This isolates dependent-proof noise from the actual arithmetic/content proof and should be reused when later claims only depend on computational projections of a structure.

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/System.lean`](./lean/LeanMn/System.lean) now contains the raw product theorem and the lifted `stateProduct` theorem.
- [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) now closes a single Phase 1 summary theorem.

EXACT ERROR MESSAGES:
- `Tactic 'rewrite' failed: motive is not type correct`
- `Tactic 'simp' failed with a nested error: maximum recursion depth has been reached`
- `omega could not prove the goal` after an over-broad `convert`

EXACT PROOF SHAPES:
- `rw [Fin.prod_univ_succ]`
- `rw [cup2M_eq_two_of_endpoint ...]`
- `have hmid : (∏ i : Fin m, ...) = ∏ i : Fin m, 3 := by congr; ext i; exact cup2M_middle m i`
- `simpa using congrArg (fun k : Nat => ∏ i : Fin k, cup2M k i) hdecomp`

### What Would Unblock This
- Phase 2 can now start without more Phase 1 cleanup.
- The next obvious task is to encode Claim 3.2.2's `3*n - 2` good cycle in a computation-friendly form and prove the 39 local table lookups against the already-fixed tables.

## Synthesis after exploration 2

### Cross-artifact pattern
When a theorem about a structured object only depends on one computational projection, prove the projection theorem first and lift it later with a narrow transport step.

### Implication for the next exploration
Phase 2 should treat the good cycle the same way:
- define the cycle as raw indexed data first
- prove local lookup facts on that data
- package the result into the higher-level `GoodCycle` statement only at the end

## Current Phase Status

Phase 1 is complete in the current Lean scaffold:
- the Dijkstra semantics compile
- the five CUP-2 tables compile from `verification_claims_v2.md`
- the 87-entry well-definedness/classification checks compile
- the arbitrary-`n` CUP-2 system compiles
- the state-product theorem `4 * 3^(n-2)` compiles
- `lake build LeanMn` succeeds

## Exploration 3

### Strategy
Start Phase 2 by formalizing the closed-form `3*n - 2` cycle object itself before attempting `GoodCycle`: encode the three-phase wavefront as a raw value formula, lift it to typed configs/movers, and materialize the 39 lookup facts as concrete Lean theorems.

### Outcome
PARTIAL

### Failure Constraint
The first attempt to bundle everything at once into cycle data plus list-index transport immediately ran into low-value dependent bookkeeping:
1. `List.ofFn` gives the right list, but `GoodCycle.closed` wants indices in `Fin configs.length`, so direct reuse of `Fin (3*n - 2)` needs casts.
2. The phase-3 branch of the raw closed form was easy to state but needed more explicit endpoint contradictions than `omega` could infer from the first proof draft.

These are implementation constraints, not conceptual blockers. The raw cycle object now compiles cleanly; the missing work is the final lift into `GoodCycle`.

### What This Rules Out
Do not start the Phase 2 proof by fighting `List.get`/`nextIndex` transports. The right order is:
- prove raw successor/stability facts on `Fin (3*n - 2)`
- only then transport them to the `GoodCycle` list interface

### Surviving Structure
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now defines:
  - `cup2CycleLen n = 3*n - 2`
  - `cup2CycleVal`
  - `cup2CycleMoverVal`
  - typed `cup2CycleConfig`, `cup2CycleMover`, `cup2CycleConfigs`, `cup2CycleNext`
- The raw bound lemmas compile:
  - `cup2CycleVal_le_two`
  - `cup2CycleVal_endpoint_lt_two`
  - `cup2CycleVal_lt_cup2M`
  - `cup2CycleMoverVal_lt`
- The published 39 lookup types from Claim 3.2.2 are now present as explicit theorems over `TBotVal`, `TLowVal`, `TMidVal`, `THighVal`, `TTopVal`.
- `lake build LeanMn` succeeds with the new Phase 2 module imported.

### Reformulations
The load-bearing representation choice for Phase 2 is now clear:
- keep the cycle as raw `Nat` formulas first
- lift to typed configs only through small bound lemmas
- postpone the `List`/`GoodCycle` interface until the raw successor theorem exists

LOAD-BEARING ASSESSMENT: yes. This is the same computational-first pattern that made Phase 1 workable, and it isolates the remaining Phase 2 work to one theorem family instead of spreading casts everywhere.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Added [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean)
- Updated [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) to import the Phase 2 module

EXACT ERROR MESSAGES:
- `Application type mismatch ... expected type Fin (cup2CycleConfigs n hn).length`
- `omega could not prove the goal` in the phase-3 endpoint branches

EXACT PROOF SHAPES:
- `repeat' (first | split_ifs with h | simp_all)`
- endpoint proof by rewriting `j = 0` or `j = n - 1` before splitting
- positivity of `cup2CycleLen` from the index bound `t.2`

### What Would Unblock This
- Next step is to prove the raw successor theorem:
  for each `t` and position `j`, `cup2OutVal` on `cup2CycleConfig t` yields either the next-state value at the mover or the same value off the mover.
- After that, the remaining lift to `GoodCycle` should be a transport exercise rather than a search problem.

## Synthesis after exploration 3

### Cross-artifact pattern
For these CUP constructions, the hard part is not the finite lookup data. The hard part is delaying dependent transport until after the computational statement is already proved.

### Implication for the next exploration
Exploration 4 should target one theorem family only:
- raw mover-correctness and non-mover stability on `cup2CycleConfig`
- no `GoodCycle` packaging until those raw lemmas are done

## Current Phase Status

Phase 2 is started but not complete:
- the closed-form cycle object is encoded
- the 39 Claim 3.2.2 lookup facts are encoded as Lean theorems
- the remaining work is the raw successor proof and the final lift to `GoodCycle`

## Exploration 4

### Strategy
Push the raw successor proof one layer deeper by proving mover-correctness first. The intended order was:
1. prove the phase-1 and phase-2 mover outputs against `cup2OutVal`
2. then add phase-3 movers
3. only after that, tackle non-mover stability and `GoodCycle`

### Outcome
PARTIAL

### Failure Constraint
The mathematics was not the blocker; the proof engineering was.
1. The first mover theorems used `let i := ...` in the theorem statement, which blocked straightforward `rw` on the local neighborhood values.
2. Replacing those statements with explicit `Fin` constructors fixed the rewrite issue for phase 1, but phase 2 still accumulated brittle arithmetic obligations around the typed mover index and position-class dispatch.
3. Forcing those obligations was not worth the churn in this pass; it was better to back out the non-compiling mover-output theorems and keep the library green.

### What This Rules Out
Do not try to prove the full mover-output family in one theorem that simultaneously:
- constructs the mover index
- proves the local neighborhood values
- reduces `cup2OutVal` to the right table branch

That bundles too many dependent obligations at once.

### Surviving Structure
- The following new compiled lemmas remain in [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean):
  - `cup2Cycle_phase1_next_mover`
  - `cup2Cycle_phase1_mover_self`
  - `cup2Cycle_phase2_next_mover`
  - `cup2Cycle_phase2_mover_self`
- These give the current and next mover values for phases 1 and 2, which is a useful slice of the raw successor theorem.
- `lake build LeanMn` still succeeds after the failed mover-output attempt was backed out.

### Reformulations
The next proof shape should separate the concerns more aggressively:
- first define the typed mover index for a phase as its own helper
- then prove left/self/right neighborhood-value lemmas for that phase
- only then state the table-output theorem

LOAD-BEARING ASSESSMENT: yes. The obstruction is not about CUP-2 itself; it is about proving too much through one dependent theorem head.

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now contains compiled mover-value lemmas for phases 1 and 2.

EXACT ERROR MESSAGES:
- `Tactic 'rewrite' failed: Did not find an occurrence of the pattern ...`
- repeated `omega could not prove the goal` obligations once phase-2 mover index arithmetic and table-branch reduction were mixed together

### What Would Unblock This
- Exploration 5 should target just Phase 1 mover output first, with a dedicated phase-local mover index and neighborhood lemmas.
- If that compiles cleanly, clone the exact proof shape for Phase 2 and then Phase 3.
- Only after the 13 mover cases compile should the 26 non-mover stability cases be added.

## Synthesis after exploration 4

### Cross-artifact pattern
For this formalization, the winning decomposition is even finer than expected:
- raw config formula
- typed mover index
- neighborhood-value lemmas
- table-output lemma
- successor packaging

Trying to skip any layer recreates the same dependent-proof friction.

### Implication for the next exploration
Phase 2 is still open, but the next proof target is now sharply defined:
- prove one phase's mover-output theorem end to end
- do not mix mover-index construction with table-case reduction in the same step

## Current Phase Status

Phase 2 is not done:
- compiled: closed-form cycle object, lookup catalog, and some mover-value lemmas
- missing: the full 13 mover-output proofs, the 26 non-mover stability proofs, and the final `GoodCycle` construction

## Exploration 5

### Strategy
Follow the decomposition identified in exploration 4 exactly:
1. keep the typed phase-1 mover as a separate definition
2. prove the mover's left/self/right neighborhood values first
3. prove the table output only after those inputs are exposed
4. package the result as a system-level transition fact

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now contains a reusable phase-1 mover kernel:
  - `lt_cup2CycleLen_of_lt_n`
  - `cup2Trans_val`
  - `cup2Phase1Config`
  - `cup2Cycle_phase1_left_input`
  - `cup2Cycle_phase1_right_input`
  - `cup2Cycle_phase1_output`
  - `cup2Cycle_phase1_trans_val`
  - `cup2Cycle_phase1_privileged`
- This is the first compiled end-to-end proof that a closed-form phase step reduces to the correct CUP-2 table branch and yields the intended mover output.

### Load-Bearing Observation
The proof shape from exploration 4 was correct. The stable decomposition is:
- typed mover/config wrapper
- raw neighborhood-value lemmas
- raw `cup2OutVal` lemma
- lifted `cup2System` transition value
- privilege packaging

Trying to jump directly from the closed-form config to the system transition was what caused the previous failures.

### Remaining Gap
This still proves only the mover side of Phase 1.
- not yet proved: phase-1 non-mover stability
- not yet proved: phase-1 full successor equality `C(t+1) = move C(t, mover)`
- not yet proved: phase-2 or phase-3 table-output kernels
- not yet packaged: `GoodCycle`

### Verification
- `lake build LeanMn.Cycle` succeeds
- `lake build LeanMn` succeeds

## Updated Phase Status

Phase 2 is still not done:
- compiled: closed-form cycle object, lookup catalog, phase-1/phase-2 mover-value lemmas, and a full phase-1 mover-output/privilege kernel
- missing: non-mover stability, phase-2 and phase-3 output kernels, the phase-level successor theorems, and the final `GoodCycle` construction

## Exploration 6

### Strategy
Stop treating phase 1 as only a mover-table problem and instead prove the actual closed-form successor step:
1. prove an off-mover stability lemma directly from `cup2CycleVal`
2. combine that with the already-compiled mover-output theorem
3. package the result as an equality of configurations under `move`
4. in parallel, add the corresponding typed scaffolding for phase 2 so the same pattern can be reused there

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now contains the full phase-1 successor theorem:
  - `lt_cup2CycleLen_of_phase1_succ`
  - `cup2Cycle_phase1_stable`
  - `cup2Cycle_phase1_step`
- The file also now contains reusable phase-2 scaffolding:
  - `lt_cup2CycleLen_of_phase2`
  - `lt_cup2CycleLen_of_phase2_succ`
  - `cup2Phase2Mover`
  - `cup2Phase2Config`
  - `cup2Cycle_phase2_stable`

### Load-Bearing Observation
The closed-form successor proof does **not** require the 26 non-mover table-stability facts. For `move`, non-movers are definitionally unchanged, so the only extra proof obligation is that the closed-form formula itself is unchanged off the mover. That can be discharged directly by unfolding `cup2CycleVal` and splitting cases.

This sharply separates two proof obligations:
- successor equality for the constructed cycle
- uniqueness of the privileged processor

Only the second one still needs the non-mover table analysis.

### Remaining Gap
- phase 2 still lacks its mover-output theorem and full step theorem
- phase 3 has not been packaged yet
- unique-privileged proofs are still missing, so `GoodCycle` is still out of reach

### Verification
- `lake build LeanMn.Cycle` succeeds
- `lake build LeanMn` succeeds

## Latest Phase Status

Phase 2 is still not done:
- compiled: lookup catalog, full phase-1 mover kernel, full phase-1 successor theorem, and phase-2 mover/config/stability scaffolding
- missing: phase-2/phase-3 mover-output theorems, phase-2/phase-3 step theorems, the non-mover privilege exclusion proofs needed for uniqueness, and the final `GoodCycle`

## Exploration 7

### Strategy
Finish phase 2 by cloning the phase-1 proof shape exactly:
1. make the phase-2 mover index arithmetic explicit
2. prove phase-2 left/right neighborhood-value lemmas
3. prove the raw phase-2 `cup2OutVal` theorem by the three mover classes
4. lift that to the system transition, privilege, and full `move` equality
5. then probe phase 3 with the same direct `split_ifs` strategy before deciding whether to merge anything

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now contains the full phase-2 bundle:
  - `cup2Phase2Mover_val`
  - `cup2Phase2Mover_ne_zero`
  - `cup2Phase2Mover_not_top`
  - `cup2Phase2Mover_left_val`
  - `cup2Phase2Mover_right_val`
  - `cup2Cycle_phase2_left_input`
  - `cup2Cycle_phase2_right_input`
  - `cup2Cycle_phase2_output`
  - `cup2Cycle_phase2_trans_val`
  - `cup2Cycle_phase2_privileged`
  - `cup2Cycle_phase2_step`

### Load-Bearing Observation
Phase 2 obeys the same decomposition as Phase 1, but only after the mover index is normalized aggressively enough that the position-class branch in `cup2OutVal` becomes syntactic. Once the mover index equalities were stated explicitly, the rest of the proof collapsed into the same pattern:
- neighborhood values
- raw table output
- system transition value
- privilege
- full step theorem

### Phase 3 Result
The first direct phase-3 attempt did **not** compile cleanly enough to merge.
- The off-mover and mover-value goals no longer reduce well under a bare `split_ifs` because the phase-3 branch introduces `let k := t - (2*n - 2)` and the boundary/non-boundary cases interact with wrapped neighbors.
- The concrete failure mode was repeated `omega could not prove the goal` obligations and one `whnf` heartbeat timeout on the raw direct approach.

### What This Means
Phase 2’s closed-form successor layer is now proved for both phase 1 and phase 2.
The next successful phase-3 attempt will need a finer decomposition than phases 1 and 2:
- separate the boundary step `t = 2n - 2`
- separate the wrap step `t = 3n - 3`
- avoid asking `split_ifs` to reason through the full `let k := ...` branch in one shot

### Verification
- `lake build LeanMn.Cycle` succeeds
- `lake build LeanMn` succeeds

## Current Phase Status

Phase 2 is still not done:
- compiled: lookup catalog, full phase-1 and phase-2 mover kernels, full phase-1 and phase-2 successor theorems
- missing: phase-3 successor theorems, the unique-privileged proofs, and the final `GoodCycle`

## Exploration 8

### Strategy
Abandon the failed “prove all of phase 3 at once” attempt and keep only the phase-3 facts that compile cleanly without introducing more proof churn:
1. add typed phase-3 mover/config wrappers
2. prove the start-step mover values
3. prove the generic nonstart mover values
4. prove the closed form of the final configuration and the zero-time configuration

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now contains:
  - `lt_cup2CycleLen_of_phase3`
  - `lt_cup2CycleLen_of_phase3_interior`
  - `lt_cup2CycleLen_of_phase3_succ`
  - `phase3_last_lt`
  - `cup2Phase3Mover`
  - `cup2Phase3Config`
  - `cup2Phase3Mover_val`
  - `cup2Cycle_phase3_start_self`
  - `cup2Cycle_phase3_start_next`
  - `cup2Cycle_phase3_nonstart_self`
  - `cup2Cycle_phase3_nonstart_next`
  - `cup2Cycle_zero_val`
  - `cup2Cycle_phase3_last_val`

### Load-Bearing Observation
The surviving phase-3 facts isolate the three subproblems that remain:
- start step at `t = 2n - 2`
- nonstart interior steps `2n - 1 ≤ t < 3n - 3`
- final wrap at `t = 3n - 3`

This is better than the earlier raw `split_ifs` attempt because the mover values and endpoint configs are now explicit theorems, not re-derived arithmetic inside every later proof.

### Remaining Gap
- phase-3 left/right neighborhood lemmas are still missing
- phase-3 table-output theorems are still missing
- phase-3 step and wrap theorems are still missing
- unique-privileged proofs and `GoodCycle` remain open

### Verification
- `lake build LeanMn.Cycle` succeeds
- `lake build LeanMn` succeeds

## Latest Phase Status

Phase 2 is still not done:
- compiled: full phase-1 and phase-2 successor theorems, plus a typed/value phase-3 scaffold
- missing: phase-3 step theorems, unique-privileged proofs, and the final `GoodCycle`

## Exploration 9

### Strategy
Finish phase 3 by keeping the same local proof pattern used for phases 1 and 2, but split it into the two remaining subcases instead of fighting the full branch structure at once:
1. prove the interior nonstart step `2n - 1 ≤ t < 3n - 3`
2. define the final-time mover/config wrappers at `t = 3n - 3`
3. prove the wrap step back to time `0`

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now contains:
  - full interior phase-3 successor layer:
    - `cup2Phase3Mover_nonstart_ne_zero`
    - `cup2Phase3Mover_nonstart_not_top`
    - `cup2Phase3Mover_nonstart_left_val`
    - `cup2Phase3Mover_nonstart_right_val`
    - `cup2Cycle_phase3_nonstart_left_input`
    - `cup2Cycle_phase3_nonstart_right_input`
    - `cup2Cycle_phase3_nonstart_output`
    - `cup2Cycle_phase3_nonstart_trans_val`
    - `cup2Cycle_phase3_nonstart_stable`
    - `cup2Cycle_phase3_nonstart_step`
  - final wrap-time wrappers and step:
    - `cup2Phase3LastMover`
    - `cup2Phase3LastConfig`
    - `cup2Phase3LastMover_val`
    - `cup2Cycle_phase3_last_left_input`
    - `cup2Cycle_phase3_last_self`
    - `cup2Cycle_phase3_last_right_input`
    - `cup2Cycle_phase3_last_output`
    - `cup2Cycle_phase3_last_trans_val`
    - `cup2Cycle_phase3_last_stable`
    - `cup2Cycle_phase3_last_step`

### Load-Bearing Observation
The trans-value proofs became stable only after switching away from global `rw` on nested config applications. The working shape was:
1. introduce local `mover` / `cfg` abbreviations
2. prove the three observed input values as separate lemmas/facts
3. rewrite the `cup2OutVal` call with those facts
4. discharge the raw table lookup

That avoids the earlier failure mode where `simp` eagerly normalized `left` and `right` into modulo arithmetic before the intended rewrite lemmas could fire.

### Remaining Gap
Phase 3’s successor theorems are now complete.

Phase 2 is still not done because the final packaging is still open:
- unique-privileged proofs for the closed-form cycle configurations
- assembly of those proofs into a `GoodCycle`

### Verification
- `lake build LeanMn.Cycle` succeeds
- `lake build LeanMn` succeeds

## Latest Phase Status

Phase 2 is still not done:
- compiled: full phase-1, phase-2, and phase-3 successor theorems, including the final wrap step to time `0`
- missing: unique-privileged proofs and final `GoodCycle` packaging

## Exploration 10

### Strategy
Exploit the newly completed phase-3 transition-value theorems immediately instead of jumping straight into `singlePrivileged`:
1. package the phase-3 start mover as privileged
2. package the phase-3 interior mover as privileged
3. package the phase-3 wrap mover as privileged

This is not the full uniqueness argument, but it closes the “existence” half of the remaining phase-3 cycle facts in a build-stable way.

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now also contains:
  - `cup2Cycle_phase3_start_privileged`
  - `cup2Cycle_phase3_nonstart_privileged`
  - `cup2Cycle_phase3_last_privileged`

### Load-Bearing Observation
These proofs were cheap once the trans-value theorems existed, but the wrap-time privileged lemma needed one extra arithmetic normalization:
- the mover self index at `t = 3n - 3` has to be rewritten explicitly as `n - 1`
- plain `simpa` was not strong enough there without the cut `3*n - 3 - (2*n - 2) = n - 1`

### Remaining Gap
Phase 2 still hinges on the non-existence half:
- prove every non-mover is not privileged on the closed-form cycle
- combine existence plus non-existence into `∃! i, privileged ...`
- package the resulting cycle as a `GoodCycle`

### Verification
- `lake build LeanMn.Cycle` succeeds
- `lake build LeanMn` succeeds

## Latest Phase Status

Phase 2 is still not done:
- compiled: full successor theorems for all three phases, including the wrap step, plus privileged-existence lemmas for the phase-3 movers
- missing: unique-privileged proofs and final `GoodCycle` packaging

## Exploration 11

### Strategy
Since the lower-bound work is splitting to another agent, put the upper-bound path on a cleaner module boundary:
1. keep the existing cycle/convergence work in the core files
2. add a dedicated `UpperBound.lean` assembly file now
3. phrase the assembly theorem so it only waits on the remaining upper-bound validity proof

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/UpperBound.lean`](./lean/LeanMn/UpperBound.lean) now contains:
  - `upper_bound_of_cup2_validity`
- [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) now re-exports:
  - `upper_bound_of_cup2_validity'`

### Load-Bearing Observation
Phase 4 really is assembly-only once the missing upper-bound theorem is stated as:
- `valid (cup2System n hn)`

Everything else is already available:
- the witness system is `cup2System n hn`
- the product identity is `cup2_stateProduct`

So the remaining proof burden is correctly localized in Phase 2/3:
- produce the actual validity proof for the CUP-2 system

### Remaining Gap
Upper-bound work remaining:
- Phase 2: unique-privileged proofs and `GoodCycle` packaging
- Phase 3: convergence modules/theorems
- Phase 4 final theorem: discharge `upper_bound_of_cup2_validity` with the eventual `valid (cup2System n hn)` proof

### Verification
- `lake build LeanMn` succeeds

## Latest Phase Status

Upper-bound track status:
- compiled: Phase 1, all cycle successor theorems, phase-3 privileged-existence lemmas, and the Phase 4 assembly surface
- missing: unique-privileged proofs, convergence, and the final `valid (cup2System n hn)` theorem

## Exploration 12

### Strategy
Reduce the remaining Phase 2 burden by separating the cycle-object packaging from the uniqueness proof itself:
1. add list/index lemmas for `cup2CycleConfigs`
2. prove the closed-step theorem for every time index `k`
3. package a `GoodCycle` constructor that only assumes unique privilege at each closed-form time

This isolates the real missing proof obligation to the non-existence half of single privilege.

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now also contains:
  - `cup2CycleConfigs_get_eq`
  - `cup2CycleConfigs_get_next_eq`
  - `cup2CycleNext_phase1`
  - `cup2CycleNext_phase2`
  - `cup2CycleNext_phase3_interior`
  - `cup2CycleNext_phase3_start`
  - `cup2CycleNext_phase3_last`
  - `cup2Cycle_closed_step`
  - `cup2GoodCycleOfUniquePrivileged`

### Load-Bearing Observation
The right decomposition is:
- existence/closure of the cycle object
- uniqueness of the privileged processor on each cycle configuration

The first piece is now finished. The constructor `cup2GoodCycleOfUniquePrivileged` shows that once we can prove
`∃! i, privileged ...`
for each time `t`, the `GoodCycle` itself is immediate.

The only nontrivial proof engineering issue in this slice was matching list indices from `List.ofFn` to the closed-form time parameter. The pair
- `cup2CycleConfigs_get_eq`
- `cup2CycleConfigs_get_next_eq`

is enough to keep later proofs out of low-level `List.get` arithmetic.

### Remaining Gap
Phase 2 is still not complete.

What remains is now fully localized:
- prove unique privilege for each closed-form configuration
- feed that theorem into `cup2GoodCycleOfUniquePrivileged`

Upper-bound work after that:
- Phase 3 convergence
- Phase 4 final validity/upper-bound theorem

### Verification
- `lake build LeanMn` succeeds

## Latest Phase Status

Upper-bound track status:
- compiled: all closed-form cycle successor theorems, phase-3 privileged-existence lemmas, the `GoodCycle` packaging layer, and the Phase 4 assembly surface
- missing: unique-privileged proofs, convergence, and the final `valid (cup2System n hn)` theorem

## Exploration 13

### Strategy
Finish Phase 2 by proving uniqueness of the privileged processor on every
closed-form cycle configuration, phase by phase:
1. prove nonmover `trans = self` theorems instead of reasoning directly with `¬privileged`
2. package each time slice into `∃! i, privileged ... i`
3. dispatch on the cycle time index `t : Fin (3*n - 2)` and instantiate
   `cup2GoodCycleOfUniquePrivileged`

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now also contains:
  - Phase 1 uniqueness layer:
    - `cup2Cycle_phase1_one_before_mover`
    - `cup2Cycle_phase1_zero_from_mover`
    - `cup2Cycle_phase1_nonmover_trans_val`
    - `cup2Cycle_phase1_nonmover_not_privileged`
    - `cup2Cycle_phase1_singlePrivileged`
  - Phase 2 uniqueness layer:
    - `cup2Cycle_phase2_one_before_front`
    - `cup2Cycle_phase2_two_before_top`
    - `cup2Cycle_phase2_top_val`
    - `cup2Cycle_phase2_nonmover_trans_val`
    - `cup2Cycle_phase2_nonmover_not_privileged`
    - `cup2Cycle_phase2_singlePrivileged`
  - Phase 3 uniqueness layer:
    - `cup2Cycle_phase3_start_two_before_top`
    - `cup2Cycle_phase3_start_nonmover_trans_val`
    - `cup2Cycle_phase3_start_nonmover_not_privileged`
    - `cup2Cycle_phase3_start_singlePrivileged`
    - `cup2Cycle_phase3_nonstart_val`
    - `cup2Cycle_phase3_nonstart_zero_before_mover`
    - `cup2Cycle_phase3_nonstart_two_before_top`
    - `cup2Cycle_phase3_nonstart_top_val`
    - `cup2Cycle_phase3_nonstart_nonmover_trans_val`
    - `cup2Cycle_phase3_nonstart_nonmover_not_privileged`
    - `cup2Cycle_phase3_nonstart_singlePrivileged`
    - `cup2Cycle_phase3_last_zero_before_top`
    - `cup2Cycle_phase3_last_nonmover_trans_val`
    - `cup2Cycle_phase3_last_nonmover_not_privileged`
    - `cup2Cycle_phase3_last_singlePrivileged`
  - Global packaging:
    - `cup2Cycle_singlePrivileged`
    - `cup2GoodCycle`
- [`LeanMn/UpperBound.lean`](./lean/LeanMn/UpperBound.lean) now also contains:
  - `cup2_valid_of_converges`
  - `upper_bound_of_cup2_converges`

### Load-Bearing Observation
The workable proof pattern was uniform across all phases:
- first normalize the closed-form state into a simple prefix/suffix value lemma
- then prove that every nonmover sees one of the stable lookup contexts
- finally combine mover privilege with nonmover non-privilege into `∃!`

For Phase 2 the useful normalization variable is the front
`2*n - 1 - t`, not the mover index itself. This makes the local-context
classification match the table rows `111 / 122 / 222 / 121 / 211`.

### Remaining Gap
Phase 2 is now complete.

Upper-bound work still remaining:
- Phase 3: convergence for `cup2System n hn`
- Phase 4: discharge `valid (cup2System n hn)` and finish the final
  upper-bound theorem from the explicit `cup2GoodCycle`

### Verification
- `lake build LeanMn.Cycle LeanMn` succeeds

## Latest Phase Status

Upper-bound track status:
- compiled: Phase 1, full Phase 2 (`cup2GoodCycle`), and the Phase 4
  assembly surface
- missing: convergence and the final `valid (cup2System n hn)` theorem

## Exploration 14

### Strategy
Build the full Part A convergence scaffold first, before returning to the
table-local `Ψ` inequalities:
1. define a self-contained frontier-count / frontier-type / `Ψ` layer for
   `cup2Spec n hn`
2. prove the ring-neighbor bookkeeping needed to isolate the two frontiers
   touched by a move
3. package the nonnegative bad-step relation that will eventually be shown
   well-founded by the `(n - fc, Ψ)` lexicographic measure

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Convergence/CopyDAG.lean`](./lean/LeanMn/Convergence/CopyDAG.lean) now contains:
  - frontier / potential definitions:
    - `frontierBitVal`
    - `cup2FrontierTypeVal`
    - `cup2W1`
    - `cup2W2`
    - `cup2PsiWeightVal`
    - `cup2FrontierBit`
    - `cup2PsiTerm`
    - `cup2Fc`
    - `cup2Psi`
  - ring-neighbor infrastructure:
    - `left_ne_self`
    - `left_right`
    - `right_left`
    - `right_ne_self`
    - `adjacentComplement`
    - `mem_adjacentComplement_iff`
    - `right_ne_of_mem_adjacentComplement`
    - `sum_univ_eq_adjacentComplement`
  - move-local split layer:
    - `cup2FrontierBit_move_eq_of_mem_adjacentComplement`
    - `cup2PsiTerm_move_eq_of_mem_adjacentComplement`
    - `localFcBefore`
    - `localFcAfter`
    - `localPsiBefore`
    - `localPsiAfter`
    - `cup2Fc_split`
    - `cup2Psi_split`
    - `cup2Fc_move_split`
    - `cup2Psi_move_split`
    - `cup2Fc_rest_move_eq`
    - `cup2Psi_rest_move_eq`
  - relation scaffold:
    - `cup2BadStepNonneg`
- [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) now imports the convergence module.

### Load-Bearing Observation
The real blocker is no longer the global bookkeeping. The move-local split
identities compile and isolate exactly the two adjacent frontiers touched by
each step. What remains is the finite case analysis proving the local
`Δfc = 0` implies `ΔΨ < 0` inequalities for the five position classes.

My first attempt to express the bot case directly with `fin_cases` /
`interval_cases` did not reduce the local table arguments aggressively
enough to finish by `omega`, so that proof was backed out to keep the build
green.

### Remaining Gap
Upper-bound convergence still needs:
- the five position-class local `Δfc = 0 -> ΔΨ < 0` lemmas
- the global theorem turning `fc` preservation on a `step` into `Ψ` decrease
- the `(n - fc, Ψ)` well-foundedness proof for `cup2BadStepNonneg`
- then the anomalous / full bad-step layer needed to finish Phase 3 and wrap
  Phase 4

### Verification
- `lake env lean LeanMn/Convergence/CopyDAG.lean` succeeds
- `lake build LeanMn.Convergence.CopyDAG` succeeds

## Exploration 15

### Strategy
Finish Part A all the way through the nonnegative-step descent theorem
instead of stopping at the local `ΔΨ` catalog:
1. classify every position-class local context that can occur on a
   nonnegative copy/anomalous step
2. turn those finite local cases into a global lexicographic decrease
   theorem for `(n - fc, Ψ)`
3. prove the relation `cup2BadStepNonneg` well-founded by `InvImage`
   over `Prod.Lex (<) (<)`

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Convergence/CopyDAG.lean`](./lean/LeanMn/Convergence/CopyDAG.lean) now additionally contains:
  - finite nonnegative local classifiers:
    - `bot_nonneg_cases`
    - `low_nonneg_cases`
    - `mid_nonneg_cases`
    - `high_nonneg_cases`
    - `top_nonneg_cases`
  - per-class local progress lemmas:
    - `bot_local_nonneg_progress`
    - `low_local_nonneg_progress`
    - `mid_local_nonneg_progress`
    - `high_local_nonneg_progress`
    - `top_local_nonneg_progress`
  - global measure infrastructure:
    - `cup2NonnegMeasure`
    - `cup2FrontierBit_le_one`
    - `cup2Fc_le_n`
    - `cup2First_lt_of_localFc_lt`
    - `cup2Fc_eq_of_localFc_eq`
    - `cup2Psi_lt_of_localPsi_lt`
  - the load-bearing Part A theorems:
    - `cup2BadStepNonneg_decreases`
    - `cup2BadStepNonneg_wf`

### Load-Bearing Observation
The right global measure for the still-open convergence work is now
compiled, not just described: `cup2BadStepNonneg` is well-founded by the
lexicographic pair `(n - fc, Ψ)`. Positive-`Δfc` anomalous steps strictly
lower the first coordinate, while zero-`Δfc` copy-neighbor steps hold the
first coordinate fixed and strictly lower the second.

This means Part A is strong enough to use downstream inside B1-B4,
especially the B4 deadlock loop where the proof text only needs "each
restart strictly decreases `(fc, Ψ)` via intervening copy-neighbor
transitions."

### Remaining Gap
Upper-bound convergence is still missing the actual Part B/C arguments:
- no B1-B4 refire-bound theorem is proved yet
- there is still no full `WellFounded (badStep (cup2System n hn) (cup2GoodCycle n hn))`
- therefore Phase 3 and Phase 4 remain open

### Verification
- `lake env lean LeanMn/Convergence/CopyDAG.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 16

### Strategy
Start Phase 3B from the lowest-risk side: transcribe the finite boundary
table audits from §3.4 into a compiled module before attempting any
scheduler/path arguments.

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Convergence/Anomalous.lean`](./lean/LeanMn/Convergence/Anomalous.lean) now exists and compiles.
- It contains the first boundary-audit lemmas needed by B1-B4:
  - `bot_drop_from_one_cases`
  - `bot_left_zero_self_one_stable`
  - `low_zero_two_exact`
  - `top_zero_self_one_drop`
  - `top_rise_copy_cases`
  - `top_drop_from_one_requires_left_zero`
  - `high_output_two_transition_cases`
  - `high_output_two_transition_requires_right_one`
  - `high_drop_from_two_cases`
  - `high_rise_from_zero_cases`
- It also lifts the first of those audits to actual ring configurations:
  - `bot_output_zero_self_one_cases_val`
  - `top_output_zero_self_one_requires_left_zero_val`
  - `top_output_one_self_zero_right_one_cases_val`
  - `high_output_two_transition_requires_right_one_val`
- [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) now imports the anomalous module, so `lake build LeanMn` checks it.

### Load-Bearing Observation
The B4 proof text's two critical finite constraints are now formalized as
actual lemmas:
- top drops from `1` require left input `0`
- genuine `T_high` transitions to output `2` require right input `1`

That is enough finite structure to start formalizing the B4 deadlock loop
without first re-reading the raw tables every turn. The configuration-level
lift means the next proof can already talk in terms of `Config (cup2Spec n hn)`
and actual boundary processors rather than raw `(L,S,R)` triples.

### Remaining Gap
`Anomalous.lean` is still only a boundary-audit scaffold:
- no B1/B2/B3/B4 path-descent theorem is proved yet
- no refire-bound theorem is available
- no link to full convergence has been added

### Verification
- `lake env lean LeanMn/Convergence/Anomalous.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 22

### Strategy
Start the actual `Interior.lean` route from the proof plan instead of
guessing another boundary bridge. The key target is the deep-interior
classification used in Claim 3.5.1:

- if a middle processor at position `j ∈ {3, ..., n-4}` fires
- and the move has `Δfc = 0`
- and the TP invariants are preserved

then the local context must be one of the three hop entries from the
analytical proof, not one of the extra zero-`Δfc` table cases.

### Outcome
SUCCESS

### What Compiled
- New module:
  [`LeanMn/Convergence/Interior.lean`](./lean/LeanMn/Convergence/Interior.lean)
- It is imported from [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean).
- [`LeanMn/Convergence/TP.lean`](./lean/LeanMn/Convergence/TP.lean) now also exposes:
  - `cup2TpPreserving_local_eqs`
- The new interior theorems are:
  - `IsMidHopTriple`
  - `midHopBudgetVal`
  - `midHopBudget`
  - `mid_tp_zero_cases`
  - `cup2TpPreserving_mid_zero_cases_val`
  - `cup2TpPreserving_mid_zero_left_two_false`
  - `cup2TpPreserving_mid_zero_left_zero_val`
  - `cup2TpPreserving_mid_zero_left_one_cases_val`
  - `cup2TpPreserving_mid_zero_budget_drop`

### Load-Bearing Observation
This is the first real Lean artifact for Phase 3C’s analytical interior
argument. `CopyDAG.lean` already knew that a zero-`Δfc`, privileged middle
move could be one of five local cases:

- `(0,2,2)`
- `(1,0,0)`
- `(1,1,2)`
- `(2,1,1)`
- `(2,2,0)`

The new TP-side equalities now rule out the two `L = 2` cases in the deep
interior. So for positions `3 ≤ j` and `j + 2 < n`, a zero-`Δfc`,
TP-preserving privileged middle move is forced into exactly the three hop
contexts used by the proof text:

- `(0,2,2) -> 0`
- `(1,0,0) -> 1`
- `(1,1,2) -> 2`

In particular, with fixed left neighbor value `2`, no such move exists:
that is now the theorem
`cup2TpPreserving_mid_zero_left_two_false`.

### Why This Matters
This is exactly the seam needed for the boundary-fixed hop impossibility
argument:

- deep interior TP-preserving zero-`Δfc` moves depend on the left neighbor
  in the rigid way described by the analytical proof
- the forbidden `L = 2` branch is now formalized
- the surviving fixed-left behaviors are now explicit Lean theorems:
  - `L = 0` forces the unique hop `2 -> 0`
  - `L = 1` forces either `0 -> 1` or `1 -> 2`
- those cases are now packaged into a strict local descent lemma:
  `cup2TpPreserving_mid_zero_budget_drop`
  says a deep-interior zero-`Δfc`, TP-preserving privileged middle move
  strictly decreases the per-site hop budget determined by its fixed left
  neighbor
- the next step can be an induction from position `3` outward, using the
  fixed left neighbor to block a full local value cycle

### Remaining Gap
Phase 4 is still not done. On the Phase 3C side the remaining work is now
more concrete:

- lift the local hop classification into a no-cycle / no-refire theorem for
  deep interior positions with fixed left neighbor
- chain that by induction from `c[2]` to get the full `Interior.lean`
  boundary-fixed hop impossibility theorem
- then combine that with the fixed 6-tuple DAG in
  [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean)

### Verification
- `lake env lean LeanMn/Convergence/Interior.lean` succeeds
- `lake build LeanMn.Convergence.TP` succeeds
- `lake build LeanMn` succeeds

## Exploration 21

### Strategy
Test the first TP-route candidate directly in Lean instead of assuming the
Python extraction had already identified the right monotone quantity:
formalize `exp2_count`, prove its local move split, and try the universal
theorem

`cup2Exp2Count n hn (move ...) ≤ cup2Exp2Count n hn c`.

If that theorem fails, keep the useful artifact and record the exact
counterexample rather than leaving a broken candidate theorem around.

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Convergence/TP.lean`](./lean/LeanMn/Convergence/TP.lean) now compiles and is imported from [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean).
- The module contains the first TP-side quantity and its local decomposition:
  - `cup2Exp2BitVal`
  - `cup2Exp2Term`
  - `cup2Exp2Count`
  - `cup2Exp2_split`
  - `cup2Exp2_move_split`
  - `cup2Exp2_rest_move_eq`
- It also now contains the corrected extracted TP interface:
  - `cup2Int21BitVal`
  - `cup2Int21Term`
  - `cup2Int21Count`
  - `cup2Int21_split`
  - `cup2Int21_move_split`
  - `cup2Int21_rest_move_eq`
  - `cup2Exp2WeightTerm`
  - `cup2Exp2Weight`
  - `cup2Exp2Weight_split`
  - `cup2Exp2Weight_move_split`
  - `cup2Exp2Weight_rest_move_eq`
  - `cup2TpInvariant`
  - `cup2TpPreservingMove`
- It also contains a compiled Lean counterexample to the naive monotonicity claim:
  - `cup2Exp2CounterexampleConfig`
  - `cup2Exp2CounterexampleMover`
  - `cup2Exp2Count_counterexample_before`
  - `cup2Exp2Count_counterexample_after`
  - `cup2Exp2Count_move_le_counterexample`

### Exact Failure
The attempted local lemma

`localExp2Mid_eq2_le (L S R : Fin 3) :
  (if TMidVal L.1 S.1 R.1 = 2 ∧ R.1 ≠ 2 then 1 else 0) ≤
    (if S.1 = 2 ∧ R.1 ≠ 2 then 1 else 0)`

is false. Lean reduced it to the concrete counterexample

`L = 2, S = 1, R = 1`

where `TMidVal 2 1 1 = 2`, so the left side is `1` and the right side is
`0`.

The exact error that exposed this was:
- `Tactic 'decide' proved that the proposition ... is false`

### Load-Bearing Observation
The oversimplified route was wrong: `exp2_count` is not monotone on every
CUP-2 move. The explicit Lean counterexample is the configuration

`[0, 2, 1, 1, 0]` on `n = 5`, moved at processor `2`,

for which:
- before move: `cup2Exp2Count = 0`
- after move: `cup2Exp2Count = 1`

This matches the actual extraction scripts more closely. The TP relation in
`clb_convergence_proof103.py` does **not** use `exp2_count` alone; it keeps
only edges preserving all three quantities:
- `exp2_count`
- `int_21`
- `exp2_weight`

So the real formalization target is a refined constant-layer relation, not a
single universal monotonicity theorem.

### What This Rules Out
- Do not continue trying to prove `cup2Exp2Count_move_le` as a global move
  theorem; it is false.
- Do not use `exp2_count` alone as the Lean bridge from bad steps to the
  fixed 6-tuple DAG.

### Remaining Gap
Phase 4 is still open. On the TP / constant-layer side, the next live task
is now better specified:
- formalize `int_21` and `exp2_weight` in Lean
- define the actual TP-edge predicate as simultaneous preservation of the
  extracted quantities
- use that stronger hypothesis, not raw anomalous boundary context, in the
  bridge to [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean)

### Verification
- `lake env lean LeanMn/Convergence/TP.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 20

### Strategy
Add the fixed `324`-state / `617`-edge 6-tuple certificate to Lean, then
replace the opaque `Fin 324` interface with a natural boundary-state
projection so the remaining convergence bridge can talk directly about
`(c_0, c_1, c_2, c_{n-3}, c_{n-2}, c_{n-1})`.

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now contains:
  - the generated fixed certificate:
    - `sixStateRankVals`
    - `sixTupleEdgeVals`
    - `sixTuple_edge_rank_decrease`
    - `sixTuple_wf`
  - the natural boundary wrapper:
    - `SixBoundary`
    - `SixBoundary.encode`
    - `sixBoundaryEdge`
  - the CUP-2 projection layer for `n ≥ 9`:
    - `cup2BoundaryIdx0`
    - `cup2BoundaryIdx1`
    - `cup2BoundaryIdx2`
    - `cup2BoundaryIdxN3`
    - `cup2BoundaryIdxN2`
    - `cup2BoundaryIdxN1`
    - `cup2Boundary6`
    - `cup2BoundaryState`
  - the first real reduction lemmas for the bridge:
    - `cup2Boundary6_move_eq_of_deep`
    - `cup2BoundaryState_move_eq_of_deep`
    - `cup2BoundaryState_changed_implies_boundary_index`
- [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) now imports `LeanMn.Convergence.SixTuple`.

### Load-Bearing Observation
The fixed 6-tuple DAG is now a real Lean artifact, but the more important
proof-theoretic move is the deep-interior reduction:

- if a move happens strictly inside positions `3 .. n-4`, the projected
  6-boundary state is unchanged
- therefore any bad step that changes the 6-boundary state must come from
  one of the six distinguished boundary-near positions

This collapses the remaining bridge theorem from “all processors” to a
finite boundary case split.

### Extra Empirical Check
I also re-ran the extracted automata to test whether the self-contained
8-tuple route is actually stable across `n`.

- 6-tuple: already confirmed identical for `n = 9` and `n = 10`
- 8-tuple: **not** identical
  - `n = 9`: `2912` states, `5683` edges
  - `n = 10`: `2914` states, `5701` edges
  - `18` edges appear in `n = 10` but not `n = 9`

So the next Lean bridge should stay on the 6-boundary projection, not
switch to an 8-tuple certificate.

### Remaining Gap
Phase 4 is still not closed. The remaining upper-bound gap is now more
explicit:
- no theorem yet that actual boundary-changing CUP-2 bad steps refine to
  `sixBoundaryEdge`
- no full `WellFounded (badStep ...)`
- no convergence theorem
- no final `valid (cup2System n hn)` proof

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 37 (probe)

### Strategy
Finish the boundary-projection interface that the failed direct bridge
was missing:
1. prove explicit `cup2Boundary6 (move ...) = { cup2Boundary6 ... with ... }`
   lemmas for the six boundary indices
2. do it with `move_apply_ne` and concrete index-inequality proofs,
   not via giant `simpa` goals over raw `cup2Boundary6 (move ...)`
3. keep the repository green before retrying the actual bridge

### Outcome
SUCCEEDED

### What Compiled
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2Boundary6_move_idx0`
  - `cup2Boundary6_move_idx1`
  - `cup2Boundary6_move_idx2`
  - `cup2Boundary6_move_idxN3`
  - `cup2Boundary6_move_idxN2`
  - `cup2Boundary6_move_idxN1`

### Load-Bearing Content
- The failed bridge attempt in Exploration 36 was not blocked by the
  finite certificate anymore; it was blocked by the lack of a usable
  projection API from configurations to `SixBoundary`.
- That API now exists in compiled form. Each boundary move is exposed as
  a literal record update on `cup2Boundary6`, with the untouched fields
  discharged by explicit `move_apply_ne` equalities.
- This removes the main elaboration obstacle from the next bridge pass:
  the boundary-changing TP-zero proof can now target these six record
  updates directly instead of trying to normalize raw
  `cup2Boundary6 (move ...)` expressions.

### Consequence
- The next live target is again exact:
  prove `cup2BoundaryChangeTpZeroStep -> cup2BoundaryTpZeroCertStep`
  using the new `cup2Boundary6_move_idx*` lemmas plus the already
  compiled local TP-zero classifiers and finite certificate.

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 34 (probe)

### Strategy
Push the future-gain split far enough that the whole TP-preserving
zero-`fc` bad-step layer decomposes into:
1. a fully resolved well-founded part
2. one explicit unresolved constant-future boundary relation

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadTpZeroStep`
  - `cup2BadFixedBoundaryTpZeroStep`
  - `cup2BadTpZeroResolvedStep`
  - `cup2TpZeroResolvedMeasure`
  - `cup2BadTpZeroStep_boundary_split`
  - `cup2BadTpZeroStep_split`
  - `cup2BadFixedBoundaryTpZeroStep_deep`
  - `cup2BadTpZeroResolvedStep_decreases`
  - `cup2BadTpZeroResolvedStep_wf`

### Load-Bearing Content
- The entire TP-preserving zero-`fc` bad-step layer is now formally split:
  - fixed-boundary steps, which reduce to the solved deep-interior hop
    relation
  - boundary-changing steps with strict future-gain drop, which are
    well-founded by `cup2TpFutureFc`
  - the only remaining unsolved branch:
    `cup2BadBoundaryChangeTpConstFutureStep`
- The resolved portion is not just classified; it now has its own
  compiled well-founded theorem via a lexicographic measure
  `(cup2TpFutureFc, deepMidHopPotential)`.

### Consequence
- Phase 4’s live upper-bound blocker is now completely explicit in Lean:
  the constant-future, boundary-changing, TP-preserving, zero-`fc`
  bad-step relation.
- Everything else inside the TP-preserving zero-`fc` bad-step layer is
  already discharged.

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 35 (probe)

### Strategy
Turn the vague TP-zero boundary obstruction into an explicit finite Lean
artifact:
1. re-audit the current unresolved slice against the stored `617`-edge
   certificate
2. isolate the exact non-certificate boundary pairs that appear before
   the future-gain filter
3. add those pairs and the corresponding guarded edge lemmas to
   [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean)

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `sixBoundaryTpZeroNonedgeVals`
  - `sixBoundaryTpZeroNonedgePair`
  - `sixBoundaryEdge_bot_001_of_not_nonedge`
  - `sixBoundaryEdge_top_011_of_not_nonedge`
  - `cup2LocalFc_eq_of_fc_eq_move`

### Load-Bearing Findings
- The raw TP-preserving, zero-`fc`, boundary-changing slice is **not**
  covered by the `617`-edge certificate, but the obstruction is now
  fully explicit and finite:
  - across `n = 9, 10, 11`, there are exactly `16` stable 6-boundary
    source-target pairs outside `sixBoundaryEdge`
  - every other raw TP-zero boundary-changing pair already lies in the
    stored `617`-edge graph
- The obstruction is no longer “some missing top/bot theorem.” It is an
  exact finite set encoded directly in Lean.
- This sharpens the remaining proof obligation further:
  - split boundary-changing TP-zero steps into
    `sixBoundaryEdge ∨ sixBoundaryTpZeroNonedgePair`
  - then prove the future-gain-constant relation excludes the `16`
    explicit nonedge pairs

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 56 (upper-bound module refactor)

### Strategy
Reshape the upper-bound side to match the lower-bound folder/module
layout without changing public imports:
1. move the theorem payload out of the flat `LeanMn/UpperBound.lean`
   file
2. create `LeanMn/UpperBound/Theorem.lean` as the assembly file
3. keep `LeanMn/UpperBound.lean` as the umbrella module that re-exports
   the folder entrypoint

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/UpperBound/Theorem.lean`](./lean/LeanMn/UpperBound/Theorem.lean) now contains:
  - `cup2_valid_of_converges`
  - `upper_bound_of_cup2_converges`
  - `upper_bound_of_cup2_validity`
- [`LeanMn/UpperBound.lean`](./lean/LeanMn/UpperBound.lean) is now the umbrella import:
  - `import LeanMn.UpperBound.Theorem`

### Load-Bearing Consequence
- The upper-bound side is now organized as a real module namespace
  rooted at `LeanMn/UpperBound/...`, parallel to the lower-bound folder.
- Existing imports keep working:
  - `import LeanMn.UpperBound`
- Future upper-bound subfiles can now be added under the same folder
  without reworking the public import path again.

### Verification
- `lake build LeanMn` succeeds

## Exploration 52 (certificate simplification)

### Strategy
Make the new boundary-slack certificate easier to target from actual
bridge proofs:
1. remove the unnecessary `Fin 1296` wrapper from the certificate
   relation
2. prove rank decrease directly from finite edge-list membership
3. add a config-level helper so later bridge lemmas only need code
   equalities plus finite edge membership

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/BoundarySlackCert.lean`](./lean/LeanMn/Convergence/BoundarySlackCert.lean) now exposes the certificate on raw `Nat` codes again:
  - `sixBoundarySlackEdge`
  - `sixBoundarySlackEdge_rank_decrease`
  - `sixBoundarySlackEdge_wf`
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BoundaryConstFutureCertStep_of_code_eq`

### Load-Bearing Content
- The first certificate version worked but forced every later bridge
  theorem to produce separate `< 1296` witnesses.
- The simplified version proves well-foundedness by:
  - converting `contains = true` to list membership
  - applying `native_decide` only to the finite stored edge list
- So later constant-future boundary bridges can now target the wrapper by
  the exact shape:
  - prove `cup2BoundarySlackCode ... c = k`
  - prove `cup2BoundarySlackCode ... c' = k'`
  - prove `sixBoundarySlackEdge k' k`

### Consequence
- The remaining Phase 4 blocker is still the same bridge theorem from
  `cup2BadBoundaryChangeConstFutureStep` to
  `cup2BoundaryConstFutureCertStep`.
- But the proof interface for that bridge is now materially cleaner,
  especially for the already-compiled outer boundary cases
  `idx0 / idx1 / idxN2 / idxN1`.

### Verification
- `lake build LeanMn.Convergence.BoundarySlackCert` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 51 (boundary-slack finite certificate)

### Strategy
Import the remaining constant-full-future boundary obstruction as a
literal finite DAG instead of leaving it only as probe output:
1. regenerate the current-variant constant-`cup2FutureFc`,
   boundary-changing projection from the local Python verifier
2. package the resulting `(boundary6, futureSlack)` edge set and rank
   function as a standalone Lean certificate
3. expose that certificate at the config level in `SixTuple.lean`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/BoundarySlackCert.lean`](./lean/LeanMn/Convergence/BoundarySlackCert.lean) is new and now contains:
  - `sixBoundarySlackEdgeVals`
  - `sixBoundarySlackRankVals`
  - `sixBoundarySlackEdgeState`
  - `sixBoundarySlackEdge`
  - `sixBoundarySlackEdge_wf`
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BoundaryConstFutureCertStep`
  - `cup2BoundaryConstFutureCertStep_wf`

### Load-Bearing Content
- The logged probe is now a first-class Lean artifact on the current
  `TMidVal 2 1 1 = 2` variant:
  - `362` projected `(boundary6, futureSlack)` states
  - `797` union edges from `n = 9` and `n = 10`
  - DAG rank `24`
- The certificate is implemented as a finite `Fin 1296` core with a
  thin `Nat` wrapper, which avoids the failed infinite-domain
  `native_decide` attempt and keeps the config-level API usable from
  `SixTuple.lean`.

### Consequence
- The remaining Phase 4 blocker is no longer “construct the right finite
  object.”
- That object is now in Lean and build-clean.
- The live proof obligation is now the bridge theorem from
  `cup2BadBoundaryChangeConstFutureStep` to
  `cup2BoundaryConstFutureCertStep`.

### Verification
- `lake build LeanMn.Convergence.BoundarySlackCert` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 49 (hidden-neighbor right probe)

## Exploration 50 (hidden-neighbor TP-zero closure)

### Strategy
Finish the hidden-neighbor TP-zero boundary slice in two steps:
1. turn the stable left-side trichotomy into an actual boundary
   certificate theorem for `idx2`
2. stop trying to mirror the false raw right-side local classifier and
   instead route `idxN3` through the already-compiled deep-interior
   TP-zero lemmas from `Interior.lean`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `sixBoundaryTpZeroCert_midL_local`
  - `cup2Boundary6_move_idx2_local`
  - `cup2Boundary_idx2_tp_zero_cert`
  - `cup2Boundary6_move_idxN3_local`
  - `cup2Boundary_idxN3_tp_zero_cert`
  - `cup2BoundaryChangeTpZeroStep_idx2_cert`
  - `cup2BoundaryChangeTpZeroStep_idxN3_cert`
- The wrapper theorem
  `cup2BoundaryChangeTpZeroStep_cert_or_mid`
  no longer leaves hidden-neighbor exceptions; it now certifies every
  TP-preserving zero-`fc` boundary-changing step directly.

### Load-Bearing Content
- The TP-zero hidden-neighbor boundary obstruction is now gone.
- `idx2` is packaged by a local finite certificate theorem.
- `idxN3` is discharged by the stronger interior TP-zero facts already
  proved in `Interior.lean`, not by the false naive local mirror.
- So the entire relation
  `cup2BoundaryChangeTpZeroStep`
  now refines to the finite boundary certificate.

### Consequence
- The old TP-zero boundary gap is no longer the live Phase 4 blocker.
- What remains is still the stronger constant-full-future boundary
  branch in `SixTuple.lean`, namely the finite
  `(boundary6, futureSlack)` bridge for
  `cup2BadBoundaryChangeConstFutureStep`.

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

### Strategy
Test whether the right hidden-neighbor branch can be reduced by the same
kind of raw local classifier that worked on the left:
1. keep the stable lifted left-side theorem
   `cup2Boundary_idx2_tp_zero_cases`
2. try the analogous raw finite classifier for the right-side branch
   `idxN3`
3. keep only the stable part and record the failure constraint if the
   naive mirror is false

### Outcome
PARTIAL SUCCESS

### What Stayed Stable
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) still contains the compiled hidden-neighbor left reduction:
  - `cup2Boundary_idx2_tp_zero_cases`

### Failure Constraint
- The naive raw right-side mirror was tested and removed.
- Concretely, the direct local proposition
  “`localFc` equality + local exp2 equality + privilege at a mid move
  forces `(cN3,cN2) ∈ {(2,2),(0,0),(1,2)}`”
  is **false**; `native_decide` rejects it.

### Load-Bearing Consequence
- The two hidden-neighbor branches are no longer symmetric proof tasks.
- `idx2` already reduces to a finite visible trichotomy.
- `idxN3` needs a strictly stronger right-side hypothesis than the naive
  local `fc + exp2 + privilege` slice; likely it must also use the extra
  TP components (`int21` / weight) or another boundary-specific bridge.

### Consequence
- The next upper-bound move should not keep trying to mirror the `idx2`
  proof shape directly onto `idxN3`.
- The right branch needs a stronger local invariant, and that is now an
  explicit proof obligation rather than a guess.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds after removing the
  false mirror attempt

## Exploration 48 (hidden-neighbor left reduction)

### Strategy
Push the hidden-neighbor boundary work forward without forcing the full
certificate wrapper in one shot:
1. attack `idx2` first, not both hidden-neighbor branches at once
2. lift the local `midL_tp_zero_cases` finite classifier from raw
   triples to the actual boundary position `idx2`
3. keep only the stable lifted case theorem and back out the brittle
   final edge-packaging attempt

### Outcome
PARTIAL SUCCESS

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2Boundary_idx2_tp_zero_cases`

### Load-Bearing Content
- The left hidden-neighbor TP-zero branch is no longer opaque.
- For a TP-preserving zero-`fc` move at `idx2`, the visible boundary data
  is now formally reduced to exactly the three finite `midL` contexts:
  - `(c1, c2) = (0, 2)`
  - `(c1, c2) = (1, 0)`
  - `(c1, c2) = (1, 1)`
- That is the same finite trichotomy behind the stored
  `sixBoundaryEdge_midL_*` lemmas; the remaining gap is only the final
  certificate packaging, not the local classification.

### Failure Constraint
- The direct theorem
  `cup2Boundary_idx2_tp_zero_cert`
  was attempted and removed.
- The brittle part is the final record-update packaging from the lifted
  `midL` classification into an actual `sixBoundaryTpZeroCertStep`
  theorem, not the underlying case reduction.

### Consequence
- The hidden-neighbor blocker is narrower than before:
  `idx2` already has a compiled visible-case reduction, and `idxN3`
  remains the only branch with no analogous lifted theorem yet.
- The next proof pass should package `cup2Boundary_idx2_tp_zero_cases`
  into the certificate and then mirror the same structure on `idxN3`.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 47 (outer local closure)

### Strategy
Finish the fully local outer boundary half of the constant-future code
bridge before touching the hidden-neighbor cases:
1. mirror the existing `idx0 / idx1` wrappers on the right side
2. package `idxN2 / idxN1` as explicit `(boundary6, futureSlack)` code
   cases
3. leave the remaining nonlocal residue isolated to `idx2 / idxN3`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadBoundaryChangeConstFuture_idxN2_code_cases`
  - `cup2BadBoundaryChangeConstFuture_idxN1_code_cases`

### Load-Bearing Content
- All four fully local boundary-changing constant-`cup2FutureFc`
  branches are now expressed in the same explicit numeric interface:
  - `idx0`
  - `idx1`
  - `idxN2`
  - `idxN1`
- For each of those branches, the bridge to the eventual finite
  certificate is reduced to:
  - one already-proved boundary projection rewrite
  - one exact `Δfc` case from the five-way split
  - one exact future-slack shift lemma
- So the remaining nontrivial boundary bridge is now exactly the hidden
  neighbor pair:
  `idx2 / idxN3`.

### Consequence
- The constant-future Phase 4 blocker is narrower than before in code,
  not just conceptually.
- The next proof move should focus only on the hidden-neighbor branches
  and not reopen any of the outer boundary algebra.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 46 (bridge cases)

### Strategy
Make the remaining constant-`cup2FutureFc` boundary bridge more literal
before attempting a full finite certificate:
1. move the left-side code-case wrappers so they sit after the exact
   `Δfc` split they depend on
2. package the `idx0 / idx1` boundary-changing constant-future steps as
   explicit `(boundary6, futureSlack)` code cases
3. briefly test direct extraction of the projected edge set from Lean
   itself, and keep only the stable result

### Outcome
PARTIAL SUCCESS

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadBoundaryChangeConstFuture_idx0_code_cases`
  - `cup2BadBoundaryChangeConstFuture_idx1_code_cases`

### Load-Bearing Content
- The fully local left-boundary branches of the remaining blocker are now
  expressed in the exact numeric shape that the eventual finite
  certificate will consume:
  source boundary state
  updated boundary state
  exact slack shift in `{-2,-1,0,+1,+2}`.
- These two theorems combine:
  - the boundary projection lemmas
  - the exact `Δfc` split
  - the new future-slack shift lemmas
  into direct code equalities, so the next certificate proof does not
  need to re-open those local rewrites.

### Failure Constraint
- A direct extraction route through a temporary `Check.lean` scratch file
  was tested and then removed.
- The obstacle is not the semantics but executability:
  `cup2FutureFc` is currently packaged as a `noncomputable` finite
  supremum over reachable bad descendants, so a plain local `#eval!`
  extractor does not run through the existing API without re-expressing
  that future-gain layer computably.

### Consequence
- The stable bridge work should continue per boundary branch, not via the
  scratch extractor.
- The next two obvious symmetric targets are the right-side local
  wrappers `idxN2 / idxN1`; the truly nonlocal residue remains
  `idx2 / idxN3`.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 19

### Strategy
Test the strongest naive bridge hypothesis: maybe every raw B1/B2/B3/B4
boundary move already lands in the fixed 6-tuple edge relation.

### Outcome
NEGATIVE RESULT

### What Was Tested
Inside [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) I defined:
- `IsB1Boundary`
- `IsB2Boundary`
- `IsB3Boundary`
- `IsB4Boundary`
- `b1BoundarySucc`
- `b2BoundarySucc`
- `b3BoundarySucc`
- `b4BoundarySucc`

Then I tried to prove by exhaustive finite check that each of these raw
boundary successor maps always satisfies `sixBoundaryEdge`.

### Load-Bearing Finding
That statement is false.

The exhaustive `native_decide` check produced concrete counterexamples
already for the naive B1 implication. So the fixed `617`-edge relation is
strictly finer than the raw local anomalous boundary graph.

Equivalently: the remaining bridge theorem cannot be

`local B1/B2/B3/B4 pattern  =>  sixBoundaryEdge`

without additional hypotheses.

### Consequence
The actual bridge must mention more than the local anomalous pattern. The
most plausible missing ingredient is the global bad-step / constant-layer
structure that was present in the extraction pipeline but not yet
formalized in Lean.

This is useful because it rules out a tempting but false shortcut before
more proof effort is spent on it.

### Remaining Gap
Phase 4 is still open, with a sharper statement of the live subproblem:
- formalize the extra global hypotheses that distinguish the true
  6-tuple certificate edges from arbitrary local B1-B4 boundary moves
- prove the real bridge from CUP-2 bad steps to `sixBoundaryEdge`
- finish full well-foundedness and convergence

### Verification
- the false theorem attempt was removed
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 18

### Strategy
Tighten the interface between the still-open full convergence theorem and
the existing Part A / Part B work:
1. make the Lean side split `badStep` by the sign of `Δfc`
2. keep the positive-`Δfc` anomalous classification available as a
   refinement rather than pretending it is a partition
3. separately check whether the planned 6-tuple automaton route is
   actually stable across `n`

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Convergence/Anomalous.lean`](./lean/LeanMn/Convergence/Anomalous.lean) now additionally contains:
  - `cup2BadStepNeg`
  - `cup2BadStep_cases`
  - `cup2BadStepPos_classified`

### Load-Bearing Observation
The Lean API now matches the real proof structure:
- every bad step is either nonnegative-`Δfc` (`cup2BadStepNonneg`) or
  negative-`Δfc` (`cup2BadStepNeg`)
- positive-`Δfc` steps are not treated as a separate branch anymore;
  instead they are a classified subset of the nonnegative side via
  `cup2BadStepPos_classified`

That is the correct seam for the remaining convergence proof: Part A
already controls the nonnegative side with `cup2BadStepNonneg_wf`, while
Part B/C still need to explain how the positive anomalous subcases cannot
recur indefinitely.

### Extra Empirical Check
I also ran the local automaton script
`probes/clb_convergence_proof106.py` and a trimmed extraction:
- for `n = 9` and `n = 10`, the 6-tuple graph has exactly `324` states,
  `617` transitions, DAG rank `24`
- the extracted transition sets for `n = 9` and `n = 10` are literally
  identical (`same_edges = True`)

This does not yet produce Lean code, but it strongly supports the Phase
3C route through a fixed 6-tuple automaton.

### Remaining Gap
Phase 4 is still blocked by the same final missing theorem layer:
- no B1/B2/B3/B4 refire-bound theorem in Lean
- no `SixTuple.lean` artifact yet
- no full `WellFounded (badStep ...)`
- no convergence theorem or `valid (cup2System n hn)` theorem

### Verification
- `lake env lean LeanMn/Convergence/Anomalous.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 17

### Strategy
Bridge the gap between raw boundary audits and actual path arguments by
classifying every real `fc`-increasing CUP-2 move as one of the four
anomalous contexts B1-B4.

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Convergence/Anomalous.lean`](./lean/LeanMn/Convergence/Anomalous.lean) now additionally contains:
  - positive-`Δfc` local classifiers:
    - `bot_positive_cases`
    - `low_positive_cases`
    - `mid_positive_cases`
    - `high_positive_cases`
    - `top_positive_cases`
  - the global/local bridge:
    - `localFc_lt_of_fc_lt_move`
  - explicit anomalous-context predicates:
    - `IsB1Config`
    - `IsB2Config`
    - `IsB3Config`
    - `IsB4Config`
  - the main classification theorems:
    - `cup2Move_fc_increase_cases`
    - `cup2Step_fc_increase_cases`

### Load-Bearing Observation
The anomalous side no longer starts from an arbitrary bad step. For any
actual CUP-2 transition with strict `fc` increase, Lean now reduces it to
exactly one of the four boundary contexts from the proof text:
- B1: `T_bot(0,0,0) -> 1`
- B2: `T_bot(1,1,2) -> 0`
- B3: `T_high(1,1,1) -> 2`
- B4: `T_top(2,0,0) -> 1`

This is the missing connection from Part A’s generic `fc/Ψ` machinery to
Part B’s case-by-case refire arguments.

### Remaining Gap
Phase 4 is still blocked by the actual refire-bound proofs:
- no B1/B2/B3/B4 segment theorem yet
- no final well-foundedness theorem for full `badStep`
- no convergence theorem or `valid (cup2System n hn)` theorem yet

### Verification
- `lake env lean LeanMn/Convergence/Anomalous.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 23

### Strategy
Globalize the new `Interior.lean` local hop-budget lemmas instead of
continuing the fixed-site induction literally:
1. define a global potential that sums the per-site hop budgets with
   right-to-left base-`3` weights
2. prove a move at deep interior position `i` only changes the terms at
   `i` and `i+1`
3. show the three TP-preserving hop cases all strictly decrease the
   weighted two-site contribution
4. package the resulting deep-interior TP-zero relation as well-founded

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Convergence/Interior.lean`](./lean/LeanMn/Convergence/Interior.lean) now additionally contains:
  - global potential layer:
    - `deepMidHopWeight`
    - `deepMidHopPotentialTerm`
    - `deepMidHopPotential`
    - `hopAdjacentComplement`
    - `mem_hopAdjacentComplement_iff`
    - `left_ne_of_mem_hopAdjacentComplement`
    - `sum_univ_eq_hopAdjacentComplement`
  - support lemmas:
    - `deepMidHopWeight_pos`
    - `deepMidHopWeight_eq_three_mul_right`
    - `deepMidHopPotentialTerm_move_eq_of_mem_hopAdjacentComplement`
    - `deepMidHopPotential_split`
    - `deepMidHopPotential_move_split`
    - `deepMidHopPotential_rest_move_eq`
  - load-bearing descent theorems:
    - `cup2TpPreserving_mid_zero_local_potential_drop`
    - `cup2TpPreserving_mid_zero_potential_drop`
    - `cup2DeepMidTpZeroStep`
    - `cup2DeepMidTpZeroStep_potential_drop`
    - `cup2DeepMidTpZeroStep_wf`

### Load-Bearing Observation
The naive global sum of the local hop budgets is the wrong measure. The
three surviving hop cases do not only decrease the budget at the mover:
they can also move budget mass one step to the right, and the case

`(1,0,0) -> 1`

changes the pair `(budget_i, budget_{i+1})` from `(2,0)` to `(1,2)`.

So an unweighted sum does not decrease. The right reformulation is a
base-`3` right-to-left weighting:

- `022 -> 0` shifts `1` unit right, so weight ratio `3:1` still drops
- `100 -> 1` shifts at most `2` units right, so base `3` is enough
- `112 -> 2` drops locally with no compensating right shift

This turns the analytical Phase 3C local hop argument into a single
compiled well-founded relation, not just a site-by-site lemma family.

### Proof-Engineering Observation
The successful proof shape mirrored `CopyDAG.lean`:
- split the global sum into the two touched positions plus a complement
- prove the complement is unchanged under the move
- normalize the touched terms all the way down to explicit Nat
  inequalities before calling automation

Two specific adjustments were required to make the local descent compile:
- derive the weight identity from explicit exponent arithmetic rather than
  rewriting through `deepMidHopWeight` after unfolding
- normalize `cup2OutVal` with concrete `hout'` equations and `simp`,
  because plain `rw` left conditional branches opaque under coercions

### Remaining Gap
Phase 4 is still not done.

This new theorem narrows the live upper-bound gap further:
- the deep-interior TP-preserving zero-`Δfc` slice is now already
  well-founded globally, not only per site
- what remains is the bridge from actual full bad steps to the
  boundary-changing / TP-changing / TP-preserving-deep-interior cases
- then the 6-boundary DAG and the existing nonnegative bad-step measure
  can be assembled into the final convergence theorem

### Verification
- `lake build LeanMn.Convergence.Interior` succeeds
- `lake build LeanMn` succeeds

## Synthesis after exploration 23

### Cross-artifact pattern
The upper-bound convergence work now has the same compiled architecture in
two different slices:
- `CopyDAG.lean`: a move changes only two local frontier terms, so a
  global `(n - fc, Ψ)` measure descends after a local case split
- `Interior.lean`: a move changes only the two local hop-budget terms at
  `i` and `i+1`, so a global weighted potential descends after a local
  case split

The shared proof pattern is no longer accidental. The remaining Phase 3
bridge should look for one more global measure/reduction of the same
kind, rather than a schedule-level induction.

### Implication for the next exploration
The most promising next target is now:
- define the actual “constant-layer deep interior” bad-step slice that
  uses the new `cup2DeepMidTpZeroStep_wf`
- then prove that once the 6-boundary state and TP invariant are fixed,
  every remaining bad step refines either to that relation or to a finite
  boundary case handled by the 6-tuple certificate

## Exploration 24 (probe)

### Strategy
Close the untouched easy convergence branch explicitly: prove the
strictly negative-`Δfc` bad-step relation is well-founded by the raw
frontier count alone.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/Anomalous.lean`](./lean/LeanMn/Convergence/Anomalous.lean) now contains:
  - `cup2BadStepNeg_wf`

PROOF SHAPE:
- `InvImage (· < ·) (cup2Fc n hn)` over configurations
- subrelation proof uses the second conjunct of `cup2BadStepNeg`

VERIFICATION:
- `lake build LeanMn.Convergence.Anomalous` succeeds

## Exploration 25 (probe)

### Strategy
Turn the new interior well-founded relation into an actual convergence
decomposition lemma: any TP-preserving, `fc`-preserving CUP-2 step should
either be boundary-near or belong to the solved deep-interior slice.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/Interior.lean`](./lean/LeanMn/Convergence/Interior.lean) now contains:
  - `cup2TpPreserving_zero_fc_step_boundary_or_deep`

LOAD-BEARING CONTENT:
- The theorem packages every `step (cup2System n hn) c c'` with
  `cup2Fc n hn c' = cup2Fc n hn c` and
  `cup2TpInvariant n hn c' = cup2TpInvariant n hn c`
  into exactly two cases:
  - a mover at boundary-near index `i` with `i ≤ 2 ∨ n - 3 ≤ i`
  - the interior relation `cup2DeepMidTpZeroStep n hn c' c`

VERIFICATION:
- `lake build LeanMn.Convergence.Interior` succeeds
- `lake build LeanMn` succeeds

## Exploration 26

### Strategy
Prove the first real fixed-boundary bridge against the 6-tuple layer:
1. show any privileged boundary-near move must change one of the six
   explicit boundary coordinates
2. combine that with the new interior decomposition theorem to conclude
   that a TP-preserving, `fc`-preserving step with unchanged boundary-6
   state is necessarily a deep-interior step

### Outcome
SUCCESS

### What Compiled
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2Boundary6_changed_of_boundary_move`
  - `cup2TpPreserving_zero_fc_step_fixed_boundary6_deep`

### Load-Bearing Observation
This is the first compiled theorem that turns “fixed boundary + fixed TP +
zero `fc`” into a solved interior relation.

The key structural fact is stronger than the earlier
`cup2BoundaryState_changed_implies_boundary_index` direction:
- not only do deep moves leave the 6-boundary projection unchanged
- every privileged move at indices
  `0, 1, 2, n-3, n-2, n-1`
  necessarily changes the corresponding recorded boundary coordinate

So once the boundary-6 state is fixed, the only remaining TP-preserving
zero-`fc` steps are the deep-interior ones already controlled by
`cup2DeepMidTpZeroStep_wf`.

### Proof-Engineering Observation
The robust proof shape for the six boundary branches was:
- identify the exact boundary index with `Fin.ext`
- `subst i`
- project the corresponding `SixBoundary` field equality
- compare `Fin.val` on that field

Trying to keep the original `i` alive and solve the branch by `simpa`
across dependent occurrences failed repeatedly; eliminating `i` first was
the right move.

### Remaining Gap
Phase 4 is still not done, but the remaining boundary work is narrower:
- fixed-boundary, fixed-TP, zero-`fc` steps now reduce to the solved
  deep-interior relation
- what still remains is the genuinely boundary-changing constant-layer
  side and its connection to the finite 6-tuple DAG / anomalous segment
  arguments

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 27 (probe)

### Strategy
Package the new fixed-boundary bridge as a reusable relation and inherit
its well-foundedness from the already-solved deep-interior slice.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2FixedBoundaryTpZeroStep`
  - `cup2FixedBoundaryTpZeroStep_deep`
  - `cup2FixedBoundaryTpZeroStep_wf`

LOAD-BEARING CONTENT:
- The “fixed boundary-6 + fixed TP + zero `fc`” layer is now a named
  relation with its own compiled `WellFounded` theorem.
- This removes that entire constant-layer slice from the remaining Phase 4
  search space; what remains is only the boundary-changing constant-layer
  side.

VERIFICATION:
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 44 (bridge interface)

### Strategy
Clear two low-level proof chores off the remaining constant-future
boundary bridge:
1. make the full `cup2BadBoundaryChangeConstFutureStep` relation split
   immediately by the six boundary mover indices, just like the older
   TP-zero bridge
2. expose exact `cup2FutureSlack` shift equalities for the five possible
   one-step `Δfc` values under constant future

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Excursion.lean`](./lean/LeanMn/Convergence/Excursion.lean) now additionally contains:
  - `cup2FutureSlack_eq_add_one_of_constFuture_deltaNegOne`
  - `cup2FutureSlack_eq_add_two_of_constFuture_deltaNegTwo`
  - `cup2FutureSlack_eq_add_one_of_constFuture_deltaPosOne`
  - `cup2FutureSlack_eq_add_two_of_constFuture_deltaPosTwo`
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadBoundaryChangeConstFutureStep_cases`

### Load-Bearing Consequence
- The live blocker is still the constant-`cup2FutureFc`,
  boundary-changing slice, but its interface is cleaner now:
  - mover classification is available directly on the full live relation,
    not only on the older TP-zero surrogate
  - slack changes can now be rewritten exactly from the stored `Δfc`
    branch, instead of only via strict inequalities
- The next bridge pass can therefore target statements of the form:
  `idx* case + exact Δfc -> exact target boundary/slack code`
  without reopening generic arithmetic.

### Verification
- `lake build LeanMn.Convergence.Excursion` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 45 (boundary-slack code scaffold)

### Strategy
Expose the remaining constant-future boundary bridge in the same literal
numeric shape that the eventual finite certificate will use:
1. define a raw `(boundary6, futureSlack)` code on configs
2. prove the fully local boundary moves rewrite directly to explicit
   boundary-update code expressions

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BoundarySlackCodeOf`
  - `cup2BoundarySlackCode`
  - `cup2BoundarySlackCode_move_idx0_local`
  - `cup2BoundarySlackCode_move_idx1_local`
  - `cup2BoundarySlackCode_move_idxN2_local`
  - `cup2BoundarySlackCode_move_idxN1_local`

### Load-Bearing Consequence
- The remaining bridge can now target literal code equalities rather than
  only structural `SixBoundary` equalities.
- For the four fully local boundary positions (`0`, `1`, `n-2`, `n-1`),
  the future certificate side is reduced to:
  - one boundary-code rewrite
  - one exact slack-shift rewrite
  - membership in the eventual finite certificate
- So the truly nonlocal residue is now concentrated even more clearly in
  the hidden-neighbor branches `idx2` and `idxN3`.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 95 (exact endpoint exceptional three-way split)

### Strategy
Refactor the remaining exact endpoint exceptional shell so it mirrors the
already-existing refined-exceptional three-way split, without adding
another heavy top-level wrapper:
1. make the three exact endpoint families first-class relations
2. add a compiled case split for the exceptional endpoint relation
3. package the direct `cfg < current` target by those three exact
   endpoint families

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedEndpointB2OverlapAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedEndpointB3AnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedEndpointB4UnsafeAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_kind_cases`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_lt_of_kind`

### Load-Bearing Consequence
- The exact endpoint exceptional shell is no longer an opaque bundled
  relation.
- The remaining Phase 4 endpoint residue now lives explicitly on the
  three concrete families:
  - `idx0_b2Overlap`
  - `idxN2_b3`
  - `idxN1_b4Unsafe`
- I also tried adding a higher-level exact-endpoint wrapper theorem on
  top of this split, but backed that part out when it hit a heartbeat
  timeout during elaboration. The lighter family split is stable and
  building.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 103 (truthful endpoint witness-cert shell)

### Strategy
Clean up the endpoint witness-cert route so it only states cert facts that
match the extracted data:
1. add a cert-side theorem on the canonical witnessed endpoint shell itself
2. avoid claiming a fibration from the exact endpoint shell into that
   canonical shell without the extra prefix state needed to make it true
3. probe the extracted witness cert against the coarse local endpoint head
   conditions to see exactly which zero-tail families it really covers

### Outcome
PARTIAL

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureEndpointRefinedTaggedAnomalousSegmentStep_toCanonicalWitnessed`
  - `cup2BadConstFutureCanonicalWitnessedEndpointRefinedTaggedAnomalousSegmentStep_wf_of_endpoint_refined_witness_cert`
- The attempted theorem lifting exact endpoint-tagged anomalous segments
  directly into the canonical witnessed shell was backed out after Lean
  exposed the real issue: the canonical target prefix depends on the
  predecessor endpoint witness, so the old plain fibration shape was false.

### Load-Bearing Consequence
- The endpoint witness cert is now isolated as a truthful cert for the
  canonical witnessed endpoint shell, not for the larger witnessed relation
  by default.
- The remaining upper-bound bridge must preserve the predecessor
  `(endpointKind, src)` prefix explicitly; there is no honest shortcut that
  forgets that dependency.
- A direct code probe on the extracted `EndpointRefinedWitnessCert` now makes
  the remaining residue sharper:
  - safe zero-tail endpoint families are universally present in the cert:
    - `idx0_b1`: `81 / 81`
    - `idx0_b2Safe`: `72 / 72`
    - `idxN1_b4Safe`: `45 / 45`
  - exceptional zero-tail families are not covered by the same coarse local
    head predicate:
    - `idx0_b2Overlap`: `0 / 9`
    - `idxN2_b3`: `42 / 54`
    - `idxN1_b4Unsafe`: `0 / 36`
- So the last Phase 4 bridge cannot be a blind cert collapse from coarse
  local endpoint conditions; it has to stay source-sensitive on the
  exceptional endpoint families.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 104 (safe zero-tail witness-cert base edges)

### Strategy
Stabilize the cert route on the part the extracted witness cert actually
covers uniformly:
1. prove the three safe zero-tail endpoint families land in the
   `EndpointRefinedWitnessCert` at the raw code level
2. keep the proof statement honest by requiring the actual zero-tail slack
   values on the source code
3. leave the exceptional endpoint families outside this cert base layer,
   since the direct probe already showed they are not uniformly present

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `endpointRefinedWitnessEdge_of_idx0_b1_code`
  - `endpointRefinedWitnessEdge_of_idx0_b2Safe_code`
  - `endpointRefinedWitnessEdge_of_idxN1_b4Safe_code`

### Load-Bearing Consequence
- The witness cert now has a formal Lean base layer for all three safe
  endpoint families.
- This matches the extracted cert data exactly:
  - `idx0_b1`: all `81 / 81` zero-tail source codes are present
  - `idx0_b2Safe`: all `72 / 72` zero-tail source codes are present
  - `idxN1_b4Safe`: all `45 / 45` zero-tail source codes are present
- The remaining cert bridge is therefore no longer “all endpoints.” The
  unresolved source-sensitive residue is still the exceptional endpoint
  families:
  - `idx0_b2Overlap`
  - `idxN2_b3`
  - `idxN1_b4Unsafe`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 102 (endpoint shell forgets to witnessed shell)

### Strategy
Collapse the duplicated endpoint-anomalous endgame:
1. make the exact endpoint-tagged relation forget directly to the witnessed
   endpoint relation by exposing the existential anomalous source `d`
2. prove well-foundedness of the exact endpoint shell from well-foundedness
   of the witnessed shell by fibration on `(kind, cfg)`
3. wire the resulting `badConstFuture` / `badStep` / `converges` wrappers so
   the remaining Phase 4 target can stay entirely on the witness-cert side

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureEndpointRefinedTaggedAnomalousSegmentStep_toWitnessed`
  - `cup2BadConstFutureEndpointRefinedTaggedAnomalousSegmentStep_wf_of_endpoint_refined_witnessed`
  - `cup2BadConstFutureStep_wf_of_endpoint_refined_witnessed`
  - `cup2BadStep_wf_of_endpoint_refined_witnessed`
  - `cup2Converges_of_endpoint_refined_witnessed`

### Load-Bearing Consequence
- The exact endpoint shell is no longer a separate endgame.
- Any future endpoint-refined witness-cert theorem can now discharge the
  exact endpoint-tagged shell immediately.
- This removes the need to keep both the projected-cert route and the
  witnessed-cert route alive at the same time; the remaining Phase 4 bridge
  can stay on the witnessed endpoint shell.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 101 (endpoint projected cert target-kind uniqueness)

### Strategy
Test whether the extracted phase-sensitive endpoint projected cert really
supports the old universal target-tag bridge, or whether the cert fixes a
unique target kind once the source code and target current code are fixed.
If the target kind is unique, the remaining Phase 4 bridge has to move to a
normalized endpoint shell instead of the false universal theorem.

### Outcome
PARTIAL

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `endpointRefinedProjectedCodePhase`
  - `endpointRefinedProjectedCodeKind`
  - `endpointRefinedProjectedCodeCurrent`
  - `endpointRefinedProjectedEdge_target_kind_unique_of_current`

### Load-Bearing Consequence
- The extracted endpoint projected cert does **not** saturate target kinds.
- For a fixed source projected code and fixed target current code, the cert
  determines a unique target kind.
- So the remaining Phase 4 bridge is not the old universal statement
  `cup2BadConstFutureEndpointRefinedTaggedAnomalousSegmentStep ->
  cup2EndpointRefinedProjectedCertStep`.
- The right closing route is now a normalized endpoint shell that matches
  the cert's actual target-kind behavior.

### Probe Result
- A direct code-level probe over
  [`LeanMn/Convergence/EndpointRefinedProjectedCert.lean`](./lean/LeanMn/Convergence/EndpointRefinedProjectedCert.lean)
  found histogram `{1: 12402}` for target-kind coverage over
  `(source projected code, target current code)`.
- So every such pair has exactly one target kind in the cert.

### Verification
- The new uniqueness theorem elaborates locally in
  [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean).
- A full `lake build LeanMn.Convergence.Main` replay was started after this
  patch, but the long-running `Main.lean` elaboration was still sitting in
  `MutualDef` when sampled, so I am not claiming a clean full build exit on
  this exploration.

## Exploration 100 (exact witness cert prefix invariant)

### Strategy
Stabilize the exact endpoint witness-cert route by proving the one cert-side
fact that is true without extra slack assumptions: every
`endpointRefinedWitnessEdge` preserves its `(phase, endpoint-kind, srcCode)`
prefix. This exposes the canonical shape of the generated cert without
over-claiming a stronger state-level normalization theorem.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `Cup2WitnessedEndpointRefinedTaggedSegmentState.normalizeTarget`
  - `endpointRefinedWitnessPrefixNatCode`
  - `endpointRefinedWitnessEdge_same_prefix`
  - `cup2EndpointRefinedWitnessCertStep_same_div`

### Load-Bearing Consequence
- The generated exact witness cert is now formalized as preserving the raw
  `/ 1296` witness prefix, i.e. the cert edges do not change the
  `(phase, endpoint-kind, srcCode)` portion of the code.
- This matches the extracted cert data: all `4781` witness edges keep the
  same source witness prefix and only change the current-configuration code.
- The stronger lifted theorem I first tried, identifying this with the
  state-level `cup2EndpointRefinedWitnessPrefixNatCode`, was false without an
  additional `< 1296` bound on the target `boundarySlackCode`. I backed that
  out and kept only the truthful raw-code invariant.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 98 (exact endpoint witness certificate)

### Strategy
Stop pushing the remaining Phase 4 residue through scalar segment-rank shells
and package the exact endpoint-refined witnessed relation itself as a finite
certificate target:
1. extract the const-future endpoint-refined witnessed graph from the current
   CUP-2 variant over `n = 9, 10, 11, 12`
2. internalize that graph as a finite Lean certificate on the exact witness
   code `(n % 3, endpointKind, srcCode, currentCode)`
3. wire `Main.lean` to expose the new cert as an alternative endgame shell

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/EndpointRefinedWitnessCert.lean`](./lean/LeanMn/Convergence/EndpointRefinedWitnessCert.lean) is new and contains:
  - `endpointRefinedWitnessEdgeVals`
  - `endpointRefinedWitnessRank1Vals`
  - `endpointRefinedWitnessRank`
  - `endpointRefinedWitnessEdge`
  - `endpointRefinedWitnessEdge_wf`
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2EndpointRefinedWitnessNatCode`
  - `cup2EndpointRefinedWitnessCertStep`
  - `cup2EndpointRefinedWitnessCertStep_of_code_eq`
  - `cup2EndpointRefinedWitnessCertStep_wf`
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep_wf_of_endpoint_refined_witness_cert`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_endpoint_refined_witness_cert`

### Load-Bearing Consequence
- The exact endpoint-refined witnessed relation now has a first-class finite
  certificate target instead of only the older projected/tagged shells.
- The extracted exact witness graph is shallow: the union over
  `n = 9, 10, 11, 12` has `4781` edges, `5045` nodes, and certificate depth `1`.
- This replaces the previous “prove a universal scalar exceptional rank
  descent” bottleneck with the cleaner bridge obligation:
  `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep ->
   cup2EndpointRefinedWitnessCertStep`.

### Verification
- `lake build LeanMn.Convergence.EndpointRefinedWitnessCert` succeeds
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 99 (endpoint-refined projected cert)

### Strategy
Stop pushing the exceptional witnessed shell directly and instead install a
finite cert for the already-existing endpoint-refined projected relation
`cup2BadConstFutureEndpointRefinedTaggedAnomalousSegmentStep`. The probe
target is the exact phase-sensitive projection on `(endpoint kind, current
boundarySlackCode)`, not another source-sensitive scalar rank shell.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/EndpointRefinedProjectedCert.lean`](./lean/LeanMn/Convergence/EndpointRefinedProjectedCert.lean)
  now contains the extracted finite DAG cert for the exact projected
  endpoint-refined anomalous-segment relation:
  - `endpointRefinedProjectedEdgeVals`
  - `endpointRefinedProjectedRank`
  - `endpointRefinedProjectedEdge_wf`
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean)
  now additionally contains:
  - `Cup2BoundaryAnomalousEndpointRefinedKind.code`
  - `cup2EndpointRefinedProjectedNatCode`
  - `cup2EndpointRefinedProjectedCertStep`
  - `cup2EndpointRefinedProjectedCertStep_wf`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_endpoint_refined_projected_cert`

### Load-Bearing Consequence
- The upper-bound convergence shell now has a clean direct endpoint-refined
  certificate target again, rather than only the older witnessed exceptional
  endpoint shells.
- The extracted cert compiles as a real Lean module on the current variant.
- The live remaining bridge is now explicit:
  `cup2BadConstFutureEndpointRefinedTaggedAnomalousSegmentStep ->
   cup2EndpointRefinedProjectedCertStep`.

### Probe Facts
- The compiled exact projected cert is the stable union extracted from
  `n = 9, 10, 11, 12`.
- It has:
  - `3099` states
  - `12402` edges
  - maximum rank depth `4`

### Verification
- `lake build LeanMn.Convergence.EndpointRefinedProjectedCert` succeeds
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 100 (projected-cert endgame wrappers)

### Strategy
Finish the projected-cert route structurally so the remaining work is only
the bridge theorem itself, not more shell assembly. Once the subrelation
`endpoint_refined_tagged -> projected_cert` is available, `badConstFuture`,
`badStep`, and `converges` should all follow immediately.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureStep_wf_of_endpoint_refined_projected_cert`
  - `cup2BadStep_wf_of_endpoint_refined_projected_cert`
  - `cup2Converges_of_endpoint_refined_projected_cert`

### Load-Bearing Consequence
- The exact projected cert path is now fully wired through the upper-bound
  convergence shell.
- The remaining Phase 4 task is a single explicit theorem:
  `cup2BadConstFutureEndpointRefinedTaggedAnomalousSegmentStep ->
   cup2EndpointRefinedProjectedCertStep`
- No additional shell refactor is needed once that bridge is proved.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 98 (exact endpoint exceptional tail split correction)

### Strategy
Stress-test the remaining exact endpoint exceptional `cfg < current` shell
directly on the current CUP-2 variant before spending more time proving it
branch-by-branch. If that shell is too coarse, refactor the Lean side so the
remaining obligations are stated on the true live branches: per-family
`zeroTail` versus `positiveTail`.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - family-specific exact endpoint tail relations:
    - `cup2BadConstFutureWitnessedEndpointB2OverlapZeroTailAnomalousSegmentStep`
    - `cup2BadConstFutureWitnessedEndpointB2OverlapPositiveTailAnomalousSegmentStep`
    - `cup2BadConstFutureWitnessedEndpointB3ZeroTailAnomalousSegmentStep`
    - `cup2BadConstFutureWitnessedEndpointB3PositiveTailAnomalousSegmentStep`
    - `cup2BadConstFutureWitnessedEndpointB4UnsafeZeroTailAnomalousSegmentStep`
    - `cup2BadConstFutureWitnessedEndpointB4UnsafePositiveTailAnomalousSegmentStep`
  - family-specific exact endpoint tail split lemmas:
    - `cup2BadConstFutureWitnessedEndpointB2OverlapAnomalousSegmentStep_tail_cases`
    - `cup2BadConstFutureWitnessedEndpointB3AnomalousSegmentStep_tail_cases`
    - `cup2BadConstFutureWitnessedEndpointB4UnsafeAnomalousSegmentStep_tail_cases`
  - family-specific reduction wrappers:
    - `cup2BadConstFutureWitnessedEndpointB2OverlapAnomalousSegmentStep_cfg_rank_lt_of_tail_cases`
    - `cup2BadConstFutureWitnessedEndpointB3AnomalousSegmentStep_cfg_rank_lt_of_tail_cases`
    - `cup2BadConstFutureWitnessedEndpointB4UnsafeAnomalousSegmentStep_cfg_rank_lt_of_tail_cases`
  - the aggregate exceptional-tail wrapper:
    - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_lt_of_kind_tail_cases`

### Load-Bearing Probe Results
- On the actual current-variant bad graph:
  - positive-tail exceptional witnesses are real for `idx0_b2Overlap` and `idxN2_b3`
  - sampled counts:
    - `n = 9`: `idxN2_b3 = 333`, `idx0_b2Overlap = 46`
    - `n = 10`: `idxN2_b3 = 1094`, `idx0_b2Overlap = 158`
    - `n = 11`: `idxN2_b3 = 3502`, `idx0_b2Overlap = 523`
  - `idxN1_b4Unsafe` still does not occur in the sampled positive-tail branch
- The coarse direct target
  `boundarySlackSegmentRank(cfg) < boundarySlackSegmentRank(current)`
  is **not** uniformly true on the sampled positive-tail `idxN2_b3` slice.
  A concrete `n = 9` violation is:
  - source `(1,0,0,0,1,0,1,1,1)`
  - anomalous result `(1,0,0,0,1,0,1,2,1)`
  - positive-tail current `(0,0,0,0,1,0,1,1,1)`
  - result code/rank `(692, 1)`
  - current code/rank `(38, 1)`

### Load-Bearing Consequence
- The remaining Phase 4 endpoint residue is not “one direct exceptional
  `cfg-rank` theorem” anymore.
- The true live proof split is now:
  - `idx0_b2Overlap`: zero-tail versus positive-tail
  - `idxN2_b3`: zero-tail versus positive-tail
  - `idxN1_b4Unsafe`: likely emptiness branch, but now explicitly isolated
- Any final argument for the exact endpoint exceptional shell has to use a
  source-sensitive or mixed certificate on the positive-tail `b2Overlap / b3`
  branches; the coarse scalar `boundarySlackSegmentRank` target is too weak.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 96 (exact endpoint zero-tail family wrappers)

### Strategy
Lift the already-compiled zero-tail strict endpoint lemmas onto the new
exact endpoint family relations, so the remaining exceptional endpoint
work is no longer phrased against the generic bundled relation.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedEndpointB2OverlapAnomalousSegmentStep_cfg_rank_lt_of_zeroTail`
  - `cup2BadConstFutureWitnessedEndpointB3AnomalousSegmentStep_cfg_rank_lt_of_zeroTail_of_rank_pos`
  - `cup2BadConstFutureWitnessedEndpointB4UnsafeAnomalousSegmentStep_cfg_rank_lt_of_zeroTail_of_rank_pos`

### Load-Bearing Consequence
- The strict zero-tail descent facts now live directly on the exact
  endpoint families:
  - `idx0_b2Overlap`
  - `idxN2_b3`
  - `idxN1_b4Unsafe`
- So the live Phase 4 endpoint residue is now even sharper:
  - prove the missing source-rank positivity / actual-source restriction
    for zero-tail `b3`
  - prove the positive-tail endpoint branch, or show it is impossible
  - formalize the apparent non-occurrence of `b4Unsafe`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 94 (zero-tail exact `b2Overlap`)

### Strategy
Exploit the new strict local `b2Overlap` slack-3 theorem on the exact
endpoint-witness shell instead of only on the coarse refined shell.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now contains:
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_lt_of_idx0_b2Overlap_zeroTail`

### Load-Bearing Consequence
- The exact endpoint exceptional shell now has a real strict
  `cfg < current` theorem on the zero-tail `idx0_b2Overlap` branch.
- This is the right shape for the remaining endpoint-side assembly:
  the last work is no longer “all exceptional endpoint cases at once,”
  but specifically:
  - `idxN2_b3`
  - the apparent impossibility branch `idxN1_b4Unsafe`
  - positive-tail handling for the exceptional endpoint families

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 93 (exceptional endpoint split)

### Strategy
Probe the remaining refined-exceptional witnessed shell directly on the
actual bad graph instead of continuing to push generic boundary-state
lemmas:
1. test the live target
   `boundarySlackSegmentRank(result) < boundarySlackSegmentRank(current)`
   on the three refined exceptional families
2. test the intermediate monotonicity question
   `boundarySlackSegmentRank(src) ≤ boundarySlackSegmentRank(current)`
3. isolate any clean local theorem that is already true in Lean without
   another certificate layer

### Outcome
PARTIAL

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `b2OverlapBoundarySucc_segment_rank_lt_three`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_segment_rank_lt_of_idx0_b2Overlap_slack_three`

### Load-Bearing Probe Results
- On the actual bad graph for `n = 9`, every witnessed refined-exceptional
  segment already satisfies
  `boundarySlackSegmentRank(result) < boundarySlackSegmentRank(current)`.
- On the actual bad graph for `n = 9, 10, 11`, the intermediate inequality
  `boundarySlackSegmentRank(src) ≤ boundarySlackSegmentRank(current)`
  holds on all witnessed refined-exceptional segments sampled.
- On the actual local anomalous const-future endpoint slice for
  `n = 9, 10, 11, 12`:
  - `b2Overlap` occurs only at source slack `3`
  - `b3` occurs only at source slack `2` or `3`
  - `b4Unsafe` does not occur in the sampled bad graph
- The tempting universal shortcut on raw boundary states is still false:
  strict segment-rank drop does **not** hold for all `B2/B3/B4` boundary
  states and all `k < 4`; the new strict theorem had to be restricted to
  the real `b2Overlap` slack-`3` slice.

### Residual
- The remaining Phase 4 shell is still the refined-exceptional direct
  `cfg < current` theorem for:
  - `b2Overlap`
  - `b3`
  - `b4Unsafe`
- But the live proof search is narrower now:
  - `b2Overlap` has a real local strict theorem in Lean
  - `b4Unsafe` looks absent on the sampled bad graph
  - `b3` is the load-bearing remaining family

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 91 - exceptional shell reduction to cfg-rank

### Strategy
Replace the old top-level exceptional endpoint shell
`src < current` with the strictly weaker and still usable target
`cfg < current`, while leaving the safe endpoint side on the existing
`cfg ≤ src < current` bridge.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_endpoint_safe_src_cfg_exceptional_cfg_rank`
  - `cup2BadConstFutureStep_wf_of_endpoint_safe_src_cfg_exceptional_cfg_rank`
  - `cup2BadStep_wf_of_endpoint_safe_src_cfg_exceptional_cfg_rank`
  - `cup2Converges_of_endpoint_safe_src_cfg_exceptional_cfg_rank`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_lt_of_refined_exceptional`
  - `cup2BadConstFutureStep_wf_of_refined_safe_endpoint_exceptional_cfg_rank`
  - `cup2BadStep_wf_of_refined_safe_endpoint_exceptional_cfg_rank`
  - `cup2Converges_of_refined_safe_endpoint_exceptional_cfg_rank`
  - `cup2BadConstFutureWitnessedRefinedExceptionalAnomalousSegmentStep_cfg_rank_lt_of_kind`
  - `cup2BadConstFutureStep_wf_of_refined_safe_exceptional_kind_cfg_rank`
  - `cup2BadStep_wf_of_refined_safe_exceptional_kind_cfg_rank`
  - `cup2Converges_of_refined_safe_exceptional_kind_cfg_rank`

### Load-Bearing Consequence
- The false universal target
  `boundarySlackSegmentRank (... x'.src) < boundarySlackSegmentRank (... x.cfg)`
  is no longer the only live shell for the exceptional endpoint side.
- The convergence API now reduces the remaining Phase 4 residue to:
  - safe endpoint families via the already-compiled
    `cfg ≤ src < current` bridge
  - exceptional refined families `b2Overlap`, `b3`, `b4Unsafe` via the
    direct target
    `boundarySlackSegmentRank (... x'.cfg) < boundarySlackSegmentRank (... x.cfg)`
- So the live blocker is now exactly the strict `cfg`-rank descent for
  those three refined exceptional kinds.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 92 - exceptional local strict shortcut is false

### Strategy
Probe the tempting shortcut that the three exceptional local boundary
successor maps already satisfy a strict segment-rank drop on raw
`(boundary, slack)` data:
- `b2BoundarySucc`
- `b3BoundarySucc`
- `b4BoundarySucc`

### Outcome
FAILED AS A ROUTE, BUT INFORMATIVE

### Concrete Probe
- Temporary Lean probe:
  - `/tmp/check_main_strict.lean`
- Tested with `native_decide` whether the following universally hold:
  - `b2BoundarySucc`: strict `<`
  - `b3BoundarySucc`: strict `<`
  - `b4BoundarySucc`: strict `<`

### Load-Bearing Finding
- All three universal strict successor statements are false on the current
  current-variant segment-rank table.
- So the remaining exceptional strict target
  `boundarySlackSegmentRank (... x'.cfg) < boundarySlackSegmentRank (... x.cfg)`
  cannot be proved by strengthening the already-compiled local lemmas
  `cfg ≤ src` to local strict descent.
- The missing strictness has to come from the witnessed segment as a
  whole, not from the anomalous endpoint move in isolation.

### Verification
- `lake env lean /tmp/check_main_strict.lean` reports all three strict
  universal propositions as false

## Exploration 90 - zero-tail exceptional witness

### Goal
- stress-test the remaining refined-exceptional `src < current` shell
  before spending more time trying to prove it in Lean

### Work
1. ran a direct current-variant Python probe on the exact
   exceptional endpoint families using
   `probes/cup2_convergence_proof.py`
2. checked whether the witnessed anomalous-segment relation really
   forces at least one const-future copy step after the anomalous
   source
3. extracted one concrete `b3` witness when it does not

### Outcome
SUCCEEDED

### Concrete Finding
- There are genuine zero-tail exceptional witnessed segments.
- For `n = 9`, the source configuration
  `(0,0,0,0,0,0,1,1,1)`
  has an anomalous `idxN2` move to
  `(0,0,0,0,0,0,1,2,1)`.
- This step is on the const-future exceptional branch, and the
  witnessed tail can be taken to be reflexive, so `src = current`.

### Load-Bearing Consequence
- The current refined-exceptional hypothesis shape
  `boundarySlackSegmentRank(src) < boundarySlackSegmentRank(current)`
  is too strong as a universal endpoint-shell target, because there
  are real exceptional witnesses with `src = current`.
- So the remaining Phase 4 route needs to be stated in terms of the
  actual direct object:
  either a `cfg < current` endpoint/result certificate, or an
  equivalent mixed shell that does not require strict `src < current`
  on zero-tail segments.

### Verification
- `lake build LeanMn.Convergence.Main` still succeeds after backing
  out the failed counterexample patch
- the counterexample witness was reproduced from the current Lean/Python
  table variant, not the old `TMid(2,1,1)=0` variant

## Exploration 82 (exceptional local cfg-rank repair)

### Strategy
Stabilize the new exceptional endpoint `cfg ≤ src` layer in
`LeanMn/Convergence/Main.lean` instead of leaving the repo in a broken
intermediate state:
1. replace the brittle hand-expanded `fin_cases` / `omega` proofs with
   closed finite `native_decide` cert lemmas for the three local
   successor inequalities
2. add explicit `Decidable` instances for the named boundary predicates
   so those finite closures stay computable
3. rebuild the endpoint exceptional wrapper theorem on top of those
   local lemmas and remove the temporary probe file

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `b2OverlapBoundarySucc_segment_rank_le`
  - `b3BoundarySucc_segment_rank_le`
  - `b4UnsafeBoundarySucc_segment_rank_le`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_segment_rank_le_of_idx0_b2Overlap_slack_lt4`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_segment_rank_le_of_idxN2_b3_slack_lt4`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_segment_rank_le_of_idxN1_b4Unsafe_slack_lt4`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_le_of_kind_slack_lt4`
- Local `Decidable` instances were added for:
  - `IsB1Boundary`
  - `IsB2Boundary`
  - `IsB3Boundary`
  - `IsB4Boundary`
  - `IsB2SafeBoundary`
  - `IsB2OverlapBoundary`
  - `IsB4SafeBoundary`
  - `IsB4UnsafeBoundary`
- Temporary probe file removed:
  - `Check.lean`

### Load-Bearing Consequence
- The upper-bound side is back in a clean build state after the failed
  exceptional local-rank attempt.
- The exceptional endpoint shell now has a real compiled `cfg ≤ src`
  theorem under the natural slack-`< 4` hypothesis.
- The remaining Phase 4 residue is no longer the local exceptional
  arithmetic. It is the source-sensitive bridge needed to exploit this
  theorem in the final `b2Overlap / b3 / b4Unsafe` convergence shell.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 86 (safe endpoint shell reduction)

### Strategy
Reduce the exact endpoint-witness shell to the already cleaner canonical
safe-endpoint relation instead of carrying the safe branch through the
source-sensitive endpoint witness layer.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedEndpointSafeAnomalousSegmentStep_forget_refined_safe_endpoint`
  - `cup2BadConstFutureWitnessedEndpointSafeAnomalousSegmentStep_src_rank_of_refined_safe_endpoint`
  - `cup2BadConstFutureWitnessedEndpointSafeAnomalousSegmentStep_cfg_rank_of_refined_safe_endpoint`
  - `cup2BadConstFutureStep_wf_of_refined_safe_endpoint_exceptional_src_cfg_rank`
  - `cup2BadStep_wf_of_refined_safe_endpoint_exceptional_src_cfg_rank`
  - `cup2Converges_of_refined_safe_endpoint_exceptional_src_cfg_rank`

### Load-Bearing Consequence
- The safe endpoint branch is no longer tied to the exact endpoint-witness
  shell.
- Any future `src < current` / `cfg ≤ src` theorem proved on the canonical
  refined safe-endpoint relation can now be lifted directly into the top
  Phase 4 convergence shell.
- The remaining exact/source-sensitive residue is therefore the
  exceptional endpoint slice only:
  - `idx0_b2Overlap`
  - `idxN2_b3`
  - `idxN1_b4Unsafe`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 88 (refined exceptional reduction)

### Strategy
Eliminate the last exact endpoint-witness wrapper from the Phase 4 shell by
lifting the exceptional endpoint branch into the refined exceptional
witnessed relation.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_forget_refined_exceptional`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_src_rank_of_refined_exceptional`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_of_refined_exceptional`
  - `cup2BadConstFutureStep_wf_of_refined_safe_refined_exceptional_src_cfg_rank`
  - `cup2BadStep_wf_of_refined_safe_refined_exceptional_src_cfg_rank`
  - `cup2Converges_of_refined_safe_refined_exceptional_src_cfg_rank`

### Load-Bearing Consequence
- The Phase 4 convergence shell is now phrased entirely on refined
  witnessed relations.
- The live residue is no longer the exact endpoint shell at all.
  It is the refined exceptional source-sensitive branch:
  - `b2Overlap`
  - `b3`
  - `b4Unsafe`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 89 (exceptional three-way split)

### Strategy
Make the remaining refined exceptional residue explicit in code by splitting
it into the three actual source-sensitive families and lifting that split
into the top-level convergence shell.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedRefinedB2OverlapAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedRefinedB3AnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedRefinedB4UnsafeAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedRefinedExceptionalAnomalousSegmentStep_kind_cases`
  - `cup2BadConstFutureWitnessedRefinedExceptionalAnomalousSegmentStep_src_rank_of_kind`
  - `cup2BadConstFutureWitnessedRefinedExceptionalAnomalousSegmentStep_cfg_rank_of_kind`
  - `cup2BadConstFutureStep_wf_of_refined_safe_exceptional_kind_src_cfg_rank`
  - `cup2BadStep_wf_of_refined_safe_exceptional_kind_src_cfg_rank`
  - `cup2Converges_of_refined_safe_exceptional_kind_src_cfg_rank`

### Load-Bearing Consequence
- The remaining Phase 4 target is now exact at the top level.
- The live residue is no longer “refined exceptional” as one bundled
  relation. It is the three explicit source-sensitive families:
  - `b2Overlap`
  - `b3`
  - `b4Unsafe`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds
- `lake build LeanMn` succeeds

## Exploration 87 (exceptional endpoint shell reduction)

### Strategy
Apply the same shell-cleaning move to the exceptional endpoint branch, but
stop at the refined exceptional witnessed relation so the remaining residue
stays source-sensitive.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_forget_refined_exceptional`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_src_rank_of_refined_exceptional`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_of_refined_exceptional`
  - `cup2BadConstFutureStep_wf_of_refined_safe_refined_exceptional_src_cfg_rank`
  - `cup2BadStep_wf_of_refined_safe_refined_exceptional_src_cfg_rank`
  - `cup2Converges_of_refined_safe_refined_exceptional_src_cfg_rank`

### Load-Bearing Consequence
- The top-level Phase 4 shell no longer needs hypotheses on the exact
  endpoint-witness relations.
- The remaining convergence target is now expressed on the two refined
  witnessed relations only:
  - canonical safe endpoint relation
  - refined exceptional witnessed relation
- So the live residue is no longer “exact endpoint witnesses.”
  It is the refined exceptional source-sensitive branch:
  - `b2Overlap`
  - `b3`
  - `b4Unsafe`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 83 (endpoint-witness canonical shell)

### Strategy
Replace the ad hoc safe-endpoint witness packing on the upper-bound side
with a canonical witnessed relation indexed by the exact anomalous
endpoint kind:
1. carry the real endpoint mover family in the state itself
2. split that witnessed relation into safe vs exceptional endpoint
   families
3. prove the safe families already satisfy the needed segment-rank
   monotonicity by reusing the existing endpoint cert lemmas

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BoundaryAnomalousEndpointRefinedKindHolds_refined`
  - `Cup2WitnessedEndpointRefinedTaggedSegmentState`
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedEndpointSafeAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep_safe_or_exceptional`
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep_forget_step`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_endpoint_refined_witnessed`
  - `cup2BadConstFutureWitnessedEndpointSafeAnomalousSegmentStep_cfg_rank_le_of_kind_slack`
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep_forget`

### Load-Bearing Consequence
- The safe endpoint families are no longer represented indirectly via a
  coarse refined tag plus extra endpoint-side conjuncts.
- They now live as a canonical witnessed relation whose state already
  records the exact anomalous endpoint family:
  - `idx0_b1`
  - `idx0_b2Safe`
  - `idx0_b2Overlap`
  - `idxN2_b3`
  - `idxN1_b4Safe`
  - `idxN1_b4Unsafe`
- The safe half of that relation already satisfies the expected
  `boundarySlackSegmentRank(cfg) ≤ boundarySlackSegmentRank(src)` facts
  by direct reduction to the existing anomalous boundary certificate
  lemmas.
- So the remaining Phase 4 residue is now cleaner: the true unsolved
  source-sensitive branch is the exceptional endpoint slice, not the
  safe endpoint families.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 85 (safe/exceptional endpoint reduction shell)

### Strategy
Exploit the new exact endpoint-witness relation to expose the remaining
Phase 4 residue as an explicit safe-vs-exceptional split at the top
level:
1. add a single theorem that proves well-foundedness of the exact
   endpoint-witness relation from separate source/cfg rank hypotheses on
   the safe and exceptional endpoint branches
2. lift that theorem back through the anomalous-segment shell
3. expose the same split directly at the
   `badConstFuture` / `badStep` / `converges` layers

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep_wf_of_safe_exceptional_src_cfg_rank`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_endpoint_safe_exceptional_src_cfg_rank`
  - `cup2BadConstFutureStep_wf_of_endpoint_safe_exceptional_src_cfg_rank`
  - `cup2BadStep_wf_of_endpoint_safe_exceptional_src_cfg_rank`
  - `cup2Converges_of_endpoint_safe_exceptional_src_cfg_rank`

### Load-Bearing Consequence
- The exact endpoint-witness relation now has a direct reduction theorem
  saying: if the safe endpoint families and exceptional endpoint
  families can each supply the required `cfg ≤ src < current` rank facts,
  then full upper-bound convergence follows.
- So the remaining Phase 4 target is no longer hidden inside the
  witnessed shell. It is now explicitly:
  - prove the missing source-rank facts for the safe endpoint families
  - prove the source/cfg rank facts for the exceptional endpoint
    families
- In particular, the true residue now sits directly on the exceptional
  endpoint slice:
  - `idx0_b2Overlap`
  - `idxN2_b3`
  - `idxN1_b4Unsafe`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 84 (endpoint-witness interface symmetry)

### Strategy
Make the new exact endpoint-witness shell usable as a first-class Phase 4
interface instead of only as a local helper:
1. add the same `cfg-rank` / `src-cfg-rank` well-foundedness lemmas that
   already exist for the coarse and refined witnessed shells
2. add the corresponding lifts back to
   `cup2BadConstFutureAnomalousSegmentStep`
3. add the downstream `badConstFuture` / `badStep` / `converges`
   wrappers

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep_wf_of_cfg_rank`
  - `cup2BadConstFutureWitnessedEndpointRefinedTaggedAnomalousSegmentStep_wf_of_src_cfg_rank`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_endpoint_refined_witnessed_cfg_rank`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_endpoint_refined_witnessed_src_cfg_rank`
  - `cup2BadConstFutureStep_wf_of_endpoint_refined_witnessed`
  - `cup2BadStep_wf_of_endpoint_refined_witnessed`
  - `cup2Converges_of_endpoint_refined_witnessed`
  - `cup2BadConstFutureStep_wf_of_endpoint_refined_witnessed_src_cfg_rank`
  - `cup2BadStep_wf_of_endpoint_refined_witnessed_src_cfg_rank`
  - `cup2Converges_of_endpoint_refined_witnessed_src_cfg_rank`

### Load-Bearing Consequence
- The exact endpoint-witness relation is now on equal footing with the
  older coarse and refined witnessed shells.
- Future reductions do not have to collapse immediately back to the
  coarser `Cup2BoundaryAnomalyRefinedKind` state space just to enter the
  generic convergence wrappers.
- So the remaining Phase 4 proof obligation can be stated directly on
  the exact endpoint families, with the safe endpoint side already
  packaged and the true residue isolated to the exceptional endpoint
  families.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 82 (canonical safe endpoint shell)

### Strategy
Correct the first safe-branch rank reduction attempt so it talks about a
truthful object:
1. back out the false broad witnessed lemmas that treated the refined
   `kind` tag as if it canonically determined the anomalous endpoint move
2. keep only the honest config-level endpoint rank lemmas, each of which
   requires the actual endpoint move witness already exposed by
   `cup2BadBoundaryChangeConstFutureAnomalousStep_cases`
3. package the safe part of the witnessed shell into a new canonical
   endpoint relation that carries the real move witness

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_segment_rank_lt_of_idx0_b1_slack`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_segment_rank_lt_of_idx0_b2Safe_slack`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_segment_rank_lt_of_idxN1_b4Safe_slack`
  - `cup2BadConstFutureWitnessedRefinedSafeEndpointSegmentStep`
  - `cup2BadConstFutureWitnessedRefinedSafeEndpointSegmentStep_cfg_rank_le_of_kind_slack`
  - `cup2BadConstFutureWitnessedRefinedSafeEndpointSegmentStep_forget`
  - `cup2BadConstFutureWitnessedRefinedSafeEndpointSegmentStep_forget_step`

### Load-Bearing Consequence
- The earlier broad witnessed safe-rank statement was too coarse: the
  existing refined witnessed relation only records that the source
  boundary satisfies a refined predicate, not that the chosen `kind`
  matches the actual anomalous mover.
- The safe endpoint branch is now stated against a truthful canonical
  subrelation carrying the real endpoint move witness.
- So the next upper-bound move is cleaner than before:
  prove the expected source-slack facts on this canonical safe endpoint
  shell, then leave the remaining obstruction isolated in the exceptional
  `b2Overlap / b3 / b4Unsafe` side.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 78 (refined boundary-slack decode interface)

### Goal
Push the remaining anomalous-segment residue closer to the actual cert
interface by moving refined boundary classifications onto raw
`cup2BoundarySlackCode` values instead of only `SixBoundary`.

### Strategy
1. add arithmetic decode helpers for the six boundary coordinates from
   `cup2BoundarySlackCodeOf`
2. prove those decoders recover the original `SixBoundary` fields when
   the slack parameter is `< 4`
3. define a raw-code version of the refined anomaly predicates and show
   refined boundary hypotheses imply the corresponding code predicate

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `boundarySlackCode_c0`
  - `boundarySlackCode_c1`
  - `boundarySlackCode_c2`
  - `boundarySlackCode_cN3`
  - `boundarySlackCode_cN2`
  - `boundarySlackCode_cN1`
  - the six recovery lemmas `*_of_codeOf`
  - `cup2BoundaryAnomalyRefinedCodeHolds`
  - `cup2BoundaryAnomalyRefinedCodeHolds_of_codeOf`

### Load-Bearing Consequence
- The refined anomaly split is no longer trapped at the structured
  `SixBoundary` level.
- Future cert bridges can now target raw `boundarySlackCode` directly,
  which is the actual state space used by the extracted finite segment
  certificates.
- This gives a clean interface for the remaining `B2/B3` overlap and
  unsafe `B4` source-code cases.

### Verification
- `lake env lean LeanMn/Convergence/Main.lean` succeeds

## Exploration 79 (result-coded cert obstruction)

### Goal
Test whether the existing extracted tagged segment cert already respects
the new refined raw-code boundary split on its tagged source coordinate.

### Strategy
1. use the new `cup2BoundaryAnomalyRefinedCodeHolds` predicate from
   `Main.lean`
2. try to prove, by finite `native_decide` over
   `taggedBoundarySlackSegmentEdgeVals`, that cert edges tagged `B1`,
   `B2`, `B3`, `B4` land in the corresponding refined raw-code classes

### Outcome
FAILED, and the failure is load-bearing

### Concrete Artifacts
- No new theorems were kept from the failed cert-classification attempt.
- The stable code change that remains is only the raw decode layer from
  Exploration 78 in
  [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean).

### Load-Bearing Consequence
- The old `TaggedSegmentCert` edge set is not source-classified by the
  refined raw-code boundary predicates.
- So the existing tagged cert is still too coarse for the final Phase 4
  bridge; it behaves like a result-coded cert rather than the stronger
  source-witnessed object the remaining proof needs.
- This confirms the live route: keep working with the witnessed /
  source-sensitive shell, not the older one-coordinate tagged cert.

### Verification
- `lake env lean LeanMn/Convergence/Main.lean` succeeds after backing
  the false lemmas out

## Exploration 80 (refined witnessed anomalous shell)

### Goal
Replace the remaining coarse witnessed anomalous-segment shell with a
source-sensitive refined witness object that carries the actual refined
boundary kind on the anomalous source configuration.

### Strategy
1. define a refined witnessed state carrying
   `Cup2BoundaryAnomalyRefinedKind`
2. define the corresponding witnessed anomalous-segment relation
3. add forgetful maps back to the coarse witnessed relation and to the
   plain anomalous-segment relation
4. push the convergence shell through that refined witness relation all
   the way up to `converges`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `Cup2WitnessedRefinedTaggedSegmentState`
  - `cup2BadConstFutureWitnessedRefinedTaggedAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedRefinedTaggedAnomalousSegmentStep_forget`
  - `cup2BadConstFutureWitnessedRefinedTaggedAnomalousSegmentStep_forget_step`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_refined_witnessed`
  - `cup2BadConstFutureStep_wf_of_refined_witnessed`
  - `cup2BadStep_wf_of_refined_witnessed`
  - `cup2Converges_of_refined_witnessed`

### Load-Bearing Consequence
- The remaining Phase 4 blocker is no longer “some witnessed segment
  relation” in an informal sense.
- It is now explicitly the well-foundedness of the refined witnessed
  anomalous segment relation, whose source kind is one of:
  - `b1`
  - `b2Safe`
  - `b2Overlap`
  - `b3`
  - `b4Safe`
  - `b4Unsafe`
- That is the right granularity for the last upper-bound residue,
  because the safe families can be attacked with the existing endpoint
  cert lemmas, leaving only the overlap / unsafe families as the real
  remaining obstruction.

### Verification
- `lake env lean LeanMn/Convergence/Main.lean` succeeds
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 81 (refined witnessed rank shell and residue split)

### Goal
Make the last Phase 4 obstruction explicit on the refined witnessed
state space instead of only at the coarse witnessed level.

### Strategy
1. mirror the coarse witnessed `cfg-rank` / `src-cfg-rank` well-founded
   wrappers onto the refined witnessed anomalous relation
2. add the refined witnessed code-space definitions needed for a future
   source-sensitive finite cert
3. split refined source kinds into safe families and exceptional
   residue families

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureWitnessedRefinedTaggedAnomalousSegmentStep_wf_of_cfg_rank`
  - `cup2BadConstFutureWitnessedRefinedTaggedAnomalousSegmentStep_wf_of_src_cfg_rank`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_refined_witnessed_cfg_rank`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_refined_witnessed_src_cfg_rank`
  - `cup2BadConstFutureStep_wf_of_refined_witnessed_src_cfg_rank`
  - `cup2BadStep_wf_of_refined_witnessed_src_cfg_rank`
  - `cup2Converges_of_refined_witnessed_src_cfg_rank`
  - `cup2WitnessedRefinedTaggedBoundarySlackNatCode`
  - `cup2WitnessedRefinedTaggedResultBoundarySlackNatCode`
  - `cup2WitnessedRefinedTaggedBoundarySlackPhaseNatCode`
  - `cup2WitnessedRefinedTaggedResultBoundarySlackPhaseNatCode`
  - `cup2BoundaryAnomalyRefinedKindSafe`
  - `cup2BoundaryAnomalyRefinedKindExceptional`
  - `cup2BadConstFutureWitnessedRefinedSafeAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedRefinedExceptionalAnomalousSegmentStep`
  - `cup2BadConstFutureWitnessedRefinedTaggedAnomalousSegmentStep_safe_or_exceptional`

### Load-Bearing Consequence
- The remaining upper-bound goal is now stated at the right level:
  prove `cfg ≤ src < current` for the refined witnessed anomalous
  relation.
- The safe refined source kinds are explicit:
  - `b1`
  - `b2Safe`
  - `b4Safe`
- The true residue is explicit too:
  - `b2Overlap`
  - `b3`
  - `b4Unsafe`
- That makes the next proof move concrete: solve the safe families
  against the existing endpoint cert lemmas, and leave only the
  exceptional residue for the last finite/source-sensitive argument.

### Verification
- `lake env lean LeanMn/Convergence/Main.lean` succeeds
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 77 (refined anomalous tags)

### Strategy
Make the remaining hidden state on the Phase 4 anomalous-segment shell
explicit in Lean instead of leaving it only in probe notes:
1. split the coarse `B2` family into safe vs `B2/B3` overlap
2. split the coarse `B4` family into safe vs unsafe
3. package a refined tagged anomalous-segment shell so the next cert can
   target the real residue directly

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `IsB2SafeBoundary`
  - `IsB2OverlapBoundary`
  - `IsB4SafeBoundary`
  - `IsB4UnsafeBoundary`
  - `Cup2BoundaryAnomalyRefinedKind`
  - `Cup2BoundaryAnomalyRefinedKind.code`
  - `Cup2BoundaryAnomalyRefinedKind.code_lt`
  - `cup2BoundaryAnomalyRefinedKindHolds`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_refined_boundary_cases`
  - `cup2BadConstFutureRefinedTaggedAnomalousSegmentStep`
  - `cup2BadConstFutureRefinedTaggedAnomalousSegmentStep_forget`
  - `cup2BadConstFutureAnomalousSegmentStep_refined_tag`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_refined_tagged`

### Load-Bearing Consequence
- The last nonlocal residue is no longer represented by the coarse
  four-way anomaly tag.
- The exact hidden-state split observed in the probes is now first-class
  in Lean:
  - `B1`
  - `B2` safe
  - `B2/B3` overlap
  - `B3`
  - `B4` safe
  - `B4` unsafe
- So the next finite certificate no longer has to recover that split
  indirectly from raw boundary codes.

### Verification
- `lake env lean LeanMn/Convergence/Main.lean` succeeds

## Exploration 76 (witnessed-only copy obstruction)

### Strategy
Test whether the remaining witnessed anomalous-segment shell can be
closed by a plain `boundarySlackSegmentRank` argument on the extracted
reverse-copy certificate, before spending more proof effort on the full
result-coded tagged cert bridge.

### Outcome
FAILED FOR THE GLOBAL CLAIMS, BUT PRODUCED A SHARPER WITNESSED SPLIT

### Concrete Findings
- The global reverse-copy rank monotonicity claim is false on the current
  Lean CUP-2 variant:
  - `boundarySlackPredCopyEdge k' k -> boundarySlackSegmentRank k' <= boundarySlackSegmentRank k`
  - counterexamples exist already in the extracted finite relation, so
    Lean rejects the theorem by `native_decide`
- The analogous global `B3` one-step rank claim is also false:
  - `boundarySlackSegmentRank ((b3BoundarySucc s).encode * 4) < boundarySlackSegmentRank (s.encode * 4 + 2)`
  - again rejected directly by `native_decide`

PROBE RESULTS ON THE ACTUAL WITNESSED REGION:
- reverse-copy rank failures in the full extracted relation: `14`
- failures restricted to the full tagged-code universe: `5`
- failures restricted to tagged current targets only: `1`
- failures in the backward closure of tagged current targets: `7`

KIND-SLICED BACKWARD-CLOSURE FAILURES:
- `B1` closure: `7`
- `B2` closure: `4`
- `B3` closure: `0`
- `B4` closure: `1`

Representative bad reverse-copy edges in the witnessed backward closure:
- `(436, 484)`
- `(530, 545)`
- `(648, 696)`
- `(720, 768)`
- `(792, 840)`
- `(864, 912)`
- `(984, 912)`

### Load-Bearing Consequence
- The remaining Phase 4 obstruction is now provably witnessed-only.
- Any final rank argument has to stay local to the tagged anomalous
  segment shell; the global reverse-copy graph is too coarse.
- `B3` is no longer part of the copy-rank obstruction.
- The live residue has collapsed to:
  - the `B1/B2` overlap families
  - one `B4` exceptional copy edge family around `(530, 545)`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds after backing out the
  false universal lemmas
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 73 (phase-aware witnessed obstruction)

### Strategy
Probe the exact witnessed anomalous-segment relation instead of the older
phase-blind boundary/slack shells:
1. extract the mixed witnessed relation on
   `((kind, srcCode, resultCode), currentCode)` for `n = 9, 10, 11, 12`
2. check whether the remaining instability is a local hidden-state issue
   or a global length-phase issue
3. if it is phase-driven, expose phase-sensitive codes in Lean so the next
   finite certificate can target the right state space

### Outcome
PARTIAL

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BoundarySlackPhaseCodeOf`
  - `cup2BoundarySlackPhaseCode`
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2WitnessedTaggedBoundarySlackPhaseNatCode`

### Load-Bearing Consequence
- The exact witnessed relation on
  `((kind, srcCode, resultCode), currentCode)` is much tighter than the
  earlier phase-blind shells, but it is still not globally stable as a
  plain boundary/slack certificate.
- The remaining instability is now isolated to one `B1` family and is
  driven by `n % 3`, not by another local boundary table case.
- Concretely:
  - `n = 11` contributes the exceptional pair `((0, 202, 848), 545)`
  - `n = 12` contributes the exceptional pair `((0, 186, 832), 521)`
  - the two configurations are the same `021` propagation family with a
    different ring-length phase
- So the next cert bridge needs a phase-aware witness code, not another
  phase-blind refinement of `boundarySlackCode`.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 75 (witnessed result shell and phase failure)

### Strategy
Test whether the remaining witnessed anomalous-segment cert can be reduced
from the full witness triple down to the anomalous result code, once the
global residue class `n % 3` is exposed:
1. add a result-coded witnessed cert shell in Lean
2. probe the phase-aware reduced relation
   `((n % 3, kind, resultCode), currentCode)`
3. if that still fails, compare against the stronger full witness code to
   see where the first real instability remains

### Outcome
PARTIAL

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2WitnessedTaggedResultBoundarySlackNatCode`
  - `cup2WitnessedTaggedResultBoundarySlackSegmentCertStep`
  - `cup2WitnessedTaggedResultBoundarySlackSegmentCertStep_wf`
  - `cup2BadConstFutureWitnessedAnomalousSegmentStep_wf_of_result_segment_cert`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_witnessed_result_segment_cert`
  - `cup2BadConstFutureStep_wf_of_witnessed_result_segment_cert`
  - `cup2BadStep_wf_of_witnessed_result_segment_cert`
  - `cup2Converges_of_witnessed_result_segment_cert`

### Load-Bearing Consequence
- The smaller result-coded target is now first-class in Lean, so the final
  convergence step can target it directly if the probe closes.
- The probe did **not** close:
  - phase-aware result coding `((n % 3, kind, resultCode), currentCode)`
    is still unstable on phase `0`
  - specifically, `n = 9` versus `n = 12` differs by `13` pairs
  - phase `1` does stabilize at this resolution: `n = 10` and `n = 13`
    match exactly
- The stronger phase-aware full witness code
  `((n % 3, kind, srcCode, resultCode), currentCode)` is also still
  unstable on phase `0` between `n = 9` and `n = 12`, again by `13`
  pairs.
- Those new phase-0 pairs are concentrated in the `B2/B3` families, not
  the earlier `B1` propagation toggle. So the remaining hidden state is
  now isolated more sharply: it is not just endpoint phase, and it is not
  just the `B1` branch.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 74 (mod-3 witness confirmation)

### Strategy
Test whether the phase-aware witness obstruction is really controlled by
`n % 3`, not by unbounded extra hidden state:
1. compute the exact witnessed relation on
   `((kind, srcCode, resultCode), currentCode)` for `n = 13`
2. compare it against the already-computed `n = 10` relation, since
   `10 % 3 = 13 % 3 = 1`
3. if they coincide, keep the next cert route on phase-aware tagged codes
   instead of adding more raw boundary data

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2TaggedBoundarySlackPhaseNatCode`
  - `cup2WitnessedTaggedResultBoundarySlackPhaseNatCode`

### Load-Bearing Consequence
- The exact witnessed relation on
  `((kind, srcCode, resultCode), currentCode)` for `n = 13` has `1593`
  pairs, exactly matching `n = 10`.
- The direct comparison `n = 10` versus `n = 13` produced:
  - `10only = 0`
  - `13only = 0`
- So the remaining instability is not drifting with ring size in an
  unbounded way. The current evidence now supports the sharper claim that
  the residual cert obstruction is phase-controlled by `n % 3`.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 71 (witnessed segment wrapper completion)

### Strategy
Complete the new witnessed anomalous-segment shell in
`Convergence/Main.lean` by threading it all the way through the existing
assembly theorems:
1. keep the witnessed relation as the only new assumption
2. derive anomalous-segment well-foundedness from a witnessed segment cert
3. lift that through the already-proved anomalous-segment and
   future-drop shells to `cup2BadConstFutureStep`, `badStep`, and
   `converges`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2BadConstFutureStep_wf_of_witnessed_segment_cert`
  - `cup2BadStep_wf_of_witnessed_segment_cert`
  - `cup2Converges_of_witnessed_segment_cert`

### Load-Bearing Consequence
- The convergence shell is now complete up to a single explicit
  certificate obligation for the witnessed anomalous-segment relation.
- So the remaining Phase 4 blocker is no longer global assembly. It is
  exactly:
  `WellFounded (cup2BadConstFutureWitnessedAnomalousSegmentStep n hn4 hn9)`
  via a correct witnessed cert relation, or a direct subrelation to one.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 72 (witnessed rank shell reduction)

### Strategy
Exploit the finite boundary/slack rank tables directly instead of keeping
the final witness shell phrased only in terms of explicit cert relations:
1. show the anomalous slack cert already decreases the segment-rank table
2. add witnessed-shell reductions that only require a direct rank drop on
   the current config, or the weaker decomposition
   `cfg <= src < target`
3. thread those reductions all the way back to
   `cup2BadConstFutureStep`, `badStep`, and `converges`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `sixBoundaryAnomalousSlackEdge_segment_rank_decrease`
  - `cup2BoundaryAnomalousConstFutureCertStep_segment_rank_decrease`
  - `cup2BadConstFutureWitnessedAnomalousSegmentStep_wf_of_cfg_rank`
  - `cup2BadConstFutureWitnessedAnomalousSegmentStep_wf_of_src_cfg_rank`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_witnessed_cfg_rank`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_witnessed_src_cfg_rank`
  - `cup2BadConstFutureStep_wf_of_witnessed_src_cfg_rank`
  - `cup2BadStep_wf_of_witnessed_src_cfg_rank`
  - `cup2Converges_of_witnessed_src_cfg_rank`

### Load-Bearing Consequence
- The remaining Phase 4 blocker is now sharper than the old cert-only
  formulation.
- A direct full `cfg -> target` rank drop is too strong on the current
  variant: the `B2/B3` overlap slice and unsafe `B4` only give equality
  on the anomalous source/result boundary codes.
- So the right final target is now the two-part witnessed statement:
  - anomalous endpoint step does not increase `boundarySlackSegmentRank`
    from `cfg` to the witnessed source `src`
  - the copy-tail segment strictly increases that rank from `src` to the
    final target config

### Verification
- `lake build LeanMn.Convergence.Main` succeeds

## Exploration 65 (mixed tagged-code reduction)

### Strategy
Reduce the remaining Phase 4 tagged anomalous-segment shell to the
smallest certificate shape that matches the current computational
evidence:
1. stop forcing the final code relation to live on homogeneous
   `(tag, code) -> (tag, code)` edges
2. allow the cert to be a smaller mixed relation
   `(source tagged code) -> (target boundarySlackCode)`
3. prove once, at the shell level, that such a mixed relation plus a
   rank function is enough to discharge
   `cup2BadConstFutureTaggedAnomalousSegmentStep`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `Cup2BoundaryAnomalyKind.code`
  - `Cup2BoundaryAnomalyKind.code_lt`
  - `mixedTaggedBoundarySlackRel_wf_of_rank`
  - `cup2TaggedBoundarySlackNatCode`
  - `cup2BadConstFutureTaggedAnomalousSegmentStep_wf_of_mixed_code_rel`
  - `cup2BadConstFutureTaggedAnomalousSegmentStep_wf_of_mixed_code_rank`

### Load-Bearing Consequence
- The remaining Phase 4 cert no longer needs to be stored as a full
  homogeneous relation on `(Cup2BoundaryAnomalyKind × Nat)`.
- A smaller mixed certificate is now sufficient:
  - source: `(Cup2BoundaryAnomalyKind × boundarySlackCode)`
  - target: `boundarySlackCode`
- This is the right interface for the extracted tagged anomalous-segment
  data.

### Probe Result
- The tagged anomalous-segment projection on the current Lean CUP-2
  variant was rechecked computationally for `n = 9, 10, 11, 12`.
- The exact mixed relation is not literally stable, but the union across
  `n = 9..12` is small and acyclic:
  - mixed relation: `1595` edges, `382` nodes, DAG
  - homogeneous target-tag lift: `6380` edges, `1229` nodes, DAG
  - homogeneous rank depth: `4`
- The new mixed shell means only the `1595`-edge / rank-`4` mixed data
  is structurally necessary for the next certificate pass.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 66 (tagged segment cert in Lean)

### Strategy
Internalize the mixed tagged anomalous-segment certificate itself, not
just the shell theorems around it:
1. materialize the extracted mixed relation on
   `(anomaly kind code, source boundarySlackCode) -> target boundarySlackCode`
2. store a target-code rank that strictly increases along that relation
3. lift it back to a config-level cert relation in `Convergence/Main.lean`

### Outcome
SUCCEEDED

### Concrete Artifacts
- Added a new generated certificate module:
  [`LeanMn/Convergence/TaggedSegmentCert.lean`](./lean/LeanMn/Convergence/TaggedSegmentCert.lean)
  containing:
  - `taggedBoundarySlackSegmentEdgeVals`
  - `taggedBoundarySlackSegmentEdgeVals_length`
  - `boundarySlackSegmentRank1Vals`
  - `boundarySlackSegmentRank2Vals`
  - `boundarySlackSegmentRank3Vals`
  - `boundarySlackSegmentRank4Vals`
  - `boundarySlackSegmentRank`
  - `taggedBoundarySlackSegmentEdge`
  - `taggedBoundarySlackSegmentLift`
  - `taggedBoundarySlackSegmentLift_rank_decrease`
  - `taggedBoundarySlackSegmentLift_wf`
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2TaggedBoundarySlackSegmentCertStep`
  - `cup2TaggedBoundarySlackSegmentCertStep_wf`
  - `cup2BadConstFutureTaggedAnomalousSegmentStep_wf_of_segment_cert`

### Load-Bearing Consequence
- The remaining Phase 4 blocker is now one explicit bridge theorem:
  show that every actual
  `cup2BadConstFutureTaggedAnomalousSegmentStep`
  lands in `cup2TaggedBoundarySlackSegmentCertStep`.
- Once that subrelation theorem exists, full convergence follows through
  the already-assembled shell in `Convergence/Main.lean`.

### Certificate Facts
- mixed tagged segment cert:
  - `1595` edges
  - rank depth `4`
- the cert is built from the stable union extracted for `n = 9..12`
  on the current Lean CUP-2 variant

### Verification
- `lake build LeanMn.Convergence.TaggedSegmentCert` succeeds
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 67 (cert cleanup and symbolic anomalous edges)

### Strategy
Clean out the unstable closure attempt around the tagged segment cert, then
salvage the stable part of that investigation by exposing the finite
anomalous slack certificate through symbolic boundary lemmas instead of only
raw numeric edge tables.

### Outcome
PARTIAL

### Concrete Artifacts
- Removed the false global closure attempt from
  [`LeanMn/Convergence/TaggedSegmentCert.lean`](./lean/LeanMn/Convergence/TaggedSegmentCert.lean):
  - dropped `taggedBoundarySlackSegmentClosedUnderPredCopyB`
  - dropped `taggedBoundarySlackSegmentClosedUnderPredCopyB_true`
  - dropped `taggedBoundarySlackSegmentEdge_closed_of_predCopy`
- Added stable symbolic anomalous-cert lemmas to
  [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean):
  - `sixBoundaryAnomalousSlackEdge_b1`
  - `sixBoundaryAnomalousSlackEdge_b2`
  - `sixBoundaryAnomalousSlackEdge_b4`

### Load-Bearing Consequence
- The attempted shortcut “mixed tagged-segment cert is closed under every
  reverse const-future copy-code edge” is false on the current Lean
  development, so the final bridge still needs a stronger hidden-state
  object than plain `(tag, boundarySlackCode)`.
- The anomalous slack certificate is now partially decompiled back into
  paper-shaped rules:
  - `B1` is clean
  - `B2` works on the non-`B3` overlap branch
  - `B4` works off the exceptional `(c1, c2) = (2, 2)` slice

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 62 (tagged anomalous-segment shell)

### Strategy
Refactor the remaining Phase 4 convergence residue so the anomalous
segment relation is tagged by the actual boundary anomaly kind that fires
at the intermediate anomalous source. This makes the last shell theorem
match the finite certificate search more directly.

### Outcome
SUCCEEDED

## Exploration 68 (anomalous const-future cert wrappers)

### Strategy
Make the symbolic anomalous slack cert usable from actual CUP-2 configs:
1. add direct config-level `Δfc` helpers for the endpoint anomalous
   contexts already isolated in `SixTuple.lean`
2. package the stable `B1`, safe `B2`, and safe `B4` branches into
   `cup2BoundaryAnomalousConstFutureCertStep`
3. probe whether those safe anomalous sources are already closed under
   reverse const-future copy-code tails

### Outcome
PARTIAL

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2Boundary_idxN1_anomalous_fc_eq_of_b4`
  - `cup2Boundary_idx0_anomalous_constFuture_cert_of_b1`
  - `cup2Boundary_idx0_anomalous_constFuture_cert_of_b2`
  - `cup2Boundary_idxN1_anomalous_constFuture_cert_of_safe_b4`

### Load-Bearing Consequence
- The anomalous slack certificate is now available at the actual config
  level for the stable non-overlap boundary cases:
  - `B1`
  - `B2` off the `B3` overlap slice
  - `B4` off the exceptional `(c1, c2) = (2, 2)` slice
- The reverse-copy closure probe is still negative even on those safe
  anomalous-source families:
  - for tag `B1`, only `2 / 27` source codes are closed under the raw
    `boundarySlackPredCopyEdge` predecessor relation
  - for tag `B2`, `0 / 27`
  - for tag `B4`, `1 / 15`
- So the remaining tagged-segment bridge still needs stronger hidden
  state than plain anomalous tag plus boundary/slack code, even after
  the safe-case wrappers are in place.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 69 (source-coded segment shell)

### Strategy
Recheck the remaining tagged-segment blocker against the actual
certificate semantics instead of continuing to push on the old result-code
interface:
1. compare the source codes used by `TaggedSegmentCert.lean` with the
   anomalous slack cert and verify whether they are source or result
   codes
2. if they are source codes, add the corresponding source-coded shell API
   in `Convergence/Main.lean`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2TaggedSourceBoundarySlackNatCode`
  - `cup2BadConstFutureTaggedAnomalousSegmentStep_source_witness`
  - `cup2TaggedSourceBoundarySlackSegmentCertStep`
  - `cup2TaggedSourceBoundarySlackSegmentCertStep_wf`

### Load-Bearing Consequence
- The extracted `TaggedSegmentCert.lean` source pairs are confirmed to be
  `(anomaly kind code, source boundarySlackCode)`, not
  `(anomaly kind code, post-anomaly result boundarySlackCode)`.
- Empirical check on the current certificate tables:
  - tag `0`: `27 / 27` segment-cert source codes are anomalous **source**
    codes and `0 / 27` are anomalous result codes
  - tag `3`: `15 / 15` source codes and `0 / 15` result codes
  - tags `1` and `2` are also overwhelmingly source-coded, with only `3`
    overlaps each
- So the right remaining Phase 4 bridge is not the old result-coded one
  in `Main.lean`; it is a source-witness bridge from an actual tagged
  anomalous segment step to the new source-coded cert interface.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 70 (witnessed anomalous-segment shell)

### Strategy
Correct the new shell reduction so it follows the actual segment witness
instead of pretending the cert is directly result-coded:
1. introduce an explicit witnessed anomalous-segment state carrying the
   anomaly kind, the anomalous source `d`, and the current config
2. prove that well-foundedness of this witnessed relation implies
   well-foundedness of the plain anomalous-segment relation by fibration
3. expose the corresponding witnessed boundary/slack cert interface,
   but leave its well-foundedness as an explicit assumption rather than
   claiming a false automatic proof

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `Cup2WitnessedTaggedSegmentState`
  - `cup2BadConstFutureWitnessedAnomalousSegmentStep`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_witnessed`
  - `cup2WitnessedTaggedBoundarySlackNatCode`
  - `cup2WitnessedTaggedBoundarySlackSegmentCertStep`
  - `cup2BadConstFutureWitnessedAnomalousSegmentStep_wf_of_segment_cert`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_witnessed_segment_cert`

### Load-Bearing Consequence
- The remaining Phase 4 blocker is now stated against the right object:
  not the old result-coded tagged segment shell, but the witnessed
  anomalous-segment relation that carries the real source witness `d`.
- The attempted automatic well-foundedness proof for the witnessed cert
  relation was backed out; that proof shape was too coarse because the
  cert edge only controls `(tag, source boundarySlackCode) -> target
  boundarySlackCode`, not an arbitrary extra state payload.
- So the next obligation is explicit:
  prove a correct well-founded cert relation for
  `cup2BadConstFutureWitnessedAnomalousSegmentStep`, or prove it
  directly refines to one.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `Cup2BoundaryAnomalyKind`
  - `cup2BoundaryAnomalyKindHolds`
  - `cup2BadConstFutureTaggedAnomalousSegmentStep`
  - `cup2BadConstFutureTaggedAnomalousSegmentStep_forget`
  - `cup2BadConstFutureAnomalousSegmentStep_tag`
  - `cup2BadConstFutureAnomalousSegmentStep_wf_of_tagged`
  - `cup2BadConstFutureStep_wf_of_tagged_anomalous_segment_wf`
  - `cup2BadStep_wf_of_tagged_anomalous_segment_wf`
  - `cup2Converges_of_tagged_anomalous_segment_wf`

### Load-Bearing Consequence
- The old residue
  `WellFounded (cup2BadConstFutureAnomalousSegmentStep n hn4 hn9)`
  now has a strictly cleaner replacement target:
  `WellFounded (cup2BadConstFutureTaggedAnomalousSegmentStep n hn4 hn9)`.
- Once the tagged relation is shown well-founded, the new shell in
  `Convergence/Main.lean` lifts that back to:
  - `WellFounded (cup2BadConstFutureStep n hn4)`
  - `WellFounded (badStep (cup2System n hn4) (cup2GoodCycle n hn4))`
  - `converges (cup2System n hn4) (cup2GoodCycle n hn4)`

### Probe Result
- A local exhaustive probe against the current Lean CUP-2 variant shows:
  - the anomalous-source-to-target projection on
    `(boundary6, futureSlack)` is already stable for `n = 8, 9, 10, 11`
    with `155` nodes and `88` edges, and is a DAG
  - the full tagged/current-source-to-target segment projection on
    `(boundary6, futureSlack)` is also a DAG; for `n = 11` it has
    `335` nodes and `1594` edges
- This points at the next concrete proof target: a finite certificate
  for the tagged anomalous-segment relation rather than the older
  untagged shell.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 64 (anomalous slack certificate)

### Strategy
Internalize the stable finite projection for the constant-future,
boundary-changing anomalous one-step branch as an actual Lean
certificate module, instead of leaving it as an external Python probe.

### Outcome
SUCCEEDED

### Concrete Artifacts
- Added a new certificate module:
  [`LeanMn/Convergence/AnomalousSlackCert.lean`](./lean/LeanMn/Convergence/AnomalousSlackCert.lean)
  containing:
  - `sixBoundaryAnomalousSlackEdgeVals`
  - `sixBoundaryAnomalousSlackRankOneVals`
  - `sixBoundaryAnomalousSlackRankTwoVals`
  - `sixBoundaryAnomalousSlackRank`
  - `sixBoundaryAnomalousSlackEdge`
  - `sixBoundaryAnomalousSlackEdge_rank_decrease`
  - `sixBoundaryAnomalousSlackEdge_wf`
- Wired it into
  [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean)
  with config-level wrappers:
  - `cup2BoundaryAnomalousConstFutureCertStep`
  - `cup2BoundaryAnomalousConstFutureCertStep_wf`
  - `cup2BoundaryAnomalousConstFutureCertStep_of_code_eq`

### Load-Bearing Consequence
- The const-future anomalous endpoint branch now has a finite Lean
  target relation on `cup2BoundarySlackCode`, independent of the older
  external probe scripts.
- The extracted current-variant certificate is compact:
  - `88` edges
  - `155` nodes
  - rank depth `2`
- This does not finish Phase 4 by itself, but it gives the remaining
  segment bridge a concrete certificate endpoint inside the repo.

### Verification
- `lake build LeanMn.Convergence.AnomalousSlackCert` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 63 (tagged code hook)

### Strategy
Expose the new tagged anomalous-segment residue through an explicit
`(kind, boundarySlackCode)` wrapper so the next proof step can be a
plain finite certificate subrelation theorem.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `cup2TaggedBoundarySlackCode`
  - `cup2BadConstFutureTaggedAnomalousSegmentStep_wf_of_code_rel`

### Load-Bearing Consequence
- The remaining Phase 4 proof obligation is now factored into one exact
  shape:
  1. define a finite relation `r` on
     `Cup2BoundaryAnomalyKind × Nat`
  2. prove every tagged anomalous segment step maps into `r` under
     `cup2TaggedBoundarySlackCode`
  3. discharge convergence via
     `cup2BadConstFutureTaggedAnomalousSegmentStep_wf_of_code_rel`
     and the earlier shell theorems

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 61 (const-future shell reduction)

### Strategy
Turn the remaining Phase 4 blocker from “prove
`WellFounded (cup2BadConstFutureStep ...)` directly” into a smaller
segment theorem:
1. add a generic assembly lemma for a relation that splits into
   well-founded copy steps plus well-founded anomalous segments
2. specialize it to the current CUP-2 const-future relations
3. expose the resulting reduction at the full convergence shell level

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `wf_of_copy_segment_wf`
  - `cup2BadConstFutureAnomalousSegmentStep`
  - `cup2BadConstFutureStep_wf_of_anomalous_segment_wf`
  - `cup2BadStep_wf_of_anomalous_segment_wf`
  - `cup2Converges_of_anomalous_segment_wf`

### Load-Bearing Consequence
- The remaining upper-bound blocker is now formally isolated as the
  segment relation
  `cup2BadConstFutureAnomalousSegmentStep`.
- Everything else in the convergence shell is assembled:
  - const-future copy steps are already discharged by
    `cup2BadConstFutureCopyStep_wf`
  - the outer future-drop layer is already discharged by
    `cup2BadStep_wf_of_badConstFutureStep_wf`
  - once the anomalous segment relation is shown well-founded, full
    convergence follows immediately by
    `cup2Converges_of_anomalous_segment_wf`

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn` succeeds

## Exploration 58 (upper-side distinctness repair)

### Strategy
Remove the last upper-side `sorry` before returning to the remaining
Phase 4 convergence assembly:
1. prove the explicit CUP-2 cycle configs are injective by phase
   classification on endpoint values
2. use the phase-local wavefront shape to separate same-phase times
3. feed that injectivity into the `GoodCycle.distinct` field

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) now additionally contains:
  - `cup2CycleConfig_eq_val`
  - `cup2Cycle_phase1_top_val`
  - `cup2Cycle_nonphase1_top_val`
  - `cup2CycleConfig_injective`
- [`LeanMn/Cycle.lean`](./lean/LeanMn/Cycle.lean) no longer has the upper-side `sorry` in
  `cup2GoodCycleOfUniquePrivileged`

### Load-Bearing Consequence
- The upper-bound side is now sorry-free:
  - `LeanMn/Cycle.lean`
  - `LeanMn/Convergence/*.lean`
  - `LeanMn/UpperBound/*.lean`
- This does not finish Phase 4 by itself, but it removes the last
  unrelated formal gap from the upper-side development. The only
  remaining upper blocker is still the final convergence assembly.

### Verification
- `lake build LeanMn.Cycle` succeeds
- `lake build LeanMn` succeeds

## Exploration 57 (hidden-neighbor boundary/slack coding)

### Strategy
Restore the finite boundary/slack certificate route as the live Phase 4
interface by making the two hidden-neighbor boundary movers look exactly
like the already-solved outer boundary movers.

Concretely:
1. add `cup2BoundarySlackCode` local rewrite lemmas for `idx2` and
   `idxN3`
2. add the matching constant-future code-case theorems for those two
   movers
3. leave the repo in a clean build state before attempting the final
   edge-membership bridge

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BoundarySlackCode_move_idx2_local`
  - `cup2BoundarySlackCode_move_idxN3_local`
  - `cup2BadBoundaryChangeConstFuture_idx2_code_cases`
  - `cup2BadBoundaryChangeConstFuture_idxN3_code_cases`

### Load-Bearing Consequence
- The constant-`cup2FutureFc` boundary-changing blocker is back in a
  fully symmetric form across all six boundary movers.
- The remaining proof obligation is no longer “derive the hidden-neighbor
  code projections”; that part is done.
- The next live step is now the genuinely finite part:
  prove the resulting `(boundary6, futureSlack)` code cases land in the
  precomputed `sixBoundarySlackEdge` certificate.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 55 (endpoint anomalous delta lift)

### Strategy
Turn the remaining endpoint anomalous constant-future slice into an
explicit positive-`Δfc` relation instead of only a boundary-shape
classification:
1. add a generic `cup2Fc_eq_of_localFc_delta` bridge from local frontier
   deltas to exact global `fc` deltas
2. lift the `B1/B2/B3/B4` local delta facts to the actual boundary
   indices `idx0`, `idxN2`, and `idxN1`
3. package the anomalous constant-future branch as exact
   `Δfc = +1 ∨ +2`, then discharge that branch by the existing
   nonnegative bad-step measure

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2Fc_eq_of_localFc_delta`
  - `cup2Boundary_idx0_anomalous_fc_cases`
  - `cup2Boundary_idxN2_anomalous_fc_eq`
  - `cup2Boundary_idxN1_anomalous_fc_eq`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_delta_cases`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_fc_pos`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_wf`

### Load-Bearing Consequence
- The anomalous remainder of
  `cup2BadBoundaryChangeConstFutureStep`
  is no longer just “endpoint anomalous”.
- It is now forced into the exact positive frontier-count cases:
  - `Δfc = +1`
  - `Δfc = +2`
- That makes the anomalous endpoint branch itself a solved,
  well-founded subrelation via
  `cup2BadBoundaryChangeConstFutureNonnegStep_wf`.
- So the remaining Phase 4 blocker is narrower again: the final global
  assembly must now combine the already-solved copy branch and the
  already-solved anomalous endpoint branch into the full convergence
  theorem.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 54 (endpoint anomalous boundary classification)

### Strategy
Replace the remaining endpoint anomalous branch by the paper's explicit
boundary contexts instead of carrying it as an abstract "non-copy"
relation:
1. add finite local table lemmas saying anomalous bot/high/top moves are
   forced into the endpoint boundary shapes
2. lift those to the actual boundary indices `idx0`, `idxN2`, and
   `idxN1`
3. classify the whole remaining
   `cup2BadBoundaryChangeConstFutureAnomalousStep`
   relation into `B1/B2/B3/B4`

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `bot_anomalous_cases`
  - `high_anomalous_cases`
  - `top_anomalous_cases`
  - `cup2AnomalousBadStep_out_of_case`
  - `cup2Boundary_idx0_anomalous_boundary`
  - `cup2Boundary_idxN2_anomalous_boundary`
  - `cup2Boundary_idxN1_anomalous_boundary`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_boundary_cases`

### Load-Bearing Consequence
- The live blocker is now sharper than "endpoint anomalous moves."
- Every remaining
  `cup2BadBoundaryChangeConstFutureAnomalousStep`
  is now forced into one of the explicit boundary contexts from the
  analytical proof:
  - `B1`
  - `B2`
  - `B3`
  - `B4`
- So the remaining Phase 4 proof obligation is no longer endpoint
  anomaly classification. It is the bridge from those classified
  `B1/B2/B3/B4` endpoint anomalies to the final boundary/future-gain
  certificate or segment argument.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 59 (convergence outer shell)

### Strategy
Make the final Phase 4 blocker explicit in a dedicated convergence
module instead of leaving it implicit inside `SixTuple.lean`:
1. package the already-proved future-drop split as a lexicographic
   relation over `(cup2FutureFc, state)`
2. derive full bad-step well-foundedness from a single remaining
   assumption `WellFounded (cup2BadConstFutureStep n hn)`
3. expose the corresponding convergence theorem so the upper-bound
   assembly can target one exact missing obligation

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now contains:
  - `cup2BadStepFutureLex`
  - `cup2BadStep_future_lex`
  - `cup2BadStep_wf_of_badConstFutureStep_wf`
  - `cup2Converges_of_badConstFutureStep_wf`
- [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) imports the new convergence module

### Load-Bearing Consequence
- The remaining Phase 4 residue is now isolated cleanly in code:
  prove `WellFounded (cup2BadConstFutureStep n hn)`.
- Everything outside that relation is already packaged:
  - full `badStep` reduces to it by `cup2BadStep_wf_of_badConstFutureStep_wf`
  - convergence follows immediately by `cup2Converges_of_badConstFutureStep_wf`
  - the upper-bound theorem in `LeanMn/UpperBound/Theorem.lean` can then
    be discharged without further structural work

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
- `lake build LeanMn.Main` succeeds

## Exploration 60 (const-future copy/anomalous umbrella)

### Strategy
Shrink the remaining `cup2BadConstFutureStep` residue before returning
to the final assembly:
1. lift the existing boundary-changing copy/anomalous split to the whole
   const-future relation
2. package the solved copy side as its own well-founded relation
3. probe whether the endpoint anomalous `B1/B2/B3/B4` shapes already
   imply the `(boundary6, futureSlack)` certificate with `k : Fin 4`

### Outcome
PARTIAL SUCCESS

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadConstFutureCopyStep`
  - `cup2BadConstFutureStep_copy_or_boundary_anomalous`
  - `cup2BadConstFutureCopyStep_wf`

### Load-Bearing Consequence
- The const-future layer is now reduced one step further in code:
  every `cup2BadConstFutureStep` is either
  - already in the solved copy-neighbor branch, or
  - in the already-isolated
    `cup2BadBoundaryChangeConstFutureAnomalousStep`
- So the remaining Phase 4 difficulty is no longer classification of the
  const-future relation itself. It is the final assembly argument that
  combines:
  - solved const-future copy descent
  - solved boundary anomalous descent
  - the outer future-drop reduction from `Convergence/Main.lean`

### Failed Shortcut
- A direct finite probe showed that the naive endpoint shortcut is still
  false:
  “`B1/B2/B3/B4` local boundary shape + `k : Fin 4` implies a
  `sixBoundarySlackEdge` step.”
- So the remaining assembly cannot simply identify anomalous endpoint
  moves with one-step edges of the stored `(boundary6, futureSlack)` DAG.
  It still needs a stronger global bridge than local endpoint shape
  alone.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 43 (probe + reduction)

### Strategy
Tighten the remaining constant-`cup2FutureFc` / boundary-changing branch
enough that the next certificate bridge can attach to a finite case tree
instead of an opaque relation.

This turn had two tracks:
1. probe the current-table full-future boundary layer to see whether the
   right finite summary is `(boundary6, futureSlack)` rather than raw
   `boundary6`
2. reflect the useful part of that probe back into Lean as exact
   one-step `Δfc` structure

### Outcome
PARTIAL SUCCESS

### What Was Settled
- On the actual current Lean variant (`TMidVal 2 1 1 = 2`), the
  boundary-changing constant-`cup2FutureFc` projection to
  `(boundary6, futureSlack)` is much cleaner than the old raw boundary
  projection:
  - for `n = 10, 11`, it has exactly `362` projected states and `795`
    edges and is a DAG
  - for `n = 9`, it has the same `362` states and `796` edges and is
    still a DAG
  - the union of the `n = 9` and `n = 10` edge sets has `797` edges and
    is still a DAG, so a uniform finite certificate still looks viable
- The same probe shows two load-bearing simplifications:
  - `futureSlack = cup2FutureFc - cup2Fc` only takes values `0,1,2,3`
    on the tested bad graph
  - for the projected constant-future boundary slice, the target
    projection is uniquely determined by
    `(source boundary6, source futureSlack, mover position, exact Δfc)`

### Concrete Lean Artifacts
- [`LeanMn/Convergence/CopyDAG.lean`](./lean/LeanMn/Convergence/CopyDAG.lean)
  now exposes:
  - `localFc_delta_bounds`
  - `cup2Fc_move_delta_bounds`
  - `cup2Step_fc_delta_bounds`
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean)
  now exposes the exact finite `Δfc` view of the live blocker:
  - `cup2BadBoundaryChangeConstFutureStep_delta_cases`
  - `cup2BadBoundaryChangeConstFutureDeltaNegTwoStep`
  - `cup2BadBoundaryChangeConstFutureDeltaNegOneStep`
  - `cup2BadBoundaryChangeConstFutureDeltaZeroStep`
  - `cup2BadBoundaryChangeConstFutureDeltaPosOneStep`
  - `cup2BadBoundaryChangeConstFutureDeltaPosTwoStep`
  - `cup2BadBoundaryChangeConstFutureStep_delta_split`

### Load-Bearing Consequence
- The remaining Phase 4 blocker is no longer “constant-future
  boundary-changing bad steps” as one monolith.
- It is now an explicit finite tree:
  1. boundary mover case (`0 / 1 / 2 / n-3 / n-2 / n-1`)
  2. exact local `Δfc ∈ {-2,-1,0,1,2}`
- That matches the probe finding that the projected target is
  deterministic at exactly that granularity.

### Next Step
- Add the `(boundary6, futureSlack)` certificate layer and prove each
  boundary mover / exact-`Δfc` branch refines to it.
- If the `n = 9` / `n ≥ 10` edge difference survives in Lean, package
  the union certificate first; the probe already says the union is still
  acyclic.

### Verification
- `lake build LeanMn.Convergence.CopyDAG` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 42 (probe)

### Strategy
Re-check the TP outer-measure route against the *actual* Lean table
variant before spending more Phase 4 proof effort on it.

### Outcome
ROUTE CORRECTION

### What Was Settled
- The old computational TP evidence was taken from the wrong CUP-2
  variant:
  - the legacy Python theorem scripts use `T_mid(2,1,1) = 0`
  - the current Lean formalization uses `TMidVal 2 1 1 = 2`
  - this is the same `4`-anomalous copy-heavy variant already encoded in
    [`LeanMn/Tables.lean`](./lean/LeanMn/Tables.lean)
- For the current Lean tables, the proposed TP code
  `(exp2_count, int_21, exp2_weight)` is **not** monotone:
  - on the actual bad graph of the current variant, there are concrete
    bad edges where `exp2_weight` increases while `exp2_count` and
    `int_21` stay fixed
  - brute-force checks on the current Python alt-variant
    `T_mid(2,1,1)=2` system for `n = 9, 10` show:
    - positive-weight TP code has `1620 / 5832` bad-edge violations
    - reversing the weight sign still has `1616 / 5827` bad-edge
      violations
    - no sign/order lexicographic arrangement of the three raw TP
      components is monotone on all bad edges for `n = 9, 10`
- The unrestricted version is now closed formally in Lean:
  [`LeanMn/Convergence/TP.lean`](./lean/LeanMn/Convergence/TP.lean)
  contains the new theorem `cup2TpCode_move_le_counterexample`
  built from the existing `n = 5` witness.

### Load-Bearing Consequence
The current Phase 4 blocker should no longer be attacked through a raw
TP-triple outer measure. That route was tuned to the old
`T_mid(2,1,1)=0` variant, not to the current Lean system.

The remaining convergence work has to stay on the actual current
variant:
- copy-neighbor / `(fc, Ψ)` descent
- the `4` boundary anomalous contexts
- the existing boundary/future-gain certificate machinery

### Verification
- `lake build LeanMn.Convergence.TP`
- `lake build LeanMn`

## Exploration 41 (probe)

### Strategy
Re-check the remaining Phase 4 blocker against the actual bad graph
instead of the stale full-future heuristic:
1. compute the constant-`cup2FutureFc` boundary-changing projection on
   the real bad graph
2. test whether the projected 6-boundary graph is itself a DAG
3. if not, pivot back to the older TP-preserving route and expose an
   outer measure that reduces arbitrary bad steps to the TP slice

### Outcome
PARTIAL SUCCESS

### What Was Settled
- The old `728`-edge note for the full bad-step future layer was stale.
  Re-extracting against the actual bad graph gives:
  - for `n = 9, 10`, the constant-`cup2FutureFc` boundary-changing
    projection on the 6-boundary has `899` source-target pairs
  - that `899`-pair projection is stable for `n = 9, 10`
- That `899`-pair 6-boundary graph is **not** a DAG:
  - it has `27` nontrivial SCCs
  - the largest SCC has size `96`
- So the direct full-future boundary certificate route is too coarse at
  the 6-boundary level; encoding that graph in Lean would not close the
  proof.
- A different computational check changed the outer proof shape:
  - on the actual bad graph for `n = 9, 10`, the TP triple
    `(exp2_count, int_21, exp2_weight)` is lexicographically
    non-increasing on every bad step
  - there were `0` lex-increase counterexamples in the exhaustive
    checks

### Concrete Artifacts
- [`LeanMn/Convergence/TP.lean`](./lean/LeanMn/Convergence/TP.lean) now contains the compiled TP-code layer:
  - `cup2TpBase`
  - `cup2TpCodeOf`
  - `cup2TpCode`
  - `localTpCodeBefore`
  - `localTpCodeAfter`
  - `cup2Exp2Count_le_n`
  - `cup2Int21Count_le_n`
  - `cup2Exp2Weight_le_sq`
  - `cup2Exp2Count_lt_base`
  - `cup2Int21Count_lt_base`
  - `cup2Exp2Weight_lt_base`
  - `cup2TpCode_eq_iff`
  - `cup2TpInvariant_eq_of_code_eq`

### Load-Bearing Finding
The viable outer Phase 4 split is no longer
`full bad graph -> cup2FutureFc plateau`.
The workable route is now:
1. prove `cup2TpCode` never increases on bad steps
2. split arbitrary bad steps into
   `cup2TpCode`-drop vs exact TP-preserving steps
3. reuse the existing TP-preserving future-gain / `617`-edge machinery
   for the inner branch

This is materially sharper than the previous full-future branch, because
the unresolved global future condition only has to be handled **inside**
the TP-preserving slice, which is exactly what the existing
`cup2TpFutureFc` / `sixBoundaryEdge` development was built for.

### Remaining Gap
- The TP-code monotonicity theorem on bad steps is not yet formalized in
  Lean
- the boundary-changing TP-preserving constant-`cup2TpFutureFc` bridge
  to `sixBoundaryEdge` is still the inner Phase 4 blocker

### Verification
- `lake build LeanMn.Convergence.TP` succeeds
- `lake build LeanMn` succeeds

## Exploration 39 (probe)

### Strategy
Stop treating the TP-only future quantity as the only available outer
measure and formalize the actual bad-step future-gain scaffold in Lean,
then expose the first top-level split against that real quantity.

### Outcome
SUCCEEDED

### Concrete Artifacts
NEW FULL-FUTURE API:
- [`LeanMn/Convergence/Excursion.lean`](./lean/LeanMn/Convergence/Excursion.lean) now additionally contains:
  - `cup2BadStepFwd`
  - `cup2BadReachable`
  - `cup2FutureFc`
  - `cup2ConstFutureBadStep`
  - `cup2Fc_le_cup2FutureFc`
  - `cup2FutureFc_mono`
  - `cup2FutureFc_step_mono`
  - `cup2TpReachable_sub_badReachable`
  - `cup2TpFutureFc_le_cup2FutureFc`
  - `cup2TpConstFutureStep_fullFuture_mono`

NEW SIX-TUPLE SPLITS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadConstFutureStep`
  - `cup2BadDropFutureStep`
  - `cup2BadFixedBoundaryConstFutureStep`
  - `cup2BadBoundaryChangeConstFutureStep`
  - `cup2BadStep_future_split`
  - `cup2BadConstFutureStep_boundary_split`
  - `cup2BadDropFutureStep_wf`

### Load-Bearing Content
- The codebase now has the real bad-step future-gain quantity
  `cup2FutureFc`, not just the TP-restricted surrogate
  `cup2TpFutureFc`.
- This yields an actual outer split for arbitrary bad steps:
  every bad step either strictly drops `cup2FutureFc` or belongs to the
  constant-full-future slice `cup2BadConstFutureStep`.
- The TP-only future layer is now explicitly embedded below the full
  bad-step future layer via
  `cup2TpReachable_sub_badReachable` and
  `cup2TpFutureFc_le_cup2FutureFc`.

### Consequence
- The Phase 4 blocker is now represented at the right level of
  abstraction in Lean.
- The remaining convergence gap is no longer “define future gain”; it is
  specifically the constant-full-future bad-step layer, especially its
  boundary-changing branch
  `cup2BadBoundaryChangeConstFutureStep`.

### Verification
- `lake env lean LeanMn/Convergence/Excursion.lean` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 40 (probe)

### Strategy
Close the fixed-boundary side of the new full-future bad-step layer
instead of leaving it bundled with the unresolved boundary-changing
branch:
1. prove any boundary-fixed bad step is already a deep-interior copy step
2. package the solved full-future branches as one well-founded relation
3. expose the exact remaining blocker as the boundary-changing
   constant-full-future slice

### Outcome
SUCCEEDED

### Concrete Artifacts
NEW GENERIC FIXED-BOUNDARY RESULTS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadFixedBoundaryStep`
  - `mid_copyNeighbor`
  - `cup2BadFixedBoundaryStep_copy`
  - `cup2BadFixedBoundaryStep_wf`
  - `cup2BadFixedBoundaryConstFutureStep_wf`

NEW RESOLVED FULL-FUTURE LAYER:
- The same file now also contains:
  - `cup2BadConstFutureResolvedStep`
  - `cup2BadStep_constFuture_resolved_split`
  - `cup2ConstFutureResolvedMeasure`
  - `cup2BadConstFutureResolvedStep_decreases`
  - `cup2BadConstFutureResolvedStep_wf`

### Load-Bearing Content
- Boundary-fixed bad steps no longer need any TP-preservation hypothesis.
  Once the 6-boundary state is unchanged, the mover is forced into the
  deep interior, and every privileged `T_mid` move is already
  copy-neighbor.
- So the full-future layer now splits into:
  - strict `cup2FutureFc` drop, already solved
  - constant-full-future but fixed-boundary, now solved
  - constant-full-future and boundary-changing, still open

### Consequence
- The remaining Phase 4 blocker is now exact in Lean:
  `cup2BadBoundaryChangeConstFutureStep`.
- Everything else in the outer full-future bad-step decomposition is now
  discharged by compiled well-founded relations.

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 32 (probe)

### Strategy
Strengthen the TP-side API from the fixed-boundary direction instead of
continuing to attack the whole constant-future graph at once. The target
was: prove any fixed-boundary, TP-preserving bad step is already a
copy-neighbor step, then expose the corresponding constant-future slice
as a solved relation.

### Outcome
SUCCEEDED

### Concrete Artifacts
NEW INTERIOR LOCAL THEOREMS:
- [`LeanMn/Convergence/Interior.lean`](./lean/LeanMn/Convergence/Interior.lean) now additionally contains:
  - `mid_tp_copyNeighbor`
  - `cup2TpPreserving_mid_copyNeighbor_val`

NEW SIX-TUPLE RELATIONS / WF RESULTS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadFixedBoundaryTpStep`
  - `cup2BadFixedBoundaryTpStep_copy`
  - `cup2BadFixedBoundaryTpStep_wf`
  - `cup2BadTpConstFutureStep`
  - `cup2BadFixedBoundaryTpConstFutureStep`
  - `cup2BadBoundaryChangeTpConstFutureTpStep`
  - `cup2BadFixedBoundaryTpConstFutureStep_wf`
  - `cup2BadTpConstFutureStep_boundary_split`

### Load-Bearing Finding
The fixed-boundary side of the TP-preserving graph does not need the
older deep-interior / zero-`fc` restriction. For deep interior indices,
the local TP equalities already force the `T_mid` output to equal one of
its two neighbors. So every fixed-boundary TP-preserving bad step is a
copy-neighbor bad step and is therefore well-founded by
`cup2CopyBadStep_wf`.

### Consequence
The constant-future TP layer is now split in the code into:
- a solved fixed-boundary branch,
- an unsolved boundary-changing branch
  `cup2BadBoundaryChangeTpConstFutureTpStep`.

That is a materially narrower blocker than before. The remaining Phase 4
assembly gap is now to control this boundary-changing constant-future TP
slice and then fold it into the final convergence theorem.

### Verification
- `lake build LeanMn.Convergence.Interior` succeeds
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 33 (probe)

### Strategy
Promote the actual constant-future TP boundary certificate into the Lean
API directly, instead of leaving it implicit behind `SixState` encoding.
The target was to add the config-level wrapper for the existing
`617`-edge six-boundary DAG and prove that wrapper well-founded.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `sixBoundaryEdge_wf`
  - `cup2BoundaryTpConstFutureCertStep`
  - `cup2BoundaryTpConstFutureCertStep_wf`

### Load-Bearing Finding
Re-checking the current TP/future-gain slice computationally against the
same future quantity formalized in Lean (`cup2TpFutureFc`, i.e. the
absolute future `fc` supremum) recovers the published seam:
- for `n = 9, 10`, the boundary-changing constant-future TP slice
  projects to exactly `617` boundary edges on `324` states
- the projected graph is a DAG of rank `24`
- the projected edge set is identical for `n = 9, 10`

So the remaining Phase 4 bridge is now even sharper:
- source relation in Lean:
  `cup2BadBoundaryChangeTpConstFutureTpStep`
- target certificate in Lean:
  `cup2BoundaryTpConstFutureCertStep`

### Consequence
The remaining blocker is no longer “find the right finite object.” The
finite object is now explicit in the development. What is still missing
is the bridge theorem from the global config relation to that explicit
certificate relation, followed by the final convergence assembly.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 29 (probe)

### Strategy
Start turning the abstract boundary-changing constant-layer relation into
casewise certified moves by bridging actual CUP-2 boundary firings to the
finite `SixBoundary` TP-zero certificate, beginning with the left endpoint
and low endpoint cases where the local table shape is simplest.

### Outcome
PARTIAL SUCCESS

### Concrete Artifacts
NEW BRIDGE LEMMAS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2Boundary6_move_idx0_local`
  - `cup2Boundary6_move_idx1_local`
  - `cup2Boundary_idx0_tp_zero_cert`
  - `cup2Boundary_idx1_tp_zero_cert`

NEW CASE SPLIT:
- The same file now also contains:
  - `cup2BoundaryChangeTpZeroStep_cases`
  - `cup2BoundaryChangeTpZeroStep_idx0_cert`
  - `cup2BoundaryChangeTpZeroStep_idx1_cert`

LOAD-BEARING CONTENT:
- The left-side boundary-changing TP-zero relation is no longer opaque:
  endpoint `idx0` and low endpoint `idx1` moves can now be converted from
  real CUP-2 steps into certified `SixBoundary` steps.
- The six-way boundary mover split is now explicit in Lean, which reduces
  the remaining bridge to the unresolved `idx2 / idxN3 / idxN2 / idxN1`
  cases plus the final assembly theorem.

VERIFICATION:
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds

## Exploration 31 (probe)

### Strategy
Test a simpler route for the remaining TP-zero layer: instead of extending
the boundary certificate again, prove directly that any `Δfc = 0` CUP-2
step is a copy-neighbor move, then reuse the already-solved copy bad-step
well-foundedness from `Excursion.lean`.

### Outcome
SUCCEEDED

### Concrete Artifacts
LOCAL COPY LEMMAS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `bot_zero_copyNeighbor`
  - `low_zero_copyNeighbor`
  - `mid_zero_copyNeighbor`
  - `high_zero_copyNeighbor`
  - `top_zero_copyNeighbor`

GLOBAL TP-ZERO BRIDGE:
- The same file now also contains:
  - `cup2Step_fc_eq_copyNeighbor`
  - `cup2BadTpZeroStep_copy`
  - `cup2BadTpZeroStep_wf`
  - `cup2BadBoundaryChangeTpConstFutureStep_wf`

LOAD-BEARING CONTENT:
- The old named blocker `cup2BadBoundaryChangeTpConstFutureStep` is no
  longer unsolved: it is now discharged by subrelation to the fully solved
  copy bad-step relation.
- More strongly, the whole TP-preserving zero-`fc` bad-step layer is now
  solved directly by `cup2BadTpZeroStep_wf`.

VERIFICATION:
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds

## Exploration 30 (probe)

### Strategy
Finish the fully visible right-boundary bridge before returning to the two
hidden-neighbor mid cases. The key idea was to add local finite
certificate lemmas for `high` and `top`, then extract the needed high-end
exp2 side condition from `cup2TpPreserving_local_eqs`.

### Outcome
SUCCEEDED

### Concrete Artifacts
RIGHT-SIDE LOCAL CERTIFICATES:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `sixBoundaryTpZeroCert_high_local`
  - `sixBoundaryTpZeroCert_top_local`

RIGHT-SIDE CONFIG BRIDGES:
- The same file now also contains:
  - `cup2Boundary6_move_idxN2_local`
  - `cup2Boundary6_move_idxN1_local`
  - `cup2Boundary_idxN2_tp_zero_cert`
  - `cup2Boundary_idxN1_tp_zero_cert`
  - `cup2BoundaryChangeTpZeroStep_idxN2_cert`
  - `cup2BoundaryChangeTpZeroStep_idxN1_cert`

NARROWING RESULT:
- `cup2BoundaryChangeTpZeroStep_cert_or_mid` now resolves every
  boundary-changing TP-zero step except the two hidden-neighbor middle
  cases `idx2` and `idxN3`.

VERIFICATION:
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds

## Exploration 38 (probe)

### Strategy
Prepare a less brittle interface for the remaining boundary-certificate
bridge by adding explicit six-index neighbor identities and
`cup2OutVal` simplification theorems at the six boundary indices, then
retry the direct theorem

`cup2BoundaryChangeTpZeroStep -> cup2BoundaryTpZeroCertStep`.

### Outcome
PARTIAL SUCCESS

### What Landed
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now has stable boundary helper lemmas:
  - `left_cup2BoundaryIdx0`, `right_cup2BoundaryIdx0`
  - `left_cup2BoundaryIdx1`, `right_cup2BoundaryIdx1`
  - `left_cup2BoundaryIdx2`
  - `right_cup2BoundaryIdxN3`
  - `left_cup2BoundaryIdxN2`, `right_cup2BoundaryIdxN2`
  - `left_cup2BoundaryIdxN1`, `right_cup2BoundaryIdxN1`
- The same file now also has stable `cup2OutVal` reduction lemmas at the
  six boundary indices:
  - `cup2OutVal_boundaryIdx0`
  - `cup2OutVal_boundaryIdx1`
  - `cup2OutVal_boundaryIdx2`
  - `cup2OutVal_boundaryIdxN3`
  - `cup2OutVal_boundaryIdxN2`
  - `cup2OutVal_boundaryIdxN1`

### What Failed
- The first direct proof of
  `cup2BoundaryChangeTpZeroStep -> cup2BoundaryTpZeroCertStep`
  still turned into a coercion-heavy record-update proof and was backed
  out.
- The failure mode is now clearer: the proof should be split into small
  per-index bridge lemmas using the new boundary neighbor/value API,
  rather than one large theorem with all six cases inline.

### Consequence
- The repo is back in a clean build state, but the remaining Phase 4
  blocker is unchanged in substance:
  `cup2BadBoundaryChangeTpConstFutureStep` still lacks a certified
  reduction to the finite boundary DAG.

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 36 (probe)

### Strategy
Tighten the remaining boundary-certificate gap without committing to the
full bridge theorem yet:
1. enlarge the fixed `617`-edge certificate by the explicit `16`
   stable TP-zero nonedge pairs
2. prove that enlarged finite relation is still well-founded
3. isolate the two missing local TP-zero classifiers that the future
   bridge will actually need (`i = 2` and `i = n - 2`)
4. test a direct config-level lift, but back it out unless the build
   stays clean

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `sixBoundaryTpZeroCertStep`
  - `sixBoundaryTpZeroCertStep_rank_decrease`
  - `sixBoundaryTpZeroCertStep_wf`
  - `cup2BoundaryTpZeroCertStep`
  - `cup2BoundaryTpZeroCertStep_wf`
  - `midL_tp_zero_cases`
  - `high_tp_zero_cases`

### Load-Bearing Findings
- The enlarged finite relation
  `sixBoundaryEdge ∨ sixBoundaryTpZeroNonedgePair`
  is itself a certified DAG under the stored `sixStateRank`; the extra
  `16` explicit nonedge pairs still decrease the same rank.
- The genuinely missing local TP-zero classifiers are now isolated and
  formalized:
  - at `i = 2`, zero-`fc` plus the relevant local `exp2` equality
    collapses to the visible `022 / 100 / 112` cases
  - at `i = n - 2`, the analogous data collapses to `011 / 100`
- I tried to lift the full
  `cup2BoundaryChangeTpZeroStep -> cup2BoundaryTpZeroCertStep`
  bridge directly, but the proof shape through raw `cup2Boundary6
  (move ...)` terms turned into a large record-elaboration / `simpa`
  failure. That attempt was removed so the repository stays clean.

### Consequence
- The next proof step is sharper than before:
  add explicit boundary-projection helper lemmas for the six boundary
  indices and then redo the bridge theorem against those record-update
  equalities, rather than against raw `cup2Boundary6 (move ...)`
  expressions.
- The new finite certificate and local TP-zero classifiers are stable
  prerequisites for that next pass; they do not need to be redone.

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 32 (probe)

### Strategy
Make the missing global future-gain hypothesis explicit in Lean instead
of leaving it only in the external scripts:
1. add a forward TP-preserving bad-step relation
2. define the corresponding finite reachability closure
3. define `phi` / future gain as the maximum reachable `fc`
4. prove monotonicity along TP-preserving bad steps

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/Excursion.lean`](./lean/LeanMn/Convergence/Excursion.lean) now additionally contains:
  - `cup2TpBadStepFwd`
  - `cup2TpReachable`
  - `cup2TpFutureFc`
  - `cup2TpConstFutureStep`
  - `cup2Fc_le_cup2TpFutureFc`
  - `cup2TpFutureFc_mono`
  - `cup2TpFutureFc_step_mono`
- [`LeanMn/Ring.lean`](./lean/LeanMn/Ring.lean) now exports explicit `DecidableEq` / `Fintype` instances for dependent configurations `Config rs`.

### Load-Bearing Content
- The missing `phi` condition is now a first-class Lean object:
  for each fixed `n`, `cup2TpFutureFc n hn c` is the finite maximum of
  `cup2Fc` over all TP-preserving bad-step descendants of `c`.
- This avoids introducing any new well-foundedness assumptions just to
  *define* the future-gain quantity; it uses only finiteness of the
  configuration space.
- The basic monotonicity theorem now compiles:
  TP-preserving bad steps cannot increase `cup2TpFutureFc`.

### Consequence
- The codebase now has the missing API needed to state the true bridge
  hypothesis behind the `617`-edge certificate:
  boundary-changing TP-zero steps with
  `cup2TpFutureFc n hn c' = cup2TpFutureFc n hn c`.
- Phase 4 is still blocked on proving that this `phi`-constant slice
  refines to the finite 6-tuple DAG and then assembling the final
  convergence theorem.

### Verification
- `lake env lean LeanMn/Convergence/Excursion.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 33 (probe)

### Strategy
Exploit the new future-gain quantity immediately on the remaining
boundary-changing constant layer:
1. refine the raw boundary-changing TP-zero relation to the actual
   **bad-step** slice
2. split that slice by whether `cup2TpFutureFc` stays constant or drops
3. close the strict-drop half by `Nat.lt_wf`

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2BadBoundaryChangeTpZeroStep`
  - `cup2BadBoundaryChangeTpConstFutureStep`
  - `cup2BadBoundaryChangeTpDropFutureStep`
  - `cup2BadBoundaryChangeTpZeroStep_future_split`
  - `cup2BadBoundaryChangeTpDropFutureStep_wf`

### Load-Bearing Content
- The boundary-changing TP-zero bad-step layer is no longer a single
  opaque blocker.
- One entire half is now solved:
  if the boundary-changing TP-zero bad step strictly decreases
  `cup2TpFutureFc`, it belongs to a separate well-founded relation by
  inverse image of `<` on `Nat`.
- The only remaining unsolved constant-layer branch is now exactly the
  `phi`-constant slice
  `cup2BadBoundaryChangeTpConstFutureStep`.

### Consequence
- The live Phase 4 bridge target is now fully explicit in Lean:
  prove that `cup2BadBoundaryChangeTpConstFutureStep` refines to the
  finite 6-tuple certificate (or an equivalent boundary DAG).
- Everything else in the boundary-changing TP-zero layer is already
  discharged.

### Verification
- `lake env lean LeanMn/Convergence/SixTuple.lean` succeeds
- `lake build LeanMn` succeeds

## Exploration 31 (probe)

### Strategy
Stabilize the copy-only branch as its own relation and re-check the
future-gain route against the actual Lean tables instead of the stale
TP-only scripts.

### Outcome
PARTIAL SUCCESS

### What Compiled
- [`LeanMn/Convergence/Excursion.lean`](./lean/LeanMn/Convergence/Excursion.lean) now contains:
  - `cup2CopyBadStep`
  - `cup2AnomalousBadStep`
  - `cup2CopyMeasure`
  - `cup2Fc_lt_of_localFc_lt_copy`
  - `cup2CopyBadStep_decreases`
  - `cup2CopyBadStep_wf`
- [`LeanMn/Main.lean`](./lean/LeanMn/Main.lean) now imports the new module.

### Load-Bearing Findings
- The copy-only bad-step slice really does close cleanly by the local
  copy-neighbor argument: every such step weakly decreases `fc`, and in
  the zero-`Δfc` cases the old local `Ψ` lemmas still supply the strict
  descent.
- Re-checking the **full** bad-step future-gain graph against the actual
  Lean tables gives a stronger computational seam than the stale
  TP-only scripts:
  - for `n = 9, 10, 11, 12`, define
    `Φ_full(c) := max { fc(s) | s reachable from c by bad steps }`
    on the actual bad graph
  - the constant-`Φ_full` boundary-changing projection to the 6-boundary
    state has exactly `728` edges on `324` nodes
  - the edge set is almost n-stable: one edge varies with `n (mod 3)`,
    while the other `727` edges agree across the tested values
  - constant-`Φ_full` **fixed-boundary** steps are all copy steps in the
    tested graphs; no anomalous fixed-boundary constant-`Φ_full` step
    appeared

### Consequence
The upper-side convergence proof now has a sharper likely target than
the old TP route:
- use `Φ_full` from the actual bad-step graph, not the stale TP-only
  surrogate
- handle the fixed-boundary constant-`Φ_full` slice by
  `cup2CopyBadStep_wf`
- handle the boundary-changing constant-`Φ_full` slice by a small
  6-boundary DAG, apparently with a residue-`3` variant

This is still not enough to wrap Phase 4, because the Lean development
does not yet contain:
- a formal definition of `Φ_full`
- the proof that constant-`Φ_full` boundary-changing steps refine to the
  `728`-edge 6-boundary graph
- the final lexicographic assembly into
  `WellFounded (badStep (cup2System n hn) (cup2GoodCycle n hn))`

### Verification
- `lake build LeanMn.Convergence.Excursion` succeeds

## Exploration 29 (probe)

### Strategy
Try to expose the finite 6-tuple certificate more directly by adding
named `sixBoundaryEdge` lemmas for each visible local boundary rewrite
pattern, with proofs discharged by `native_decide`.

### Outcome
FAILED

### What Broke
The direct theorem shape
`theorem ... (s : SixBoundary) ... : sixBoundaryEdge { s with ... } s := by native_decide`
does not compile.

Lean rejects the proof goal with:
- `Expected type must not contain free variables`

The issue is not the edge facts themselves; it is the proof form.
`native_decide` cannot close these goals while the record `s` remains a
free variable in the expected proposition.

### Load-Bearing Observation
The right finite proof shape will need one of:
- explicit elimination of the remaining unconstrained coordinates
- a helper theorem over fully concrete boundary states
- or a decidable bridge theorem that first rewrites the constrained
  fields and only then invokes the finite certificate

So the 6-tuple route still looks viable, but it needs a different
interface than the naive “polymorphic `native_decide` lemma” attempt.

### Remaining Gap
Phase 4 is still blocked only on
`cup2BoundaryChangeTpZeroStep`, but the next step is now sharper:
- refactor the desired boundary-edge facts into a proof form that the
  finite certificate can actually discharge

### Verification
- `lake build LeanMn.Convergence.SixTuple` currently fails on the new
  raw `native_decide` boundary-edge lemmas

## Exploration 30 (probe)

### Strategy
Audit the extracted `6`-tuple certificate against the actual extraction
pipeline instead of guessing the missing bridge:
1. repair the failed generic edge-lemma experiment so the Lean build is
   clean again
2. compare the published `617`-edge graph with the simpler graph induced
   by *nonnegative* TP-preserving bad steps only
3. check whether the missing global hypothesis is really the extracted
   `phi`-constancy condition, or whether it can be dropped

### Outcome
PARTIAL SUCCESS

### What Was Settled
- The Lean build is restored after keeping only the genuinely true
  generic `sixBoundaryEdge_*` lemmas. The attempted universal lemmas for
  raw `bot_001`, `high_211`, and `top_011` were removed because they are
  false.
- The local extraction audit confirms the real source of the published
  `617`-edge graph:
  - it is built from TP-preserving bad steps
  - then filtered by the extracted `phi[s] = phi[c]` condition
- If the extraction is restricted to **nonnegative** TP-preserving bad
  steps only, the resulting boundary graph is still n-stable for
  `n = 9, 10`, still a DAG of rank `24`, but it has **594** edges rather
  than `617`.

### Load-Bearing Finding
The missing bridge really is a global future-gain condition, not just TP
preservation and not just bad-step membership.

Concrete counterexample check:
- there exist bad, TP-preserving, zero-`Δfc` boundary steps with source
  6-tuple `(0,1,0,0,2,0)` that are *not* edges of the published
  `617`-edge graph
- so even
  `badStep + TP-preserving + Δfc = 0 + boundary-change`
  is still too weak

This sharpens the proof obligation:
- the true bridge must isolate the `phi`-constant / maximal-future-gain
  slice of the constant-layer bad-step graph
- the precomputed 6-tuple DAG only controls that refined slice

### Consequence
The current Lean API is still missing a load-bearing definition:
- a recursively defined future-gain / `phi` quantity (or an equivalent
  analytically simplified surrogate)

Without that, the `SixTuple.lean` certificate cannot yet be connected to
the actual bad-step relation.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds again after removing
  the false universal edge lemmas

## Exploration 28 (probe)

### Strategy
Make the remaining constant-layer boundary problem explicit in the Lean
API by splitting TP-preserving, zero-`fc` steps into fixed-boundary and
boundary-changing subrelations over the raw `SixBoundary` projection.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `cup2Boundary6_changed_implies_boundary_index`
  - `cup2BoundaryChangeTpZeroStep`
  - `cup2TpZeroStep_boundary_split`

LOAD-BEARING CONTENT:
- The remaining Phase 4 hole is now represented directly as the relation
  `cup2BoundaryChangeTpZeroStep`.
- Everything outside that relation is already handled:
  - fixed-boundary constant-layer steps by `cup2FixedBoundaryTpZeroStep_wf`
  - deep-interior TP-zero steps by `cup2DeepMidTpZeroStep_wf`
  - negative-`Δfc` bad steps by `cup2BadStepNeg_wf`
  - nonnegative bad steps by `cup2BadStepNonneg_wf`

VERIFICATION:
- `lake build LeanMn.Convergence.SixTuple` succeeds

## Exploration 53 (constant-future split refinement)

### Strategy
Shrink the remaining full-future boundary blocker before returning to the
finite certificate:
1. split `cup2BadBoundaryChangeConstFutureStep` into copy-neighbor vs
   anomalous subrelations
2. discharge the copy-neighbor side directly with the existing
   `(cup2FutureFc, cup2CopyMeasure)` descent
3. prove the low / near-boundary-mid movers cannot occur in the
   anomalous remainder

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/SixTuple.lean`](./lean/LeanMn/Convergence/SixTuple.lean) now additionally contains:
  - `low_copyNeighbor`
  - `move_eq_move_same_index`
  - `cup2CopyBadStep_not_anomalous`
  - `cup2BadBoundaryChangeConstFutureCopyStep`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep`
  - `cup2BadBoundaryChangeConstFutureStep_copy_or_anomalous`
  - `cup2BadBoundaryChangeConstFutureCopyStep_decreases`
  - `cup2BadBoundaryChangeConstFutureCopyStep_wf`
  - `cup2BadBoundaryChangeConstFuture_idx1_copy`
  - `cup2BadBoundaryChangeConstFuture_idx2_copy`
  - `cup2BadBoundaryChangeConstFuture_idxN3_copy`
  - `cup2BadBoundaryChangeConstFutureAnomalousStep_cases`

### Load-Bearing Consequence
- The old live blocker
  `cup2BadBoundaryChangeConstFutureStep`
  is no longer a single opaque relation.
- Its copy-neighbor portion is now already discharged by the existing
  full-future resolved measure.
- The anomalous remainder is now forced onto the three endpoint-side
  movers:
  - `idx0`
  - `idxN2`
  - `idxN1`
- So the remaining Phase 4 proof obligation is no longer “all
  boundary-changing constant-future bad steps.” It is the anomalous
  endpoint branch only.

### Verification
- `lake build LeanMn.Convergence.SixTuple` succeeds
- `lake build LeanMn` succeeds

## Exploration 97 (exact endpoint `idxN2_b3` source-rank packaging)

### Strategy
Replace the remaining abstract zero-tail `idxN2_b3` source-rank positivity
hypothesis with an explicit theorem on the actual exact endpoint shell, so
the residue is stated in terms of concrete `boundary6` / slack cases rather
than a bare `0 < rank` assumption.

### Outcome
SUCCEEDED

### Concrete Artifacts
- [`LeanMn/Convergence/Main.lean`](./lean/LeanMn/Convergence/Main.lean) now additionally contains:
  - `b3BoundaryCode_rank_pos_iff`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_src_rank_pos_iff_of_idxN2_b3`
  - `cup2BadConstFutureWitnessedEndpointExceptionalAnomalousSegmentStep_cfg_rank_lt_of_idxN2_b3_zeroTail_of_cases`
  - `cup2BadConstFutureWitnessedEndpointB3AnomalousSegmentStep_cfg_rank_lt_of_zeroTail_of_cases`

### Load-Bearing Consequence
- The exact endpoint `idxN2_b3` zero-tail branch no longer needs to carry an
  opaque source-rank positivity assumption.
- The remaining `b3` residue is now exposed as explicit source-side
  `boundary6` / slack cases on `c0`, `c1`, and `c2`.
- This is the right interface for the next proof pass: either prove those
  cases from the witnessed `idxN2_b3` relation or isolate the impossible
  remainder directly.

### Verification
- `lake build LeanMn.Convergence.Main` succeeds
