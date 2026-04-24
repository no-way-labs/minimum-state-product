# M5 M6 Exact Closure Plan

Date: 2026-04-14

This note is the SmallN-only closure plan for:

- `M_5_lower`
- `M_6_lower`

It is written to avoid touching the `n ≥ 9` lower-bound track.

The plan below is based on the current SmallN code and the first pass of the
new `LeanMn/SmallN/LowerBound` subtree.

## Status update after the residual-census audit

The historical residual counts

- `164` for `n = 5`
- `30` for `n = 6`

should no longer be treated as exact targets by default.

Current audit status:

- the new `gen_smalln_lower_bound.py` computes an exact, explicitly specified
  search object,
- the historical `164/30` pair is reproducible from a **bounded legacy DFS**
  regime,
- so the old numbers are best interpreted as legacy search artifacts unless and
  until an exact residual object is defined that reproduces them independently.

For the audit details, see:

- `LeanMn/SmallN/N5_RESIDUAL_CENSUS_AUDIT_2026-04-14.md`

## Bottom line

`n = 5, 6` still look closable.

But they are **not** closable by the naive route:

- not by quantifying over all systems,
- not by dumping all raw good cycles into Lean,
- not by trying to make the `n ≥ 9` machinery accept smaller `n`.

They are closable by a **finite residual certification** route inside
`LeanMn.SmallN`, provided the raw cycle space is quotiented aggressively before
data lands in Lean.

## What is already in place

The new SmallN-only subtree now has:

- `LowerBound/Core.lean`
- `LowerBound/Arithmetic.lean`
- `LowerBound/Blockers.lean`
- `LowerBound/N5Types.lean`
- `LowerBound/N5Data.lean`
- `LowerBound/N5Check.lean`
- `gen_smalln_lower_bound.py`

The key facts already formalized are:

1. exact ordered sub-threshold profile sets for `n = 5, 6`,
2. exact `n = 5` rotation-profile front-end,
3. a reusable sink-kernel bitmask routine,
4. the first `n = 5` candidate-shape predicates.

Current verified `n = 5` profile split:

- ordered sub-threshold profiles: `26`,
- rotation classes: `6`,
- represented by:
  - `(2,2,2,2,2)`
  - `(2,2,2,2,3)`
  - `(2,2,2,2,4)`
  - `(2,2,2,3,3)`
  - `(2,2,3,2,3)`
  - `(2,2,2,2,5)`

## The critical lesson from the generator

The raw cycle space is too large to use as the final proof object.

Measured with the new generator:

- `(2,2,2,2,2)`:
  - `32` canonical-start full-support cycles
- `(2,2,2,2,3)`:
  - `480` canonical-start full-support cycles
- `(2,2,2,3,3)`:
  - `40,320` canonical-start full-support cycles

So the exact closure route for `n = 5` is **not**:

> generate all canonical-start cycles for `(2,2,2,3,3)` and ship them to Lean.

That is still much too large.

The exact current generator already shows a strong quotient effect, but it does
**not** support using the historical `164/30` pair as exact targets:

- `(2,2,2,3,3)`:
  - raw canonical-start full-support cycles: `40,320`
  - post-relabel recanonicalized classes: `2,027`
- `(2,2,3,2,3)`:
  - raw canonical-start full-support cycles: `6,912`
  - post-relabel recanonicalized classes: `292`

So the next task is no longer "find the one missing symmetry that forces
`2027 -> 164`." The next task is to define the **actual residual proof object**
precisely.

## The exact quotient already available

The raw cycle search must be quotiented in this order.

For a raw good cycle `C`, normalize by:

1. **cycle rotation**
   - choose the lexicographically least cyclic presentation,
2. **cycle reversal**
   - if the obstruction proof is orientation-symmetric, choose the lesser of
     forward and reversed presentations,
3. **ring rotation**
   - rotate processor indices into a fixed profile representative,
4. **per-processor state relabeling**
   - relabel states at each processor by first-seen order along the chosen
     cycle presentation:
     - first seen state ↦ `0`
     - second new state ↦ `1`
     - third new state ↦ `2`
     - etc.
5. **determined-entry normal form**
   - from the normalized cycle, compute the determined transition entries and
     use their serialized table as the final dedup key if config-level
     normalization is still too coarse.

This quotient is now implemented well enough to support exact audits.

The key empirical facts are:

- for `(2,2,2,3,3)`, raw canonical-start cycles = `40,320`,
- adding per-processor first-seen relabeling plus post-relabel
  recanonicalization drops the count to `2,027`,
- for `(2,2,3,2,3)`, the analogous exact count is `292`,
- replaying the legacy bounded DFS reproduces the historical `82`, `164`, and
  `30` counts exactly.

So the next actual job is:

> define the exact residual object that Lean should certify, compute it exactly,
> and only then re-implement that exact object in Lean.

## Exact `n = 5` closure route

### Phase 1: finish the profile front-end

Keep `LowerBound/Arithmetic.lean` and `LowerBound/N5Types.lean` as the live
front-end.

Add:

- `N5ProfileTag`
  - `allBinary`
  - `fourBinary3`
  - `fourBinary4`
  - `tailA` for `(2,2,2,3,3)`
  - `tailB` for `(2,2,3,2,3)`
  - `fourBinary5`

Use the theorem in `N5Types.lean` to route every ordered sub-threshold profile
to exactly one of these six classes.

### Phase 2: split easy classes from the true residual

For `n = 5`, the true residual is only:

- `tailA = (2,2,2,3,3)`
- `tailB = (2,2,3,2,3)`

All other `n = 5` classes are "easy" in the sense that their raw cycle spaces
are small enough to kill directly by finite certification.

Recommended file split:

- `LowerBound/N5DataEasy.lean`
- `LowerBound/N5DataTail.lean`
- `LowerBound/N5Check.lean`
- `LowerBound/N5Proof.lean`

### Phase 3: direct finite closure of the easy classes

For these four classes:

- `(2,2,2,2,2)`
- `(2,2,2,2,3)`
- `(2,2,2,2,4)`
- `(2,2,2,2,5)`

do **not** over-engineer the candidate object.

Use:

- full cycle config lists,
- mover lists,
- direct determined-entry reconstruction,
- direct blocker checks:
  - TF conflict,
  - forced-kernel nonemptiness,
  - optionally direct bad-cycle witness if cheaper.

For the smaller two classes:

- `(2,2,2,2,2)`
- `(2,2,2,2,3)`

the current generator counts are already small enough that a direct
`native_decide` closure should be realistic.

For `(2,2,2,2,4)` and `(2,2,2,2,5)`:

- first run the generator,
- record exact normalized candidate counts,
- if they are still modest, keep them in the same direct route,
- if not, add one more normalization layer before data emission.

### Phase 4: reconstruct the true `n = 5` residual census

This is the central task.

Use `gen_smalln_lower_bound.py` to:

1. enumerate raw canonical-start full-support cycles for:
   - `(2,2,2,3,3)`
   - `(2,2,3,2,3)`
2. compute exact normalized classes using:
   - cycle rotation,
   - reversal,
   - ring rotation,
   - per-processor first-seen state relabeling,
   - post-relabel recanonicalization,
   - determined-entry table serialization when needed.
3. explicitly classify those exact classes into the analytically relevant
   subfamilies:
   - sweep
   - fc=2 / BAF
   - wiggle / higher-complexity residuals
4. decide which of those exact classes still need finite certification after
   the existing analytical reductions are applied.

Do not proceed to Lean tail data emission until the residual object is defined
in these exact terms.

### Phase 5: choose the final candidate object for the tail

For whatever exact residual set survives Phase 4, the final Lean candidate
object should be the **normalized determined-cycle certificate**, not the raw
cycle.

Recommended shape:

```lean
structure N5TailCandidate where
  profile : N5ProfileTag
  configs : Array (Array Nat)
  movers  : Array Nat
```

This is intentionally concrete.

Do not compress it further unless elaboration forces you to.

The point is:

- the candidate list should be a concrete exact finite set,
- the configs and mover word reconstruct the determined entries,
- the determined entries reconstruct the forced graph,
- the forced graph reconstructs the blocker.

### Phase 6: exact checker API

`N5Check.lean` should expose:

```lean
def candidateBlocked5 : N5TailCandidate -> Bool
def easyCandidateBlocked5 : N5CandidateCycle -> Bool
```

The checker should:

1. reconstruct determined mover/non-mover entries,
2. reject immediate TF inconsistency,
3. build the non-good forced graph,
4. compute sink deletion via `Blockers.sinkKernelMask`,
5. return `true` when the residual kernel is nonempty.

Do not mix proposition-valued proof search into the checker.

### Phase 7: exact `n = 5` proof assembly

`N5Proof.lean` should prove:

1. every easy-class candidate is blocked,
2. every tail candidate in the emitted exact residual data list is blocked,
3. every raw valid sub-threshold `n = 5` system maps to one of those
   candidates.

The completeness theorem should be split into two layers:

```lean
theorem valid_n5_maps_to_rotationClass ...
theorem valid_tail_cycle_maps_to_normalizedCandidate ...
```

Do not try to prove the whole theorem in one jump.

Final theorem:

```lean
theorem M_5_lower_proved
    (sys : System) (hn : sys.rs.n = 5) (hsub : stateProduct sys.rs < 96) :
    ¬ valid sys
```

### Phase 8: wire only after `M_5_lower_proved` is green

Only after:

- `lake build LeanMn.SmallN.LowerBound.N5Proof`

should `SmallN/Theorem.lean` stop using the `M_5_lower` axiom.

## Exact `n = 6` closure route

`n = 6` should be split differently from `n = 5`.

Do **not** treat it as a second raw finite monster from the start.

Use the existing SmallN files:

- `M6Routing.lean`
- `M6PhaseFront.lean`
- `M6SystemFront.lean`
- `M6AllNormalCore.lean`

as the front-end reducer for the non-residual classes.

### Phase 1: keep exact `n = 6` profile classification finite

`Arithmetic.lean` already gives the exact ordered profile space.

The docs say the `n = 6` sub-threshold rotation-class count is `27`.

Do not try to land all `27` as raw cycle data.

### Phase 2: route non-tail classes structurally

For `n = 6`, use the existing SmallN front-end to route profiles by binary
count and pattern:

- `6` binaries:
  - direct finite obstruction
- `5` binaries:
  - route through `M6Routing` / `M6PhaseFront` / `M6SystemFront`
- `4` binaries:
  - keep the same structural route when it closes quickly,
  - otherwise fall back to direct finite data
- `3` binaries:
  - the only genuine residual is `(2,2,2,3,3,3)`

This keeps `n = 6` from becoming one giant data dump.

### Phase 3: define the exact `n = 6` tail object

For the sole real tail:

- `(2,2,2,3,3,3)`

run the same exact-vs-legacy audit discipline as for `n = 5`:

1. raw canonical-start full-support cycle enumeration,
2. cycle rotation / reversal,
3. ring rotation,
4. per-processor first-seen state relabeling,
5. post-relabel recanonicalization,
6. determined-entry normal form when needed,
7. explicit identification of the exact residual object, rather than blind
   targeting of the historical `30`.

### Phase 4: reuse the same finite checker architecture

The `n = 6` checker should use the exact same architecture as `n = 5`:

- reconstruct determined entries,
- build non-good forced graph,
- apply sink deletion,
- certify nonempty kernel.

Keep the API parallel:

```lean
def candidateBlocked6 : N6TailCandidate -> Bool
```

### Phase 5: exact `n = 6` theorem split

`N6Proof.lean` should prove:

1. non-tail classes reduce to already-blocked SmallN forms,
2. every tail candidate in the normalized exact residual list is blocked,
3. every valid sub-threshold `n = 6` system maps to one of those cases.

Final theorem:

```lean
theorem M_6_lower_proved
    (sys : System) (hn : sys.rs.n = 6) (hsub : stateProduct sys.rs < 288) :
    ¬ valid sys
```

Only after that should `SmallN/Theorem.lean` stop using `M_6_lower`.

## Exact file plan

Stay under `LeanMn/SmallN`.

Recommended next file additions:

- `LowerBound/N5DataEasy.lean`
- `LowerBound/N5DataTail.lean`
- `LowerBound/N5Proof.lean`
- `LowerBound/N6Types.lean`
- `LowerBound/N6Data.lean`
- `LowerBound/N6Check.lean`
- `LowerBound/N6Proof.lean`

The local generator should remain:

- `LeanMn/SmallN/gen_smalln_lower_bound.py`

Do not add any new dependency on `LeanMn/LowerBound/Theorem`.

## Hard requirements

1. Keep all edits inside `LeanMn/SmallN` and the new SmallN-only subtree.
2. Do not modify the `n ≥ 9` lower-bound files.
3. Do not ship raw `40k`-scale cycle data to Lean.
4. Do **not** target the historical `164/30` pair as exact goals unless a
   precisely defined exact residual object reproduces them independently of the
   bounded legacy DFS.
5. Keep the blocker executable and Boolean.
6. Prefer explicit data over abstraction once the exact normalized residual
   sets are
   known.

## Immediate next tasks

1. Keep `gen_smalln_lower_bound.py` as the computational source of truth for:
   - the exact current search object,
   - the historical legacy-bounded search object,
   - and the explicit comparison between them.
2. Add an exact cycle-type classifier that matches the analytical split more
   faithfully than the current provisional walk taxonomy.
3. Decide what the Lean residual object actually is:
   - exact normalized cycle classes,
   - or a smaller explicitly defined residual object with its own completeness
     theorem.
4. Only after that decision, emit `N5DataTail.lean`.
5. Implement `candidateBlocked5`.
6. Prove `M_5_lower_proved`.
7. Then repeat the same exact-vs-legacy discipline for `n = 6`, using the
   existing `M6*` SmallN front-end to avoid unnecessary finite data outside the
   true tail.
