# SmallN Next-Step Decision

Date: 2026-04-14

This note records the recommended next step after the residual-census audit and
the closure-plan cleanup.

## Facts now established

1. The historical `164` / `30` pair is reproducible from the bounded legacy DFS
   regime.
2. Those numbers should therefore not be treated as exact targets by default.
3. The current exact `n = 5` generator object is well-defined and reproducible:
   - `(2,2,2,3,3)` → `2027` post-relabel recanonicalized classes
   - `(2,2,3,2,3)` → `292` post-relabel recanonicalized classes
4. A Python prototype of the `candidateBlocked5` kernel check already succeeds
   on the exact normalized classes:
   - `(2,2,2,3,3)` → `2098/2098` determined-key classes blocked
   - `(2,2,3,2,3)` → `312/312` determined-key classes blocked
5. Combined exact `n = 5` tail summary:
   - raw cycles: `47232`
   - exact normalized determined-key classes: `2410`
   - post-relabel recanonicalized classes: `2319`
   - blocker result: `2410/2410` blocked by nonempty kernel
6. `LeanMn.SmallN.LowerBound.N5Check` now has a real conservative
   `candidateBlocked5` skeleton and builds.
7. Under the current exact topological classifier, those exact `n = 5` classes
   are all `sweep`-type in the sense `|W| ≥ 2`.
8. The current exact enumerator is good enough for `n = 5` audit work, but too
   blunt for `n = 6`:
   - an exact run on `(2,2,2,3,3,3)` did not finish in several minutes and was
     stopped
   - the legacy bounded run reproduces `30`, but that is no longer considered a
     trustworthy exact target
9. The exact `n = 5` normalized tail artifact has been emitted to:
   - `LeanMn/SmallN/N5_TAIL_EXACT_2026-04-14.json`
   - size: about `13M`
   - records: `2410`
10. Direct single-file Lean emission of those `2410` candidates into one
    `N5DataTail.lean` module is **not** viable as-is:
    - the generated file was about `912K`
    - standalone build hit a Lean stack overflow
    - conclusion: exact data emission will need **chunking**, not a single huge
      array literal

## Decision

The best next move is:

### A. Treat `n = 5` and `n = 6` differently

Do **not** force one unified brute-force route.

- `n = 5`: continue from the exact audited generator object
- `n = 6`: do not rely on the current exact brute enumerator; use a more
  targeted front-end reduction

This matches the architectural split already suggested by the SmallN closure
plan.

### B. For `n = 5`, choose one of two proof objects explicitly

Only two serious options remain.

#### Option 1: conservative exact route

Use the exact current object:

- `(2,2,2,3,3)` → `2027`
- `(2,2,3,2,3)` → `292`

Pros:

- no ambiguity
- no dependence on legacy counts
- generator already computes it exactly

Cons:

- larger Lean data payload
- likely more expensive checker runs

#### Option 2: smaller exact residual object

Define a new exact residual object strictly smaller than the current exact
cycle census, together with a completeness theorem showing every sub-threshold
valid system maps into it.

Pros:

- smaller Lean footprint
- closer to the original finite-residual plan

Cons:

- requires new mathematics / completeness work before any Lean payoff

### Recommendation

For momentum, prefer **Option 1 for `n = 5`**.

Reason:

- the main ambiguity has already been removed,
- the exact current object is real,
- the blocker prototype already kills the exact current object at the Python
  level,
- moving from "ambiguous small object" to "exact larger object" is better than
  staying blocked on a legacy artifact.

If the exact `2027 + 292` object proves too expensive in Lean, that will be a
concrete engineering fact rather than a guess.

### C. For `n = 6`, do not start from the exact brute enumerator

Instead:

1. use the existing `M6Routing` / `M6PhaseFront` / `M6SystemFront` /
   `M6AllNormalCore` front-end to shrink the search space structurally,
2. only then define the residual finite object that still needs certification.

This is the only plausible route that avoids replacing one legacy artifact
(`30`) with one giant exact brute-force object.

## Immediate action recommendation

If work continues right now, the next coding task should be:

1. decide whether to keep the current `List`-based `candidateBlocked5` checker
   or switch immediately to an `Array`-native candidate type,
2. emit the exact `2410`-candidate route in **chunked Lean data files** rather
   than one monolithic `N5DataTail.lean`,
3. then start `N5DataTail.lean` as a thin aggregator over those chunks, rather
   than from the historical `164`.
