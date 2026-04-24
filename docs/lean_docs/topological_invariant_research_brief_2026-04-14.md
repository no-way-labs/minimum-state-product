# Topological Invariant Research Brief

Date: 2026-04-14

This note is for side research on the following question:

> Is there a structural or topological invariant that rules out all
> sub-threshold small-`n` systems in one shot, or at least collapses most of
> the current lower-bound casework into a single mechanism?

The intended scope is computational and conceptual, not Lean implementation.
If something good comes out of this, it can later be translated into Lean.

## Why this is plausible

The current lower-bound story already looks like fragments of one larger
obstruction:

- sweeps are killed by a shadow cycle,
- residual `n = 5, 6` tails are killed by a forced non-good kernel / SCC,
- entry-conflict arguments kill certain non-sweep words before any completion
  matters,
- all of these are really statements about recurrent structure in the
  complement of the good cycle.

That strongly suggests that the real hidden object is not "a property of the
transition table" but "a property of the induced directed dynamics on the
configuration graph."

## The sharp target

The strongest useful outcome would be a theorem of the form:

> For any sub-threshold candidate good cycle `C`, the dynamics determined by
> `C` on the non-good region carries a nontrivial recurrent obstruction.

Possible equivalent-looking formulations:

- the determined non-good graph has nonempty Conley-type index,
- the sink kernel is forced to be nonempty,
- the complement of the good cycle carries a nontrivial directed homology
  class,
- a suitable index/flux/degree cannot vanish below threshold.

If such a theorem existed in the right form, the lower bound would stop being
"many unrelated tricks" and become "one invariant, several concrete
manifestations."

## What the invariant must do

A serious candidate invariant has to satisfy all of the following.

1. It must be computable from the candidate good cycle and its determined
   entries, not from the full space of completed transition tables.
2. It must be invariant under the normalizations already used on the cycle
   side: cycle rotation, ring rotation, state relabeling, and probably
   orientation symmetry when valid.
3. It must obstruct every sub-threshold residual family:
   - `n = 5`, `ms = (2,2,2,3,3)`
   - `n = 6`, `ms = (2,2,2,3,3,3)`
   - ideally also the analytically killed sweep/non-sweep classes.
4. It must not falsely kill threshold witnesses:
   - `n = 5`, `ms = (2,2,2,3,4)`
   - `n = 6`, `ms = (2,2,2,4,3,3)`
   - `n = 7`, `ms = (3,2,2,2,3,4,3)` or rotation
   - `n = 8`, `ms = (2,2,3,4,3,3,2,3)`
5. It must interact correctly with the central-daemon semantics: a nontrivial
   recurrent class in the bad region must actually imply non-convergence.

## What the current project already suggests

The best current evidence is:

- `verification_claims_v2.md` says the only residual small-`n` families are
  the pure tails for `n = 5, 6`, and that they are closed by finite forced
  kernel lemmas.
- `exploration_log_cic.md` repeatedly treats sweep shadow and forced SCC as
  parallel manifestations of the same obstruction class.
- the `SmallN` closure plan already points to normalized determined-cycle
  certificates rather than whole systems as the right finite proof object.

Read first:

- `docs/verification_claims_v2.md`
- `docs/verification_claims.md`
- `exploration_logs/exploration_log_cic.md`
- `lean/LeanMn/SmallN/M56_CLOSURE_PLAN_2026-04-14.md`

Concrete scripts worth mining:

- `docs/verify_lower_bound.py`
- `docs/verify_witnesses.py`
- `probes/cic_completion_failure2.py`
- `probes/cic_lifting_proof2.py`

## Candidate invariant families

These are the most promising directions.

### 1. Directed Conley-index style obstruction

Object:

- finite directed graph on non-good configurations induced by determined moves,
- or the sink kernel after iterative sink deletion.

Hope:

- shadow cycles, forced SCCs, and bad kernels all become instances of one
  "nontrivial recurrent index" statement.

Risk:

- may only repackage the existing kernel argument, not simplify it.

Best first question:

- can one define a recurrence index that is visibly nonzero for all
  sub-threshold candidates and zero for threshold witnesses?

### 2. Binary-skeleton plus fiber bundle

Object:

- project configurations onto the binary coordinates,
- treat the non-binary coordinates as fibers over that binary base,
- study how determined edges move within and across fibers.

Hope:

- the true obstruction may live on a small binary skeleton, with ternary and
  quaternary coordinates only mediating fiber transport.
- this matches the recurring "binary 6-cycle + fiber switching" picture in the
  CIC notes.

Risk:

- many valid witnesses also have rich binary projections, so the projection
  alone is too coarse.

Best first question:

- is there a fiber-transport monodromy around the binary skeleton that is
  forced below threshold but broken at the witness?

### 3. Relative homology / complement class

Object:

- view the good cycle as an embedded 1-cycle in the configuration graph or a
  cubical complex model of the state space,
- study the complement of the good cycle together with determined edges.

Hope:

- the obstruction may be a nontrivial relative class in the bad region that the
  adversary can follow forever.

Risk:

- plain undirected homology is probably too coarse; the issue is directed and
  scheduler-sensitive.

Best first question:

- does the bad region retain a canonical 1-class after removing sinks, and is
  that class exactly what shadow/SCC are detecting?

### 4. Index / flux / circulation defect

Object:

- assign a signed local current or discrete 1-form to determined moves,
- aggregate it around the ring or around binary boundaries.

Hope:

- winding, shadow displacement, and forced pumping might be manifestations of
  one conserved/nonconserved quantity.

Risk:

- too many earlier scalar invariants have already turned out to be too weak.

Best first question:

- is there a local-to-global flux whose vanishing is incompatible with closure
  below threshold?

### 5. Discrete Morse / Lyapunov impossibility

Object:

- search for a universal "bad-region cannot be acyclic" certificate rather than
  a cycle witness directly.

Hope:

- a single theorem saying "every attempted Lyapunov collapse leaves a nonempty
  kernel" would subsume sink deletion.

Risk:

- this may again just restate the kernel argument.

Best first question:

- can sink-kernel nonemptiness be recognized by a simpler invariant than full
  iterative deletion?

## Benchmark set

Any candidate invariant should be tested on these cases first.

### Must be obstructed

- `n = 5`, `ms = (2,2,2,3,3)`
- `n = 5`, `ms = (2,2,3,2,3)` if treated as a separate profile class
- `n = 6`, `ms = (2,2,2,3,3,3)`
- small RFC-dispatched classes should ideally be killed too, but they are
  secondary for the invariant search

### Must survive

- `n = 5`, witness `ms = (2,2,2,3,4)`
- `n = 6`, witness `ms = (2,2,2,4,3,3)`
- `n = 7`, witness `ms = (3,2,2,2,3,4,3)` or rotation
- `n = 8`, witness `ms = (2,2,3,4,3,3,2,3)`

### Must explain the regime change

- `n = 4` valid witness behavior versus `n = 5` failure
- why recurrent bad structure becomes unavoidable once the good set is a small
  fraction of the full state space

## Minimal experiment program

Do not start with abstraction. Start with datasets.

1. Extract the exact residual cycle sets used in the old SCC scripts.
2. For each cycle, compute:
   - sink-kernel size
   - SCC count and largest SCC size
   - shortest bad directed cycle length
   - binary projection graph
   - fiber-switching statistics
   - cycle-space rank of the bad graph
   - any candidate flux / degree / parity summaries
3. Compute the same summaries for the threshold witnesses.
4. Look for quantities that:
   - are constant or sign-stable across all killed sub-threshold cases,
   - differ sharply at the witness,
   - are expressible without reference to ad hoc case splits.

If nothing sharp appears at that level, the invariant is probably not scalar.
Then move to structured objects: quotient graph, transport operator, index
object, or directed homology class.

## Falsification tests

Before getting excited about a candidate invariant, try to break it.

1. Does it wrongly obstruct the `n = 5` witness at product `96`?
2. Does it depend on the arbitrary presentation of the cycle?
3. Does it collapse under state relabeling or ring rotation?
4. Does it distinguish sweep from non-sweep only because of word-level
   artifacts, rather than because of the induced bad dynamics?
5. Is it really new, or just sink-kernel nonemptiness in disguise?

## What would count as success

Weak success:

- one invariant that cleanly explains the `n = 5, 6` residual kernel lemmas
  without full brute-force replay.

Medium success:

- a theorem reducing shadow and forced kernel to one common obstruction on the
  determined bad graph.

Strong success:

- a single obstruction theorem that covers all sub-threshold small-`n` classes,
  and maybe also clarifies the `n ≥ 9` lower-bound mechanism.

## What probably will not work

- plain product counting alone,
- pure undirected graph invariants,
- invariants that ignore completion-versus-determined structure,
- anything that cannot see the distinction between sub-threshold tails and the
  threshold witnesses.

## Suggested output format for side work

If you pursue this, keep notes in the following format:

1. candidate invariant definition
2. exact domain of definition
3. normalization invariance checks
4. benchmark results on:
   - `n = 5` tail
   - `n = 6` tail
   - `n = 5` witness
   - `n = 6` witness
5. one sentence on whether it is genuinely simpler than the current SCC/shadow
   split

The goal is not to produce philosophy. The goal is to isolate a candidate that
survives contact with the known witness/residual data.
