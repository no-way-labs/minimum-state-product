# UB Staircase Research

## Purpose

This note is a working synthesis of the upper-bound cold-start investigations.
It is not a proof document. Its purpose is to record:

- what is now believed to be structurally true
- what has been computationally checked
- what routes are no longer preferred
- what exact theorem targets remain

This should be the source-of-truth research note for the staircase route.

## Current UB Status

The current Lean UB route still has one live convergence gap:

- [ConstLayerDAG.lean](./lean/LeanMn/Convergence/ConstLayerDAG.lean): `cphi_bridge`

The previous `Φ_full / CΦ / 617-edge` route exposed a genuinely global transport
problem. Cold-start exploration was used to test whether a different, more
local convergence proof exists.

## Main Conclusion

There is now enough evidence to do more than "take the staircase route
seriously." The current state is:

1. A viable **Phase 1 predicate** exists on the actual CUP-2 tables.
2. Same-score runs freeze the support of those Phase 1 bad patterns.
3. The remaining dynamics decompose into independent **active intervals**.
4. The only unbounded core is a **pure-mid interval system** with fixed boundary
   values.
5. The pure-mid core now has a concrete proof via an explicit rank.
6. The old raw mixed-step / gadget assembly route is blocked.
7. The best current redesign is a **macro route**:
   - contract score-preserving pure-mid motion to a `CoreNormal` relation
   - define a macro step as one boundary move followed by pure-mid normalization
   - prove a cycle/SCC projection theorem from the real same-score graph to the
     macro graph

So the staircase route is no longer just a plausible alternative architecture.
It is the current **working proof route**. Broad exploration should stop and
theorem construction should begin.

## Stable Findings

### 1. Phase 1 predicate

The best-supported Phase 1 score is the **uncreatable-triple score**:

- at position `1`: `(1,2,1)`
- at positions `2..n-3`: `(2,0,2)`
- at position `n-2`: `(2,0,1)` or `(2,1,0)`
- at position `n-1`: `(2,0,0)`

Call the total count of these occurrences `Phase1Score`.

This predicate was independently identified by multiple runs on the exact
CUP-2 tables, and is currently the best-supported Phase 1.

### 2. Uncreatability / closure

The Phase 1 bad triples are locally uncreatable from the CUP-2 tables.
Therefore:

- `Phase1Score` never increases under any move
- the zero-score class is forward-invariant

This part is table-local and appears formalizable directly.

### 3. Same-score support freezing

In any same-`Phase1Score` execution, existing bad triples cannot disappear and
reappear elsewhere. So their radius-1 supports freeze.

This yields a decomposition:

- frozen bad blocks
- active intervals between them

### 4. Independent active intervals

Once bad supports are frozen, the active regions evolve independently.
Multiple bad triples do not create a new global mechanism; they only create
more intervals.

The original use of this reduction was to prove raw mixed-step acyclicity.
That route is now disfavored. The current preferred use is:

- contract same-score pure-mid motion inside the active intervals
- reason on the induced macro graph on `CoreNormal` states

### 5. Only one unbounded core remains

The only genuinely unbounded case is the **pure-mid interval**:

- all positions use `T_mid`
- left and right boundaries are fixed values in `{0,1,2}`
- the interval remains `(2,0,2)`-free

Endpoint gadgets involving `P_0, P_1, P_{n-2}, P_{n-1}` are bounded-size and
should be handled separately once the pure-mid core is done.

## Best Cold-Start Leads

### Lead A: `oans4` / `ub_staircase_pure_mid_package.md`

Best current direct proof lead:

- [oans4.md](./docs/ub_coldstart_answers/oans4.md)
- [ub_staircase_pure_mid_package.md](./lean/docs/ub_staircase_pure_mid_package.md)

Claim: for the pure-mid core, every allowed score-preserving rewrite strictly
decreases the edge-word rank

```text
ρ = (N21, N01, N20, N02, -M)
```

or, in Lean-friendly `Nat` form,

```text
ρ_nat = (N21, N01, N20, N02, μ)
```

where the `Nuv` count certain adjacent edge-types, `M` is a signed position
sum, and `μ` is the equivalent `Nat`-valued last coordinate.

This is no longer just the strongest **candidate** proof of pure-mid interval
acyclicity. It is the current **working proof object** for the pure-mid core.

Important: this rank is for the **pure-mid core only**. It does not by itself
handle the post-core global assembly.

### Lead B: `cans3` / `cans4` reduction

Best current structural reduction:

- [cans3.md](./docs/ub_coldstart_answers/cans3.md)
- [cans4.md](./docs/ub_coldstart_answers/cans4.md)

Key theorem package:

- `F1`: firing a Phase 1 bad triple strictly decreases score
- `F2`: every score-preserving move occurs at distance at least 2 from all
  Phase 1 bad triples
- same-score dynamics are confined to active intervals

The `REDO` section of `cans4.md` usefully isolates the `rb = 2` pure-mid case
as the hardest structural regime for induction-style proofs. Even if the rank
route is preferred, this analysis remains valuable as a fallback decomposition.

### Lead C: `ans3` / `ans4` active-sub-ring DAG evidence

- [ans3/phase1_descent_analysis.md](./docs/ub_coldstart_answers/ans3/phase1_descent_analysis.md)
- [ans4/ANALYSIS.md](./docs/ub_coldstart_answers/ans4/ANALYSIS.md)

These provide strong computational support for:

- active sub-rings are DAGs for tested sizes
- pure-mid chains are acyclic for all tested boundary conditions
- local scalar/additive potentials are not the right tool

These are better viewed as support for the pure-mid theorem than as final proof
artifacts.

### Lead D: direct verifier support

- [ub_puremid_proof.md](./lean/docs/ub_puremid_proof.md)
- [staircase_puremid_verify.py](./probes/staircase_puremid_verify.py)
- [staircase_gadget_verify.py](./probes/staircase_gadget_verify.py)

These give:

- a complete case audit of the 13 legal pure-mid rewrites
- a direct statement of the pure-mid rank-drop proof
- computational confirmation that the pure-mid graphs are acyclic for all tested
  boundary pairs
- computational confirmation that the bounded gadget behaves like a finite
  interface problem, not a new unbounded mechanism

### Lead E: `oans5` macro route

Best current post-pure-mid redesign:

- [oans5.md](./docs/ub_coldstart_answers/oans5.md)

Key ideas:

- `CoreNormal` should be a relation-based cross-section, not a unique normal form
- `Normalize` should be treated as a relation, not a deterministic map
- the bridge from the actual same-score graph to the macro graph should be a
  cycle/SCC projection theorem, not a reachability quotient

This is currently the strongest post-pure-mid staircase design.

## Exact Theorem Targets

The staircase route now looks like the following theorem stack.

### Target 1: Phase 1 local facts

These should be proved directly from the CUP-2 tables.

```text
phase1_absent_legit:
  legitimate states have Phase1Score = 0

phase1_closed:
  Phase1Score = 0 is forward-invariant

phase1_noninc:
  every move satisfies Phase1Score(next) ≤ Phase1Score(curr)
```

### Target 2: Phase 1 descent

The actual Phase 1 descent theorem:

```text
phase1_descent:
  for every n ≥ 9 and every state with Phase1Score > 0,
  every infinite central-daemon execution eventually reaches a strictly smaller
  Phase1Score
```

Equivalent graph form:

```text
for every n ≥ 9 and every k > 0,
the same-score graph G_{n,k}^{=} is acyclic
```

### Target 3: Active interval reduction

This is the key reduction theorem:

```text
same-score runs freeze bad supports and reduce to independent active intervals
```

This should let `phase1_descent` reduce to interval acyclicity.

### Target 4: Pure-mid interval acyclicity

This is no longer just the "current main bottleneck theorem"; it is the theorem
whose proof should now be formalized directly.

Suggested statement:

```text
pure_mid_interval_acyclic:
  for every length m ≥ 1 and every boundary pair (a,b) ∈ {0,1,2}²,
  the score-preserving transition graph on (2,0,2)-free T_mid intervals is acyclic
```

This is the theorem most strongly supported by the current cold-start work.
The current plan should assume the `ρ_nat` proof route as the default.

### Target 5: CoreNormal / Normalize API

This is now the preferred next theorem target after the pure-mid core:

```text
normalization_exists_and_stays_in_same_fiber:
  for every same-score state x there exists y such that
  Normalize(x,y) and
  y lies in the same frozen-support / boundary fiber as x
```

This theorem turns the solved pure-mid core into a usable API for the macro route.

### Target 6: Macro cycle projection

This is now the main post-pure-mid bottleneck theorem:

```text
every nonempty same-score SCC projects to a macro SCC on CoreNormal states
```

Equivalent informal form:

```text
if the real same-score graph has a cycle at positive score,
then the macro graph on CoreNormal states has a cycle
```

### Deprecated target: bounded gadget lemma

The old bounded gadget / mixed-step theorem is no longer the preferred target.
It belonged to the failed raw mixed-step assembly route.

## What Is Proved vs What Is Only Checked

### Believed proved / directly provable from tables

- uncreatability of the Phase 1 bad triples
- absence of Phase 1 bad triples from legitimate states
- `Phase1Score` nonincrease
- firing a Phase 1 bad triple decreases the score
- score-preserving moves cannot touch the frozen radius-1 support of a bad triple
- exact enumeration of the 13 legal pure-mid rewrites
- local rank-drop formulas for the first four coordinates of the pure-mid rank

### Only computationally checked so far

- active interval DAG behavior for small sizes
- pure-mid interval acyclicity for tested lengths and all boundary pairs
- bounded endpoint gadget acyclicity for tested small mixed systems
- phase-by-phase staircase behavior beyond the local Phase 1 facts
- full agreement between the mathematical `ρ` proof sketch and all tested
  pure-mid transitions
- macro graph acyclicity on positive fibers for tested `n`
- nonuniqueness of normalization

### Explicitly not yet proved

- full `phase1_descent` for all `n ≥ 9`
- pure-mid interval acyclicity for arbitrary length in Lean
- normalization existence / same-fiber theorem
- macro cycle/SCC projection theorem
- any later staircase phases beyond Phase 1

## Rejected / Downgraded Routes

### 1. Current preferred `Φ_full / cphi_bridge` closure route

This route is no longer the preferred research direction.
Reason: the transport/global locality step remains the single global gap, and
the staircase route now has more concrete local structure.

### 2. Paper B1–B4 as the main Lean route

This remains disfavored as the main formalization route.
Reason: the project history already shows how easily it explodes into large
formal infrastructure, and the current staircase route is more structurally
targeted.

### 3. Simple additive local potentials

Repeatedly ruled out / strongly disfavored by cold-start analysis.
This includes:

- scalar local disagreement energies
- fixed-width additive local-window potentials
- simple privilege-count measures

These are not the current proof target.

### 4. Wrong-system batches

The following were exploratory but are not evidence for the actual system:

- [wrong_system/](./docs/ub_coldstart_answers/wrong_system)

They should not be cited for the exact CUP-2 proof.

## Recommended Immediate Next Step

Stop broad exploration.

The pure-mid core should continue to be formalized and used, but the next
theorem-construction target after it is now:

1. define `CoreNormal` precisely on full configurations
2. define `Normalize` as a relation
3. prove normalization existence inside a fixed same-score fiber
4. define the macro-step relation
5. attack the macro cycle/SCC projection theorem

This supersedes the old plan of proving a raw mixed-step gadget lemma.

## Working Verdict

The staircase route is now concrete enough to build, but the preferred build
path is:

- pure-mid theorem first
- macro route second

not:

- pure-mid theorem first
- raw mixed-step gadget theorem second

The Phase 1 predicate has stabilized, the pure-mid theorem is explicit, and the
best remaining design is the relational macro route from `oans5`.
