# Post-Feedback Course

Date: April 6, 2026

This note synthesizes the two review responses:

- `review_packet_feedback_1.md`
- `review_packet_feedback_2.md`

into a concrete next-step course for the obstruction branch.

## 1. Main message from the feedback

Both reviewers agree on the critical point:

> the current result is real, but it is still an explicit-family obstruction,
> not yet a lower bound.

So the branch must now optimize around a **bridge theorem**.

The branch should not spend more time polishing explicit-family statements unless
that work supports one of the following:

1. a universal spectral obstruction,
2. a universal witness-extraction theorem,
3. or a reduction theorem linking arbitrary subthreshold systems to the current
   explicit obstruction class.

## 2. Two serious programs

The feedback identifies two serious forward programs.

### Program A. Pure spectral transport

This is the more ambitious route suggested in
`review_packet_feedback_1.md`.

The target is a purely spectral lower-bound argument with three pieces:

1. **Target signature lemma**
   Identify a scalar whose forbidden fraction is large on the target object.

2. **Spectral transport lemma**
   Show a local update can move only a controlled amount of forbidden mass.

3. **Iteration / contradiction**
   Use convergence to force forbidden mass transport beyond what subthreshold
   systems can support.

This is a beautiful route if it works, but it is also the highest-risk route.
The main risk is that the transport bound is quantitatively too weak.

### Program B. Universal witness extraction

This is the more conservative and currently more plausible route from
`review_packet_feedback_2.md`.

The target is:

1. define a canonical obstruction witness `Phi_S` for an arbitrary subthreshold
   system,
2. show the current explicit shadow indicators are special cases or model cases
   of `Phi_S`,
3. prove `Phi_S` carries a forbidden-mass floor,
4. and only then compare with the valid side.

This route keeps the current explicit-family work relevant as model evidence,
instead of discarding it.

### Correction: likely a two-track witness program

The lower-bound architecture has two main obstruction types:

1. **entry conflict (EC)**
2. **shadow / bad-cycle obstruction**

So Program B should not be read too narrowly as “one scalar to rule them all.”
The more realistic target is:

- either a single canonical witness `Phi_S`,
- or a disjunctive theorem:
  every subthreshold system yields either
  an EC witness or a shadow witness with positive obstruction mass.

Further correction from the first EC probe:

- the shadow side naturally couples to the current forbidden-mass observable,
- the naive EC-side overlap witnesses do not: they are width-3 local and hence
  have zero width-`n-2` forbidden mass.

So the realistic target is now even more likely to be:

- a **two-track witness program with different quantitative observables**,
  not one scalar measured in one common way.

## 3. Recommended branch priority

The obstruction branch should prioritize:

### Priority 1. Universal witness extraction

This is the best fit to the current state of the branch.

Reason:

- we already have a strong explicit-family obstruction,
- we already have a symbolic core for that family,
- and the next natural question is exactly:
  “what is the canonical witness of arbitrary subthresholdity?”

### Priority 2. Spectral transport as a kill-or-keep test

The pure transport program is important, but should be run first as a **fast
feasibility test**, not as the whole branch.

Reason:

- if a single local update can move too much forbidden mass, the entire pure
  spectral transport route probably dies,
- and we should discover that early.

So the right use of Program A is:

- run a small number of sharply targeted computations to decide whether Piece 2
  has any realistic bite,
- then either continue or shelve it.

## 4. Concrete branch split

### Track W. Witness extraction (main line)

Goal:

Define a canonical obstruction witness program for arbitrary subthreshold
systems.

Immediate tasks:

1. Identify candidate witness objects from arbitrary subthreshold systems:
   - forced kernel indicator,
   - peel depth,
   - shadow indicator,
   - EC overlap indicator,
   - EC overlap count / confusability-edge count,
   - escape obstruction scalar,
   - or a new witness extracted from forced mover-entry dynamics.
2. Decide what makes a witness canonical:
   - invariant under relabeling,
   - stable under normalization,
   - intrinsic to the system, not to a chosen sweep family.
3. Test whether the explicit shadow indicators can be recovered as special cases
   of the candidate witness.

Success criterion:

The branch produces a theorem candidate of one of the forms:

> every subthreshold system canonically yields `Phi_S`,
> and `ForbidFrac_{n-2}(Phi_S) >= epsilon`.

or

> every subthreshold system yields either an EC witness or a shadow witness
> with obstruction mass at least `epsilon`.

This now should be read more carefully as:

> every subthreshold system yields either
> - an EC witness with positive EC-side complexity,
> - or a shadow witness with positive forbidden mass.

### Track T. Spectral transport feasibility (sidecar)

Goal:

Determine early whether the pure spectral transport route is viable.

Immediate tasks:

1. Compute the forbidden-mass transport of a single local update on pure ANOVA
   test functions.
2. Measure how much forbidden energy a local update can move across the
   width-`n-2` boundary in small systems.
3. Decide whether the bound is small enough to support an iteration argument.

Success criterion:

- either a promising small transport bound emerges,
- or we learn quickly that the route is quantitatively hopeless.

### Immediate warning from target-signature data

The good-cycle indicator `chi_good` does **not** currently look like the right
target signature.

Current data:

- valid witnesses:
  - `CUP-2(n=5..9)`: forbidden fractions roughly `0.128 .. 0.170`
  - `Sol3(n=4..9)`: roughly `0.130 .. 0.204`
- explicit obstruction families:
  - shadow-side canonical sweeps: roughly `0.143 .. 0.153`
  - canonical BAF EC family: roughly `0.108 .. 0.136`

So `chi_good` lives on essentially the same spectral scale on both valid and
explicitly obstructed systems. This strongly suggests that Piece 1 of the pure
spectral transport program should **not** use `chi_good` directly.

## 5. What to stop doing

From here, the branch should stop:

1. broadening explicit-family tables unless needed for witness extraction,
2. beautifying exact decoder theorems with no obstruction target,
3. extending class-value data further unless it changes the witness picture.

The current explicit-family package is already strong enough as motivating
evidence.

## 6. Immediate next theorem ladder

### Step 1. Canonical witness definition

Find the best candidate `Phi_S` for arbitrary subthreshold systems.

### Step 2. Explicit-family identification

Show the current shadow-floor obstruction is a special case of `Phi_S`, not a
disconnected example.

### Step 3. Floor theorem on explicit broader classes

Keep the current explicit-family floor theorem as evidence and a testbed.

### Step 4. Universalization

Prove every subthreshold system produces enough of the obstruction mechanism for
the floor theorem to bite.

## 7. Decision rule

When choosing the next task:

- if it helps define or universalize `Phi_S`, do it;
- if it tests whether pure transport is viable, do it quickly;
- otherwise, shelve it.

## 8. Bottom Line

The branch should now pursue:

- **main line**: universal witness extraction,
- **sidecar**: quick feasibility test for pure spectral transport,
- while keeping the current explicit shadow-floor theorem as a model case, not
  as the endpoint.

And the universal witness extraction itself should now be treated as
two-track:

- shadow witness track,
- EC witness track,

with the expectation that the two tracks may require different observables.
