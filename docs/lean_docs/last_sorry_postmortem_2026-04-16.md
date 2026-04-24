# Last Sorry Postmortem

Date: 2026-04-16

## Purpose

This note explains:

1. what work has actually been completed on the last `ConstLayerDAG` residue
2. what theorem-search routes were tried
3. why the work has kept stalling
4. what is now known with reasonable confidence
5. what the next sane step is

This is intentionally more candid than the running exploration notes. The goal
is to explain not just *what* happened, but *why progress has looked so jagged*
and why the current state is still one live `sorry` instead of zero.

## Current State

As of this note:

- the live theorem path is still down to one remaining `sorry` in
  `LeanMn/Convergence/ConstLayerDAG.lean`
- `lake build LeanMn.Convergence.ConstLayerDAG` passes
- `lake build LeanMn` passes
- the remaining residue is inside the strict non617 boundary-changing branch of
  `cphiBoundary_nodrop_non617_impossible`

So the repo is not broken in the ordinary sense. The problem is concentrated:
one final structural theorem is still missing.

## What Has Been Accomplished

There has been real progress. The work did not stay at the same point the whole
time.

### 1. Upper bound theorem boundary was fixed

The exported upper bound theorem was split into the actual two-regime form:

- `5 <= n <= 8`: explicit small witnesses
- `n >= 9`: CUP-2 route

That removed the false dependency on the broken small-`n` CUP-2 convergence
wrapper and made the public theorem boundary mathematically honest.

### 2. `ConstLayerDAG` proof debt was reduced from 7 `sorry`s to 1

The earlier bridge debt was not a single missing proof. It was a cluster of:

- local destination-cap lemmas
- branch-specific contradictions
- one final structural residue

Those local pieces were mostly closed. The only remaining debt is the final
structural theorem.

### 3. Several real Lean support layers now exist

The repo now has genuine support around the last residue, including:

- exact small-family scratch theorems for earlier strict buckets
- `P012ExactScratch`
- `P012SourceScratch`
- `P002ExceptionalScratch`

These are not fake proofs or external certificates. They are Lean files
checked by the kernel. The problem is not soundness. The problem is that the
last theorem boundary was not isolated early enough, so too much effort went
into helper layers before the final abstraction stabilized.

## What I Was Trying To Prove

The last residue is not "some random impossible branch." It is the final strict
non617 boundary-changing `CΦ` branch after the easier strict and nonnegative
families have already been peeled away.

In practical terms, the live residue eventually narrowed to the strict
`P1:(0,1,2)` branch on the destination side.

The intended endgame became:

1. isolate the exact destination family that still survives the live
   hypotheses
2. prove a destination-side cap there
3. use that cap to contradict `PhiFull` equality in the live branch

That is the right high-level plan. The issue was how it got formalized.

## What Went Wrong

There were several distinct failures. They are worth separating.

### Failure 1: I spent too long below the natural theorem boundary

This is the main failure.

Once the work reached the final residue, I should have switched fully to
"theorem boundary discovery" mode:

- what is the exact finite or parametric object?
- what is the smallest true theorem strong enough to close the branch?

Instead, too much time was spent proving local helper lemmas directly on raw
`Config`s. In Lean, that means dependent `Fin` arithmetic, explicit move-index
transport, and repeated `rw`/`omega` plumbing.

That created the appearance of steady motion, but a lot of that motion was
below the level where the final theorem actually lived.

Put bluntly:

- the math object was getting clearer
- the proof engineering was still aimed too low

That mismatch is the biggest reason the work kept turning into grind.

### Failure 2: several plausible theorem shapes were false

This was not just one hard proof. Multiple candidate theorem statements turned
out to be wrong.

Examples:

- generic strict `FutureFc` drop on the last branch was false
- some source-side provider statements in the `P012` path were false
- the earlier small-window exact route was too small and unstable as `n` grew

So a lot of time was spent not on "failing to finish a proof" but on
discovering that a proposed theorem was not the right theorem.

That is real theorem-search work, but it is expensive and it looks like churn
from the outside.

### Failure 3: the widened exact scratch overapproximated the real destination residue

The widened exact `P012` route originally left a destination-side exceptional
case that looked structurally worse than it really was.

Later probe work showed that the actual TP-bad closure of the exceptional
destination family is much smaller and cleaner than the overapproximation
suggested.

So part of the delay came from working with a technically valid but too-coarse
model of the residue.

### Failure 4: the full-exact ladder route was mathematically real, but not the right closing route

The full exact ladder

```text
012...101 -> 112...101 -> 122...101 -> 022...101 -> 002...101
```

is real and useful. It exists in the probe picture, and parts of it were
packaged in Lean.

But the naive argument I kept trying to force from it was wrong in spirit:

- the first rung drops actual Lean `cup2Fc` too much
- so transporting the needed `PhiFull` lower bound through that ladder was not
  the cheap contradiction it first appeared to be

So even though the ladder was genuine structure, it was not the theorem
boundary that would finish the proof quickly.

### Failure 5: I had to correct a metric mismatch

At one point, the probe work was using a frontier proxy that was not the same
as Lean's actual `cup2Fc`.

That did not invalidate all of the probe work, but it did invalidate some
interpretations of the exceptional-family behavior.

This has now been corrected. The current exceptional-family notes and probe use
actual Lean-style `cup2Fc` rather than the older proxy.

This correction was necessary, but it cost time and forced some reframing of
the route.

## The Routes That Were Tried

Here is the clean version of the route history.

### Route A: direct generic strict-drop contradiction

Idea:

- prove the final strict non617 branch forces a generic `PhiFull` drop

Result:

- too coarse
- fragmented quickly into special buckets
- not the right theorem boundary

### Route B: exact `P012` small-window scratch

Idea:

- use a fixed exact local signature around the `P1:(0,1,2)` family

Result:

- useful intermediate support
- but too small as a model of the full parametric family
- left a destination-side exception that looked worse than the actual closure

### Route C: source-side asymmetric scratch

Idea:

- use the asymmetry of the actual source closure to get a source cap

Result:

- this gave useful support facts
- but did not isolate the destination obstruction
- not sufficient to close the branch

### Route D: full-exact ladder transport

Idea:

- use the universal full-exact ladder to move from source to destination and
  carry the contradiction through

Result:

- mathematically interesting
- not the right contradiction route
- still too much proof plumbing relative to payoff

### Route E: exceptional destination family

Idea:

- stop treating the destination anomaly as a vague exception
- identify its exact TP-bad closure and prove a direct family cap there

Result:

- this is the first route that now looks genuinely right
- it has not finished yet
- but it is the sharpest current theorem boundary

## What Is Actually Known Now

The most important facts now are:

### 1. The exceptional destination family has an exact middle-strip language

Across `n = 9, 10, 11, 12`, the actual TP-bad closure of the exceptional
destination start has middle strips exactly of the form

```text
1^a 0^b 2^c
```

with:

- `a + b + c = n - 6`
- `c >= 1`

That is a real structural compression. It is no longer an amorphous family.

### 2. The family has a finite boundary layer

The same destination family has a finite six-boundary layer of size `36`.

So the actual state space seems to factor as:

- a finite boundary state
- plus a small parametric middle-strip automaton

That is exactly the kind of object that should be formalized abstractly rather
than through raw config proofs.

### 3. The actual Lean `cup2Fc` behavior seems to follow a small regime formula

Probe work now suggests that `cup2Fc` is determined by:

- a finite boundary budget
- plus a tiny regime constant depending on whether:
  - `a = 0, b = 0`
  - `a = 0, b > 0`
  - `a > 0, b = 0`
  - `a > 0, b > 0`

This is the right next theorem target.

### 4. `P002ExceptionalScratch` is now the correct work surface

This file now contains:

- the exact family predicate
- the canonical exceptional start witness
- boundary extraction lemmas
- middle-index helper lemmas
- finite boundary budget caps

That is a much better theorem surface than continuing to grind in
`ConstLayerDAG` directly.

## Why It Still Is Not Done

Because the final cap theorem has still not been stated and proved at the
correct abstraction level.

More precisely:

- I now know the right family
- I have most of the right support lemmas
- but I have not yet landed the regime-by-regime `cup2Fc` formula in Lean

That formula is the missing bridge between:

- the exact family structure
- and the actual contradiction needed by the last `ConstLayerDAG` residue

So the current failure is no longer "I don't know what to try."

The current failure is:

- I kept trying to prove the cap too directly on concrete sums
- instead of first proving the regime formula cleanly on the abstract family

That is a much narrower and more honest diagnosis.

## What Should Happen Next

The next pass should do exactly this:

1. stay in `P002ExceptionalScratch`
2. prove the regime formulas for actual Lean `cup2Fc`
3. derive the family cap `cup2Fc <= 5`
4. bridge that back into the last strict `P1:(0,1,2)` destination case
5. use it to close the last `sorry` in `ConstLayerDAG`

What should *not* happen next:

- more direct config-level grind in `ConstLayerDAG`
- more attempts to use the full-exact ladder as the main contradiction route
- more helper lemmas below the family theorem boundary unless they are directly
  required by the regime formula

## Bottom Line

The reason this is still not solved is not that nothing has been learned.

It is that:

- the real theorem boundary emerged late
- several plausible theorem shapes were false
- too much Lean effort was spent below the natural abstraction level

The work is now much closer to the correct abstraction:

- exact family identified
- finite boundary layer identified
- corrected `cup2Fc` behavior identified
- dedicated scratch file in place

So the situation is:

- earlier: too many possible routes, not enough compression
- now: one credible route, but the central family-cap theorem still not landed

That is why it still feels like grind, and why that grind needs to stop being
config-level and start being theorem-level.
