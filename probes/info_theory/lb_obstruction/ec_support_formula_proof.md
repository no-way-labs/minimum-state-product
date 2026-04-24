# BAF Conflict-State Support Formula

Date: April 6, 2026

This note upgrades the current EC-side bridge object `chi_conf` from an audited
pattern to a proof-ready theorem candidate.

## 1. Setup

Fix:

- `n >= 5`,
- a non-sweep `fc = 2` BAF mover word on `C_n`,
- with consecutive binary processors at `{0,1,2}`,
- and the simple state-sequence realization used in the EC package
  (`[0,1,0]` at every processor).

Let the two turnaround steps of the mover word be `t_1` and `t_2`.

Let

`ConfState`

denote the set of good-cycle states whose local triple at some processor lies in
an overlap context `M_p ∩ N_p`.

## 2. Canonical Theorem

### Theorem. Canonical support formula for `chi_conf`.

On the BAF family above,

`ConfState = {g_0, ..., g_{2n-1}} \ {g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`.

Equivalently:

- the only non-conflict states are the two turnaround states and their
  immediate successors,
- every other good-cycle state is a conflict state.

Hence

`|ConfState| = 2n - 4`.

This canonical theorem is now written in full in `ec_obstruction_theorem.md`.

## 3. Broader BAF Extension Candidate

The broader tested BAF-family statement is:

If a non-sweep `fc=2` BAF word has turnarounds `t_1, t_2`, then

`ConfState = {all good-cycle states except g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`.

This remains a theorem candidate, but it has now been audited on every tested
non-sweep `fc=2` BAF word through `n=9`.

A proof of this broader theorem should proceed in two arc-local pieces:

1. prove that on each directed arc from one turnaround to the other, every step
   after the immediate successor of the starting turnaround and before the
   ending turnaround contributes a conflict witness,
2. prove that exactly the four boundary steps
   `t_1, t_1+1, t_2, t_2+1`
   fail to do so.

## 4. Why this should be true

The palindromic EC argument already identifies the conflict mechanism:

- every processor strictly interior to a traversed arc contributes an overlap,
- the two turnarounds are the places where the bidirectional symmetry breaks,
- and the immediate successor steps are the boundary cases where the relevant
  local context has not yet stabilized into the palindromic matching form.

So the support formula is the dynamic version of the same statement:

- away from the two turnaround neighborhoods, the cycle sits in the palindromic
  regime and produces overlap,
- exactly at those four exceptional steps it does not.

On the canonical word this is visible step-by-step:

- at the first turnaround step and its successor, the matching context has not
  yet formed,
- throughout the interior of each directed arc, some interior processor sees one
  of the two overlapping contexts `(1,0,0)` or `(1,1,0)`,
- at the second turnaround step and its successor, the local matching again
  breaks.

The broader BAF theorem candidate says this description is actually
word-generic: only the two turnarounds and their immediate successors matter,
not the detailed placement of those turnarounds around the cycle.

## 5. Lemma Chain

The right proof breaks into four local lemmas.

It is convenient to index the conflict witnesses processor-by-processor.

For each interior processor `j in {1, ..., n-3}`, define the four candidate EC
steps

`A_j = {j, j+1, 2n-2-j, 2n-1-j}`.

The key claim is that these are exactly the good-cycle steps at which processor
`j` sees one of its two overlap contexts.

For the broader BAF extension, the same role is played by the two directed
arcs determined by the turnaround steps.

### Lemma 4.1. Away from the turnarounds, the BAF word is locally palindromic.

For any step `t` that is not one of

`t_1, t_1+1, t_2, t_2+1`,

the local mover/non-mover geometry around the relevant interior processor is the
same as in the standard palindromic EC argument:

- one occurrence is a clockwise non-mover view,
- one occurrence is a counter-clockwise mover view,
- and the local context matches exactly.

This is the positive direction: every non-exceptional step lies in
`ConfState`.

The witness can be chosen explicitly:

- if the mover at step `t` is strictly interior to the directed arc, then that
  mover processor witnesses the overlap at step `t`,
- if the mover at step `t` is the last processor before the ending turnaround,
  then the previous interior processor witnesses the overlap at step `t`.

More concretely, on a directed arc from one turnaround to the other:

- the first interior step contributes an overlap at the mover processor itself,
- the middle interior steps contribute both:
  - a mover overlap at the current processor,
  - and a non-mover overlap at the previous processor,
- the last interior step contributes an overlap at the previous processor.

So every step in the open arc, and every step whose predecessor lies in the
open arc, belongs to `ConfState`.

For the clockwise arc this gives exactly the steps `j` and `j+1`.
For the counter-clockwise arc it gives exactly the steps
`2n-2-j` and `2n-1-j`.

Hence processor `j` contributes precisely the step set `A_j`.

This is the prototype for the general BAF word:

- interior mover steps are witnessed by the mover itself,
- arc-terminal interior steps are witnessed by the immediately preceding
  interior processor.

### Lemma 4.2. At a turnaround step, no palindromic matching occurs.

At `t_1` and `t_2`, the walk changes direction. The local triple that would be
needed for the palindromic match is missing because one neighbor is at the
turnaround discontinuity.

So `g_{t_1}` and `g_{t_2}` are not in `ConfState`.

### Lemma 4.3. At the immediate successor of a turnaround, the matching context
has not yet formed.

At `t_1+1` and `t_2+1`, one of the two neighboring processors has not yet
returned to the state needed for the overlap context.

So `g_{t_1+1}` and `g_{t_2+1}` are not in `ConfState`.

### Lemma 4.4. No other exceptions exist.

Every step outside those four positions falls under Lemma 4.1.

Combining Lemmas 4.2–4.4 gives the exact support formula.

### Lemma 4.5. Union formula for `ConfState`.

The full conflict-state set is exactly

`ConfState = ⋃_{j=1}^{n-3} A_j`.

#### Proof sketch

By Lemma 4.1 every non-exceptional step lies in the conflict set of at least
one interior processor.

By Lemma 4.2 and Lemma 4.3, the four exceptional steps do not lie in the
conflict set of any processor.

So the union over interior processors is exact.

### Lemma 4.6. Simplification of the union.

One has

`⋃_{j=1}^{n-3} A_j = {1,2,...,n-2} ∪ {n+1,n+2,...,2n-2}`.

#### Proof

The first two pieces of `A_j` are `j` and `j+1`, whose union over
`j = 1, ..., n-3` is exactly `{1, ..., n-2}`.

The last two pieces are `2n-2-j` and `2n-1-j`, whose union over
`j = 1, ..., n-3` is exactly `{n+1, ..., 2n-2}`.

So the union formula follows. ∎

Combining Lemma 4.5 and Lemma 4.6 gives the desired support theorem.

### Broader BAF reduction

The canonical theorem is the model case. The broader theorem candidate reduces
to proving the following arc-local statement for an arbitrary BAF word:

> On each directed arc, every step after the immediate successor of the
> starting turnaround and before the ending turnaround lies in `ConfState`.

Once this is proved on both arcs, the broader support formula follows
immediately.

## 6. Why this is Lean-friendly

This statement is much better for formalization than the raw forbidden-mass
claim.

It talks only about:

- the mover word,
- local contexts,
- step indices,
- and four explicit exceptional positions.

There is no spectral language in the proof itself.

The additional audited fact is:

- `ec_conflict_geometry_probe.py` verifies the support formula on every tested
  non-sweep `fc=2` BAF word through `n=9`.

Audit summary:

- `n=5`: 5 non-sweep words, 0 failures
- `n=6`: 10 non-sweep words, 0 failures
- `n=7`: 7 non-sweep words, 0 failures
- `n=8`: 12 non-sweep words, 0 failures
- `n=9`: 9 non-sweep words, 0 failures

So the intended flow is:

1. prove the support formula symbolically,
2. derive `|ConfState| = 2n-4`,
3. then use the support description as the input to any later spectral or
   information-theoretic analysis.

## 7. What remains open

The canonical theorem is effectively closed.

The current gap is the broader BAF extension:

to close it, the next step is to write the arc-local lemma in terms of the
actual BAF step indexing and local context formulas already used in the
palindromic EC proof, then isolate the four boundary exceptions.
