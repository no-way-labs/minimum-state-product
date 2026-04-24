## Draft reviewer reply

Thank you, this is a helpful critique. We agree that the current packet does **not** yet prove the full lower bound, and we will revise the presentation so that this point is explicit and central.

Our intended claim is narrower:

1. we now have two explicit obstruction packages,
2. they appear to arise from two genuinely different mechanisms,
3. those mechanisms naturally live under different observables,
4. and this leads to a more plausible universal target, namely a **disjunctive witness theorem** rather than a one-scalar theorem.

### 1. On the absence of a universal lower-bound theorem

We agree with the reviewer that the bridge to a true lower bound is still open.

The revision will state this plainly. The present contribution is not “the lower bound is proved,” but rather:

- a shadow-side explicit-family obstruction theorem package,
- an EC-side explicit-family obstruction theorem package,
- and a sharpened structural proposal for the universal theorem one should actually try to prove.

We view this as progress in the *shape* of the lower-bound program. In particular, the revised packet no longer treats the explicit-family evidence as if it were already universal.

### 2. Why the program is now two-track

The main reason for the two-track reformulation is mathematical, not presentational.

On the shadow side, the natural observable is width-`n-2` forbidden interaction mass. That quantity cleanly detects the explicit sweep-shadow families and separates them from the same-`n` valid coarse-layer references in the tested range.

On the EC side, however, the naive overlap scalar is width-3 local. Consequently its width-`n-2` forbidden fraction is identically zero. So the EC mechanism is **not** naturally visible through the same forbidden-mass observable.

This is the key structural reason we now separate the program into:

- a **shadow track**, measured by forbidden high-order interaction mass, and
- an **EC track**, measured by overlap / confusability complexity.

So the two-track formulation is not an ad hoc weakening. It is a correction forced by the behavior of the observables themselves.

### 3. Why this is not just two unrelated tricks

We understand the concern that the current version could read as a case split between unlike objects. That is a fair concern, and we will sharpen the framing.

Our claim is not that we have two unrelated obstructions. Rather, the working hypothesis is that both are manifestations of one underlying local-information failure:

- on the shadow side, this appears as nonlocal dependence detectable by high-order forbidden interaction mass,
- on the EC side, this appears as local-view ambiguity or zero-error confusability.

The observables differ, but the proposed unifying principle is that **subthresholdity forces failure of local distinguishability**, and that failure can surface in more than one mathematical form.

We agree that this unification is not yet theorem-level in the current draft, and we will label it explicitly as the programmatic target.

### 4. What we believe is genuinely new here

We would emphasize three points.

#### (a) The shadow-side package is already nontrivial on its own

For the explicit 3-binary `{2,3}` sweep-shadow families through `n = 7`, the width-`n-2` forbidden fraction is uniformly bounded below by `71/504`, while the same-`n` valid coarse-layer reference values are much smaller. This gives a concrete same-`n` obstruction gap.

#### (b) The EC-side reformulation identifies the correct failure mode

The important conceptual step is not merely that `E_conf > 0` on tested families. It is that the EC mechanism does **not** belong to the same scalar framework as the shadow mechanism. The width-3 locality calculation makes that precise.

#### (c) The lower-bound target is now more realistic

The packet no longer insists on a universal theorem of the form “one witness, one observable.” Instead, it identifies a more plausible target:

> every subthreshold system yields either an EC witness or a shadow witness.

We think this is the right correction to the program.

### 5. What remains open

We will make the following limitations explicit in the revision.

The current work does **not** show:

- that every subthreshold system exhibits the shadow obstruction,
- that every subthreshold system exhibits the EC obstruction,
- or that one of the two must occur universally.

Those statements belong to the open bridge theorem.

So the present state is:

- explicit-family theorem packages on both tracks,
- some symbolic structure and some computational certification,
- but not yet the universal disjunctive theorem.

### 6. What we will change in the revision

In response to the review, we plan to revise the packet in three ways.

#### (i) Narrow the formal claims

We will separate clearly between:

- what is proved symbolically,
- what is computationally certified,
- and what is still conjectural.

#### (ii) State the universal target explicitly

We will write the intended endgame as a formal programmatic theorem target, rather than leaving it implicit:

> every subthreshold system yields either a positive EC-side witness or a positive shadow-side witness.

This will make the open bridge problem precise.

#### (iii) Strengthen the motivation for the two observables

We will foreground the locality argument showing why the EC side cannot be forced into the same forbidden-mass framework. This is the main conceptual reason for the revised architecture.

### 7. Bottom line

We agree with the reviewer that the universal lower-bound theorem is still missing.

Where we differ is in how to interpret that gap. Our view is that the present packet still contributes something substantive: it identifies that the obstruction program is likely **disjunctive**, and that the two principal obstruction mechanisms naturally require different observables.

We think that is not just a retreat from the original ambition. It is a better specification of the lower-bound problem itself.

Accordingly, in the revision we will present the work as:

- two explicit obstruction theorem packages,
- a proof-driven reason they do not collapse to one scalar observable,
- and a sharpened universal target, namely the EC-or-shadow disjunctive witness theorem.