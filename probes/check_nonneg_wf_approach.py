#!/usr/bin/env python3
"""
Explore: can we prove badStep WF via nonneg/neg decomposition alone?

We have:
  cup2BadStepNonneg_wf: WF via (n-fc, psi) lex measure
  cup2BadStepNeg_wf: WF via InvImage on fc

Can we use wf_of_copy_segment_wf with:
  copy = nonneg  (fc(c') >= fc(c))
  anom = neg     (fc(c') < fc(c))

Segment: exists d, chain_nonneg(d, c) ∧ neg(c', d)
Need: some measure strictly decreasing from c to c'

Along nonneg chain from d to c: fc non-decreasing, so fc(d) <= fc(c).
Also (n-fc(d), psi(d)) > (n-fc(c), psi(c)) [strictly by WF].
So n-fc(d) >= n-fc(c), meaning fc(d) <= fc(c).

Neg step d -> c': fc(c') < fc(d) <= fc(c).

So fc(c') < fc(c)! The segment strictly decreases fc!

Wait, that's not right. The chain goes from d to c via ReflTransGen, meaning
d is reached from c (in the WF direction). Actually no...

In wf_of_copy_segment_wf:
  ReflTransGen copy z x means z is reachable from x via copy steps
  So x ->copy ... ->copy z ->anom y

So the chain is: x ->copy z ->anom y.
fc(x) <= fc(z) [nonneg chain, fc non-decreasing along the chain]
fc(y) < fc(z) [neg step]

So fc(y) < fc(z) but fc(z) >= fc(x), so fc(y) might be >= fc(x).

Hmm. But wait - the WF direction is reversed from "reaches".
In WF terminology, copy y x means y is "smaller" than x.
For nonneg: cup2BadStepNonneg c' c means c' is "smaller" (c' is the outcome of one step from c).
So ReflTransGen copy z x means x -> ... -> z in the step direction.
fc is NON-DECREASING in the step direction for nonneg: fc(c') >= fc(c).
So fc(x) <= ... <= fc(z).
Then anom y z: fc(y) < fc(z).
Need: measure of y < measure of x.

We know: fc(y) < fc(z) >= fc(x). So fc(y) MIGHT be >= fc(x).

BUT: we can use FutureFc! If we restrict to constFuture...
No, FutureFc is noncomputable.

What about using (fc, something) as a measure for the segment?
Actually, nonneg steps can increase fc, and neg steps decrease it.
The (n-fc, psi) measure works for nonneg but goes the wrong way for neg.

OK so the direct nonneg/neg decomposition doesn't work because nonneg
chains can increase fc arbitrarily before a neg step drops it.

What about the measure n (total ring size, trivially constant) minus
something? Or some other global measure?

Actually, let me think about the lex measure (n - fc, psi):
- For nonneg steps: strictly decreases (proved in CopyDAG.lean)
- For neg steps: n - fc INCREASES (fc drops), so the lex measure increases

So we can't combine them with a single measure.

BUT: what if we use the MINIMUM fc reached so far as a ratchet?
Actually, that's what FutureFc does, but in the max direction.

Let me think about it differently. Is there a simple GLOBAL measure that
works for ALL bad steps (both nonneg and neg)?

The convergence MEMORY.md says the proof uses:
  Psi = FutureFc * (R+1) + rank
  where R = 7n-30

This is a two-level measure where FutureFc is non-increasing on ALL steps,
and rank decreases within constant FutureFc.

The problem is FutureFc is noncomputable. Can we replace it with something
computable?

What about using fc itself as the top-level measure?
- Nonneg steps have fc >= fc_prev, so n-fc doesn't increase -> good
- Neg steps have fc < fc_prev, so n-fc increases -> bad

That doesn't work.

What if we use max(fc reachable via nonneg steps) instead of FutureFc?
That's still noncomputable (needs ReflTransGen).

OK, what about a completely different approach? Can we just prove
badStep is WF directly without the FutureFc decomposition?

The two things we have:
1. cup2BadStepNonneg_wf: nonneg steps are WF
2. cup2BadStepNeg_wf: neg steps are WF

These are proved independently. The question is: can nonneg ∨ neg be WF?

In general, WF(R1) and WF(R2) does NOT imply WF(R1 ∨ R2).
We need some compatibility condition.

One sufficient condition: R1 and R2 decrease the same well-order.
But they don't: nonneg decreases (n-fc, psi), neg decreases fc.

Another condition: R1 is a subrelation of R2's transitive closure, or vice versa.
Not true either.

What about: define a COMBINED measure that handles both?
For nonneg: the measure (n-fc, psi) strictly decreases.
For neg: fc strictly decreases, i.e., (n-fc) strictly increases.

So between consecutive neg steps, fc drops. Between neg steps,
nonneg steps can pump fc back up. But the nonneg pumping is bounded
by the WF of (n-fc, psi).

Key insight: between two consecutive neg steps, there's a finite
chain of nonneg steps (WF). And across the neg step, fc drops.
So the "fc just before a neg step" is strictly decreasing!

Wait, that's exactly what FutureFc captures. But we can prove it
more directly:

Use wf_of_copy_segment_wf with:
  copy = nonneg (WF, proved)
  anom = neg

Segment: x ->nonneg ... ->nonneg z ->neg y
We need: WF of the segment relation.

Measure for segment: fc(y) vs fc(x)?
fc(y) < fc(z) and fc(z) >= fc(x) ... so fc(y) < fc(z) but not necessarily < fc(x).

Measure for segment: (n - fc(y), psi(y)) vs (n - fc(x), psi(x))?
n - fc(y) > n - fc(z) ... but n - fc(z) <= n - fc(x), so n - fc(y) might be > n - fc(x). Good for lex!
Actually wait: n-fc(y) > n-fc(z) >= n-fc(x)? No, n-fc(z) <= n-fc(x) because fc(z) >= fc(x).
So n-fc(y) > n-fc(z) and n-fc(z) <= n-fc(x).
So n-fc(y) > n-fc(z) but compared to n-fc(x), could go either way.

Example: fc(x)=3, nonneg chain to fc(z)=5, neg step fc(y)=4.
n-fc(y) = n-4, n-fc(x) = n-3. So n-fc(y) > n-fc(x). The first component INCREASED.

Hmm. So the segment measure (n-fc, psi) doesn't decrease.

Let me try: measure = fc.
fc(y) < fc(z) >= fc(x). With example fc(x)=3, fc(z)=5, fc(y)=4: fc(y)=4 > fc(x)=3.
So fc doesn't decrease across segments either.

What about: can we bound the total number of neg steps?
Each neg step drops fc by at least 1 (actually by at least 2 since fc has the same parity).
The total fc available is bounded by n.
So the total number of neg steps is at most n/2.
But between neg steps, nonneg steps can pump fc back up!

However, each nonneg step is from the WF relation, so there are finitely many of them.
And there are finitely many neg steps (bounded by... well, not directly).

Actually, the problem is that neg steps can be interleaved with nonneg steps that
pump fc back up. The total could be unbounded.

Unless... the nonneg measure (n-fc, psi) is GLOBALLY bounded and strictly decreasing
on nonneg steps. So the total number of nonneg steps ever is bounded by the initial
(n-fc, psi) value. And between neg steps, the nonneg pumping increases fc, which
increases the nonneg measure used so far, limiting future nonneg steps.

Wait, the key point: EVERY nonneg step decreases (n-fc, psi). This is a GLOBAL
budget. The total number of nonneg steps is bounded by the initial value of (n-fc, psi).
And every neg step decreases fc. But it can "restore budget" for future nonneg steps
by increasing n-fc.

So we'd need to track the total budget carefully. This seems like a ramsey-type
argument. The product of the two measures?

Actually, this is a classic problem in well-founded orderings. If we have two WF
relations R1 and R2, and R1 \cup R2, we need to show it's WF. One way:

Use the product ordering: (measure1, measure2) with lex.
If R1 decreases measure1 and doesn't increase measure2, and R2 decreases measure2,
then R1 \cup R2 decreases (measure1, measure2) lexicographically.

For us:
- Nonneg: decreases (n-fc, psi). What happens to fc? fc increases or stays same.
- Neg: decreases fc (increases n-fc).

Measure1 = fc (for neg steps)
Measure2 = (n-fc, psi) (for nonneg steps)

But neg steps INCREASE fc... wait, neg means fc(c') < fc(c), so fc DECREASES in
the step direction. And nonneg means fc(c') >= fc(c), so fc non-decreases.

So:
- Nonneg steps: fc non-decreases, (n-fc, psi) strictly decreases
- Neg steps: fc strictly decreases, (n-fc, psi) ??? could go either way

For lex (fc_desc, (n-fc, psi)):
  where fc_desc = fc (ordered descending)

Nonneg: fc_desc non-increases (fc goes up), second component strictly decreases -> lex decreases!
Neg: fc_desc strictly decreases -> lex decreases!

WAIT. This might work!

Let me restate: define a lex measure (n - fc, something) ... no.

Let me be precise. Define:
  mu(c) = (fc(c), psi(c))  with lex ordering: (a1,a2) < (b1,b2) iff a1 > b1, or a1 = b1 and a2 < b2.

Wait, I need to be careful about direction.

In WF ordering: c' is "smaller" than c if there's a bad step from c to c'.

For nonneg step c -> c': fc(c') >= fc(c), and (n-fc(c'), psi(c')) < (n-fc(c), psi(c)) lex.
For neg step c -> c': fc(c') < fc(c).

I want a single measure mu such that mu(c') < mu(c) for BOTH cases.

Try mu(c) = (fc(c), n * n - psi(c)) where the first component is compared DESCENDING
and the second ascending. That is:

mu(c) < mu(d)  iff  fc(c) > fc(d)  OR  (fc(c) = fc(d) AND psi(c) > psi(d))

Hmm, this doesn't work for nonneg steps where fc increases.

OK let me think again.

For nonneg: (n - fc(c'), psi(c')) < (n - fc(c), psi(c)) lex-Nat.
  This means: either n-fc(c') < n-fc(c) [i.e. fc(c') > fc(c)],
  or n-fc(c') = n-fc(c) [fc same] and psi(c') < psi(c).

For neg: fc(c') < fc(c), i.e., n-fc(c') > n-fc(c).

So for nonneg, n-fc either decreases or stays same (with psi decreasing).
For neg, n-fc strictly increases.

These go in OPPOSITE directions for n-fc! So no single lex on (n-fc, psi) works.

But what about: mu(c) = (fc(c) + (n - fc(c)) * K + psi(c)) for some large K?
Or maybe a more creative combination.

Actually, what about the sum: mu(c) = (n - fc(c)) * M + psi(c) where M is
large enough? For nonneg: this strictly decreases (proved). For neg:
n-fc increases by at least 1 (actually 2, since fc parity), so mu increases
by at least 2M. But psi could decrease by at most... what's the max psi?

From MEMORY: psi = sum of psi terms. The nonneg measure is lex (n-fc, psi),
so within a fixed fc, psi strictly decreases. But across fc changes, psi could
change arbitrarily.

Hmm, this approach won't work if psi can decrease enough to compensate.

Let me look at this from a totally different angle. Instead of trying to find
a single measure, can we restructure the proof to avoid proving
cup2BadConstFutureStep_wf altogether?

The REAL theorem we need is: WellFounded (badStep ...).

Currently:
  badStep = constFuture ∨ dropFuture
  constFuture is WF (NEEDS AXIOM)
  segments of constFuture terminated by dropFuture are WF
  combined via wf_of_copy_segment_wf

Alternative:
  badStep = nonneg ∨ neg
  nonneg is WF (PROVED)
  segments of nonneg terminated by neg are WF (NEED TO PROVE)
  combined via wf_of_copy_segment_wf

For the segment WF: x ->nonneg ... ->nonneg z ->neg y
Need: some measure m(y) < m(x).

We know:
  (n-fc(z), psi(z)) <= (n-fc(x), psi(x)) [since z reached from x via nonneg chain]
  fc(y) < fc(z) [neg step]

So n-fc(y) > n-fc(z) and (n-fc(z), psi(z)) <= (n-fc(x), psi(x)).
  n-fc(z) <= n-fc(x)  =>  fc(z) >= fc(x)  =>  fc(y) < fc(z) but fc(y) vs fc(x) unknown.

BUT: we also know (n-fc(z), psi(z)) < (n-fc(x), psi(x)) only if the chain is non-empty.
If the chain is empty (z = x), then fc(y) < fc(x). Great!
If the chain is non-empty, fc(z) >= fc(x) but could be much larger.

So the segment measure doesn't obviously decrease.

But wait: the (n-fc, psi) measure for NONNEG steps is already a combined single value.
Let me call it nonneg_rank(c) = (n - fc(c)) * PSIMAX + psi(c), so it's a single Nat.
nonneg_rank strictly decreases on every nonneg step.

For the segment: x ->nonneg^* z ->neg y
  nonneg_rank(z) <= nonneg_rank(x) [chain of nonneg steps]
  neg step: fc drops, so n-fc goes up, so nonneg_rank could go up or down.

What about: segment measure = nonneg_rank?
  nonneg_rank(y) vs nonneg_rank(x):
  = (n - fc(y)) * PSIMAX + psi(y) vs (n - fc(x)) * PSIMAX + psi(x)
  n-fc(y) = n - fc(y), n-fc(x) = n - fc(x).
  We know fc(y) < fc(z) >= fc(x).
  If fc(y) >= fc(x): nonneg_rank(y) >= (n-fc(y))*PSIMAX >= (n-fc(x))*PSIMAX > nonneg_rank(x)
  Wait, n-fc(y) >= n-fc(x) means nonneg_rank(y) >= n-fc(x)*PSIMAX which could be > nonneg_rank(x).
  So nonneg_rank doesn't decrease.

OK I'm going in circles. Let me think about what DOES work.

The classical result: if a relation R can be decomposed as R = R1 ∪ R2 where
R1 is WF and R2 is WF and R2;R1* ⊆ R1* (R2 followed by R1 chain embeds into R1 chain),
then R is WF.

We don't have that condition here.

Another approach: Dickson's Lemma style. Use a pair of measures.
Define mu(c) = (nonneg_rank(c), fc(c)) with the product ordering (NOT lex).
Product ordering: (a,b) < (c,d) iff a ≤ c and b ≤ d and (a,b) ≠ (c,d).
This is WF by Dickson's Lemma.

For nonneg step: nonneg_rank decreases, fc non-decreases -> product DOESN'T decrease.
For neg step: fc decreases, nonneg_rank ??? -> can't say.

Product ordering doesn't help because nonneg_rank and fc move in opposite directions.

I think the fundamental issue is that the system CAN oscillate:
nonneg steps increase fc (and decrease nonneg_rank), then neg steps decrease fc.
The total is bounded but proving it requires a global argument (FutureFc).

Maybe the only way forward is to make FutureFc computable (by implementing
decidable ReflTransGen for Fintype), then doing the proof for specific n by
native_decide, plus an n-independence argument.

OR: find a completely different measure that works for all steps simultaneously.

Actually, wait. Let me reconsider. The existing CopyDAG.lean proves that
nonneg_rank = cup2NonnegMeasure strictly decreases on all nonneg steps. This
measure encodes (n - fc, psi) as a single natural number.

What if there's a DIFFERENT measure that strictly decreases on ALL bad steps
(both nonneg and neg)? Let me check computationally.
"""

print("This is an analysis script, not meant to be run.")
print("The conclusion: need a different approach to avoid the false axiom.")
