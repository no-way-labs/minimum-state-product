# Consecutive-Binary Shadow Orbit v2

We keep the corrected setup:

- `gc = (C_0 --p_0--> C_1 --p_1--> ... --p_{L-1}--> C_0)` is a good cycle.
- `P_i, P_{i+1}, P_{i+2}` are binary.
- `F` flips the two outer binary processors `b1=i`, `b2=i+2`.
- `S_0 := F(C_0)`.
- The shadow is **not** defined by `S_k = F(C_k)`. Instead we choose privileged
  processors `q_k` in the actual system and set
  `S_{k+1} := move(S_k, q_k)`.

The right question is therefore not "does `F(C_k)` itself form a cycle?",
but:

> Can one choose privileged processors `q_k` so that the orbit from `S_0`
> stays outside the good cycle forever?

If yes, finiteness gives a bad cycle, hence a `ShadowTrap`.

This note makes two points.

1. The corrected orbit-based construction only needs an **eventual** bad cycle,
   not a first return to `S_0` and not period `L`.
2. For the consecutive-binary outer-pair flip, the blueprint proof does **not**
   currently establish the needed badness/escape invariant. The exact gap is
   identified below.

## 1. What Is Actually Sufficient

Let `Conf` be the finite directed graph of configurations, with an edge
`X -> Y` when `Y = move(X,q)` for some privileged processor `q` in `X`.

Call a configuration *bad* if it is not on the good cycle `gc`.

### Proposition 1 (Infinite Bad Orbit Suffices)

Assume there is a sequence

`S_0, S_1, S_2, ...`

such that for every `k`:

1. `S_k` is bad;
2. some privileged processor `q_k` is chosen in `S_k`;
3. `S_{k+1} = move(S_k, q_k)`.

Then some tail of this orbit is a `ShadowTrap`.

#### Proof

Because `Conf` is finite, some configuration repeats: `S_r = S_s` for some
`0 <= r < s`. Choose `s` minimal for this `r`. Then:

- `S_r, ..., S_{s-1}` is nonempty;
- all these configurations are bad, hence disjoint from `gc`;
- by construction, each step `S_t -> S_{t+1}` (`r <= t < s-1`) is a legal
  privileged move, and `S_{s-1} -> S_s = S_r` is also legal;
- minimality of `s` implies `S_r, ..., S_{s-1}` are pairwise distinct.

So the list `S_r, ..., S_{s-1}` satisfies exactly the Lean `ShadowTrap`
requirements. ∎

### Consequence

This answers **Q1** already:

- We do **not** need to prove that the orbit returns to `S_0`.
- We do **not** need to prove that its period is `L`.
- We only need to produce an infinite orbit that never hits the good cycle.

So the load-bearing lemma is:

> **Escape Lemma.** Starting from `S_0 = F(C_0)`, one can choose privileged
> moves forever while staying outside `gc`.

Everything else follows from Proposition 1.

## 2. The Only Automatic Local Fact

Let

`W := {i-1, i, i+1, i+2, i+3}`.

These are exactly the processors whose local radius-1 contexts can see one of
the two flipped coordinates.

### Lemma 2 (Far Processors Commute With `F`)

If `X = F(C_t)` for some good configuration `C_t` and `q notin W`, then the
local triple of `q` is the same in `X` and in `C_t`. Hence:

- `q` is privileged in `X` iff `q` is privileged in `C_t`;
- `move(X,q) = F(move(C_t,q))`.

In particular, if the good mover `p_t` lies outside `W`, then

`move(F(C_t), p_t) = F(C_{t+1})`.

#### Proof

`F` changes only the coordinates `i` and `i+2`. If `q notin W`, then neither
`q` nor its two neighbors is one of those coordinates, so the entire local
triple at `q` is unchanged. The transition rule at `q` therefore gives the
same output in `X` and in `C_t`, and only coordinate `q` changes in both
moves. ∎

This is the only unconditional part of the mover-entry idea.

## 3. Why The Blueprint Does Not Yet Adapt

The non-consecutive blueprint used a stronger invariant: the shadow configs
were described explicitly in terms of the good cycle, so one could track which
good-cycle mover entry was being replayed.

After the correction, we no longer have such an invariant.

The previous attempt silently used

`S_k = F(C_k)`,

but this is exactly what was corrected away. Once that identity is removed,
the proof obligations change qualitatively.

### 3A. Answer to A: Does Mover-Entry Selection Work?

Only partially.

If the current shadow config really has the form `F(C_t)`, then:

- for `q notin W`, Lemma 2 gives an automatic mover-entry match;
- for `q in W`, one needs a separate local context-matching lemma.

Concretely, the five difficult positions are:

1. `q = i` or `q = i+2`:
   the shadow mover sees the endpoint binary with its own value flipped.
   To replay the good cycle, one needs an immediate-repeat type lemma.

2. `q = i+1`:
   the shadow mover sees the doubly-flipped triple
   `(1-C_t[i], C_t[i+1], 1-C_t[i+2])`.
   This is not the good-step mover triple at time `t`; it must be shown to
   occur somewhere else as a mover triple with the correct output.

3. `q = i-1` or `q = i+3`:
   the shadow mover sees a singly-altered triple because one neighbor was
   flipped by `F`.
   Again this is not automatic from the good step `t`.

So even on the restricted family `F(C_t)`, mover-entry routing is only
automatic outside `W`.

But the real problem is worse:

> After the first non-commuting step, we are no longer entitled to write the
> current shadow config as `F(C_t)` for any `t`.

At that point the above five-case analysis no longer even applies, because it
was a case analysis for configs of the special form `F(C_t)`.

Therefore the mover-entry blueprint is **not** yet a global inductive rule.

### 3B. Answer to B: Can We Prove Disjointness?

Not from the stated hypotheses.

At time `0`, disjointness is exactly:

`F(C_0) notin gc`.

Equivalently:

> there is no pair of good-cycle configurations differing only at the two outer
> binary positions `{i, i+2}`.

This is a Hamming-2 statement.

Now:

- **H-1 uniqueness does not apply.**
  The start state is Hamming distance `2` from `C_0`, not `1`.
  Moreover the known H-1 arguments require additional hypotheses such as
  `fc(p)=m_p`, gcd conditions, or no-consecutive-fire structure, none of which
  are present in the current setup.

- A putative **H-2 uniqueness** lemma would settle only the **start state**
  `S_0`.
  It would say `F(C_t) notin gc` for configs of the special form `F(C_t)`.
  But later shadow states `S_k` are not known to be of that form.

So even a perfect Hamming-2 lemma on the `F`-image set would not prove full
disjointness of the corrected orbit.

The only genuinely sufficient replacement would be a **dynamic badness
invariant**, for example:

- every reached shadow config has at least two privileged processors, or
- every chosen shadow successor stays outside `gc`.

That is exactly the missing escape lemma.

### 3C. Answer to C: Does The Orbit Close After `L` Steps?

No such conclusion follows from the present data.

The claim "the shadow closes after exactly `L` steps" requires a much stronger
structure:

1. every shadow step is labeled by a good-cycle mover occurrence;
2. different shadow steps use different labels;
3. after `L` steps all labels have been used once.

Only then can one argue that each processor has fired the same total number of
times as on the good cycle, so the perturbation returns to its start.

In the corrected consecutive-binary setting, none of these three points has
been proved:

- mover-entry routing is unresolved in the five-site window;
- after leaving the `F(C_t)` family, there is no occurrence label at all;
- the current setup does not even assume that the `L` good mover occurrences
  are pairwise distinguishable by their local contexts.

Thus the only unconditional closure statement is the weak one from
Proposition 1:

- if you can keep the orbit bad forever, then some periodic bad tail exists.

Its period can be anything; it need not be `L`.

### 3D. Answer to D: Where Can Mover-Entry Selection Fail?

There are three separate failure modes.

1. **Local match failure.**
   A privileged processor in the current shadow config may see a local triple
   that never occurs as a mover triple on the good cycle.

2. **Good-successor failure.**
   A privileged processor may match a good mover entry, but firing it may land
   in `gc`. Then the disjointness invariant is lost.

3. **Invariant failure.**
   After a non-commuting step, the current shadow config is no longer known to
   be `F(C_t)` for any `t`, so the entire window-based comparison with the good
   cycle loses its anchor.

The previous draft identified (1) inside the five-site window. The corrected
orbit reveals that (3) is the more serious global obstruction.

## 4. Answers to Q1-Q3

### Q1 (Orbit closes)

What is true:

- finite state space + liveness imply that any infinite chosen orbit is
  eventually periodic.

What is **not** proved:

- first return to `S_0`;
- exact period `L`;
- even existence of an infinite bad orbit.

For the shadow argument, only the last item matters.

### Q2 (Disjoint from the good cycle)

This is the real bottleneck.

To get a `ShadowTrap`, it is enough to prove:

> from every reached bad shadow config, there exists a privileged move to
> another bad shadow config.

That is stronger than a one-time Hamming-2 statement at `S_0`, and it is the
part the current blueprint does not supply.

### Q3 (Distinct)

Once an infinite bad orbit is available, distinctness is automatic:

- take the first repeated bad configuration;
- the segment between the two occurrences is a cycle with all configs distinct.

So distinctness is not an independent obstacle. It comes for free after the
escape lemma.

## 5. What Would Actually Finish The Consecutive Case

The corrected shadow proof can be completed if one proves **either** of the
following.

### Option 1: A Closed Shadow Family

Construct a set `B` of bad configurations such that:

1. `S_0 = F(C_0)` lies in `B`;
2. `B` is disjoint from `gc`;
3. every config in `B` has a privileged move to another config in `B`.

Then Proposition 1 immediately yields a `ShadowTrap`.

### Option 2: A Direct Escape Lemma

Prove directly that one can choose privileged processors

`q_0, q_1, q_2, ...`

so that the orbit from `S_0` never enters `gc`.

Again Proposition 1 then yields a `ShadowTrap`.

The mover-entry strategy is one possible way to prove Option 2, but for the
outer-pair flip it currently lacks the necessary invariant.

## 6. Bottom Line

The corrected consecutive-binary shadow argument does **not** presently prove:

- mover-entry routing for all shadow steps,
- disjointness of the corrected orbit from the good cycle,
- return to `S_0`, or
- period `L`.

What it really needs is a **dynamic badness/escape invariant**.

So the mathematically correct conclusion is:

> The outer-pair flip `S_0 = F(C_0)` is a promising start state, but the
> corrected shadow-orbit proof is incomplete under the stated hypotheses.
> The proof breaks exactly at the step where one must show that the orbit can
> be kept forever outside the good cycle after the `S_k = F(C_k)` ansatz has
> been abandoned.

Equivalently:

- `H-1` is not enough;
- a static `H-2` lemma would still be insufficient by itself;
- the missing ingredient is a **global escape lemma**, not a local start-state
  observation.

If the goal is to close the consecutive-binary branch completely, the cleaner
route is likely the direct binary-overlap / entry-conflict argument, not this
shadow construction.
