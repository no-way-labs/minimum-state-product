# M4 Last Native Decide Handoff

## Scope

This handoff covers the remaining bounded `native_decide` island on the live
`M_4` lower-bound path after `LB2222` was closed.

Current theorem status:

- `lake build LeanMn.SmallN.LB2222` passes
- `lake build LeanMn.SmallN.Theorem` passes
- `M_4_lower` is live in `SmallN/Theorem.lean`

Recent commits:

- `e8f1d9c` `Prove M4 lower bound via LB2222`
- `dd864d4` `Remove config-card native_decide from LB2222 path`

## What is still computational

The remaining live `native_decide` is in:

- `LeanMn/SmallN/LB2222.lean`

Specifically:

- `hasExplicitBadCycle_of_wordFromChoiceFun4_len15_count4`
- wrapper `hasExplicitBadCycle_of_wordFromChoices4_len15_count4`

This theorem is used only in the all-`fireCount = 4` branch of
`goodCycle_gives_blocked_q4_cycle`.

Everything else on the live `M_4` path is now structural / analytic.

## Current shape of the all-4 branch

In `goodCycle_gives_blocked_q4_cycle`:

1. assume `htf : isTFBlocked ... = false`
2. assume `hfc4 : ∀ p : Fin 4, gc.fireCount p = 4`
3. reconstruct the mover word as:
   - `w := gcWordFrom gc 0 gc.configs.length ...`
   - `LocalNoStayWord4 w`
   - `w = wordFromChoices4 a ds`
   - `ds.length = 15`
   - `count j (wordFromChoices4 a ds) = 4` for all `j`
4. invoke the bounded finite theorem above to get
   `hasExplicitBadCycle (pathFromWord4 bits0 ...) = true`
5. transport back to `gcPathN ...`
6. close with `hasExplicitBadCycle_sound`

So the only missing non-computational replacement is:

> a symbolic proof that any 16-step `LocalNoStayWord4` word with counts
> `4,4,4,4` cannot survive `htf = false`.

## Strong computational facts already learned

These were checked locally with Python during the current session.

### Fact 1

Every 16-step `LocalNoStayWord4` mover word with counts `4,4,4,4` is
non-simple.

In practice:

- all `9800` such words fail `SimpleWord4`

This strongly suggests the right replacement theorem is actually a
`SimpleWord4` contradiction, not an explicit-bad-cycle theorem.

### Fact 2

The first repeated prefix state always appears with offsets heavily concentrated
at:

- `4`
- `8`
- `12`

The first repeat pair histogram found computationally included:

- `(0,4)`
- `(0,8)`
- `(2,6)`
- `(1,5)`
- `(3,7)`
- `(4,8)`
- `(0,12)`
- and a few later variants

### Fact 3

Looking at checkpoint states at times `0,4,8,12,16`, there are only `64`
distinct checkpoint sequences in the entire all-4 local-no-stay universe.

Typical checkpoint states are among:

- `(0,0,0,0)`
- `(1,1,1,1)`
- `(1,0,1,0)`
- `(0,1,0,1)`

This is much smaller than the original 15-bit choice space and is probably the
right combinatorial compression.

### Fact 4

If you restrict to the all-4 words that are not already immediately killed by
the existing first-4 symbolic conflict lemmas, the first 4 movers are of the
two sweep-like forms:

- `(s,l,a,r)` relative to the first mover
- `(s,r,a,l)` relative to the first mover

So after existing local conflict lemmas, the residue already looks sweep-like.

### Fact 5

For many surviving words, the first 8-step checkpoint state is already zero,
and the 8-step prefix count vector is often:

- `(2,2,2,2)`

but not always. Exotic even-count 8-prefixes also occur, e.g.

- `(2,0,2,4)`
- `(3,1,1,3)`
- `(1,2,3,2)`

So “state at time 8 is zero” alone is not enough to force the old 8-step sweep
theorem directly.

## Best current conjecture

The likely clean replacement theorem is something like:

```lean
theorem not_simple_of_localNoStay_len16_count4
    {w : Word4}
    (hlocal : LocalNoStayWord4 w)
    (hlen : w.length = 16)
    (hcount : ∀ j : Proc4, w.count j = 4) :
    ¬ SimpleWord4 w
```

Then the all-4 branch could avoid `hasExplicitBadCycle` entirely:

1. derive `SimpleWord4 w` from `gcWordFrom_simple_pre gc`
2. derive `LocalNoStayWord4 w`
3. derive `w.length = 16`
4. derive `count j w = 4`
5. contradict the new theorem

This would be cleaner than replacing the current bounded `native_decide` with a
different bounded `native_decide`.

## Suggested proof route

### Route A: checkpoint-state theorem

Prove a theorem on 4-step checkpoints:

- define the prefix states at times `0,4,8,12`
- use global counts `4,4,4,4` to constrain the parity transitions across each
  4-step block
- show one checkpoint state must repeat before time `16`

This would directly imply `¬ SimpleWord4`.

Pros:

- small finite state space conceptually
- likely robust and readable

Cons:

- needs new block-parity lemmas

### Route B: 4-step block classification

Classify all 4-step `LocalNoStayWord4` blocks by:

- start mover
- end parity vector
- count vector

Then prove every admissible concatenation of four such blocks with total counts
`4,4,4,4` yields a repeated prefix state.

Pros:

- computational exploration already points here

Cons:

- a little bookkeeping-heavy

### Route C: kill the residue after the first-4 local conflict lemmas

Reuse existing symbolic lemmas on the first four movers to shrink the residue to
the sweep-like starts:

- `(a, left a, anti a, right a, ...)`
- `(a, right a, anti a, left a, ...)`

Then prove no 16-step all-4 continuation of those starts stays simple.

Pros:

- maximally reuses current infrastructure

Cons:

- probably still needs a checkpoint/block argument afterward

## Files that matter

Primary:

- `lean/LeanMn/SmallN/LB2222.lean`
- `lean/LeanMn/SmallN/BinaryQ4Word.lean`

Relevant existing lemmas in `BinaryQ4Word.lean`:

- `prefixState4_append_self_self_eq`
- `prefixState4_append_abab_eq`
- `not_simple_of_adjacent_repeat_with_tail`
- `not_simple_of_abab_before_end`
- all the `sigConflict4_*` first-4 / local pattern lemmas
- `first_four_sweep_or_reverse_of_localNoStay`

Relevant existing lemmas in `LB2222.lean`:

- `gcWordFrom_localNoStay`
- `gcWordFrom_simple_pre`
- `gcWordFrom_simple`
- `gc_prefixFireCount_eq_count_gcWordFrom`
- all zero-gap / wrap lemmas now in the file

## Things already ruled out

- Replacing the last theorem with `isTFBlocked = true` by `native_decide`:
  false; there are all-4 words that are not TF-blocked for some starts.
- Using only the old 8-step balanced sweep theorem:
  insufficient; exotic even-count 8-prefixes exist.
- Treating the residue as a path / explicit-bad-cycle problem first:
  probably overkill; the real obstruction appears at the mover-word /
  `SimpleWord4` level.

## Recommended next move

Do not touch files outside `LeanMn/SmallN` first.

Start in `BinaryQ4Word.lean` and aim for:

1. a theorem that 16-step `LocalNoStayWord4` + counts `4,4,4,4` implies
   `¬ SimpleWord4`
2. replace `hasExplicitBadCycle_of_wordFromChoiceFun4_len15_count4` usage in
   `LB2222.lean`
3. delete the wrapper theorem if no longer needed

That should remove the last live `native_decide` from the `M_4` theorem path.
