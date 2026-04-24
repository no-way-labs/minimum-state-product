# Product-72 Controller-Reuse Theorem

This note packages the current controller-language reading of the two `n=5`
product-72 impossibility proofs.

Families:

- `(2,2,2,3,3)`
- `(2,2,3,2,3)`

Both are below `M_5 = 96`.

## What the old shadow theorems actually show

The old small-`n` shadow-cycle proofs can be rephrased as follows.

Fix a consistent good cycle `G` in one of the product-72 families.

1. The repeated-shadow controller complexity stays at most `2`.
2. Good-cycle mover entries determine a local controller on repeated shadows.
3. Those same controller entries are reused at non-good anti-sweep/repeated
   shadows.
4. The reused moves stay in a finite bad off-cycle region.
5. Therefore the daemon has a recurrent bad orbit.

This is exactly the pattern predicted by the abstract
[controller_recurrence_theorem.md](./lean/docs/controller_recurrence_theorem.md).

## Static observations

### 1. Controller capacity

Current exact/sampled evidence:

- canonical-start consistent cycles in both families stay in controller-capacity
  profile `(2,2,2,2,2)`
- the standard consistent cycles in both families have repeated-shadow
  pair-controllers at forgotten processor `3`

So the product-72 world is a `2`-controller world.

### 2. Repeated-shadow pair-controllers at `p = 3`

For the standard consistent cycle in each family:

- forgetting processor `3`, repeated-shadow controllers include the pair
  `{3,4}`

In sampled canonical-start cycles:

- the repeated-shadow pair-controller histogram at `p = 3` is
  `{2,3}` and `{3,4}`

This matches the threshold witness bridge:

- the witness `w5` upgrades that local pair-controller picture to the
  triple-controller `{2,3,4}`.

## Dynamic observations

### 1. Explicit bad reuse region

In both product-72 families, one can start from an anti-sweep / non-good state
and follow forced moves that are all reused good-cycle mover entries.

So the bad orbit is not using free entries. It is generated entirely by
controller-entry reuse.

### 2. Shadow mover words

For the first 40 canonical-start cycles in each family, the observed shadow
mover words fall into the same four 10-step words, i.e. the same two 5-step
rotation classes.

That suggests the dynamic obstruction is shared across both binary layouts.

## Candidate family theorem

### Theorem (Product-72 Controller Reuse)

Let `sys` be a consistent system in one of the two `n=5` product-72 families,
and let `G` be a good 10-cycle.

Then:

1. the repeated-shadow controller complexity is at most `2`
2. the determined mover entries from `G` generate a finite bad reuse region `B`
3. the induced reused-mover map on `B` contains a directed cycle

Hence `sys` is not convergent.

## Why this formulation is useful

This theorem would replace the older presentation

- “there is a shadow cycle”

with the more reusable statement

- “a deterministic 2-controller on repeated shadows induces a bad reuse region,
  hence recurrence”

That is more likely to scale to other small-`n` families.

## Likely proof decomposition

1. Identify the repeated-shadow pair-controller(s) in the product-72 family.
2. Show that anti-sweep/repeated-shadow non-good states realize the same
   controller entries.
3. Prove closure of that bad reuse region under the reused movers.
4. Invoke the abstract recurrence theorem.

## Strongest bridge to the witness side

At forgotten processor `p = 3`:

- product-72 sub-threshold world: pair-controllers `{2,3}` and `{3,4}`
- threshold witness `w5`: triple-controller `{2,3,4}`

So the threshold witness can be interpreted as fusing the adjacent pair
controllers that the sub-threshold world can realize only separately.

This is the cleanest current `n=5` controller-complexity bridge.
