# Information-Theoretic Theorem Targets

Date: April 6, 2026

This file records the most theorem-shaped statements suggested by the
information-theoretic exploration in `exploration_log.md`.

They are ordered from strongest current evidence to most speculative.

## T1. Forbidden-Interaction Suppression for Valid Witness Ranks

Let `F(c)` be the full-space extension of the bad-side convergence rank:

- `F(c) = 0` if `c` is good
- `F(c) = rank(c) + 1` if `c` is bad

Let `E_forbid^{(n-2)}(F)` be the ANOVA `L^2` energy of `F` on interaction
supports not contained in any cyclic window of length `n-2`.

### Empirical statement

For valid witness families (`CUP-2`, `Sol3`), `E_forbid^{(n-2)}(F)` is tiny and
decays rapidly with `n`, while shuffled labels with the same value multiset have
substantially larger forbidden energy.

### Candidate theorem

There exists a structural reason tied to convergence on the ring that forces
the rank extension of a valid system to suppress the width-`n-2` forbidden
vertex-cover interaction modes.

### Why this matters

This is currently the strongest invariant found that:

- is not explained by raw model dimension,
- survives null-model calibration,
- and visibly separates valid witnesses from invalid/subthreshold obstruction
  families.

## T2. Two-Level Suppression Theorem

The existing convergence proof uses:

- `FutureFc`
- plus rank inside the constant-`FutureFc` slice

### Empirical statement

At width `n-2`, for valid witnesses:

- `fc` and `FutureFc` already have near-zero forbidden interaction energy,
- the constant-`FutureFc` slice rank carries the residual nonlocal correction.

### Candidate theorem

The width-`n-2` forbidden interaction suppression of the full rank factors into:

1. a frontier layer that is already almost entirely inside the allowed subspace,
2. a slice-rank correction that is small and structured.

### Why this matters

This is the cleanest bridge from the info-theory exploration back to the actual
proof architecture.

## T3. Tiny `FutureFc` Code Theorem

### Empirical statement

The coarse convergence layer `FutureFc` admits an exact tiny decoder once
obvious local prefixes are included.

Observed minimum exact extra basis sizes:

- `CUP-2`:
  - `n=5,6,7`: `1`
  - `n=8`: `2`
  - `n=9,10`: `3`
  - `n=11`: `5`
- `Sol3`:
  - `n=4,5,6,7`: `1`
  - `n=8,9`: `2`
  - `n=10`: `3`
  - `n=11`: `5`

At `CUP-2(n=12)`, the current low-order weighted-pair/count bank is no longer
exact; one nonlocal `(1,1)` pair correction repairs it for `FutureFc`.

### Stronger family-basis form

The decoder is not just tiny; it appears to organize by stable family bases.

Observed exact family bases:

- `CUP-2(n=9..11)`:
  - `even_val_sum`
  - `weight_pair_00`
  - `weight_pair_02`
  - `weight_pair_11`
  - `weight_pair_22`

- `Sol3(n=9..11)`:
  - `even_val_sum`
  - `weight_pair_00`
  - `weight_pair_01`
  - `weight_pair_02`
  - `weight_pair_22`

At `CUP-2(n=12)`, the first nonlocal correction

- `count_lag2_11`

restores exactness on top of the `CUP-2` family basis.

### Candidate theorem

`FutureFc` is a deterministic function of a tiny low-order code whose size grows
slowly with `n`, and whose first nonlocal correction is highly structured.

### Why this matters

This is currently the cleanest exact-code target in the entire program.

## T4. Small Residual Slice-Code Theorem

Fix a valid witness family and condition on the base invariants:

- `FutureFc`
- the boundary 6-tuple
- the proof107 interior invariants `(exp2, int21, exp2_weight)`

### Empirical statement

For `CUP-2` and `Sol3` at `n=9`, the remaining slice-rank entropy closes with
just a few weighted-pair / sum features.

For `CUP-2`, a fixed weighted-pair scaffold remains exact through `n=10`,
extends to exactness through `n=11` with two additional pair features, and is
still near-exact at `n=12`.

### Candidate theorem

The residual constant-`FutureFc` slice rank of valid token-ring witnesses is
determined by a tiny low-order weighted adjacent-pair code.

### Strong form

There exists a finite family of adjacent-pair statistics whose restriction to
the first `k(n)` members determines the slice rank for the `n`-processor
witness, with `k(n)` growing slowly.

## T5. Minimal Exact Basis Growth Law

### Empirical statement

For the residual slice code after conditioning on base invariants:

- `CUP-2(n=9)`: minimal exact extra basis size `3`
- `CUP-2(n=10)`: size `4`
- `CUP-2(n=11)`: size `5`
- `Sol3(n=9)`: size `3`

### Candidate theorem

The minimal exact basis size for the residual slice code grows slowly and stays
inside a fixed weighted-pair algebra.

### Caveat

By `n=12`, the first correction is no longer a cheap one- or two-feature
extension of the six-feature scaffold. So the exact growth law is still open.

## T6. Invalid-Family Gap Theorem

### Empirical statement

Explicit subthreshold residual families (`n=5,6`) built from forced mover-entry
kernels have substantially larger forbidden width-`n-2` energy than valid
witness ranks at the same sizes.

### Candidate theorem

Subthreshold obstruction families cannot suppress forbidden width-`n-2`
interaction energy below a witness-scale floor.

### Why this matters

This is the nearest current route from the witness-side invariant toward a
lower-bound statement.

## T7. What Is Probably False

These are the theorem targets that the exploration now strongly suggests are
not the right form:

- Any theorem based only on good-cycle support counts or local entropy
- Any theorem based only on privileged-cylinder cover counts
- Any theorem treating width-`n-1` exactness as inherently meaningful without
  null-model calibration
- Any theorem claiming the residual slice code is affine-linear
- Any theorem claiming the residual slice code is simply lexicographic

## Best Next Proof Targets

If choosing only three targets to keep:

1. Prove or explain suppression of forbidden width-`n-2` interaction energy.
2. Prove the two-level decomposition of that suppression into `FutureFc` plus
   small slice residual.
3. Prove an exact tiny-code theorem for `FutureFc`.
