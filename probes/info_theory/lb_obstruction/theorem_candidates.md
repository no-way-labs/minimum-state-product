# LB Obstruction Theorem Candidates

Date: April 6, 2026

This file records theorem candidates that survive the obstruction-focused
redirect.

## Candidate A. Explicit Subthreshold Floor on Forced-Kernel Residual Families

Let `K_C` be the forced-kernel obstruction scalar for a full good cycle `C` in
an explicit subthreshold residual family, taken either as:

- kernel indicator,
- or peel depth.

At width `n-2`, the forbidden interaction fraction of `K_C` is bounded away
from the valid witness coarse-layer regime.

### Current evidence

For the tested residual families:

- `n=5`:
  - kernel indicator: `0.068713 .. 0.097222`
  - peel depth: `0.071082 .. 0.079303`
- `n=6`:
  - kernel indicator: `0.031332 .. 0.049383`
  - peel depth: `0.020846 .. 0.024903`

Valid witness coarse-layer comparison:

- `CUP-2(n=5)`: `FutureFc = 0.026144`
- `CUP-2(n=6)`: `FutureFc = 0.008582`

So the forced-kernel residual families remain above the valid `FutureFc`
coarse-layer values by substantial same-`n` margins.

### Best current theorem form

There exists a positive floor `δ_n` for the explicit forced-kernel residual
families such that

`forbidden_frac(K_C) >= δ_n`

with `δ_5 > 0.06` and `δ_6 > 0.02`, while valid witness coarse-layer values
remain strictly below those thresholds.

This is not yet a universal subthreshold theorem, but it is the first genuine
forbidden-condition candidate on the redirected branch.

### Preferred primary scalar

At present, the best primary floor candidate is `kernel_indicator`.

Reason:

- it is the simpler obstruction-side scalar,
- and at the currently tested sizes its minimum same-`n` gap above the valid
  coarse `FutureFc` layer is stronger overall:
  - `n=5`: `0.068713 - 0.026144 = 0.042569`
  - `n=6`: `0.031332 - 0.008582 = 0.022750`

By contrast, `peel_depth` is slightly stronger at `n=5` but weaker at `n=6`:

- `n=5`: `0.071082 - 0.026144 = 0.044938`
- `n=6`: `0.020846 - 0.008582 = 0.012264`

So the cleanest next theorem candidate is:

> For every full good cycle in the explicit forced-kernel residual families at
> `n=5,6`, the forbidden width-`n-2` fraction of the kernel indicator is bounded
> below by a positive floor that remains strictly above the valid coarse-layer
> `FutureFc` regime at the same `n`.

This is still a finite explicit-family theorem, not yet a universal
subthreshold theorem.

## Candidate B. Universal Coarse-Layer Suppression

Every valid system in a suitable near-threshold class has width-`n-2`
forbidden mass for the coarse convergence layer below a small class-dependent
ceiling.

Current witness-side data alone is not enough to state this universally, but it
is the strongest admissible universal theorem target.

## Candidate C. Explicit Shadow-Cycle Floor on 3-Binary `{2,3}` Families

Consider the explicit `{2,3}` state vectors with exactly 3 binary processors and
the remaining processors ternary, together with the canonical uniform sweep
cycle and its shadow cycle.

Define the shadow indicator

`S_C(c) = 1[c belongs to the shadow cycle of C]`.

### Current evidence

At width `n-2`, the forbidden interaction fraction of `S_C` is much larger than
the valid coarse `FutureFc` regime at matching sizes.

For all ternary-value assignments tested on the explicit rotation classes:

- `n=5`:
  - `(2,2,2,3,3)`: exact value `0.152778`
  - `(2,2,3,2,3)`: exact value `0.222222`
- `n=6`:
  - `(2,2,2,3,3,3)`: exact value `0.146605`
  - `(2,2,3,2,3,3)`: exact value `0.152778`
  - `(2,2,3,3,2,3)`: exact value `0.158951`
  - `(2,3,2,3,2,3)`: exact value `0.194444`
- `n=7`:
  - `(2,2,2,3,3,3,3)`: exact value `0.151896`
  - `(2,2,3,2,3,3,3)`: exact value `0.154982`
  - `(2,2,3,3,2,3,3)`: exact value `0.140873`
  - `(2,2,3,3,3,2,3)`: exact value `0.154982`
  - `(2,3,2,3,2,3,3)`: exact value `0.172619`

Valid same-`n` coarse-layer references:

- `CUP-2(n=5)`: `0.026144`
- `CUP-2(n=6)`: `0.008582`
- `CUP-2(n=7)`: `0.002573`

So the explicit shadow-cycle class gives a much stronger same-`n`
forbidden-mass floor candidate than the forced-kernel residual families.

### Best current theorem form

For the explicit 3-binary `{2,3}` sweep-shadow families at `n=5,6,7`, the
shadow indicator has width-`n-2` forbidden fraction bounded below by a positive
floor that remains well above the valid coarse-layer `FutureFc` regime at the
same sizes.

This is not yet a universal subthreshold theorem, but it is currently the
strongest explicit forbidden-condition candidate on the branch.

### Sharpened explicit-family theorem form

For the tested 3-binary `{2,3}` sweep-shadow families at `n=5,6,7`, the shadow
indicator forbidden fraction is:

- invariant under all tested ternary-value assignments within a fixed
  binary-placement rotation class,
- and equal to the following exact rational values:

| n | binary-placement class | exact forbidden fraction |
| --- | --- | --- |
| 5 | `(2,2,2,3,3)` | `11/72` |
| 5 | `(2,2,3,2,3)` | `2/9` |
| 6 | `(2,2,2,3,3,3)` | `95/648` |
| 6 | `(2,2,3,2,3,3)` | `11/72` |
| 6 | `(2,2,3,3,2,3)` | `103/648` |
| 6 | `(2,3,2,3,2,3)` | `7/36` |
| 7 | `(2,2,2,3,3,3,3)` | `689/4536` |
| 7 | `(2,2,3,2,3,3,3)` | `703/4536` |
| 7 | `(2,2,3,3,2,3,3)` | `71/504` |
| 7 | `(2,2,3,3,3,2,3)` | `703/4536` |
| 7 | `(2,3,2,3,2,3,3)` | `29/168` |

In particular, across all tested classes and assignments:

`forbidden_frac(shadow_indicator) >= 71/504 > 0.1408`.

By contrast, the valid same-`n` coarse-layer references satisfy:

- `CUP-2(n=5) = 0.026144`
- `CUP-2(n=6) = 0.008582`
- `CUP-2(n=7) = 0.002573`

So the explicit shadow class already gives a strong same-`n` separation:
the tested subthreshold shadow indicators never enter the witness coarse-layer
regime.

## Candidate D. Subthreshold Code Failure

Subthreshold systems cannot realize the same reduced-prefix recovery structure
as the valid coarse layer.

Current status: no theorem-shaped evidence yet. Keep only if the reduced-prefix
package is explicitly tested on obstruction-side families or on broader invalid
candidate classes.
