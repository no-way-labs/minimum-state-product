# Global Shadow-Floor Theorem Draft

Date: April 6, 2026

This note states the weaker paper-facing theorem that should come before the
full class-value law.

The point is to isolate the first obstruction theorem that is both:

- strong enough to be meaningful for the lower bound,
- and simple enough to be proved or certified cleanly.

## 1. Context

Fix a `{2,3}` state vector with exactly three binary processors and all
remaining processors ternary.

Fix the canonical uniform sweep cycle and its induced shadow cycle as in
`shadow_floor_theorem.md`, and write

`chi_{m,epsilon}(c) = 1[c belongs to the shadow cycle]`.

Let

`ForbidFrac_{n-2}(chi_{m,epsilon})`

denote the width-`n-2` forbidden interaction fraction of the shadow indicator.

## 2. Theorem Statement

### Theorem A. Explicit shadow-floor law through `n = 7`.

For every tested explicit 3-binary `{2,3}` sweep-shadow family at
`n = 5,6,7`, and for every tested ternary assignment `epsilon`,

`ForbidFrac_{n-2}(chi_{m,epsilon}) >= 71/504`.

Equivalently, on the tested explicit shadow class,

`ForbidFrac_{n-2}(chi_{m,epsilon})`

never enters the valid witness coarse-layer suppression regime.

### Same-n comparison corollary

The valid coarse-layer references satisfy:

- `CUP-2(n=5)`: `ForbidFrac_3(FutureFc) = 0.026144`,
- `CUP-2(n=6)`: `ForbidFrac_4(FutureFc) = 0.008582`,
- `CUP-2(n=7)`: `ForbidFrac_5(FutureFc) = 0.002573`.

So for all tested sizes `n = 5,6,7`,

`ForbidFrac_{n-2}(chi_{m,epsilon})`

is separated from the valid coarse-layer regime by a large same-`n` gap.

## 3. Proof Skeleton

The proof naturally splits into two parts.

### Part I. Assignment reduction within a binary-placement class

For a fixed binary-placement class `m`, any two ternary assignments differ by
independent swaps `1 <-> 2` on some ternary coordinates.

By the relabeling-invariance proposition and the sweep/shadow equivariance
proposition from `shadow_floor_theorem.md`:

1. the shadow indicators for different ternary assignments are related by
   coordinatewise relabeling,
2. forbidden interaction fraction is invariant under such relabeling.

Therefore, within each fixed binary-placement class, it is enough to compute
one representative assignment.

### Part II. Representative-class verification

For each binary-placement rotation class at `n=5,6,7`, compute one
representative shadow indicator and its exact width-`n-2` forbidden fraction.

The resulting exact class values are:

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

The minimum among these values is `71/504`, attained at
`(2,2,3,3,2,3,3)`.

That proves Theorem A.

## 4. Status

What is already symbolic:

- relabeling invariance of forbidden interaction fraction,
- the sweep/shadow equivariance roadmap reducing all ternary assignments in a
  fixed class to one representative.

What is currently computationally certified:

- the representative class values in the table above,
- the valid same-`n` coarse-layer references.

So Theorem A is currently a computationally certified explicit-family theorem
with a genuine symbolic reduction step, not yet a fully symbolic theorem.

## 5. Why This Is the Right First Theorem

This weaker floor theorem is preferable to the stronger class-value law as a
first paper result because:

1. it avoids overcommitting to exact per-class values before the equivariance
   machinery is fully formalized,
2. it already yields a strong same-`n` separation from the valid coarse-layer
   regime,
3. and it is closer to the lower-bound use case, which only needs a forbidden
   floor, not exact class constants.

## 6. Next Steps

The next proof tasks are:

1. formalize the sweep/shadow equivariance lemma chain from
   `shadow_floor_equivariance_lemmas.md`,
2. decide whether the paper should present:
   - Theorem A as the main obstruction theorem,
   - with the class-value table as a stronger computational corollary.
