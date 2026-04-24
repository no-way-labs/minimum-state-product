# Explicit Shadow-Floor Theorem Package

Date: April 6, 2026

This note packages the strongest current obstruction-side theorem candidate from
the information-theory branch.

The target is an explicit-family lower-bound obstruction:

> explicit 3-binary `{2,3}` sweep-shadow families have width-`n-2` forbidden
> interaction mass bounded well above the valid coarse-layer regime.

## 1. Setup

Fix a ring state vector `m in {2,3}^n` with exactly three binary processors and
all remaining processors ternary.

Fix a ternary assignment

`epsilon in {1,2}^T`

on the ternary positions `T`.

Let `C_{m,epsilon}` be the canonical uniform sweep cycle.

Let `S_{m,epsilon}` be the explicit shadow family attached to
`C_{m,epsilon}` by the shifted-waterfall construction from the shadow theorem
proof:

- the good sweep configurations are `g_j`,
- the shadow shift data are `d_i`,
- and the shadow configurations are `s_k(i)` defined pointwise from the same
  waterfall indicators with processor-dependent shifts.

The search routine `find_shadow_cycle` is used only as a corroborative audit
that it rediscovers this explicit shadow object on the tested classes.

### Canonical proof-ready placement

The explicit shifted-waterfall shadow formulas currently available in the paper
proof are written for the canonical placement with binary processors at
positions `0,1,2`. In that canonical case:

- choose nonzero values `v_i`, where `v_i = 1` on binary coordinates and
  `v_i = epsilon(i)` on ternary coordinates,
- write the good sweep as `C = (g_0, ..., g_{2n-1})` with

`g_j(i) = v_i * 1[1 <= ((j-i) mod 2n) <= n]`,

- define the shadow shifts

`d_i = n-2-i` for `0 <= i <= n-5`,

`d_{n-4} = 0`,

`d_{n-3} = n+1`,

`d_{n-2} = 2`,

`d_{n-1} = 2n-1`,

- and then define the explicit shadow family by

`s_k(i) = v_i * 1[1 <= ((k+d_i) mod 2n) <= n]`.

This is the proof-ready symbolic object for the canonical class.

### Scope note

Our computational explicit-family package is broader than the current symbolic
formula package: it covers all tested 3-binary `{2,3}` rotation classes through
`n=7`, not only the canonical consecutive-triple placement.

So the present state is:

1. **symbolic proof route**:
   fully identified for the canonical explicit shadow family,
2. **computational certification**:
   available for the broader tested placement classes.

Closing that gap requires an additional normalization theorem transporting the
canonical explicit shadow family to the broader binary-placement classes, or a
new explicit formula family for arbitrary placement.

### Directed-gap normalization clue

The canonical sweep construction fixes a direction:

`[0,1,...,n-1,0,1,...,n-1]`.

So the relevant placement invariant is not the unordered or reflection-quotiented
gap pattern of the three binary processors, but the **directed cyclic gap
triple**

`(g_1, g_2, g_3)`

recording the clockwise distances between consecutive binary positions, modulo
cyclic rotation only.

This explains the first apparent discrepancy in the data:

- at `n=6`, the two classes
  `(2,2,3,2,3,3)` and `(2,2,3,3,2,3)` are reflections of one another, but not
  cyclic rotations;
- they therefore need not share a shadow-floor value for the directed sweep
  construction, and indeed they do not.

So the current best normalization clue is:

- cyclic rotation should preserve the class value,
- reflection need not preserve it because it reverses the sweep orientation.

The remaining normalization problem is therefore not “gap pattern up to
dihedral symmetry,” but rather:

> which additional directed placement data, beyond cyclic rotation, controls the
> shadow-floor value?

Define the shadow indicator

`chi_{m,epsilon}(c) = 1[c in S_{m,epsilon}]`.

For a scalar `f` on the full configuration space, write

`ForbidFrac_w(f)`

for the width-`w` forbidden interaction fraction computed by the exact ANOVA
decomposition used in `anova_interaction_spectrum.py`.

In this note, `w = n-2`.

## 2. A Real Invariance Lemma

### Proposition 2.1. Coordinatewise relabeling preserves forbidden interaction fraction.

Let

`tau = tau_0 × ... × tau_{n-1}`

be a coordinatewise bijection of the full configuration space

`X = Π_i [m_i]`,

where each `tau_i : [m_i] -> [m_i]` is a permutation of processor `i`'s local
state set.

Then for every scalar `f : X -> R` and every width `w`,

`ForbidFrac_w(f ∘ tau) = ForbidFrac_w(f)`.

#### Proof

The map `tau` is a permutation of the finite product space `X`, so it preserves
the uniform product measure and therefore preserves `L^2` norm.

For each interaction support `S subseteq [n]`, the subspace of functions
depending only on coordinates in `S` is preserved by precomposition with `tau`,
because `tau` acts independently on each coordinate and does not change the
support set itself. Hence the ANOVA subspace attached to a support `S` is
carried isometrically to itself.

Therefore the `L^2` energy of `f` on each support `S` is unchanged under
precomposition by `tau`. Since the allowed/forbidden split for width `w`
depends only on the support `S`, not on the state labels, the total forbidden
energy and the total energy are both preserved. Their ratio is preserved as
well. ∎

## 3. Equivariance Heuristic for the Shadow Class

The canonical sweep and shadow constructions use only:

- the choice of binary positions,
- the choice of one nonzero ternary sweep value at each ternary position,
- and deterministic local transition entries derived from that choice.

Swapping labels `1 <-> 2` independently on any ternary coordinate is a
coordinatewise relabeling of the full configuration space. Under this relabeling
the canonical sweep cycle and the induced shadow cycle transform equivariantly.

So within a fixed binary-placement class, different ternary assignments should
be regarded as relabelings of the same shadow indicator. By Proposition 2.1,
their forbidden fractions are therefore forced to agree.

This equivariance is the clean symbolic explanation for the assignment-stability
seen computationally below.

### Proposition 3.1. Sweep/explicit-shadow equivariance under ternary relabeling.

Fix a binary-placement class `m in {2,3}^n` with exactly three binary
processors and ternary set `T`.

Let `epsilon, epsilon' in {1,2}^T` be two ternary assignments. Define a
coordinatewise bijection `tau_{epsilon -> epsilon'}` on the full configuration
space by:

- identity on binary coordinates,
- identity on ternary coordinate `j` if `epsilon(j) = epsilon'(j)`,
- swap `1 <-> 2` on ternary coordinate `j` if `epsilon(j) != epsilon'(j)`.

Then:

1. `tau_{epsilon -> epsilon'}(C_{m,epsilon}) = C_{m,epsilon'}`,
2. `tau_{epsilon -> epsilon'}(S_{m,epsilon}) = S_{m,epsilon'}`,
3. therefore
   `chi_{m,epsilon'} = chi_{m,epsilon} ∘ tau_{epsilon -> epsilon'}^{-1}`.

#### Proof sketch

For the canonical sweep cycle:

- binary processors always move `0 -> 1 -> 0`,
- ternary processor `j` always moves `0 -> epsilon(j) -> 0`.

Applying `tau_{epsilon -> epsilon'}` changes only the nonzero ternary label at
each ternary coordinate, so it transports the sweep path for `epsilon`
coordinatewise to the sweep path for `epsilon'`. Hence it carries
`C_{m,epsilon}` to `C_{m,epsilon'}`.

For the explicit shadow family:

- the shadow formulas use the same waterfall indicator values as the good sweep,
- the only ternary data entering those formulas are the chosen nonzero ternary
  sweep values,
- coordinatewise relabeling acts pointwise on those values.

So the same pointwise transport argument carries the explicit shadow family for
`epsilon` to the explicit shadow family for `epsilon'}`.

The indicator identity follows immediately. ∎

#### Corroborative audit

`shadow_equivariance_check.py` verifies the stated cycle-level transport on all
tested explicit shadow-floor classes through `n=7`:

- `n=5`: 2 binary-placement classes,
- `n=6`: 4 classes,
- `n=7`: 5 classes,

for a total of `109` assignment comparisons and `0` failures, checking both:

1. transport of the returned canonical sweep cycle,
2. transport of the returned shadow cycle from `find_shadow_cycle`.

This does not serve as the symbolic proof. It only corroborates that the search
routine rediscovers the explicit transported shadow object on the tested class.

### Corollary 3.2. Assignment-invariance reduces to one representative per class.

Within a fixed binary-placement class, all ternary assignments have the same
forbidden fraction for the shadow indicator. By Proposition 2.1 and
Proposition 3.1, it is enough to compute one representative assignment per
binary-placement class.

## 4. Explicit Class-Value Law Through n = 7

For the tested 3-binary `{2,3}` sweep-shadow classes, the shadow indicator
forbidden fraction is constant across all tested ternary assignments within each
binary-placement class, and equals:

| n | binary-placement class | exact value |
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

### Corollary 4.1. Uniform tested floor.

Across all tested classes and assignments,

`ForbidFrac_{n-2}(chi_{m,epsilon}) >= 71/504 > 0.1408`.

## 5. Same-n Comparison With Valid Witness Coarse Layer

The valid coarse-layer reference values are:

- `CUP-2(n=5)`: `ForbidFrac_3(FutureFc) = 0.026144`
- `CUP-2(n=6)`: `ForbidFrac_4(FutureFc) = 0.008582`
- `CUP-2(n=7)`: `ForbidFrac_5(FutureFc) = 0.002573`

So the explicit shadow-floor class sits far above the valid same-`n`
coarse-layer regime throughout the tested range.

## 6. Best Current Theorem Statement

### Theorem candidate.

For every tested explicit 3-binary `{2,3}` sweep-shadow family at
`n = 5,6,7`, the shadow indicator has width-`n-2` forbidden interaction
fraction at least `71/504`, while the valid witness coarse-layer value is much
smaller at the same `n`.

This is the strongest current explicit-family forbidden-condition candidate on
the obstruction-focused branch.

## 7. Proof Status

What is currently symbolic:

- Proposition 2.1: coordinatewise relabeling invariance of forbidden fraction.
- the reduction principle: assignment-stability should follow from equivariance
  of the explicit sweep/shadow formulas under ternary relabeling.

What is currently computationally certified:

- the exact class values in Section 4,
- the tested floor `71/504`,
- the same-`n` valid witness comparisons in Section 5.

## 8. What Is Missing

To turn this into a clean paper theorem, the remaining steps are:

1. Prove the sweep/shadow equivariance under independent ternary relabelings.
   Here the proof object should be the explicit shadow family from the paper,
   not the search routine.
2. Decide whether to state:
   - the stronger class-value law,
   - or the weaker global floor law `>= 71/504`.
3. Decide whether to stop at the explicit-family theorem, or attempt to widen
   from the sweep-shadow class toward a broader subthreshold architecture class.

At present, the weaker global floor law looks like the cleaner first theorem.
