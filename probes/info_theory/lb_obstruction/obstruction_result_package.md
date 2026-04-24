# Obstruction Result Package

Date: April 6, 2026

This note packages the current obstruction-side results into a paper-ready
preliminary structure.

The package is organized to separate:

1. the **symbolic core** we know how to target cleanly,
2. the **broader computational shell** that already gives a strong explicit
   obstruction class,
3. the **main theorem statement** that is honest now,
4. and the **remaining gap** to a universal lower-bound theorem.

Important scope note:

- this package currently has a much stronger **shadow-side obstruction track**,
- and now a first explicit-family **entry-conflict model case** plus a broader
  BAF witness theorem candidate,
- but not yet a unified universal witness theorem.

The full lower-bound picture likely requires both.

## 1. The Core Claim

The strongest current obstruction-side statement is not yet universal across all
subthreshold systems. It is an explicit-family theorem candidate on the
**shadow-side**:

> explicit 3-binary `{2,3}` sweep-shadow families have width-`n-2` forbidden
> interaction mass bounded far above the valid same-`n` coarse-layer regime.

This is already meaningful because:

- it is a forbidden-condition theorem candidate,
- it is same-`n`,
- it uses an explicit family already central to the lower-bound architecture,
- and it has a clean symbolic mechanism for assignment-invariance.

## 2. Main Preliminary Theorem

### Theorem A. Explicit shadow-floor theorem through `n = 7`.

For every tested explicit 3-binary `{2,3}` sweep-shadow family at
`n = 5,6,7`, and for every tested ternary assignment, the shadow indicator

`chi_{m,epsilon}(c) = 1[c belongs to the shadow cycle]`

has width-`n-2` forbidden interaction fraction at least

`71/504 > 0.1408`.

Moreover, the valid same-`n` coarse-layer references satisfy:

- `CUP-2(n=5)`: `ForbidFrac_3(FutureFc) = 0.026144`,
- `CUP-2(n=6)`: `ForbidFrac_4(FutureFc) = 0.008582`,
- `CUP-2(n=7)`: `ForbidFrac_5(FutureFc) = 0.002573`.

So on the tested explicit shadow class, the shadow indicator never enters the
valid coarse-layer suppression regime.

### Status

Computationally certified on the explicit class, with a real symbolic reduction
step via relabeling-equivariance.

## 3. Symbolic Core

The symbolic core currently consists of two pieces.

### 3.1 Relabeling invariance of forbidden fraction

Coordinatewise relabeling of state labels preserves the width-`w` forbidden
interaction fraction of any scalar on the full configuration space.

This is a genuine proved proposition in
`shadow_floor_theorem.md`.

### 3.2 Assignment reduction by sweep/shadow equivariance

Within a fixed binary-placement class, different ternary assignments are related
 by coordinatewise `1 <-> 2` relabelings on ternary coordinates.

The intended symbolic route is:

1. canonical sweep cycles transport under these relabelings,
2. the explicit shadow family transports as well,
3. therefore assignment-invariance follows from 3.1.

This route is now written down in:

- `shadow_floor_theorem.md`
- `shadow_floor_equivariance_lemmas.md`
- `shadow_floor_symbolic_route.md`

## 4. Broader Computational Shell

The broader explicit-family package currently established is:

### 4.1 Exact class values through `n = 7`

For the tested 3-binary `{2,3}` sweep-shadow classes, the exact class values are
tabulated in `shadow_floor_theorem.md`.

### 4.2 Assignment-stability audit

`shadow_equivariance_check.py` verifies, on the full tested class through `n=7`,
that coordinatewise ternary relabelings transport:

- the returned canonical sweep cycle,
- the returned shadow cycle from `find_shadow_cycle`,

with `109` assignment comparisons and `0` failures.

### 4.3 Directed normalization correction

The correct symmetry notion for the canonical sweep construction is:

- cyclic rotation,
not
- full dihedral symmetry.

This matters because reflection reverses the sweep orientation and need not
preserve the class value.

So the current broader computational shell should be understood as a
**directed** explicit-family package.

## 5. What This Gives Toward the Lower Bound

This package does **not** yet prove the lower bound.

What it does give is:

1. a strong explicit forbidden-condition theorem candidate,
2. a same-`n` obstruction gap against the valid coarse layer,
3. and a symbolic mechanism that could plausibly generalize.

What it does **not** yet give is a settled general EC-side obstruction theorem.
We now do have an explicit-family EC-side package note:

- `ec_obstruction_theorem.md`

and that note now contains:

- a canonical model-case law,
- a broader BAF witness theorem candidate `E_conf > 0`,
- a strong tested universality pattern suggesting the sharper law
  `E_conf = 2(n-3)` on the tested non-sweep `fc=2` family,
- a derived global EC bridge object `chi_conf` with substantial nonzero
  forbidden mass on the tested BAF family,
- and a weaker global EC bridge theorem candidate
  `ForbidFrac_{n-2}(chi_conf) >= 37/324` on the tested BAF family through
  `n=8`,
- and a word-level support-geometry candidate for `chi_conf` on the tested BAF
  family,
- and now a broader BAF support theorem package in
  `ec_baf_support_theorem.md`,
- together with a canonical subtraction formula
  `chi_conf = chi_good - chi_exc` on the canonical BAF family.

One important new correction is now in place:

- the broader BAF support theorem is **not** enough by itself to explain the
  weak EC bridge constant,
- because even inside the simple two-turnaround BAF family, the same coarse
  support shape can produce different forbidden fractions.

So the EC bridge theorem must depend on **turnaround placement geometry**, not
just the support cardinality or the “two arcs minus four states” description.

The first concrete candidate for that extra datum is now visible:

- on the simple two-turnaround BAF family through `n=9`,
- and on the full valid-fiber minima through `n=7`,

the EC bridge value appears to be constant once one fixes the cyclic distance
from the turnaround vertex to the middle binary processor `1`.

The first symmetry reduction for this datum is now packaged in:

- `ec_distance_class_reduction.md`,

which uses reflection about processor `1` to reduce the simple two-turnaround
BAF family to one representative per distance-to-`1` class.

On the solved small range `n=5,6,7`, the full valid-fiber minima already match
those simple class representatives exactly.

Those representatives are now explicit:

- `W_d = W_{1+d}`,
- where
  `W_v = [0,1,...,v, v-1,...,0, n-1,...,v, v+1,...,n-1]`.

And there is now a first coefficient-level route on those representatives:

- `ec_mask_family_route.md`

shows that a tiny anchored forbidden-mask family already has positive energy on
every tested `W_d` through `n=9`.

This has now improved to the strongest current EC theorem route:

- `ec_basis_coefficient_route.md`

which uses one explicit product basis vector `Psi_d` on the candidate support
and verifies nonvanishing of `<chi_conf(W_d), Psi_d>` through `n=11`.

That route is now upgraded to an exact representative theorem:

- `ec_basis_coefficient_theorem.md`

gives a closed-form expression and exact sign pattern for
`<chi_conf(W_d), Psi_d>`, so the EC side now has a real theorem proving
positive forbidden energy on the candidate support of every representative
`W_d`.

But this theorem is currently representative-family only:

- on the small full-fiber checks, the same coefficient need not retain a fixed
  sign across all valid goods in a class,
- so the broader lift back to the tested BAF family will have to be support-
  level or use a more flexible basis choice.

The first concrete support-level route is now in:

- `ec_support_lift_route.md`,

with the key example `n=6, d=2`, where the coefficient theorem does not lift
rigidly but several tiny forbidden supports still have the same positive energy
across all valid goods in the class.

That route now has its first actual full-class theorem:

- `ec_smallrange_support_lift_theorem.md`,

which proves on the solved small range `n=5,6,7,8,9` that the full tested BAF
class already admits class-stable tiny forbidden supports depending only on the
distance class `d`.

This also changes the right EC bridge target:

- the old finite-range constant `37/324` remains a useful local theorem
  candidate through `n=8`,
- but the representative family at `n=10` already drops below that value.

So the next honest symbolic EC target is positivity, or an explicit
`n`-dependent floor, not a universal constant across all `n`.

But this is still not yet a general EC witness theorem.

That is enough to justify continued obstruction-side work.

## 6. What Remains Open

Four layers remain open.

### A. Canonical explicit-family proof completion

The sweep/shadow equivariance proof still needs to be written cleanly against
the explicit shadow-family formulas, rather than left as a proof sketch.

### B. Directed normalization theorem

To move from the canonical symbolic core to the broader placement classes, we
still need a normalization theorem or an explicit arbitrary-placement shadow
formula.

### C. Universal lower-bound theorem

Nothing here yet says that **every** subthreshold system must exhibit a
forbidden-mass floor. That is the real lower-bound target, still open.

### D. Entry-conflict obstruction track

The branch now has an explicit-family EC package, but not yet a general EC
witness theorem. If the final lower bound genuinely has two main mechanisms

- entry conflict,
- shadow obstruction,

then a universal witness theorem will likely need either:

- a unified witness,
  or
- a disjunctive EC-or-shadow witness theorem.

### E. Partial reunification clue

The split-observable lesson still holds for **raw** EC overlap counts: they are
width-3 local and have zero width-`n-2` forbidden mass.

But the derived global EC witness `chi_conf` already has substantial positive
forbidden mass on the tested BAF family. So the EC and shadow tracks may
partially reunify at the level of **derived global witnesses**, even if they do
not reunify at the level of raw local witnesses.

### F. Current best EC-side next theorem

The next EC-side proof target is now clear:

> strengthen the weak EC bridge theorem using the broader BAF support theorem
> together with turnaround-placement geometry.

This is more valuable than further audit at the moment, because:

- the support formula is already proved in the simple realization and audited
  through `n=9`,
- it is local in nature,
- and the new geometry probe now isolates a plausible extra datum:
  turnaround-distance-to-`1`.

## 7. Recommended Paper Framing

If we were forced to write the result package today, the clean framing would be:

### Main theorem

The weaker global floor theorem on the explicit 3-binary `{2,3}` sweep-shadow
class through `n=7`.

### Symbolic proposition

Coordinatewise relabeling invariance of forbidden interaction fraction, together
with the sweep/shadow equivariance route.

### Computational corollaries

- exact class-value table,
- assignment-stability through `n=7`,
- same-`n` comparison with valid coarse `FutureFc`.

### Explicit caveat

This is an explicit-family **shadow-side** obstruction theorem package, not yet
a universal subthreshold theorem.

## 8. Bottom Line

The obstruction branch now has:

- a paper-facing theorem statement,
- a symbolic core,
- a broader computational shell,
- and a precise statement of what remains open.

That is enough structure to continue serious proof work without wandering.
