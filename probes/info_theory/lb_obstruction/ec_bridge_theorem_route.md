# EC Bridge Theorem Route

Date: April 6, 2026

This note records the cleanest current route from the EC support theorems to the
weak global EC bridge law.

## 1. Current ingredients

The EC side now has four pieces:

1. **Canonical overlap law**
   `E_conf = 2(n-3)` on the canonical BAF family.

2. **Broader BAF support theorem**
   `ConfState` is the complement of the two turnarounds and their immediate
   successors.

3. **Canonical subtraction formula**
   `chi_conf = chi_good - chi_exc`.

4. **Weak global EC bridge law**
   On the tested BAF family through `n=8`,
   `ForbidFrac_{n-2}(chi_conf) >= 37/324`.

## 2. The actual theorem gap

The weak bridge law is still presented as a computational theorem candidate.

The symbolic gap is now very specific:

> explain why the conflict-state indicator `chi_conf`, whose support is the
> complement of four distinguished states in the good cycle, must retain a
> positive amount of forbidden width-`n-2` mass.

So the bridge theorem is no longer about discovering the right object. It is
about understanding the spectral effect of removing the four exceptional states
from `chi_good`.

## 3. New route correction: support geometry alone is too coarse

The first version of Route A was still too optimistic. The broader BAF support
theorem shows that `chi_conf` always has the same **coarse** support shape:

- two long arcs of the good cycle,
- with exactly four exceptional steps removed.

But that coarse description does **not** determine the forbidden fraction.

The new probe

- `ec_bridge_geometry_probe.py`

shows two negative facts:

1. on the simple two-turnaround BAF family through `n=9`, every tested word has
   the same normalized turnaround-gap class `(n,n)`, but the forbidden
   fractions of `chi_conf` still vary,
2. on the full valid-fiber minima through `n=5,6,7`, the same gap class still
   produces multiple distinct minima.

So a bridge theorem phrased only as

> “indicator of two arcs with four deleted boundary states”

is too coarse.

The missing datum is word-level geometry: where the two turnaround neighborhoods
sit relative to the anchored binary block and the induced good-cycle embedding.

There is now also a first positive candidate for that datum:

- on the simple two-turnaround BAF family through `n=9`,
- and on the full valid-fiber minima through `n=7`,

the observed value of `ForbidFrac_{n-2}(chi_conf)` is constant once one fixes
the cyclic distance from the turnaround vertex to the **middle binary
processor** `1`.

So the smallest currently plausible invariant is not the coarse gap class, but
the **turnaround-distance-to-1** invariant.

There is also a plausible symbolic explanation for this collapse:

- after anchoring the consecutive binary triple at `{0,1,2}`,
- reflection in the middle binary processor `1`,
  `rho(i) = 2 - i (mod n)`,
  preserves the anchored family,
- and this reflection sends a turnaround at vertex `v` to a turnaround at the
  unique vertex `v'` with the same cyclic distance from `1`.

So the first genuine symmetry route on the EC bridge side is now:

> equality within a distance-to-`1` class should come from reflection symmetry
> fixing the middle binary processor.

This reduction is now packaged explicitly in:

- `ec_distance_class_reduction.md`.

On the solved small range `n=5,6,7`, the full valid-fiber minima already match
the simple representative in each distance class, so this reduction is not just
model-family bookkeeping; it already captures the tested class minima.

The representatives are now explicit:

- `W_d = W_{1+d}`,
- with
  `W_v = [0,1,...,v, v-1,...,0, n-1,...,v, v+1,...,n-1]`.

So the next EC bridge problem is genuinely finite-dimensional:
understand `ForbidFrac_{n-2}(chi_conf(W_d))` as a function of `n` and `d`.

There is now also a first coefficient-level route:

- `ec_mask_family_route.md`

shows that on the tested representative range `n=5..9`, one tiny anchored
forbidden mask already has positive ANOVA energy for every `W_d`.

And this has now been sharpened further:

- `ec_basis_coefficient_route.md`

isolates one explicit product basis vector `Psi_d` on that support whose inner
product with `chi_conf(W_d)` is already nonzero on the tested range through
`n=11`.

This is now upgraded again:

- `ec_basis_coefficient_theorem.md`

gives an exact closed-form formula for `<chi_conf(W_d), Psi_d>` together with
its sign pattern.

Important lift obstruction:

- this exact coefficient theorem is currently a theorem on the reduced
  representative family `W_d`,
- but it does **not** lift verbatim to the full tested BAF fibers.

On the small full-fiber checks:

- for `n=5,6,7`, the same coefficient can flip sign across valid goods in the
  same distance class,
- and at `n=6`, distance class `d=2`, every simple local product basis choice
  on the same support fails somewhere.

So the representative theorem is real, but the full-class lift must be
support-level rather than coefficient-rigid.

This next bridge direction is now recorded in:

- `ec_support_lift_route.md`.

And the first actual lift theorem is now recorded in:

- `ec_smallrange_support_lift_theorem.md`,

which proves on the solved small range `n=5,6,7,8,9` that the full tested BAF
class already has class-stable tiny forbidden supports.

The candidate mask family is:

- `d=0`: delete `{1}`,
- `d>0` even: delete `{1,d+1}`,
- `d` odd: delete `{0,d+1}` or `{2,d+1}`.

So the next theorem target can now be phrased much more sharply:

> use the exact formula for `<chi_conf(W_d), Psi_d>` to prove positivity of the
> forbidden energy on the candidate support for every distance class `d`.

Another route correction is now clear:

- the finite-range constant `37/324` was a useful local theorem candidate,
- but it is not the right asymptotic target.

On the representative family at `n=10`, the computed values are already:

- `d=0`: `0.091306584362`
- `d=1`: `0.110368084134`
- `d=2`: `0.110039437586`
- `d=3`: `0.111825560128`
- `d=4`: `0.108439071788`
- `d=5`: `0.112354252401`

So the minimum is already below `37/324 ≈ 0.114198`.

That means the right symbolic target is now:

- positivity of the EC bridge witness,
  or
- an explicit `n`-dependent lower bound,

not a universal constant across all `n`.

## 4. Refined proof routes

### Route A. Support-plus-placement geometry

Use the support theorem directly:

- `chi_conf` is the indicator of a set of `2n-4` distinguished good-cycle
  states,
- those states occur in two long arcs of the good cycle,
- the four removed exceptional states form a sparse correction,
- and the forbidden fraction depends on how the turnaround neighborhoods are
  placed relative to the binary block.

Potential theorem shape:

> for this support-plus-placement geometry, the width-`n-2` forbidden fraction
> is bounded below by an explicit positive quantity.

This route still avoids comparison with `chi_good`, but it can no longer ignore
turnaround placement.

### Route B. Perturbative cycle-indicator route

Use

`chi_conf = chi_good - chi_exc`.

Then try to show:

1. `chi_good` already carries substantial forbidden mass on the BAF family,
2. subtracting the four-state indicator `chi_exc` cannot destroy all of it.

This is conceptually attractive, but may require delicate control because
forbidden fractions are ratios, not linear functionals.

## 5. Recommended route

At present, Route A still looks better, but only in its refined form.

Reason:

- the support theorem is now explicit and local,
- the bridge theorem should still be stated in geometric language,
- but the new probe shows the geometry must include turnaround placement,
- and the perturbative route risks getting stuck on ratio bookkeeping.

So the next proof sprint should aim at:

> positivity, or an explicit `n`-dependent lower bound, for the forbidden
> width-`n-2` mass attached to the BAF support geometry together with the
> turnaround-placement data.

## 6. Immediate next steps

1. Rewrite the weak bridge theorem in support-plus-placement language:
   not just “for `chi_conf`,” but
   “for indicators of the BAF conflict-state geometry with anchored turnaround
   placement.”
2. Mine the simple two-turnaround BAF family for the smallest placement datum
   that controls the forbidden fraction.
   Current best candidate: cyclic distance from the turnaround vertex to
   processor `1`.
3. Use that datum to reduce the bridge theorem to a finite placement-class
   analysis.
4. Use the anchored mask family on `W_d` to prove nonvanishing of one forbidden
   coefficient per distance class.
5. Only after that, revisit the perturbative route via `chi_good - chi_exc`.

## 7. Bottom Line

The EC bridge theorem is **not** just a support-geometry theorem in disguise.

It is a support-plus-placement theorem, and at the coefficient level it now
looks like a nonvanishing theorem for one tiny anchored forbidden mask per
distance class.

That is the right object to prove next.
