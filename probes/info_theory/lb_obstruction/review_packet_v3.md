# Review Packet V3: Obstruction Program

Date: April 6, 2026

## Executive Summary

This packet updates the obstruction-side information-theory program for the
lower bound after the first real theorem package on the EC side.

The branch now has three qualitatively different layers:

1. a **shadow-side explicit-family obstruction package**
2. an **exact EC representative theorem**
3. a **full-class EC support-lift theorem through `n=9`**

So the status is no longer:

> explicit examples plus route sketches

but rather:

> one exact EC theorem on a reduced family,
> one lifted EC theorem on the full tested class,
> and one remaining universal bridge problem.

The central open question is still the same:

> can these explicit EC and shadow witnesses be lifted to a universal
> EC-or-shadow obstruction theorem for arbitrary subthreshold systems?

## 1. Problem Setting

We study deterministic self-stabilizing token rings.

A system consists of:

- `n` processors on a cycle,
- processor `i` having `m_i` local states,
- local update rule

`f_i : [m_{i-1}] × [m_i] × [m_{i+1}] -> [m_i]`.

The lower-bound problem asks for the minimum state product

`M_n = min Π_i m_i`

over valid systems.

The current combinatorial lower-bound picture has two main obstruction
mechanisms:

1. **entry conflict (EC)**
2. **shadow / bad-cycle obstruction**

The goal of this branch is to find information-theoretic witnesses for those
obstructions.

## 2. Common Quantities

### 2.1 Shadow-side quantity

For a scalar `f` on the full configuration space, define

`ForbidFrac_{n-2}(f)`

to be the width-`n-2` forbidden interaction fraction from the exact ANOVA
decomposition.

This is the main shadow-side observable.

### 2.2 EC-side quantities

For a good cycle and processor `p`, define:

- mover-context set `M_p`,
- non-mover-context set `N_p`,
- overlap count

`ov_p = |M_p ∩ N_p|`.

Define the total EC witness

`E_conf = Σ_p ov_p`.

This is the raw zero-error / confusability quantity.

There is also a derived global EC witness:

- `chi_conf`, the indicator of good-cycle states participating in an EC overlap.

That derived witness is what reconnects the EC track to the forbidden-mass
observable.

## 3. Shadow-Side Package

### Main explicit-family theorem

For the explicit 3-binary `{2,3}` sweep-shadow families through `n=7`, the
shadow indicator `chi_shadow` satisfies

`ForbidFrac_{n-2}(chi_shadow) >= 71/504 > 0.1408`.

Same-`n` valid coarse-layer references:

- `CUP-2(n=5)`: `0.026144`
- `CUP-2(n=6)`: `0.008582`
- `CUP-2(n=7)`: `0.002573`

So the explicit shadow class sits far above the valid same-`n` coarse-layer
regime.

### Exact class values through `n=7`

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

### Symbolic status

Current symbolic pieces:

- coordinatewise relabeling preserves forbidden interaction fraction
- explicit sweep/shadow family is compatible with ternary relabeling
- assignment-invariance follows

Important scope note:

- the canonical symbolic formulas are best understood on a canonical binary
  placement
- broader placement classes are still computational shell

So the shadow side is still strongest as an explicit-family theorem package.

## 4. EC-Side Package

The EC side is now materially stronger than it was in the previous packet.

### 4.1 Raw EC law

On the canonical BAF family with consecutive binary triple `{0,1,2}`,

`E_conf = 2(n-3)`.

This is the first exact EC-side model theorem.

More broadly, the tested non-sweep `fc=2` BAF family still suggests the same
law through `n=9`.

### 4.2 Support theorem for the derived global witness

For the broader BAF family, if the turnaround steps are `t_1, t_2`, then

`ConfState = {all good-cycle states except g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`.

So the derived EC bridge object has explicit support geometry:

- two long arcs of the good cycle,
- with exactly four exceptional states removed.

### 4.3 Exact representative theorem

The EC branch now has a genuine exact theorem on a reduced family.

Reduce to the simple two-turnaround representatives `W_d`, where `d` is the
cyclic distance from the turnaround vertex to the middle binary processor `1`.

For each `W_d`, define the explicit product basis vector `Psi_d` on the
candidate support.

Then [ec_basis_coefficient_theorem.md](./lb_obstruction/ec_basis_coefficient_theorem.md) gives a closed-form formula for

`I_{n,d} = <chi_conf(W_d), Psi_d>`.

Exact sign pattern:

- `d=0`: positive
- odd `d`: positive
- even `d >= 2`: negative

So `I_{n,d} != 0` for every representative `W_d`, and the candidate forbidden
support already carries positive forbidden energy on every representative.

This is the first exact theorem on the EC bridge side beyond raw overlap.

### 4.4 Full-class support-lift theorem through `n=9`

The representative theorem does **not** lift coefficientwise verbatim to the
full tested BAF class.

But the right lift object turns out to be support-level, not coefficient-level.

The branch now has a full-class support theorem through `n=9`:

- `d=0`: complement `{1}`
- `d=1`: complement `{0,2}`
- even `d>=2`: complement `{1}`
- odd `d>=3`: complement `{0}` and, by reflection, `{2}`

This is proved/computationally certified in
[ec_smallrange_support_lift_theorem.md](./lb_obstruction/ec_smallrange_support_lift_theorem.md).

Representative exact values:

| n | distance class d | support complement | exact / class-stable value |
| --- | --- | --- | --- |
| 5 | 0 | `{1}` | `1/216` |
| 5 | 1 | `{0,2}` | `1/108` |
| 5 | 2 | `{1}` | `1/1296` |
| 6 | 0 | `{1}` | `7/5832` |
| 6 | 1 | `{0,2}` | `2/729` |
| 6 | 2 | `{1}` | `1/1944` |
| 6 | 3 | `{0}` or `{2}` | `1/1458` |
| 7 | 0 | `{1}` | `17/52488` |
| 7 | 1 | `{0,2}` | `4/6561` |
| 7 | 2 | `{1}` | `5/52488` |
| 7 | 3 | `{0}` or `{2}` | `1/8748` |
| 8 | 0 | `{1}` | `13/157464` |
| 8 | 1 | `{0,2}` | `1/6561` |
| 8 | 2 | `{1}` | `13/472392` |
| 8 | 3 | `{0}` or `{2}` | `2/59049` |
| 8 | 4 | `{1}` | `5/236196` |
| 9 | 0 | `{1}` | about `2.093365e-05` |
| 9 | 1 | `{0,2}` | `19/531441` |
| 9 | 2 | `{1}` | about `6.350658e-06` |
| 9 | 3 | `{0}` or `{2}` | about `7.526706e-06` |
| 9 | 4 | `{1}` | about `4.233772e-06` |

### 4.5 Why the `n=9` statement is honest

The support theorem through `n=9` is a full-class theorem, not just a
direct-family corollary.

[ec_word_family_audit.py](./lb_obstruction/ec_word_family_audit.py) reports:

- `n=9`: `tested=9`, `direct=9`, `missing=0`, `extra=0`

So the direct two-turnaround word family and the full tested BAF class still
coincide at `n=9`.

### 4.6 What changed from the previous packet

The previous packet still framed the EC side mainly as:

- a route,
- a candidate bridge law,
- a derived global witness.

That is now obsolete.

The correct current framing is:

- exact representative theorem
- support-level lift theorem through `n=9`
- next unresolved extension at `n=10`

## 5. What Is Actually Proved

At this point the branch has:

### Actually proved / theorem-packaged

- shadow-side explicit-family floor theorem package through `n=7`
- EC raw canonical overlap law
- EC support theorem for `chi_conf`
- exact EC representative coefficient theorem
- EC support-lift theorem through `n=9`

### Computationally certified but not yet lifted universally

- broader shadow placement shell
- direct-family/full-class audits at the tested sizes
- EC support-pattern persistence only through the tested range

## 6. What This Does Not Yet Prove

This still does **not** prove the lower bound.

Specifically, we do not yet have:

- a universal theorem saying every subthreshold system yields one of these
  witnesses
- a universal EC-or-shadow disjunction
- or a system-level theorem connecting arbitrary subthreshold systems to the
  EC/shadow obstruction families

So the current state is:

- genuine theorem packages on explicit obstruction families,
- especially a significantly improved EC package,
- but still no universal bridge theorem.

## 7. The Actual Remaining Bridge Problem

The central open question is now sharper than before:

> can the explicit EC and shadow witness packages be lifted to a universal
> obstruction theorem for arbitrary subthreshold systems?

Right now the most realistic universal target looks like:

> every subthreshold system yields either
> - an EC witness with positive support-level forbidden mass,
> - or a shadow witness with positive forbidden mass.

That is stronger and more concrete than the earlier “maybe some common scalar
exists” framing.

## 8. Best Current Next Step

The next step is not more packet refinement. It is one of:

1. extend the EC support-lift pattern to `n=10`
2. prove the support family symbolically rather than only by computation
3. or return to the shadow side and try to build a lift theorem comparable to
   what now exists on the EC side

If the goal is pure lower-bound momentum, my recommendation is:

- keep pushing the EC support-lift pattern first,
- because that branch now has the strongest theorem-level traction.

## 9. Review Question

The right review question is no longer:

> do these explicit obstruction families look interesting?

It is now:

> given the exact EC representative theorem and the full-class EC support-lift
> theorem through `n=9`, what is the most plausible route to the universal
> EC-or-shadow bridge theorem?
