# Review Packet V2: Obstruction Program

Date: April 6, 2026

## Executive Summary

This packet updates the obstruction-side information-theory program for the
lower bound.

The main change since the first packet is conceptual:

> the obstruction program is now explicitly **two-track**:
> 1. a **shadow-side** track,
> 2. an **entry-conflict (EC)** track.

This matters because the two mechanisms appear to require **different
observables** at the raw level:

- the shadow side is naturally detected by width-`n-2` forbidden interaction
  mass,
- the EC side is naturally detected by zero-error / confusability overlap, not
  by the same forbidden-mass observable.

However, the current branch has now uncovered a partial bridge:

- a **derived global EC witness** can again have substantial nonzero
  width-`n-2` forbidden mass.

So the likely endgame is still a **disjunctive
witness theorem**:

> every subthreshold system yields either an EC witness or a shadow witness.

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

The current mathematical lower bound is driven by two main obstruction
mechanisms:

1. **entry conflict (EC)**
2. **shadow / bad-cycle obstruction**

The goal of this branch is to see whether these mechanisms admit an
information-theoretic reformulation that could support a lower-bound proof.

## 2. Common Quantities

### 2.1 Shadow-side quantity

For a scalar `f` on the full configuration space, define

`ForbidFrac_{n-2}(f)`

to be the width-`n-2` forbidden interaction fraction from the exact ANOVA
decomposition.

This is the main quantity on the shadow side.

### 2.2 EC-side quantity

For a good cycle and processor `p`, define:

- mover-context set `M_p`,
- non-mover-context set `N_p`,
- overlap count

`ov_p = |M_p ∩ N_p|`.

Define the total EC witness

`E_conf = Σ_p ov_p`.

This is the main quantity on the EC side.

There is now also a second EC-side quantity of interest:

- the **conflict-state indicator** `chi_conf`, a derived global EC witness on
  the good cycle.

## 3. Shadow-Side Result

### Main preliminary theorem

For the explicit 3-binary `{2,3}` sweep-shadow families through `n=7`, the
shadow indicator `chi` satisfies

`ForbidFrac_{n-2}(chi) >= 71/504 > 0.1408`.

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

### Symbolic core

1. coordinatewise relabeling preserves `ForbidFrac_w`,
2. the explicit sweep/shadow family should be equivariant under ternary
   relabeling,
3. therefore assignment-invariance follows.

Important scope note:

- the explicit shifted-waterfall formulas are currently proof-ready for a
  **canonical** binary placement,
- the broader placement classes are still computationally certified shell.

## 4. EC-Side Result

### Main preliminary theorem

On the canonical BAF family with consecutive binary triple `{0,1,2}`,

`E_conf = 2(n-3)`.

So the EC witness is strictly positive for every `n >= 5`.

### Broader tested theorem candidate

For all tested non-sweep `fc=2` words in the same consecutive-binary setting,
the computational evidence suggests the stronger law

`E_conf = 2(n-3)`

through `n=9`.

Tested minima:

- `n=5`: `4`
- `n=6`: `6`
- `n=7`: `8`
- `n=8`: `10`
- `n=9`: `12`

### Broader support theorem

The support of the derived global EC witness `chi_conf` is now organized by a
broader BAF theorem:

- if the turnaround steps are `t_1, t_2`,
- then `ConfState` is exactly the complement of
  `{g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`.

This statement has been audited on every tested non-sweep `fc=2` BAF word
through `n=9`, and is now written as a theorem package in
`ec_baf_support_theorem.md`.

### Derived global EC bridge object

Let `chi_conf` be the indicator of the good-cycle states that participate in an
EC overlap witness.

On the tested non-sweep `fc=2` BAF family, `chi_conf` has substantial positive
width-`n-2` forbidden mass:

- `n=5`: minima in `0.115741 .. 0.166667`
- `n=6`: minima in `0.129630 .. 0.175926`
- `n=7`: minima in `0.129012 .. 0.153086`
- `n=8`: minima in `0.114198 .. 0.135802`

So the EC side may reconnect to the same forbidden-mass observable used on the
shadow side, but only after passing to a **derived global** witness rather than
the raw local overlap count.

On the tested non-sweep `fc=2` BAF family through `n=8`, this yields a weak
global bridge law:

`ForbidFrac_{n-2}(chi_conf) >= 37/324 > 0.1141`.

### Canonical structural relation

On the canonical BAF family,

`chi_conf = chi_good - chi_exc`,

where `chi_exc` is the indicator of the four distinguished turnaround/endpoint
states.

So the EC bridge object is literally the good-cycle indicator with four
exceptional states removed.

In particular, `chi_conf` remains on the same spectral scale as `chi_good`:

- `chi_good` forbidden fractions:
  `0.136111, 0.121914, 0.120811, 0.115226, 0.108406` for `n=5..9`
- `chi_conf` forbidden fractions:
  `0.115741, 0.131944, 0.137037, 0.125857, 0.118313`

### Word-level support geometry

For the tested non-sweep `fc=2` BAF family through `n=8`, the support of
`chi_conf` appears to have a simple word-level description:

- if the two turnaround steps are `t_1` and `t_2`,
- then the non-conflict states are exactly the four good-cycle states
  at indices
  `{t_1, t_1+1, t_2, t_2+1}` modulo `2n`,
- and every other good-cycle state lies in `ConfState`.

So the EC bridge object is now much more structured than just an arbitrary
derived set.

### Key structural lesson

The naive full-space EC overlap scalar is width-3 local, hence has

`ForbidFrac_{n-2} = 0`.

So the EC side is **not** naturally captured by the same forbidden-mass
observable as the shadow side at the raw level.

But the derived global EC witness `chi_conf` already has substantial nonzero
forbidden mass on the tested BAF family, so the two tracks may partially
reunify at the level of derived global witnesses.

## 5. The New Branch Picture

The obstruction program now looks like this:

### Shadow track

- witness: shadow indicator or related bad-set witness
- observable: forbidden width-`n-2` interaction mass

### EC track

- witness: overlap / confusability witness such as `E_conf`
- observable: zero-error / confusability complexity
- possible bridge observable: forbidden mass of a derived global witness such as
  `chi_conf`

### Likely universal theorem shape

Not

> one scalar witness measured by one common observable

but rather

> every subthreshold system yields either
> - an EC witness with positive EC-side complexity,
> - or a shadow witness with positive forbidden mass.

## 6. What Is Symbolic vs Computational

### Currently symbolic

- shadow-side relabeling invariance of forbidden fraction
- the sweep/shadow equivariance route
- the EC witness formulation
- the canonical BAF overlap proof idea

### Currently computationally certified

- exact shadow-floor class values through `n=7`
- tested floor `>= 71/504`
- same-`n` shadow-vs-valid gap
- tested EC law `E_conf = 2(n-3)` through `n=9`
- tested positive forbidden-mass bridge for `chi_conf` through `n=8`

## 7. What This Does Not Yet Prove

This does **not** yet prove the lower bound.

Specifically, it does not yet show:

- that every subthreshold system exhibits the shadow obstruction,
- or that every subthreshold system exhibits the EC obstruction,
- or that one of them must occur universally.

So the current state is:

- strong explicit-family obstruction packages on both sides,
- but no universal bridge theorem yet.

## 8. The Bridge Problem

The central open question is now:

> Can the explicit shadow and EC witnesses be lifted to a universal witness
> theorem for arbitrary subthreshold systems?

There are three plausible routes:

1. **Universal witness extraction**
   define a canonical witness for arbitrary subthreshold systems,
   and show the explicit model cases are special cases;

2. **Reduction / normalization**
   reduce arbitrary subthreshold systems to explicit obstruction-bearing forms;

3. **Disjunctive theorem**
   prove directly that every subthreshold system yields either an EC witness or
   a shadow witness.

At present, the disjunctive theorem looks most realistic.

## 9. What Review Is Most Useful Now

The most useful feedback now is not:

- “are these explicit-family computations interesting?”

but:

- is the **two-track / two-observable program** the right shape?
- is the **disjunctive witness theorem** the right universal target?
- which bridge route looks most plausible:
  extraction, reduction, or direct disjunction?

## 10. Bottom Line

We now have:

1. a shadow-side explicit-family obstruction theorem package,
2. an EC-side explicit-family obstruction theorem package,
3. a clear reason they likely need different observables,
4. and a plausible universal target:
   a disjunctive EC-or-shadow witness theorem.

That is enough structure to review seriously as a lower-bound program, even
though the universal theorem itself is still open.
