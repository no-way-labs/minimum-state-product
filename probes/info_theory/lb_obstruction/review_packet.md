# Obstruction Review Packet

Date: April 6, 2026

## Executive Summary

We are investigating a new lower-bound obstruction for self-stabilizing token
rings, framed in information-theoretic language.

The current strongest preliminary result is an **explicit-family obstruction
theorem candidate**:

> For a broad explicit class of subthreshold systems built from 3 binary
> processors and ternary fill, the indicator of the associated shadow cycle has
> large width-`n-2` forbidden interaction mass.

More concretely, on all tested such families through `n = 7`, the forbidden
interaction fraction is at least

`71/504 > 0.1408`,

while the valid witness coarse-layer values at the same sizes are much smaller:

- `CUP-2(n=5)`: `0.026144`
- `CUP-2(n=6)`: `0.008582`
- `CUP-2(n=7)`: `0.002573`

So the tested subthreshold shadow families sit far above the valid
same-`n` coarse-layer regime.

This does **not** yet prove the full lower bound. It is an explicit-family
obstruction result with a real symbolic core and a broader computational shell.

## 1. Problem Setting

We study deterministic self-stabilizing token rings.

A system consists of:

- `n` processors on a directed cycle,
- processor `i` having `m_i` local states,
- and a local transition function

`f_i : [m_{i-1}] × [m_i] × [m_{i+1}] -> [m_i]`.

Processor `i` is privileged at a global configuration `c` when

`f_i(c_{i-1}, c_i, c_{i+1}) != c_i`.

A system is valid if:

1. there is a legitimate good cycle with exactly one privileged processor at
   each step,
2. from every configuration, every daemon schedule eventually reaches the good
   cycle.

The lower-bound problem asks for the minimum possible state product

`M_n = min Π_i m_i`

over valid systems.

The existing proof program for the lower bound is combinatorial
(shadow cycles, entry conflict, escape, wiggle-shadow, etc.). The present line
of work asks whether one can isolate an information-theoretic obstruction that
captures some of the same impossibility.

## 2. The Information-Theoretic Quantity

For a scalar `f` on the full configuration space, we compute its exact ANOVA
decomposition under the uniform product measure and ask how much `L^2` energy
lies on interaction supports forbidden by the width-`n-2` local window model.

Call the resulting ratio

`ForbidFrac_{n-2}(f)`.

Intuition:

- small forbidden fraction means `f` is almost entirely controlled by
  interaction modes visible to length-`n-2` windows,
- large forbidden fraction means `f` retains substantial genuinely nonlocal
  dependence.

For the valid witness families, the strongest coarse-layer object found so far
is `FutureFc`, the maximum frontier count reachable from a bad configuration.
Its forbidden fraction is tiny.

## 3. The Explicit Shadow-Family Obstruction

### 3.1 The family

Consider state vectors in `{2,3}^n` with exactly three binary processors and
all remaining processors ternary.

For such a vector:

- choose a canonical uniform sweep good cycle,
- determine the forced mover entries from that sweep,
- build the associated shadow cycle through non-good configurations.

Define the shadow indicator

`chi(c) = 1[c belongs to the shadow cycle]`.

This is the obstruction-side scalar studied here.

### 3.2 Main preliminary theorem candidate

For every tested explicit 3-binary `{2,3}` sweep-shadow family at
`n = 5,6,7`, and every tested ternary assignment, the shadow indicator satisfies

`ForbidFrac_{n-2}(chi) >= 71/504 > 0.1408`.

This is the current best explicit-family obstruction statement.

### 3.3 Exact class values

Through `n = 7`, the tested class-by-class values are:

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

The minimum among all these tested values is `71/504`.

## 4. Same-`n` Comparison With Valid Witnesses

The point is not merely that the obstruction values are “nonzero.” The point is
that they are separated by a large same-`n` gap from the valid coarse witness
regime.

Valid witness coarse-layer references:

- `CUP-2(n=5)`: `ForbidFrac_3(FutureFc) = 0.026144`
- `CUP-2(n=6)`: `ForbidFrac_4(FutureFc) = 0.008582`
- `CUP-2(n=7)`: `ForbidFrac_5(FutureFc) = 0.002573`

So on the tested sizes:

- explicit shadow-family obstruction values are all `> 0.1408`,
- valid coarse-layer values are all `< 0.027`,
- and in fact decay quickly with `n`.

This is why the shadow-floor class is interesting as a lower-bound obstruction
candidate.

## 5. Symbolic Core

The current symbolic core has two parts.

### 5.1 Relabeling invariance of forbidden fraction

If `tau` is a coordinatewise relabeling of the state sets, then for every scalar
`f`

`ForbidFrac_w(f ∘ tau) = ForbidFrac_w(f)`.

This part is a genuine short proof: coordinatewise relabelings preserve the
uniform product measure and preserve ANOVA support subspaces support-by-support.

### 5.2 Assignment-invariance by equivariance

Within a fixed binary-placement class, changing the ternary assignment means
swapping `1 <-> 2` on some ternary coordinates.

The intended symbolic route is:

1. the canonical sweep cycle transports under these coordinatewise relabelings,
2. the associated explicit shadow family transports as well,
3. therefore the shadow indicator transports,
4. so its forbidden fraction is assignment-invariant.

This is the right conceptual explanation for why all tested ternary assignments
in a fixed class give the same forbidden fraction.

## 6. Important Scope Correction

There is an important distinction between:

1. the **canonical symbolic core**,
2. the **broader tested explicit-family shell**.

The explicit shifted-waterfall shadow formulas currently written down are
proof-ready for a canonical placement of the binary processors. The broader
tested placement classes are currently supported computationally, not yet by a
full symbolic normalization theorem.

So the current state is:

- canonical explicit shadow family: symbolic route identified,
- broader placement classes: computationally certified,
- normalization theorem from canonical to broader classes: still open.

## 7. What Is Actually Proved vs Certified

### Symbolically proved / cleanly argued

- relabeling invariance of forbidden fraction
- the correct proof route for assignment-invariance
- the scope split between canonical symbolic core and broader computational shell

### Computationally certified

- exact class values through `n=7`
- the floor `>= 71/504`
- same-`n` comparison with valid coarse witnesses
- transport of the returned canonical sweep cycles and returned shadow cycles
  under ternary relabelings on all tested classes through `n=7`

## 8. What This Does and Does Not Give

### What it gives

- a real explicit-family obstruction theorem candidate
- a large same-`n` separation from the valid coarse-layer regime
- a symbolic mechanism that plausibly explains the assignment stability

### What it does not yet give

- a universal lower-bound theorem for all subthreshold systems
- a proof that every subthreshold system must have a forbidden-mass floor
- a proof of the full lower bound for `M_n`

So this is best viewed as:

- a serious preliminary obstruction result,
- not yet the final lower-bound theorem.

## 9. Most Important Open Problems

1. Prove the sweep/shadow equivariance cleanly for the explicit shadow family.
2. Decide whether the first paper theorem should be:
   - the stronger exact class-value law,
   - or the weaker global floor law `>= 71/504`.
3. Find the right normalization theorem from the canonical symbolic core to the
   broader placement classes, or explicitly accept the broader class as
   computational shell only.
4. Most importantly: determine whether this explicit-family obstruction can be
   upgraded to a universal forbidden condition on subthreshold systems.

## 10. Bottom Line

The current best obstruction-side result is:

> On a broad explicit family of 3-binary `{2,3}` sweep-shadow systems through
> `n=7`, the shadow indicator has width-`n-2` forbidden interaction fraction at
> least `71/504`, far above the valid same-`n` coarse-layer regime.

This is a real and interesting lower-bound-facing obstruction package.
It is not yet universal, but it is now sharp enough to review seriously.
