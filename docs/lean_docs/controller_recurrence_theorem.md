# Controller-Reuse Recurrence Theorem

This note isolates the dynamic half of the controller-complexity program.

It is meant to be theorem-oriented rather than exploratory. The exploration log
contains the residue that led here; this file records the current candidate
definitions and theorem schemas.

## Motivation

The old small-`n` shadow-cycle proofs and the new controller-complexity route
appear to be the same mechanism at different resolutions.

Static side:
- low-state systems support only deterministic `2`-controllers on repeated
  shadows

Dynamic side:
- those `2`-controllers can be reused off-cycle
- the reused moves can close into a recurrent bad orbit

This note is about the dynamic side only.

## Candidate Definitions

Fix a system `sys`, a good cycle `G = ((c_t, m_t))`, and a processor `p`.

### 1. `p`-shadow

The `p`-shadow of a configuration is the projection forgetting the local state
at `p`.

### 2. Repeated-shadow controller

A repeated-shadow controller at `p` consists of:

- a finite set `S` of repeated `p`-shadows occurring on `G`
- a quotient `A` of the local state set at `p`
- a partial deterministic map

  `Ctrl : S × A -> Fin n`

such that for every good-cycle time `t` whose `p`-shadow lies in `S`, the mover
`m_t` depends only on:

- the repeated `p`-shadow of `c_t`
- the controller class of the local state `c_t[p]`

This is the static controller object imported from the good cycle.

### 3. Controller entry

A controller entry is a triple

`(s, a, i)` with `s ∈ S`, `a ∈ A`, `i = Ctrl(s,a)`.

### 4. Realization off-cycle

An off-cycle state `x` realizes the controller entry `(s,a,i)` if:

- `x` has `p`-shadow `s`
- the local state `x[p]` lies in controller class `a`
- mover `i` is enabled at `x`

### 5. Bad reuse region

A bad reuse region is a finite nonempty set `B` of off-cycle states such that:

- every `x ∈ B` realizes some controller entry coming from `G`
- if `x ∈ B` realizes `(s,a,i)`, then the successor `T_i(x)` is defined and
  also lies in `B`
- `B` is disjoint from the good cycle and from the legitimate/convergent target
  region

This is the controller-language version of the old “shadow cycle region.”

## Main Theorem Schema

### Theorem (Controller-Reuse Recurrence)

Let `sys` be a system and `G` a good cycle. Suppose:

1. there is a deterministic repeated-shadow controller `(S, A, Ctrl)` at some
   processor `p`
2. there is a bad reuse region `B` for this controller

Then the induced successor map on `B`

`F(x) = T_i(x)` where `x` realizes `(s,a,i)`

is a total deterministic self-map on a finite nonempty set. Therefore `F`
contains a directed cycle in `B`. Hence `sys` has a recurrent bad orbit and is
not convergent.

## Why This Formulation

This theorem is better than the slogan

- `controller complexity <= 2 -> bad orbit`

for two reasons:

1. recurrence on a finite deterministic map is trivial; the real mathematical
   work is constructing the bad reuse region
2. the theorem should isolate the reusable abstract mechanism, not hide the
   family-specific geometry needed to prove closure

So the correct decomposition is:

- abstract theorem: reuse-closed deterministic subsystem gives recurrence
- family-specific theorem: low-state repeated-shadow behavior generates such a
  subsystem

## Family-Specific Corollary Schema

### Corollary (2-Controller Recurrence)

If a sub-threshold family admits only controller complexity `<= 2` on the
relevant repeated shadows, and the determined good-cycle entries generate a bad
reuse region for those `2`-controllers, then the family is impossible.

This is the form that matches the product-72 `n=5` shadow theorems.

## Evidence from Product-72 Families

For the two `n=5` product-72 families:

- `(2,2,2,3,3)`
- `(2,2,3,2,3)`

the existing shadow-cycle analyses already appear to instantiate this theorem.

What the old proofs provide:

- a concrete good cycle
- a deterministic repeated-shadow `2`-controller
- a finite off-cycle bad region built from anti-sweep / repeated-shadow states
- soundness of reused mover entries
- closure of the bad region under those reused moves

So the old shadow theorem should be re-readable as a concrete proof that a bad
reuse region exists.

## Current Proof Obligations

The main open work is not the abstract recurrence theorem. It is:

1. define repeated-shadow controller / realization / bad reuse region cleanly
2. prove one family-specific closure theorem in these definitions
3. connect the static controller-complexity theorem to the dynamic bad-region
   theorem

The most natural pilot family is the product-72 `n=5` case, since the old
shadow-cycle arguments are already available.

## Current formalization status

The scratch Lean file
[ControllerReuse.lean](./lean/LeanMn/SmallN/ControllerReuse.lean)
now contains generic theorem-level versions of the abstract recurrence engine:

- `BadReuseRegion.reusedSucc`
- `BadReuseRegion.exists_recurrence_pair`
- `BadReuseRegion.exists_nontrivial_cycle`

So the dynamic side has crossed the same threshold as the static binary side:
the abstract mechanism is no longer only in notes. The remaining work is to
instantiate these definitions for concrete small-`n` families and connect them
to controller-complexity bounds.
