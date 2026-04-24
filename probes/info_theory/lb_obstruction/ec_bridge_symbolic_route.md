# EC Bridge Symbolic Route

Date: April 6, 2026

This note records the current best symbolic route from local entry conflict to a
global witness that can interact with the shadow-side forbidden-mass observable.

The key lesson from the EC branch so far is:

- the **raw** overlap count is too local,
- but a **derived global** EC quantity, the conflict-state indicator
  `chi_conf`, is already spectrally visible on the tested BAF family.

So the right symbolic route is no longer “measure overlap directly,” but
“globalize the overlap witness first.”

## 1. Objects

Fix a good cycle `C = (g_0, ..., g_{L-1})` and mover word `w`.

For processor `p`, define:

- mover-context set `M_p`,
- non-mover-context set `N_p`,
- overlap set `O_p = M_p ∩ N_p`.

Define the conflict-state set

`ConfState(C) = { g_t : exists p, local_triple_p(g_t) in O_p }`.

Define the indicator

`chi_conf(c) = 1[c in ConfState(C)]`.

This is the current best EC-side bridge object.

## 2. Why `chi_conf` is qualitatively different from raw overlap

The raw overlap scalar

`total_overlap(c) = Σ_p 1[local_triple_p(c) in O_p]`

is a sum of width-3 local terms, so it is invisible to the width-`n-2`
forbidden-mass observable.

But `chi_conf` is not a local function of one triple. It asks whether the whole
configuration is one of the globally designated conflict states along the good
cycle. This is a genuine globalization step.

That is why `chi_conf` can carry nonzero forbidden width-`n-2` mass even though
`total_overlap` cannot.

## 3. Symbolic theorem ladder

The current best ladder is:

### Step A. Local EC theorem

Prove a local overlap theorem such as:

> in the BAF family, every interior processor contributes two overlapping
> mover/non-mover contexts.

This is the current `E_conf = 2(n-3)` package.

### Step B. Conflict-state extraction theorem

Show that these local overlaps pick out a canonical set of global conflict
states along the cycle.

For the canonical BAF family, the conflict states are exactly the good-cycle
states in which one of the interior processors sits in the palindromic overlap
context.

### Step C. Global witness theorem

Show that `chi_conf` is the right EC-side global witness:

- invariant under the relevant symmetries,
- canonically extracted from the cycle,
- and spectrally visible.

### Step D. Family extension

Extend the above from the canonical BAF model case to the broader non-sweep
`fc=2` family, ideally first proving positivity and then any stronger exact law.

## 4. Why this matters for the universal program

If `chi_conf` is the right EC-side bridge object, then the likely universal
shape becomes:

- shadow track:
  explicit shadow indicator or a related bad-set witness,
- EC track:
  conflict-state indicator or a related globalized overlap witness.

This is much better than trying to force a purely local overlap scalar into the
same framework as the shadow side.

## 5. Immediate proof questions

1. Is `chi_conf` canonical enough beyond the canonical BAF family?
2. Can `ConfState(C)` be characterized intrinsically, without referring to the
   full list of overlap contexts one by one?
3. Does `chi_conf` admit any symmetry / relabeling reduction analogous to the
   shadow-side package?
4. Can one prove positivity of `ForbidFrac_{n-2}(chi_conf)` directly from the
   geometry of the conflict states, rather than only by computation?

## 6. Current best use

At present, `chi_conf` should be treated as:

- the leading EC-side bridge object,
- parallel to the shadow indicator on the shadow side,
- and the most promising candidate for a future disjunctive witness theorem.
