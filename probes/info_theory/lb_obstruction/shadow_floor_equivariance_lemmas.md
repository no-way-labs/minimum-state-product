# Sweep/Shadow Equivariance Lemma Plan

Date: April 6, 2026

This note unpacks Proposition 3.1 of
`shadow_floor_theorem.md` into a Lean-facing lemma chain tied to the actual
construction primitives in `docs/verify_lower_bound.py`.

The goal is to replace the current proof sketch

> “the canonical sweep and induced shadow cycle commute with coordinatewise
> ternary relabeling”

by a finite sequence of tautological lemmas.

## 1. Objects

Fix:

- a state vector `ms in {2,3}^n` with exactly three binary processors,
- the ternary index set `T = {i | ms[i] = 3}`,
- two ternary assignments `epsilon, epsilon' : T -> {1,2}`.

Define the coordinatewise relabeling

`tau_{epsilon -> epsilon'} : Config(ms) -> Config(ms)`

by:

- identity on every binary coordinate,
- on ternary coordinate `j`:
  - identity if `epsilon(j) = epsilon'(j)`,
  - swap `1 <-> 2` if `epsilon(j) != epsilon'(j)`.

We want to show that `tau` commutes with:

1. `construct_sweep_cycle`,
2. `check_cycle_consistency`,
3. `find_shadow_cycle`.

## 2. Sweep Equivariance

### Lemma 2.1. Coordinatewise relabeling preserves the zero state.

For every configuration `c`, if `c_j = 0`, then

`tau(c)_j = 0`.

This is immediate because `tau_j` only swaps `1` and `2` on ternary
coordinates and is identity on binary ones.

### Lemma 2.2. Coordinatewise relabeling sends the chosen nonzero sweep value to the new chosen value.

For ternary `j`,

`tau_j(epsilon(j)) = epsilon'(j)`.

Again immediate from the definition of `tau_j`.

### Lemma 2.3. `construct_sweep_cycle` commutes with relabeling.

Let `C_epsilon` be the cycle produced by

`construct_sweep_cycle(ms, n, epsilon, up_order, down_order)`.

Then, whenever the construction succeeds,

`map tau C_epsilon = C_{epsilon'}`.

#### Proof skeleton

`construct_sweep_cycle` is built by starting from the all-zero configuration and
performing a deterministic list of single-site updates:

- binary processor `p`: `0 -> 1` on the up pass, `1 -> 0` on the down pass,
- ternary processor `p`: `0 -> epsilon(p)` on the up pass, `epsilon(p) -> 0` on
  the down pass.

By Lemma 2.1 and Lemma 2.2, `tau` sends each step of the `epsilon` construction
to the corresponding step of the `epsilon'` construction. Induct on the sweep
path length.

## 3. Consistency / Determined-Entry Equivariance

### Lemma 3.1. Single-mover property is preserved by relabeling.

If two configurations differ in exactly one coordinate, then their `tau`-images
differ in exactly the same coordinate.

This holds because each coordinate map `tau_i` is bijective.

### Lemma 3.2. Local context equality is preserved by relabeling.

For every processor `p`,

`(L,S,R) = (L',S',R')` iff
`(tau(L), tau(S), tau(R)) = (tau(L'), tau(S'), tau(R'))`

coordinatewise.

### Lemma 3.3. `check_cycle_consistency` commutes with relabeling.

If `check_cycle_consistency(C_epsilon)` succeeds with determined table `det`,
then `check_cycle_consistency(C_{epsilon'})` succeeds with the transported table
`tau_*(det)`.

Here `tau_*(det)` is obtained by relabeling every local input/output tuple in
`det` coordinatewise.

#### Proof skeleton

The consistency checker only uses:

- the single-mover property,
- equality of local contexts,
- and equality of required outputs on repeated local contexts.

These are preserved by Lemma 3.1 and Lemma 3.2.

## 4. Forced-Move Equivariance

### Lemma 4.1. Forced privilege is preserved by relabeling.

Let `det' = tau_*(det)`. For every configuration `c` and processor `p`,

`p` is forced-privileged at `c` under `det`
iff
`p` is forced-privileged at `tau(c)` under `det'`.

### Lemma 4.2. Forced successors commute with relabeling.

If firing processor `p` takes `c` to `c'` under `det`, then firing the same
processor `p` takes `tau(c)` to `tau(c')` under `det'`.

These are direct from the definition of transported local entries.

## 5. Shadow-Path Equivariance

The subtle point is `find_shadow_cycle`, because it is an algorithm, not just a
set definition. But its choice rule is still deterministic:

1. scan processors in increasing index order,
2. list all forced moves,
3. take the first forced move whose successor stays outside the good set.

### Lemma 5.1. Good-set membership is preserved.

`c in C_epsilon` iff `tau(c) in C_{epsilon'}`.

This is immediate from Lemma 2.3.

### Lemma 5.2. “First escaping forced move” is preserved.

If `find_shadow_cycle` at configuration `c` chooses processor `p` and successor
`c'`, then at `tau(c)` it also chooses processor `p` and successor `tau(c')`.

#### Proof skeleton

By Lemma 4.1 and Lemma 4.2, the forced-move list at `tau(c)` is exactly the
transport of the forced-move list at `c`, in the same processor order. By
Lemma 5.1, the predicate “successor lies outside the good set” is preserved.
So the first processor in index order satisfying the escape test is unchanged.

### Lemma 5.3. `find_shadow_cycle` commutes with relabeling.

Whenever `find_shadow_cycle(det, C_epsilon)` returns shadow path `S_epsilon`,

`map tau S_epsilon = S_{epsilon'}`.

#### Proof skeleton

Induct on the shadow walk. Use Lemma 5.2 at each step.

#### Computational check

The script `shadow_equivariance_check.py` verifies this exact algorithmic
commutation on all tested explicit shadow-floor classes through `n=7`, with
zero failures.

## 6. Final Corollaries

### Corollary 6.1. Shadow indicator transport.

`chi_{m,epsilon'} = chi_{m,epsilon} ∘ tau^{-1}`.

### Corollary 6.2. Assignment-invariance within a binary-placement class.

By Corollary 6.1 and relabeling invariance of forbidden fraction,

`ForbidFrac_{n-2}(chi_{m,epsilon}) = ForbidFrac_{n-2}(chi_{m,epsilon'})`.

So one representative assignment per binary-placement class suffices.

## 7. Why This Is Lean-Compatible

This decomposition is well matched to Lean:

- every lemma is finite and local,
- no ANOVA machinery enters until the final invariance statement,
- the construction primitives are deterministic recursive functions,
- and the only nontrivial induction is the shadow-path induction in Lemma 5.3.

The main remaining formal burden is to define the transported table `tau_*(det)`
and to state the good-cycle / shadow-cycle functions in a way that makes their
determinism visible to Lean.
