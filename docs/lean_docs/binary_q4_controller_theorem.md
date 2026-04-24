# Binary Q4 Controller Theorem

This note isolates the static binary `n=4` theorem that should replace the
heavy `native_decide` core of `LB2222`.

The goal is to prove, by hand, that the binary obstruction-free world admits
only controller complexity `<= 2`.

## Setting

Consider a fair simple balanced binary mover word

`w = w_0 ... w_7`, `w_t ∈ {0,1,2,3}`

on the ring `C4`, with each processor appearing exactly twice.

For each processor `j`, let `p_t ∈ (Z/2)^4` be the prefix parity vector before
time `t`.

Define the local signature

`sig_j(t) = (p_t[left(j)], p_t[j], p_t[right(j)])`.

This is the binary TF context for `j`, ignoring the antipodal bit.

## Symbolic conflict criterion

### Lemma 1

If there exist `t < u` and `j` such that

- `sig_j(t) = sig_j(u)`, and
- exactly one of `w_t, w_u` equals `j`,

then the word forces a TF conflict for processor `j`.

This is the basic symbolic detection lemma.

## Word normal form target

We want:

### Theorem A

If `w` is fair, simple, balanced, and has no symbolic TF conflict, then

`w = σσ`

where `σ` is cyclic or reverse-cyclic.

## Current proof decomposition

The current best route is:

### Lemma 2: permutation-halves

No symbolic conflict implies the first four moves are all distinct.
Hence

`w = σ τ`

with `σ, τ` permutations of `{0,1,2,3}`.

Status:
- reduced to a much smaller obstruction problem

Current best reduction:
- simple words kill adjacent first-half repeats
- simple words also kill the alternating pattern `abab`
- therefore any non-distinct first half is forced into one of three forms:
  - `abac`
  - `abca`
  - `abcb`

### Lemma 3: adjacent-antipodal obstruction

If `σ` contains consecutive `anti(j), j`, then `σσ` has a symbolic conflict.

Reason:
- firing `anti(j)` does not change `sig_j`
- so the same signature appears before `anti(j)` and before `j`
- `j` is non-mover at the first and mover at the second
- apply Lemma 1

Status:
- conceptually done

### Lemma 4: no adjacent antipodal pair on `C4`

For a permutation `σ` of `C4`, if no adjacent pair is antipodal, then `σ` is
cyclic or reverse-cyclic.

Status:
- conceptually done

### Lemma 5: second-half agreement

If `w = σ τ` has no symbolic conflict, then `τ = σ`.

This is the only genuinely hard remaining gap.

## Current reduction of Lemma 5

Two simplifications are already known:

1. If `τ` is not cyclic/reverse-cyclic, then it has an adjacent antipodal pair,
   so the same local obstruction as Lemma 3 kills it.
2. Therefore only the 7 cyclic/reverse-cyclic permutations `τ != σ` remain.

The current best reduction is:

1. normalize `σ = (0,1,2,3)` by dihedral symmetry
2. record the only first-half nonmover signatures that matter:
   - processor `0`: `010`, `011`
   - processor `1`: `110`, `111`
   - processor `2`: `110`
3. observe that every cyclic/reverse-cyclic `τ` is a forward or reverse sweep
4. compute the second-half mover signatures:
   - forward sweep: `111, 011, 011, 010`
   - reverse sweep: `111, 110, 110, 010`
5. use a small placement argument:
   - forward sweep with start `a != 0` forces either processor `1` to move on
     `111` or processor `0` to move on `011`
   - reverse sweep forces either processor `1` or `2` to move on `110`, or
     processor `1` to move on `111`

Each of those signatures already occurred for that processor as a nonmover in
the first half, so Lemma 1 gives conflict.

Thus the only conflict-free second half is the identical forward sweep
`τ = σ`.

This is no longer a raw 7-case check. It is a small normalized family
reduction into two sweep-shape lemmas.

Current formalization status:

- a scratch Lean file now contains
  - the adjacent-repeat simplicity obstruction
  - the `abab` simplicity obstruction
  - the first-four repeat-shape theorem for simple words
  - the adjacent-antipodal symbolic-conflict theorem
  - the local relative-position classification on `Proc4`
  - the `C4` combinatorial theorem turning “no adjacent antipodal pair” into
    forward/reverse sweep form
  - the full normalized forward-sweep mismatch family
  - the full normalized reverse-sweep family
  - rotation invariance of `sigConflict4`
  - generic rotated sweep-word theorems

Concretely, [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean) now contains:

- `sigConflict4_forwardSweepFrom0_of_ne_p0`
- `sigConflict4_reverseSweepFrom0`
- `forwardSweepWord4_eq_rot`
- `reverseSweepWord4_eq_rot`
- `sigConflict4_forwardSweepWord4_of_ne`
- `sigConflict4_reverseSweepWord4`
- `Proc4_rel_cases`
- `sweep_or_reverse_of_distinct_no_adjacent_anti`
- `not_simple_of_adjacentRepeat4_before_end`
- `not_simple_of_abab_before_end`
- `first_four_repeat_shape_of_simple`

So the second-half disagreement family is no longer just a note-level
classification. It is already packaged in Lean for arbitrary forward/reverse
sweep words, modulo the earlier permutation-halves and cyclic/reverse-cyclic
reductions.

So the remaining static binary work is no longer “formalize from scratch,” but
“eliminate the residual `abac` / `abca` / `abcb` forms and then connect the
current scratch-theorems to permutation-halves.”

## Controller corollary

Once Theorem A is proved, the projection theorem is immediate:

### Theorem B

If `w = σσ` with `σ` cyclic or reverse-cyclic, then for any forgotten
processor `p`:

1. the forgetful projection has exactly two repeated shadows
2. those two shadows are complementary
3. both carry the same mover set `{p, succσ(p)}`

Hence the repeated-shadow controller is deterministic of size `2`.

This is the binary `controller complexity <= 2` theorem.

## What remains

The binary side is conceptually close to done. The only real unresolved step is
now the exclusion of the residual `abac` / `abca` / `abcb` first-half repeat
forms, which is the last content of permutation-halves. After that, the current
scratch lemmas already cover the rest of the static normal-form route.

Everything else now looks like straightforward formalization work once the right
representation of words, prefix parities, and signatures is fixed.
