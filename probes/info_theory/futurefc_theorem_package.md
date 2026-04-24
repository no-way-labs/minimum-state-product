# FutureFc Theorem Package

Date: April 6, 2026

This note packages the strongest currently theorem-shaped `FutureFc` results
into explicit statements with proof status.

The goal is to separate:

- what is now a genuine proved lemma,
- what is an exact finite theorem certified by exhaustive verification,
- and what obstruction remains before the full two-level
  `FutureFc + slice-rank` suppression theorem can be proved symbolically.

## 1. Definitions

Fix a valid witness family `W_n` (`CUP-2(n)` or `Sol3(n)`) with bad
configuration set `Bad(W_n)`.

For `c in Bad(W_n)` define:

- `fc(c)`: frontier count,
- `FutureFc(c)`: the maximum `fc` value reachable from `c` by bad steps,
- `P(c) = (boundary6(c), tp(c))`, where
  - `boundary6(c) = (c_0, c_1, c_2, c_{n-3}, c_{n-2}, c_{n-1})`,
  - `tp(c) = (exp2(c), int21(c), exp2_weight(c))`.

The tuple `P(c)` is exactly the boundary plus the proof107 interior invariants
used elsewhere in the convergence architecture.

For interior starts `j = 2, ..., n-3` and cyclic indexing:

- `weight_pair_ab(c) = Σ_j j * 1[(c_j, c_{j+1}) = (a,b)]`,
- `count_lagd_ab(c) = Σ_j 1[(c_j, c_{j+d}) = (a,b)]`,
- `weight_lagd_ab(c) = Σ_j j * 1[(c_j, c_{j+d}) = (a,b)]`,
- `even_val_sum(c) = Σ_{j even, 2 <= j <= n-3} c_j`.

An exact prefix code for `FutureFc` on `W_n` is a feature tuple `B(c)` such
that

`P(c) = P(c') and B(c) = B(c')  =>  FutureFc(c) = FutureFc(c')`

for all bad configurations `c,c'`.

An exact axis-aligned tree decoder on `B` is a finite multiway decision tree
whose internal nodes query one coordinate of `B` and whose leaves return
`FutureFc`.

## 2. Two Analytic Lemmas

### Proposition 2.1. Lagged pair corrections are width-allowed coordinates.

For every lag `d >= 1` and pair type `(a,b)`, the features `count_lagd_ab` and
`weight_lagd_ab` lie in the additive contiguous-window space `V_w` for every
`w >= d+1`.

In particular:

- `count_lag2_11`, `weight_lag2_11` are in `V_w` for every `w >= 3`,
- `weight_lag3_11` is in `V_w` for every `w >= 4`.

#### Proof

For fixed `j`, the indicator

`1[(c_j, c_{j+d}) = (a,b)]`

depends only on the contiguous block

`(c_j, c_{j+1}, ..., c_{j+d})`,

which has width `d+1`. So both

- `count_lagd_ab(c) = Σ_j 1[(c_j, c_{j+d}) = (a,b)]`,
- `weight_lagd_ab(c) = Σ_j j * 1[(c_j, c_{j+d}) = (a,b)]`

are sums of width-`d+1` local window terms. By the local-feature subspace
theorem, each belongs to `V_w` for every `w >= d+1`. ∎

### Proposition 2.2. Exact finite codes admit finite decision-tree decoders.

Let `B = (b_1, ..., b_k)` be an exact prefix code for a finite target `T`.
Then `T` admits an exact multiway axis-aligned decision tree of depth at most
`k`.

#### Proof

Induct on `k`.

If `k = 0`, exactness means `T` is constant on each prefix class, so depth `0`
works.

For `k > 0`, split first on `b_1`. Inside each branch, the remaining tuple
`(b_2, ..., b_k)` is still an exact prefix code for the restricted target,
because equality of all remaining coordinates together with equality of the
fixed branch value is equality of the full code. By induction, each branch has
an exact depth-`<= k-1` decoder. Adding the root split on `b_1` gives depth
`<= k`. ∎

This gives a soft tree bound once exactness is known. The sharper depths below
are separate exhaustive facts.

## 3. Exact FutureFc Code Theorems

Define the common solved-range basis

`B_com = (even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22)`.

Define the family bases

- `B_cup = (even_val_sum, weight_pair_00, weight_pair_02, weight_pair_11, weight_pair_22)`,
- `B_sol = (even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22)`.

Define the repaired `CUP-2(n=12)` basis

`B_cup^+ = (even_val_sum, weight_pair_00, weight_pair_02, weight_pair_11, weight_pair_22, count_lag2_11)`.

### Theorem 3.1. Common solved-range exact code for FutureFc.

For every bad configuration `c` in either family and every solved cross-family
size `n = 9,10,11`,

`FutureFc(c) = D_{W_n}(P(c), B_com(c))`

for some decoder `D_{W_n}` depending only on the family and on `n`.

Equivalently, `(P, B_com)` is an exact prefix code for `FutureFc` on:

- `CUP-2(n=9,10,11)`,
- `Sol3(n=9,10,11)`.

#### Proof status

Computationally certified by exhaustive collision checks on all bad
configurations using `futurefc_basis_family_probe.py`. No two bad
configurations with the same `(P, B_com)` data have different `FutureFc`
values on the listed cases.

### Theorem 3.2. Stable family code and first nonlocal correction.

1. `B_cup` is an exact prefix code for `FutureFc` on `CUP-2(n=9,10,11)`.
2. `B_cup` is not exact on `CUP-2(n=12)`.
3. Adjoining one nonlocal `(1,1)` correction repairs exactness at `n=12`:
   each of
   - `count_lag2_11`,
   - `weight_lag2_11`,
   - `weight_lag3_11`
   added to `B_cup` gives an exact prefix code on `CUP-2(n=12)`.
4. `B_sol` is an exact prefix code for `FutureFc` on `Sol3(n=9,10,11)`.

So the first confirmed departure from the adjacent-pair family occurs exactly
at `CUP-2(n=12)`, and it is repaired by one specific lagged `(1,1)` statistic.

#### Proof status

Computationally certified by exhaustive collision checks:

- `B_cup` exact on `n=9,10,11`,
- `B_cup` non-exact on `n=12`,
- `B_cup^+` exact on `n=12`,
- `B_sol` exact on `n=9,10,11`.

The relevant scripts are `futurefc_basis_family_probe.py` and
`futurefc_nonlocal_pair_probe.py`.

### Theorem 3.3. Reduced-prefix exact coarse code.

The full proof107 prefix `P = (boundary6, exp2, int21, exp2_weight)` is not
minimal for the coarse `FutureFc` layer on the solved range.

#### Sol3 reduced prefix

Let

`P_sol^red(c) = (boundary6(c), exp2_weight(c))`.

Then on `Sol3(n=9,10,11)` the tuple `(P_sol^red, B_sol)` determines each of:

- `exp2`,
- `int21`,
- `fc`,
- `FutureFc - fc`,
- `FutureFc`.

So on the solved `Sol3` range, the full TP triple is recovered from
`boundary6 + exp2_weight + B_sol`.

#### CUP-2 reduced prefix

Let

`P_cup^red(c) = (boundary6(c), exp2_weight(c), int21(c))`.

Then:

- on `CUP-2(n=9,10,11)`, `(P_cup^red, B_cup)` determines each of
  `exp2`, `fc`, `FutureFc - fc`, and `FutureFc`,
- on `CUP-2(n=12)`, `(P_cup^red, B_cup^+)` determines the same quantities.

So on the currently solved `CUP-2` range, the only TP scalar still needed at
the coarse layer beyond `exp2_weight` is `int21`; `exp2` is recovered from the
reduced prefix plus the tiny code.

#### Proof status

Computationally certified by exhaustive fiber checks using
`futurefc_fiber_probe.py`.

### Theorem 3.4. Reduced-prefix recovery-tree theorem on the solved range.

The reduced-prefix exact coarse code of Theorem 3.3 is accompanied by uniformly
shallow exact tree recovery for the omitted TP data and for the coarse gap.

#### CUP-2 recovered TP data

For `CUP-2`, with reduced prefix

`P_cup^red = (boundary6, exp2_weight, int21)`,

the recovered scalar `exp2` has exact multiway tree depths:

- `n=9`: depth `0`,
- `n=10`: depth `1`,
- `n=11`: depth `1`.

#### CUP-2 recovered coarse gap

For the coarse gap

`gap(c) = FutureFc(c) - fc(c)`,

the reduced-prefix exact tree depths are:

- `CUP-2(n=9)`: depth `2`,
- `CUP-2(n=10)`: depth `3`,
- `CUP-2(n=11)`: depth `3`,
- `CUP-2(n=12)` on the repaired basis `B_cup^+`: depth `3`.

#### Sol3 recovered TP data

For `Sol3`, with reduced prefix

`P_sol^red = (boundary6, exp2_weight)`,

the recovered scalar `int21` has exact tree depths:

- `n=9`: depth `2`,
- `n=10`: depth `3`,
- `n=11`: depth `3`.

#### Sol3 recovered coarse gap

For the same reduced prefix and basis, the coarse gap depths are:

- `Sol3(n=9)`: depth `3`,
- `Sol3(n=10)`: depth `3`,
- `Sol3(n=11)`: depth `4`.

So across the full solved reduced-prefix range, the omitted TP data and the
coarse gap are uniformly shallow-tree recoverable.

#### Proof status

Computationally certified by exact minimal-depth searches using
`futurefc_target_tree_probe.py`.

#### Dominant-root remark

The recovery trees are not structurally chaotic. On the inspected solved-range
cases, their roots are heavily concentrated on a very small feature set:

- `even_val_sum` is the dominant root observable,
- then a small family of weighted-pair coordinates appears,
- and on repaired `CUP-2(n=12)` the nonlocal `count_lag2_11` appears only as a
  lower-frequency splitter.

Representative root-split counts:

- `CUP-2(n=11)`, target `exp2`:
  `even_val_sum: 358`, `weight_pair_02: 36`, `weight_pair_22: 36`
- `Sol3(n=11)`, target `int21`:
  `even_val_sum: 5832`, `weight_pair_02: 1377`, `weight_pair_01: 243`
- `Sol3(n=11)`, target `gap`:
  `even_val_sum: 254`, `weight_pair_01: 201`, `weight_pair_00: 140`,
  `weight_pair_02: 123`
- `CUP-2(n=12)`, target repaired `gap`:
  `even_val_sum: 3866`, `weight_pair_11: 2282`, `weight_pair_02: 960`,
  `weight_pair_00: 337`, `count_lag2_11: 182`

This is the current best analytic clue for a symbolic proof of the
reduced-prefix theorem.

#### CUP-2 local two-stage clue

On the solved local `CUP-2` branch, the reduced-prefix recovery of `exp2`
appears to be close to an explicit two-stage theorem:

- `CUP-2(n=10)`: `even_val_sum` alone already determines `exp2`,
- `CUP-2(n=11)`: after the primary split on `even_val_sum`, the only remaining
  exceptional groups are `72`, and every one of them is resolved by either
  `weight_pair_02` or `weight_pair_22` (in fact both work).

More concretely, at `n=11` there are only two normalized exceptional patterns
after the `even_val_sum` split:

- one family with ambiguity `8 -> {2,3}`,
- one family with ambiguity `8 -> {1,2}`.

So the best current symbolic candidate for the local `CUP-2` branch is:

1. split on `even_val_sum`,
2. on the tiny exceptional family, split on `weight_pair_02`
   or equivalently `weight_pair_22`.

This clean two-stage description is not yet known to extend in the same form to
repaired `CUP-2(n=12)` or to the `Sol3` `int21` branch, so it should currently
be treated as a solved-local `CUP-2` clue rather than as a uniform theorem.

### Theorem 3.5. Compact reduced-prefix `exp2` theorem for CUP-2.

Let

`E_cup(c) = (even_val_sum(c), weight_pair_11(c), weight_pair_22(c))`.

Then on the reduced `CUP-2` coarse prefix

`P_cup^red(c) = (boundary6(c), exp2_weight(c), int21(c))`,

the scalar `exp2` is an exact function of `E_cup` throughout the currently
solved local range:

- `CUP-2(n=9)`,
- `CUP-2(n=10)`,
- `CUP-2(n=11)`,
- `CUP-2(n=12)`.

Equivalently, `(P_cup^red, E_cup)` is an exact prefix code for `exp2` on those
four sizes.

Moreover, the exact decoder stays very shallow:

- `n=9`: max depth `0`,
- `n=10`: max depth `1`,
- `n=11`: max depth `1`,
- `n=12`: max depth `2`.

So the local `CUP-2` branch has a genuinely compact corrected theorem:
the proof107 scalar `exp2` itself is recovered from the reduced coarse prefix by
just three weighted statistics, with depth at most `2` through `n=12`.

#### Proof status

Computationally certified by exhaustive fiber checks and minimal-depth tree
searches using `futurefc_fiber_probe.py` and `futurefc_target_tree_probe.py`.

## 4. Shallow Decoder Theorem

### Theorem 4.1. Verified shallow exact FutureFc decoders.

On the exact bases above, `FutureFc` admits exact multiway axis-aligned
decision-tree decoders with the following verified maximum depths:

| Family / basis | Sizes | Max depth |
| --- | --- | --- |
| `B_com` on `CUP-2` | `n=9,10,11` | `3` |
| `B_sol` on `Sol3` | `n=9,10` | `2` |
| `B_sol` on `Sol3` | `n=11` | `3` |
| `B_cup^+` on `CUP-2` | `n=12` | `4` |

More explicitly, on the family bases:

- `CUP-2(n=9,10,11)` on `B_cup`: depth `3`,
- `CUP-2(n=12)` on `B_cup^+`: depth `4`,
- `Sol3(n=9,10)` on `B_sol`: depth `2`,
- `Sol3(n=11)` on `B_sol`: depth `3`.

#### Proof status

Computationally certified by exact minimal-depth search with
`futurefc_decision_tree_probe.py`.

#### Remark

Proposition 2.2 already gives the weaker analytic bounds

- depth `<= 5` on the 5-coordinate bases,
- depth `<= 6` on the repaired `CUP-2(n=12)` basis.

The point of Theorem 4.1 is that the actual optimal depths are much smaller:
`2`, `3`, and `4`.

## 5. First Bridge Toward The Two-Level Theorem

The `FutureFc` package now gives the first clean theorem-level step toward the
two-level `FutureFc + slice-rank` suppression theorem.

### Frontier Code Package

1. By Proposition 2.1, every coordinate used in the solved `FutureFc` codes,
   including the `n=12` repair terms, is a width-`n-2` allowed coordinate.
2. By Theorems 3.1 and 3.2, `FutureFc` is exactly determined by a tiny tuple of
   those coordinates once the proof-architecture prefix `P` is fixed.
3. By Theorem 4.1, the decoder is not opaque: it is a shallow tree.
4. By Theorem 3.3, on the solved range the coarse layer actually needs a
   smaller prefix than the full proof107 TP triple:
   - `Sol3`: `boundary6 + exp2_weight`,
   - `CUP-2`: `boundary6 + exp2_weight + int21`.
5. By Theorem 3.4, this reduced-prefix exactness is already mediated by shallow
   recovery trees for the omitted TP data and for the coarse gap.

### Residual Slice Package Already In Place

The solved slice branch provides the matching residual side:

- common exact slice basis through `n=11`,
- shallow exact slice decoders through the solved range,
- and at `n=9` the measured forbidden width-`n-2` energy satisfies:
  - `CUP-2`: `FutureFc = 0.000255`, `cf_rank = 0.006709`,
  - `Sol3`: `FutureFc = 0.000170`, `cf_rank = 0.025427`.

This is exactly the first theorem-facing bridge back to the convergence
architecture:

- the frontier layer is now an exact tiny allowed-coordinate code,
- the residual slice rank is the remaining carrier of nontrivial forbidden mass.

## 6. What Is Still Missing

The exact obstruction is now narrow.

To turn Theorems 3.1, 3.2, and 4.1 from computational theorems into symbolic
theorems, we still need a structural explanation of the collision-free fibers:

`(P(c), B(c)) = (P(c'), B(c'))  =>  FutureFc(c) = FutureFc(c')`.

That is the current proof bottleneck. The missing ingredient is not more basis
mining. It is one of the following:

1. a recursive description of `FutureFc` on prefix groups,
2. a monotone branching rule proving that the tree splits are forced by the
   witness dynamics,
3. or a direct reduction from the `FutureFc` dynamics to the proof107 TP data
   plus one tiny weighted-pair quotient.

The new reduced-prefix theorem sharpens point `3`: the right coarse-layer
reduction target is probably not the full TP triple, but rather:

- `boundary6 + exp2_weight` on `Sol3`,
- `boundary6 + exp2_weight + int21` on `CUP-2`,

together with the tiny weighted-pair code.

Until that implication is proved symbolically, the exact code theorem is best
viewed as computationally certified rather than analytically explained.
