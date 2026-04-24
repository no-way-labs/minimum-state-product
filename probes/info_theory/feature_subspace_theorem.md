# Local Feature Subspace Theorem

Date: April 6, 2026

This note records a simple but useful theorem suggested by the information-theory
exploration.

## Setup

For a ring with state vector `m = (m_0, ..., m_{n-1})`, let

`X = Π_i [m_i]`

be the full configuration space, and consider the additive contiguous-window
model of width `w`:

`V_w = { f : X -> R | f(x) = const + Σ_i g_i(x_i, x_{i+1}, ..., x_{i+w-1}) }`

with cyclic indexing.

Equivalently, in the ANOVA / interaction decomposition, `V_w` is the span of
all interaction components supported on subsets contained in some cyclic window
of length `w`.

## Theorem

If a scalar feature on configurations can be written as a finite sum of local
window terms of width at most `ℓ`, then it belongs to `V_w` for every `w ≥ ℓ`.

### Proof

Suppose

`F(x) = Σ_j h_j(x_j, x_{j+1}, ..., x_{j+ℓ-1})`.

Each summand already depends on a single cyclic window of length `ℓ`. If
`w ≥ ℓ`, then that same set of coordinates is contained in a cyclic window of
length `w`, so each summand belongs to `V_w` by definition. Therefore their
sum belongs to `V_w` as well. ∎

## Corollary: Scaffold Features Are Allowed Coordinates

All of the low-order scalar features used in the slice-code exploration are
exactly in the allowed subspace for width `n-2`:

- `count_val_v`
- `interior_sum`
- `even_val_sum`
- `odd_val_sum`
- `count_pair_ab`
- `weight_pair_ab`
- `count_triple_abc`
- `weight_triple_abc`

Indeed:

- the value-count and value-sum features are sums of width-1 local terms,
- pair features are sums of width-2 local terms,
- triple features are sums of width-3 local terms.

Since `n-2 ≥ 3` in all theorem-range cases, each such feature lies in
`V_{n-2}` exactly.

## Corollary: Lagged Pair Corrections Are Also Allowed Coordinates

For `d >= 1` and pair type `(a,b)`, define the cyclic lag-`d` features

- `count_lagd_ab(x) = Σ_j 1[(x_j, x_{j+d}) = (a,b)]`
- `weight_lagd_ab(x) = Σ_j j * 1[(x_j, x_{j+d}) = (a,b)]`

with cyclic indexing.

Each such feature is a sum of local window terms of width `d+1`, because the
indicator

`1[(x_j, x_{j+d}) = (a,b)]`

depends only on the contiguous block

`(x_j, x_{j+1}, ..., x_{j+d})`.

Therefore:

- `count_lagd_ab`, `weight_lagd_ab` belong to `V_w` for every `w >= d+1`,
- in particular:
  - `count_lag2_11`, `weight_lag2_11` lie in `V_w` for every `w >= 3`,
  - `weight_lag3_11` lies in `V_w` for every `w >= 4`.

So the first nonlocal `FutureFc` repair terms found at `CUP-2(n=12)` are still
allowed width-`n-2` coordinates. They are nonlocal only relative to the
adjacent-pair algebra, not relative to the width-`n-2` window model.

## Interpretation

This explains one part of the exploration:

- the scaffold features themselves are not mysterious;
- they are all coordinates drawn from the width-`n-2` allowed subspace.

So the actual interesting fact is **not** that these features have low forbidden
interaction energy. That is automatic.

The interesting fact is that:

- the bad-side convergence rank is almost determined by a very small tuple of
  such allowed coordinates,
- the exact `FutureFc` code continues to hold even after adjoining the first
  lag-2 / lag-3 correction terms,
- and for valid witnesses its remaining forbidden interaction energy is tiny.

In other words, the phenomenon is about the rank’s compressibility into a few
allowed coordinates, not about the individual features themselves.

## Relation to Current Targets

This note sharpens the theorem program:

1. There is no need to prove that the scaffold features themselves suppress
   forbidden modes. They do so trivially because they are local.
2. The real target is to explain why the convergence rank is almost a function
   of only a few of those local coordinates.
3. The residual theorem target remains:
   prove or explain suppression of forbidden width-`n-2` interaction energy for
   the bad-side rank (or for its constant-`FutureFc` slice rank).
