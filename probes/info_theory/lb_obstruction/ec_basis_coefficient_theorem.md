# EC Basis-Coefficient Theorem

Date: April 6, 2026

This note upgrades the EC basis-coefficient route to an exact representative
theorem.

The theorem is still explicit-family, not universal. But it is the first EC-side
statement on the obstruction branch with an exact closed-form coefficient and a
real sign proof.

## 1. Setup

Fix `n >= 5` and a distance class `d in {0,...,floor(n/2)}`.

Let `W_d` be the canonical representative from
`ec_distance_class_reduction.md`, and let

`f_{n,d} = chi_conf(W_d)`

be the corresponding conflict-state indicator on the full configuration space
for

`ms = (2,2,2,3,...,3)`.

Define the candidate complement `C_d` by:

- `d=0`: `C_d = {1}`
- `d=1`: `C_d = {0,2}`
- `d >= 2` even: `C_d = {1,d+1}`
- `d >= 3` odd: `C_d = {0,d+1}`

Let `S_d = [n] \ C_d`.

For each coordinate `i`, define the mean-zero local function

`phi_i(x_i) = 1[x_i = 0] - 1/m_i`.

Define the product basis vector

`Psi_d(x) = Π_{i in S_d} phi_i(x_i)`.

Write

`I_{n,d} = <f_{n,d}, Psi_d>`

for the `L^2` inner product on the full product space.

Let

`r = -1/2`.

Finally, define the positive base factors

- `A_{n,0} = 2^{n-7} / 3^{2n-6}`
- `A_{n,1} = 2^{n-6} / 3^{2n-6}`
- `A_n = 2^{n-8} / 3^{2n-7}`  for `d >= 2`

These are exactly the values of `2 * Psi_d(0)` divided by the full space size.

## 2. Projection-Chain Description

Project away the complement coordinates `C_d`.

With respect to the natural increasing order on the kept coordinates `S_d`,
define:

- `P_a` = the prefix vector with the first `a` kept coordinates equal to `1`
  and the rest `0`,
- `Q_b` = the suffix vector with the last `b` kept coordinates equal to `1`
  and the rest `0`.

Then the projected conflict-state multiset has the following exact form.

### Lemma 2.1. Projected conflict chains.

1. If `d=0`, the projected conflict multiset is

   `2 * {Q_b : 0 <= b <= n-3}`.

2. If `d=1`, the projected conflict multiset is

   `4 * Q_0 + 2 * Σ_{b=1}^{n-4} Q_b`.

3. If `d >= 3` is odd, the projected conflict multiset is

   `4 * Q_0 + 2 * Σ_{a=1}^{d-1} P_a + 2 * Σ_{b=1}^{n-d-3} Q_b`.

4. If `d >= 2` is even, the projected conflict multiset is

   `2 * Q_0 + 4 * P_1 + 2 * Σ_{a=2}^{d-1} P_a + 2 * Σ_{b=1}^{n-d-3} Q_b`.

In every case, the two projected exceptional states are the next prefix and
suffix steps beyond the conflict chains.

#### Proof

This is a direct read-off from the explicit representative word `W_d` together
with the broader BAF support theorem:

- the conflict steps are exactly all good-cycle steps except the two
  turnaround steps and their immediate successors,
- on the simple realization, the good-cycle states along `W_d` are contiguous
  interval indicators on the ring,
- after deleting the chosen complement coordinates `C_d`, those interval
  indicators collapse to the prefix/suffix chains listed above.

The multiplicities are exactly the multiplicities seen when the two directed
passes project to the same kept-coordinate pattern:

- overlap at `Q_0` for odd classes,
- overlap at `P_1` for even classes,
- and no other multiplicity larger than `2`. ∎

## 3. Basis Values on the Chains

Let `w_d = Psi_d(0)`.

Then:

- `w_0 = 2^{n-5} / 3^{n-3}`
- `w_1 = 2^{n-4} / 3^{n-3}`
- `w_d = 2^{n-6} / 3^{n-4}` for `d >= 2`

### Lemma 3.1. Basis values on the chains.

Moreover:

- `Psi_d(Q_b) = w_d * r^b`,
- for `d >= 2`, `Psi_d(P_1) = -w_d`,
- for `d >= 2` and `a >= 2`, `Psi_d(P_a) = w_d * r^{a-2}`.

#### Proof

Each `Q_b` is obtained from the zero vector by flipping `b` ternary kept
coordinates from `0` to `1`, and each such flip multiplies the basis value by
`-1/2 = r`.

For the prefix chain, the first kept coordinate in the relevant classes is a
binary coordinate, so the first prefix flip multiplies by `-1`. The second
prefix flip lands on the second binary coordinate and multiplies by another
`-1`. Every subsequent prefix flip is ternary and multiplies by `r = -1/2`. ∎

## 4. The Exact Coefficient Formula

### Theorem 4.1. Exact basis coefficient on the representative family.

For every `n >= 5`:

1. `d = 0`:

   `I_{n,0} = A_{n,0} * (1 - r^{n-2}) / (1-r)`.

2. `d = 1`:

   `I_{n,1} = A_{n,1} * (2 - r - r^{n-3}) / (1-r)`.

3. `d >= 3` odd:

   `I_{n,d} = A_n * (2 - r^{d-2} - r^{n-d-2}) / (1-r)`.

4. `d >= 2` even:

   `I_{n,d} = - A_n * (1 + r^{d-2} + r^{n-d-2}) / (1-r)`.

#### Proof

By Lemma 2.1 and Lemma 3.1, `I_{n,d}` is the full-space normalization factor
times the weighted sum of the basis values on the projected conflict multiset.

For `d=0`, only the suffix chain appears, so

`I_{n,0} = A_{n,0} * Σ_{b=0}^{n-3} r^b`

which is the stated geometric sum.

For `d=1`, we get

`I_{n,1} = A_{n,1} * (2 + Σ_{b=1}^{n-4} r^b)`

which simplifies to the stated formula.

For odd `d >= 3`, the chain formula is

`I_{n,d} = A_n * (2 + Σ_{a=1}^{d-1} u_a + Σ_{b=1}^{n-d-3} r^b)`

where `u_1 = -1` and `u_a = r^{a-2}` for `a >= 2`. So

`I_{n,d} = A_n * (1 + Σ_{j=0}^{d-3} r^j + Σ_{b=1}^{n-d-3} r^b)`.

Evaluating the two geometric sums gives

`I_{n,d} = A_n * (2 - r^{d-2} - r^{n-d-2}) / (1-r)`.

For even `d >= 2`, the chain formula is

`I_{n,d} = A_n * (-1 + Σ_{j=0}^{d-3} r^j + Σ_{b=1}^{n-d-3} r^b)`,

because the zero vector contributes once, `P_1` contributes twice with sign
`-1`, and the remaining chains contribute with the values from Lemma 3.1.

Evaluating the geometric sums gives

`I_{n,d} = - A_n * (1 + r^{d-2} + r^{n-d-2}) / (1-r)`. ∎

## 5. Sign Consequences

### Corollary 5.1. Exact sign pattern.

For every `n >= 5`:

- `I_{n,0} > 0`
- `I_{n,d} > 0` for every odd `d`
- `I_{n,d} < 0` for every even `d >= 2`

In particular,

`I_{n,d} != 0`

for every representative `W_d`.

#### Proof

Since `r = -1/2`, we have `1-r = 3/2 > 0`.

For `d=0`, the numerator `1-r^{n-2}` is positive.

For `d=1`, the numerator `2-r-r^{n-3}` is strictly positive because
`-r = 1/2` and `|r^{n-3}| < 1/2`.

For odd `d >= 3`, we have `r^{d-2} < 0`, so

`2 - r^{d-2} - r^{n-d-2} >= 2 - |r^{n-d-2}| > 1`.

For even `d >= 2`, the quantity

`1 + r^{d-2} + r^{n-d-2}`

is strictly positive because `r^{d-2} > 0` and `|r^{n-d-2}| < 1`. The leading
minus sign therefore makes `I_{n,d}` strictly negative. ∎

### Corollary 5.2. Positive forbidden energy on the candidate support.

For every `n >= 5` and every distance class `d`,
the ANOVA coefficient on the candidate support `S_d` is nonzero.

Hence the forbidden energy on `S_d` is strictly positive, and therefore

`ForbidFrac_{n-2}(chi_conf(W_d)) > 0`.

#### Proof

`Psi_d` lies in the ANOVA subspace for `S_d`, and its inner product with
`chi_conf(W_d)` is exactly `I_{n,d}`. By Corollary 5.1 this is nonzero, so the
orthogonal projection of `chi_conf(W_d)` onto that support subspace is nonzero.
Therefore the energy on that support is positive. Since `S_d` is forbidden, the
total forbidden energy is positive as well. ∎

## 6. Computational Audit

`ec_basis_inner_probe.py` verifies exact agreement with the coefficient values
through `n=11`.
