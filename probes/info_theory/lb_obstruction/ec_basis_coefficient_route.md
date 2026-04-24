# EC Basis-Coefficient Route

Date: April 6, 2026

This note records the strongest current EC bridge route.

It improves on `ec_mask_family_route.md`: instead of proving merely that some
forbidden ANOVA energy is positive, it isolates an explicit product basis vector
whose inner product with `chi_conf(W_d)` is already nonzero on the tested
representative range.

## 1. Setup

Work on the representative family `W_d` and the candidate complements from:

- `ec_distance_class_reduction.md`
- `ec_mask_family_route.md`

For the local state size `m_i` at coordinate `i`, define the mean-zero
coordinate function

`phi_i(x_i) = 1[x_i = 0] - 1/m_i`.

So:

- on a binary coordinate, `phi_i(0) = 1/2`, `phi_i(1) = -1/2`,
- on a ternary coordinate, `phi_i(0) = 2/3`, `phi_i(1) = -1/3`,
  `phi_i(2) = -1/3`.

For the candidate support `S_d = [n] \ C_d`, define the explicit product basis
vector

`Psi_d(x) = Π_{i in S_d} phi_i(x_i)`.

Since each `phi_i` has mean zero, `Psi_d` lies in the ANOVA subspace for the
support `S_d`.

Therefore:

> if `<chi_conf(W_d), Psi_d> != 0`, then the forbidden energy on the mask
> `S_d` is positive.

## 2. Candidate complements

Use the same anchored family as in `ec_mask_family_route.md`:

- `d = 0`: `C_d = {1}`
- `d > 0` even: `C_d = {1, d+1}`
- `d = 1`: `C_d = {0,2}`
- `d > 1` odd: `C_d = {0, d+1}`

By reflection about processor `1`, the odd-distance alternative `{2,d+1}`
behaves identically.

## 3. Computed nonvanishing

`ec_basis_inner_probe.py` verifies nonvanishing through `n=11`.

Representative values:

- `n=8`
  - `d=0`: ` 2.222730274856476e-05`
  - `d=1`: ` 1.1431184270690449e-04`
  - `d=2`: `-6.985723720977495e-05`
  - `d=3`: ` 8.890921099425904e-05`
  - `d=4`: `-5.080526342529087e-05`
- `n=9`
  - `d=0`: ` 5.057005387239602e-06`
  - `d=1`: ` 2.4932212606855713e-05`
  - `d=2`: `-1.481820183237651e-05`
  - `d=3`: ` 1.8346345125799487e-05`
  - `d=4`: `-8.467543904215148e-06`
- `n=10`
  - `d=0`: ` 1.1107117775590859e-06`
  - `d=1`: ` 5.592760479944573e-06`
  - `d=2`: `-3.371336924826402e-06`
  - `d=3`: ` 4.233771952107575e-06`
  - `d=4`: `-2.1952891603520756e-06`
  - `d=5`: ` 3.763352846317844e-06`
- `n=11`
  - `d=0`: ` 2.482767502779134e-07`
  - `d=1`: ` 1.2370280189285505e-06`
  - `d=2`: `-7.40474518372724e-07`
  - `d=3`: ` 9.234152817353968e-07`
  - `d=4`: `-4.529961759456663e-07`
  - `d=5`: ` 7.666089131388202e-07`

So the explicit basis coefficient remains nonzero well past the original
`n <= 9` representative computations.

## 4. Sign pattern

On the tested range, the sign pattern is:

- `d = 0`: positive
- `d > 0` odd: positive
- `d > 0` even: negative

This is the first robust symbolic-looking parity pattern on the EC bridge side.

## 5. Why this matters

This is the strongest current theorem route because it removes two layers of
indirection:

1. it works on the explicit representatives `W_d`,
2. it uses one explicit basis vector `Psi_d`,
3. and nonvanishing of `<chi_conf(W_d), Psi_d>` already implies the candidate
   forbidden mask has positive energy.

So the EC bridge target can now be phrased as:

> prove `<chi_conf(W_d), Psi_d> != 0` for every `n` and every distance class
> `d`.

That is much more concrete and Lean-compatible than trying to control the full
forbidden spectrum.

## 6. Projection-chain proof route

The projection data from `ec_mask_family_route.md` suggest a direct proof.

For the chosen complement `C_d`, the averaged function

`g_d = E_{C_d}(chi_conf(W_d))`

on the kept coordinates is supported on a tiny union of two monotone chains
meeting at the zero vector, with the exceptional projections sitting as the
next step beyond each chain end.

Pairing `g_d` with the product basis `Psi_d` should reduce to an explicit
alternating sum of the chain weights.

So the remaining gap is no longer spectral in nature. It is:

> compute one explicit alternating sum on the projection chains and show it is
> nonzero.
