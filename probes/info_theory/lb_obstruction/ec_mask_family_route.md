# EC Mask-Family Route

Date: April 6, 2026

This note records the first coefficient-level route to the weak EC bridge
theorem on the representative family `W_d`.

The key point is that one does not need the whole forbidden spectrum. On the
tested range, a very small anchored family of forbidden masks already carries
positive energy for every distance class.

## 1. Setup

Work on the representative family `W_d` from
`ec_distance_class_reduction.md`.

Let `f_d = chi_conf(W_d)` be the corresponding conflict-state indicator on the
full configuration space for the anchored multiset

`ms = (2,2,2,3,...,3)`.

For a small complement set `C subseteq [n]`, write

`S = [n] \ C`

for the corresponding interaction support.

When `|C| <= 2`, the support `S` has size at least `n-2`; such supports are
forbidden unless they lie in one of the allowed width-`n-2` windows. The mask
families below are explicitly non-window supports, hence genuinely forbidden.

## 2. Candidate Mask Family

The tested data suggest the following anchored forbidden masks:

- `d = 0`:
  - complement `C_0 = {1}`
- `d > 0` even:
  - complement `C_d = {1, d+1}`
- `d` odd:
  - complement `C_d^- = {0, d+1}`
  - complement `C_d^+ = {2, d+1}`

So the candidate family is always supported by deleting only one or two
anchored coordinates.

## 3. Computed Positivity

`ec_mask_family_probe.py` verifies on the tested range `n=5..9` that these
candidate masks already have positive forbidden ANOVA energy on every
representative `W_d`.

Representative values:

- `n=8`
  - `d=0`: complement `{1}` has energy `8.2558553e-05`
  - `d=1`: complement `{0,2}` has energy `1.52415790e-04`
  - `d=2`: complement `{1,3}` has energy `5.5039035e-05`
  - `d=3`: complements `{0,4}` and `{2,4}` both have energy `6.7740351e-05`
  - `d=4`: complement `{1,5}` has energy `4.2337720e-05`
- `n=9`
  - `d=0`: complement `{1}` has energy `2.0933650e-05`
  - `d=1`: complement `{0,2}` has energy `3.5751852e-05`
  - `d=2`: complement `{1,3}` has energy `1.2701316e-05`
  - `d=3`: complements `{0,4}` and `{2,4}` both have energy `1.5053411e-05`
  - `d=4`: complement `{1,5}` has energy `8.4675440e-06`

The same pattern is already visible on `n=5,6,7`.

## 4. Why this matters

This is the first EC bridge route that looks theorem-shaped:

- reduce to representatives `W_d`,
- choose one tiny anchored forbidden mask from the family above,
- prove its ANOVA coefficient is nonzero,
- conclude `ForbidFrac_{n-2}(chi_conf(W_d)) > 0`.

That would give positivity of the weak EC bridge theorem without having to
understand the entire forbidden spectrum.

## 5. Current theorem candidate

### Candidate Proposition

For every `n >= 5` and every distance class `d in {0,...,floor(n/2)}`, at
least one mask in the anchored family above has strictly positive forbidden
ANOVA energy on `chi_conf(W_d)`.

Consequently,

`ForbidFrac_{n-2}(chi_conf(W_d)) > 0`.

## 6. Remaining gap

The gap is now narrower:

- not “why is the full forbidden spectrum positive?”
- but “why does one tiny anchored mask coefficient survive?”

That is a much more manageable symbolic target.
