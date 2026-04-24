# EC Small-Range Support-Lift Theorem

Date: April 6, 2026

This note records the first genuine lift of the EC bridge theorem beyond the
canonical representatives.

It is still only proved on the solved small range `n=5,6,7,8,9`, but it already
shows that the right full-class bridge object is support-level rather than
coefficient-level.

## 1. Setup

Work on the tested full BAF class:

- consecutive binary triple `{0,1,2}`,
- non-sweep `fc=2` words admitting valid good cycles,
- and the full valid-good fibers for those words.

For a good cycle in this class, let `d` be the cyclic distance from the
turnaround vertex to the middle binary processor `1`.

For a support `S`, write `E_S(chi_conf)` for the exact ANOVA energy of the
conflict-state indicator on the support `S`.

## 2. Theorem Statement

### Theorem. Small-range support-level EC lift through `n=9`.

For every valid good cycle in the tested full BAF class on `n=5,6,7,8,9`, there is
a fixed tiny forbidden support depending only on the distance class `d` whose
support-energy is strictly positive.

More precisely:

1. If `d=0` or `d=2`, the singleton complement `{1}` works.
2. If `d=1`, the pair complement `{0,2}` works.
3. If `d=3`, the singleton complement `{0}` works, and by reflection so does
   `{2}`.

So on the solved small range, the EC bridge theorem already lifts from the
representative family to the full tested BAF class at the level of support
energy.

## 3. Exact Values

The support energies are class-stable on the solved range:

| n | distance class d | support complement | exact energy |
| --- | --- | --- | --- |
| 5 | 0 | `{1}` | `1/216` |
| 5 | 1 | `{0,2}` | `1/108` |
| 5 | 2 | `{1}` | `1/1296` |
| 6 | 0 | `{1}` | `7/5832` |
| 6 | 1 | `{0,2}` | `2/729` |
| 6 | 2 | `{1}` | `1/1944` |
| 6 | 3 | `{0}` or `{2}` | `1/1458` |
| 7 | 0 | `{1}` | `17/52488` |
| 7 | 1 | `{0,2}` | `4/6561` |
| 7 | 2 | `{1}` | `5/52488` |
| 7 | 3 | `{0}` or `{2}` | `1/8748` |
| 8 | 0 | `{1}` | `13/157464` |
| 8 | 1 | `{0,2}` | `1/6561` |
| 8 | 2 | `{1}` | `13/472392` |
| 8 | 3 | `{0}` or `{2}` | `2/59049` |
| 8 | 4 | `{1}` | `5/236196` |

At `n=9`, the same support pattern remains class-stable on the full tested
class. Computed values are:

- `d=0`, `{1}`:
  approximately `2.093365e-05`
- `d=1`, `{0,2}`:
  exactly `19/531441`
- `d=2`, `{1}`:
  approximately `6.350658e-06`
- `d=3`, `{0}` or `{2}`:
  approximately `7.526706e-06`
- `d=4`, `{1}`:
  approximately `4.233772e-06`

## 4. Why this matters

This is the first direct evidence that:

- the exact representative theorem on `W_d` is not an isolated artifact,
- the naive coefficient lift can fail,
- but a support-level lift can still survive on the full tested class.

That is exactly the shape we need for the eventual bridge theorem.

## 5. Computational certification

The theorem is certified by:

- `ec_support_lift_probe.py`

on the solved small range.

The important point is not just positivity. It is class stability:

- the same support works for every valid good cycle in the listed class,
- and the energy value is constant across the class.

## 6. Why the `n=9` extension is honest

The direct word family has now been audited against the tested full BAF class
through `n=9` by:

- `ec_word_family_audit.py`

which reports:

- `n=9`: `tested=9`, `direct=9`, `missing=0`, `extra=0`.

So the `n=9` support statement is now a full-class statement, not merely a
direct-family corollary.

## 7. Remaining gap

This is still only a small-range theorem.

The next step is to decide whether the same support pattern extends:

- even `d`: complement `{1}`
- `d=1`: complement `{0,2}`
- odd `d >= 3`: complement `{0}` or `{2}`

to the full tested class beyond `n=9`.
