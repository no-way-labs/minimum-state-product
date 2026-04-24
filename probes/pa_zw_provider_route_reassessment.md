# ZW Provider Route Reassessment

Date: 2026-04-10
Status: RA/PA follow-up to `pa_zw_provider_proof.md`

## Executive summary

The right target for `zw_provider_ec` is not the archive-style
"there exists a binary with `fireCount = 2`" route.

That route is too strong as a universal entry point. A small valid
zero-winding example exists with:

- `n = 5`
- moduli `[2, 2, 2, 3, 3]`
- fire counts `[4, 6, 6, 3, 3]`
- mover word `[0, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 0, 4, 4, 3, 3, 3, 4, 0, 0]`

This word satisfies the RA-side validity checks used in the provider scripts:

- all `fireCount >= 2`
- some `fireCount >= 3`
- binary fire counts even
- zero winding with `cwStepCount > 0`
- locality of the mover walk

But no binary processor has `fireCount = 2`.

So the clean PA target should be a direct provider-interval theorem, not a
global `fc = 2` theorem for some binary.

## Stronger RA-supported invariant

Across an additional random RA pass on top of the existing provider script,
the following stronger local pattern held with zero failures in 2605 valid
sampled cycles:

> There exists a processor `i`, consecutive `i`-fires `a1 < a2`, and a step
> `k2` with `a1 < k2 < a2`, such that exactly one neighbor of `i` fires
> exactly twice in `[k2, a2)` and the other neighbor fires zero times in
> `[k2, a2)`.

Equivalently, one of the following holds:

- `intervalFireCount (left i) k2 a2 = 2` and
  `intervalFireCount (right i) k2 a2 = 0`
- `intervalFireCount (left i) k2 a2 = 0` and
  `intervalFireCount (right i) k2 a2 = 2`

with the side that fires twice always binary.

This is stronger than the old "0 or binary-even on each side" witness, and it
avoids the false global `fc = 2` entry point.

### n ≥ 9 spot-checks

Focused random checks on representative `n = 9, 11, 13` layouts also came back
clean for the exact `0/2` witness:

| n | binary layout | valid sampled cycles | exact `0/2` witness failures |
|---|---|---:|---:|
| 9 | `[2,2,2,3,3,3,3,3,3]` | 199 | 0 |
| 9 | `[2,3,3,2,3,3,2,3,3]` | 220 | 0 |
| 9 | `[2,3,2,3,2,3,3,3,3]` | 184 | 0 |
| 9 | `[2,2,2,2,3,3,3,3,3]` | 108 | 0 |
| 11 | `[2,2,2,3,3,3,3,3,3,3,3]` | 49 | 0 |
| 11 | `[2,3,3,3,2,3,3,3,2,3,3]` | 61 | 0 |
| 13 | `[2,2,2,3,3,3,3,3,3,3,3,3,3]` | 10 | 0 |

So the exact `0/2` target is not just a small-`n` artifact; it continues to
match the observed `n ≥ 9` behavior.

## What the RA runs support

### Supported strongly by computation

1. `exists_provider_interval_exact2`

   Under the `zw_provider_ec` hypotheses, there is always a witness of exact
   `0/2` form as above.

2. `exists_provider_interval`

   The weaker theorem from `pa_zw_provider_proof.md` also continues to hold:
   one side silent, the other side binary-even.

3. The old clustering statement is plausible but probably not the best outer
   theorem boundary.

   It still held in small random checks, but it is less direct than the `0/2`
   witness theorem and does not by itself package the exact suffix LE wants.

### Falsified as a universal first step

1. `exists b, isBinary b /\ fireCount b = 2`

   False in general under the current `zw_provider_ec` hypotheses.

2. Archive passthrough route with `fc = 2` as the first mandatory witness

   Not safe unless extra hypotheses are added.

## Recommended PA decomposition

### Mechanical LE lemma

`general_step_pair_ec`

Input:

- processor `i`
- consecutive `i`-fires `a1 < a2`
- `k2` with `a1 < k2 < a2`
- no `i`-fire in `(a1, a2)`
- either `(L = 0 and R = 2)` or `(L = 2 and R = 0)` in `[k2, a2)`
- the side with count `2` is binary

Output:

- `hasEntryConflict gc`

This is a direct generalization of the existing local proof pattern already in
`ZeroWinding.lean` (`palindromic_step_pair_caseA`).

### Real PA target

`exists_provider_interval_exact2`

Under the `zw_provider_ec` hypotheses:

- `gc.zeroWinding`
- `0 < gc.cwStepCount`
- all `fireCount >= 2`
- some `q` with `fireCount q >= 3`
- `hasGe3Binary`

prove:

```
∃ (i : Fin n) (a1 a2 k2 : Fin gc.configs.length),
  a1.val < a2.val /\
  gc.moverAt a1 = i /\
  gc.moverAt a2 = i /\
  (∀ k, a1.val < k.val -> k.val < a2.val -> gc.moverAt k != i) /\
  a1.val < k2.val /\ k2.val < a2.val /\ gc.moverAt k2 != i /\
  (
    (isBinary sys.rs (left i)  /\
     gc.intervalFireCount (left i)  k2.val a2.val = 2 /\
     gc.intervalFireCount (right i) k2.val a2.val = 0)
    \/
    (isBinary sys.rs (right i) /\
     gc.intervalFireCount (left i)  k2.val a2.val = 0 /\
     gc.intervalFireCount (right i) k2.val a2.val = 2)
  )
```

Then `zw_provider_ec` is just:

1. obtain the exact `0/2` witness
2. call `general_step_pair_ec`

## Why this boundary is better

1. It matches what the RA searches actually find.
2. It avoids the false `fc = 2` global claim.
3. It pushes all genuine math into one combinatorial existence theorem.
4. Everything after that is routine Lean assembly from existing lemmas:
   `configVal_eq_of_noFire_between` and
   `binary_config_eq_of_even_intervalFireCount`.

## Suggested proof stance

Use the archive route only as inspiration, not as the live theorem boundary.

The likely shape is:

1. If some binary has non-isolated firings, close by existing entry-conflict
   machinery.
2. Otherwise binary firings are isolated.
3. Use zero-winding edge-balance / traversal-count structure to force one
   neighbor interval with a binary `double return` and no far-neighbor suffix.
4. Package that directly as `exists_provider_interval_exact2`.

The mathematical gap is step 3. Everything else looks mechanical.
