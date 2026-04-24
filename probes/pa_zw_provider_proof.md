# ZW Provider EC Proof

## Update (2026-04-10, later pass)

See `pa_zw_provider_route_reassessment.md` before using this note as the LE
spec. The original proof route here is still useful background, but the
archive-style entry point

`exists b, isBinary b /\ fireCount b = 2`

is not universally valid under the current `zw_provider_ec` hypotheses.

The current best-supported target is a direct local provider theorem of exact
`0/2` form: some processor `i` has consecutive fires `a1 < a2` and a step `k2`
between them such that one neighbor fires exactly `2` times in `[k2, a2)` and
the other neighbor fires `0` times there.

## Target Sorry

`zw_provider_ec` in `ZeroWinding.lean` (line 44):
Under ZW with cw > 0, all fc >= 2, >= 3 binary, n >= 9, some proc q with fc >= 3,
prove `hasEntryConflict gc`.

## Theorem Statement

```
theorem zw_provider_ec
    (gc : GoodCycle sys) (hn : sys.rs.n >= 9) (hconv : converges sys gc)
    (hno_safe : ...) (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount)
    (hfc_ge2 : forall p, gc.fireCount p >= 2)
    (q : Fin sys.rs.n) (hq : gc.fireCount q >= 3) :
    hasEntryConflict gc
```

## Proof Architecture (3 Steps)

### Step 0: General EC Construction (sorry-free)

**Lemma (general_step_pair_ec)**: Given proc i, consecutive fire steps a1 < a2
(moverAt a1 = i, moverAt a2 = i, no i-fire in (a1, a2)), and step k2
with a1 < k2 < a2, moverAt k2 != i, satisfying:

- `left(i)` fires 0 in [k2, a2), OR is binary with even fires in [k2, a2)
- `right(i)` fires 0 in [k2, a2), OR is binary with even fires in [k2, a2)

Then hasEntryConflict gc.

**Proof**: Direct generalization of existing `palindromic_step_pair_caseA` in ZeroWinding.lean.
Construct EC witness (k1 = a2, k2, target = i):
- moverAt a2 = i (mover); moverAt k2 != i (non-mover)
- config(k2, left(i)) = config(a2, left(i)): by `state_eq_of_noFire_between` or `binary_state_eq_of_even_fireCount`
- config(k2, i) = config(a2, i): by `state_eq_of_noFire_between` (i fires 0 in [k2, a2))
- config(k2, right(i)) = config(a2, right(i)): same as left

### Step 1: Existence of Provider Interval (SORRY -- computationally verified)

**Claim (exists_provider_interval)**: Under the given hypotheses, there exist
proc i with a binary neighbor b, consecutive fires (a1, a2) of i, and step k2
in (a1, a2) with moverAt k2 = b, such that in [k2, a2):
- i fires 0 (automatic: between consecutive fires)
- b (binary) fires an even number >= 2 of times
- far neighbor f fires 0 times

**Equivalent formulation via two sub-claims**:

**Sub-claim 1A (Clustering Lemma)**: For some binary b and some neighbor i of b,
between two consecutive fires of b, i fires 0 times.

This means those two b-fires land in the SAME interval of i, giving b >= 2 in that interval.

**Sub-claim 1B (Suffix Lemma)**: Given b fires >= 2 in an interval (a1, a2) of i,
there exists k2 = some b-fire step after the last f-fire in the interval, such that
b fires even times and f fires 0 in [k2, a2).

**Proof sketch for 1B**: Let b_1 < ... < b_m be b-fires in (a1, a2), m >= 2.
Let F = last f-fire position (or a1 if no f fires). Take j = largest index with
b_j > F and b_{j+1} > F (exists since b_m > F by the approach-step structure).
Then k2 = b_{m-1} if m - (m-1) + 1 = 2 is even (always is). Suffix [b_{m-1}, a2) has
b fires = 2 (even), f fires = 0. QED.

**Proof sketch for 1A**: Consider binary b with fc(b) >= 2. b fires at steps s_1, ..., s_F.
The fires of neighbor i are interleaved with the fires of b. If i fires in every
interval of b: fc(i) >= fc(b). If this holds for BOTH neighbors of ALL 3 binary procs:
total neighbor fires >= 2 * sum_binary fc >= 12. But CL can be as low as 2n+1 = 19,
and binary fires = 6, leaving 13 for 6 non-binary procs (average 2.17).
For ALL neighbors to have fc >= fc(b) >= 2, we need sum >= 12 -- which is possible.

For n = 9 with 3 non-adjacent binary (each fc = 2): if ALL 6 ternary neighbors have
fc >= 3 (needed since fc(b) = 2 and "i fires in every interval" means fc(i) >= 2,
but we need fc(i) > fc(b) to prevent the split), the total is >= 6+18 = 24.
For CL < 24: CONTRADICTION -- the assumption fails, so clustering holds.
For CL >= 24: the counting argument doesn't close, but computation confirms it still holds.

The full analytical argument for 1A remains an open gap. It likely requires using
the zero-winding constraint (CW steps = CCW steps) or the walk's ring topology.

### Step 2: EC Construction

Given the data from Step 1: apply general_step_pair_ec with the identified
(i, a1, a2, k2). The conditions are satisfied by construction.

## Computational Verification

Verified with 100% pass rate across all tested configurations:

| Config | n | Binary positions | Valid cycles | Failures |
|--------|---|-----------------|--------------|----------|
| consec | 5 | 0,1,2 | 3509 | 0 |
| consec | 7 | 0,1,2 | 907 | 0 |
| consec | 9 | 0,1,2 | 240 | 0 |
| spaced | 9 | 0,3,6 | 226 | 0 |
| alt | 9 | 0,2,4 | 252 | 0 |
| consec | 11 | 0,1,2 | 64 | 0 |
| 4-bin | 5 | 0,1,2,3 | 1796 | 0 |
| 4-bin | 9 | 0,1,2,3 | 120 | 0 |
| consec | 13 | 0,1,2 | 13 | 0 |

**Total: 7127 valid cycles, 0 failures.**

Key empirical findings:
1. The winning suffix ALWAYS has binary-neighbor fires = 2 (exactly)
2. 94% of cycles solved at depth 2 (double return: two consecutive same-neighbor fires before a2)
3. The clustering lemma (1A) independently verified: 0 counterexamples across 11,407 cycles
4. The claim "for some binary b, some neighbor fires 0 between consecutive b-fires" verified: 100%

## Lean Implementation Plan

### Sorry decomposition

Replace `zw_provider_ec` (1 sorry) with:

```lean
-- Sorry-free: construct EC from interval data
private theorem general_step_pair_ec (gc : GoodCycle sys)
    (i : Fin sys.rs.n) (a1 a2 k2 : Fin gc.configs.length)
    (hlt : a1.val < a2.val) (ha1 : gc.moverAt a1 = i) (ha2 : gc.moverAt a2 = i)
    (hno_i : forall k, a1.val < k.val -> k.val < a2.val -> gc.moverAt k != i)
    (hk2_gt : a1.val < k2.val) (hk2_lt : k2.val < a2.val)
    (hk2_ne : gc.moverAt k2 != i)
    (hL : gc.intervalFireCount (left i) k2.val a2.val = 0 \/
          (isBinary sys.rs (left i) /\ Even (gc.intervalFireCount (left i) k2.val a2.val)))
    (hR : gc.intervalFireCount (right i) k2.val a2.val = 0 \/
          (isBinary sys.rs (right i) /\ Even (gc.intervalFireCount (right i) k2.val a2.val)))
    : hasEntryConflict gc

-- SORRY: existence of provider interval (computationally verified)
private theorem exists_provider_interval (gc : GoodCycle sys)
    (hn : sys.rs.n >= 9) (h3bin : hasGe3Binary sys.rs)
    (hfc_ge2 : forall p, gc.fireCount p >= 2)
    (q : Fin sys.rs.n) (hq : gc.fireCount q >= 3)
    : exists (i : Fin sys.rs.n) (a1 a2 k2 : Fin gc.configs.length),
        a1.val < a2.val /\
        gc.moverAt a1 = i /\ gc.moverAt a2 = i /\
        (forall k, a1.val < k.val -> k.val < a2.val -> gc.moverAt k != i) /\
        a1.val < k2.val /\ k2.val < a2.val /\
        gc.moverAt k2 != i /\
        ((gc.intervalFireCount (left i) k2.val a2.val = 0) \/
         (isBinary sys.rs (left i) /\ Even (gc.intervalFireCount (left i) k2.val a2.val))) /\
        ((gc.intervalFireCount (right i) k2.val a2.val = 0) \/
         (isBinary sys.rs (right i) /\ Even (gc.intervalFireCount (right i) k2.val a2.val)))
```

This isolates the sorry to a pure combinatorial existence claim about mover sequences.
The general_step_pair_ec is sorry-free from existing infrastructure.

## Remaining Gap

The clustering lemma (Sub-claim 1A) does not have a complete analytical proof.
The counting argument closes it for CL < 8B (B = number of binary procs), which
covers CL close to 2n. For large CL, the argument requires additional structural
constraints from the walk topology and zero-winding.

The gap is isolated in `exists_provider_interval`. The sorry is PURELY COMBINATORIAL
(no topology, no convergence -- just fire count distribution on a cyclic walk).

## Verification Scripts

- `pa_zw_provider_test2.py`: Full mechanism verification (8595+297 cycles, 0 failures)
- `pa_zw_provider_v3.py`: Binary-neighbor restriction (7000+ cycles, 0 failures)
- `pa_zw_provider_final_test.py`: Consecutive b-fires with no f after (100%)
- `pa_zw_provider_both.py`: Winning suffix always has binary-nbr fires = 2
- `pa_zw_provider_anyb.py`: Some binary b always has b >= 2 in some neighbor interval (100%)
- `pa_zw_provider_zeroi.py`: Clustering lemma direct test (100%)
- `pa_zw_provider_sameside.py`: Same-side excursion analysis
