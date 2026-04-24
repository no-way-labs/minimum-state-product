# §1.8 SMT relaxed-convention exhaustive search — findings

**Status (2026-04-23, updated).** **All 5 n = 5 sub-threshold
multisets UNSAT-certified** with the sym-break encoding. First
pass (no sym-break) closed 3/5; adding a WLOG symmetry break on
(good set, rule table) via value-swap + cyclic-rotation closes the
remaining 2 within 100 s each. n = 5 sub-threshold is now
exhaustively ruled out: no relaxed-valid rule table exists at any
of the five multisets, giving M_5^rel ≥ 96 = M_5 cleanly.

Sanity check at threshold ({2,2,2,3,4}, prod = 96) returns SAT
and the extracted rule table verifies via
`relaxed_verifier.verify_relaxed` with `valid = True`, confirming
the encoding correctness.

## 1. What was proved

The encoding (`smt_relaxed_n5_n6.py`) encodes the five relaxed-convention
validity properties as first-order z3 constraints:

1. **Liveness**: ∀ c, ∃ p: priv_p(c)
2. **Mutual exclusion on good**: ∀ good c, at most one p privileged at c
3. **Closure**: good[c] ∧ f[p,l,s,r] = v → good[c with position p ← v]
4. **Convergence**: rank function strictly decreases along bad → bad edges
5. **Fairness**: per-processor rank rankp_q strictly decreases when
   mover ≠ q, for every good c

Decision variables:

- f[p, l, s, r] ∈ Fin(m_p) — the rule table (one per processor-context)
- good[c] ∈ Bool — good partition
- rank[c] ∈ [0, N) — convergence well-order
- rankp[p][c] ∈ [0, N) — per-processor fairness rank (one copy per p)

Variable count at n = 5 ms = [2,2,2,2,2]: 40 f-vars + 32 good-bools +
32 rank-ints + 160 rankp-ints = 264 total; ~500 implication clauses.

## 2. n = 5 results

No-sym-break (first pass):

| ms              | prod | M_5 | sub-threshold | z3 verdict | time     |
|-----------------|-----:|----:|---------------|------------|---------:|
| {2,2,2,2,2}     |   32 |  96 | yes           | UNSAT      |  0.3 s   |
| {2,2,2,2,3}     |   48 |  96 | yes           | UNSAT      | 21.7 s   |
| {2,2,2,2,4}     |   64 |  96 | yes           | UNSAT      | 111.1 s  |
| {2,2,2,3,3}     |   72 |  96 | yes           | UNKNOWN    | > 1800 s |
| {2,2,2,2,5}     |   80 |  96 | yes           | UNKNOWN    | > 1800 s |
| **{2,2,2,3,4}** |   96 |  96 | **no (at)**   | **SAT**    |  14.0 s  |

With sym-break (`--sym-break` flag):

| ms              | prod | M_5 | sub-threshold | z3 verdict | time     |
|-----------------|-----:|----:|---------------|------------|---------:|
| {2,2,2,2,2}     |   32 |  96 | yes           | UNSAT      |  0.02 s  |
| {2,2,2,2,3}     |   48 |  96 | yes           | UNSAT      |  0.14 s  |
| {2,2,2,2,4}     |   64 |  96 | yes           | UNSAT      |  8.94 s  |
| {2,2,2,3,3}     |   72 |  96 | yes           | **UNSAT**  | 31.6 s   |
| {2,2,2,2,5}     |   80 |  96 | yes           | **UNSAT**  | 90.2 s   |
| **{2,2,2,3,4}** |   96 |  96 | **no (at)**   | **SAT**    |  0.48 s  |

Total n=5 sub-threshold runtime with sym-break: ~130 s. **5/5
exhaustive.**

Sanity check at threshold: z3 produces f-table and good set; the
output passes `relaxed_verifier.verify_relaxed` end-to-end.

## 3. What this says

**Exhaustive n=5 result:** no relaxed-valid rule table exists at
any n=5 sub-threshold multiset. Therefore
**M_5^rel = M_5 = 96** — the connected-model minimum at n=5
transports cleanly to the Knuth-relaxed convention.

This directly answers §8.7 question (2) at n=5 negatively (no,
M_5^rel is not strictly smaller than M_5), and closes the
transport question for n=5 completely.

**Upgrade over random search:** `relaxed_search_n5_n6.py` runs 5.5M
random rule-table samples at small-n sub-threshold and finds zero
valid systems; this SMT result converts one family of that null result
into **exhaustive certificates**. For the 3 closed multisets above,
no rule table whatsoever is relaxed-valid.

**Paper §8.7 strengthening:** the transport claim "relaxed conventions
do not open the LB at n = 5 sub-threshold" is now backed by a z3
certificate at 3/5 sub-threshold multisets, rather than only random
sampling.

## 4. Symmetry break (applied)

The `--sym-break` encoding adds three WLOG constraints:

1. **`good[(0, ..., 0)] = True`.** Under the per-processor
   value-swap group ∏_p S_{m_p}, every good set has an orbit
   representative in which the origin is good (the action is
   transitive on configs). This breaks the value-swap group.
2. **`f[p, 0, 0, 0] = 0` for p ≥ 1.** Combined with liveness and
   mutex-on-good at origin, this forces processor 0 to be the unique
   mover at origin. WLOG under cyclic rotation of processor indices
   (the ring is directed, but rotation is a symmetry).
3. **`f[0, 0, 0, 0] = 1`.** WLOG under value-swap at position 0
   (fixing the output of the origin's move to value 1 rather than
   2, 3, ...). Forced anyway if m_0 = 2.

Net effect: search space collapses by approximately `n · ∏ m_p`
and the two UNKNOWN multisets close in seconds to minutes.

## 5. n = 6 sweep (sym-break)

There are exactly 12 n = 6 sub-threshold multisets (sorted, m_i ≥ 2,
∏ m < M_6 = 288). Partial sweep so far (6 / 12):

| ms                   | prod | z3 verdict | time     |
|----------------------|-----:|------------|---------:|
| {2^6}                |  64  | UNSAT      |  0.07 s  |
| {2^5, 3}             |  96  | UNSAT      |  0.36 s  |
| {2^5, 4}             | 128  | UNSAT      | 26.71 s  |
| {2^4, 3^2}           | 144  | UNSAT      | 29.76 s  |
| {2^5, 5}             | 160  | UNSAT      | 135.1 s  |
| {2^3, 3^3}           | 216  | UNSAT      | 1904.8 s |

Remaining 6 multisets (sweep running in background via
`sweep_smt_relaxed_n6.sh`): {2^5, 6}, {2^4, 3, 4} (both 192),
{2^5, 7} (224), {2^4, 3, 5} (240), {2^5, 8}, {2^4, 4^2} (both 256).
Worst-case budget 60 min each → ~6 h wall-clock.

## 5. n = 6 note

Not attempted in this pass. At n = 6 the smallest sub-threshold
multiset is `{2^6}` with prod = 64 (M_6 = 288). Variable count scales:
~70 f-vars, 64 good-bools, 64 + 6·64 = 448 rank-ints = 578 vars at
all-binary. Closure constraints scale N · n · max(m-1) = 64 · 6 · 1 =
384. This should still be tractable if n = 5 sub-threshold prod ≤ 64 is.

## 6. Artifact

- `smt_relaxed_n5_n6.py` — z3 encoding + CLI driver
  (`--ms`, `--timeout`, `--verify`, `--quiet`).
- Sanity: `--verify` flag runs the relaxed_verifier post-hoc on any
  SAT output; for {2,2,2,3,4} ms this returned `valid=True`.

## 7. Reproducibility

```bash
# Run from the repo root.
for ms in 2,2,2,2,2 2,2,2,2,3 2,2,2,2,4 2,2,2,2,5 2,2,2,3,3; do
    python3 docs/m5rel/smt_relaxed_n5_n6.py --ms "$ms" --timeout 1800 --quiet
done
python3 docs/m5rel/smt_relaxed_n5_n6.py --ms 2,2,2,3,4 --verify --quiet
#   sanity: SAT, valid=True
```

Runtimes on the session machine: prod 32/48/64 UNSAT in < 2 min each;
prod 72/80 UNKNOWN at 10 min; prod 96 (at-threshold) SAT in 14 s.
