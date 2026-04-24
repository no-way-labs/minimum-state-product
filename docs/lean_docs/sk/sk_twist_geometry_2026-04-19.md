# Twist geometry of closed anchored threadings — 2026-04-19

**Status:** empirical finding, not a proof. Sharpens the "6 twists"
observation from `probe_sk_min_caseC_threading_2026-04-19.py`.
**Constraint:** does not ship, does not reduce sorry count.

## Setup

For each tube vertex `c ∈ N_1(C) ∩ VC-NG` in a sub-threshold record
(n = 6, 7, 8), we consider the base girth cycle in D_tube (length L =
|C|, 1895/1895 records). A **closed anchored threading** picks an
anchored signature `σ = (i, q, v) ∈ Σ(c)` at every vertex so that
consecutive anchors are connected under T_loose (the coarsest
transport, all-pairs compatible). Each step is classified as:

- **A** — anchor unchanged, firing hits the defect: `p = q`.
- **B** — anchor advances along the base cycle: `p = M[i]`.
- **C** — a "twist," neither A nor B.

We run DP for the **minimum C-count** closed threading. Prior finding:
that minimum is **exactly 6** for n ≥ 6 in > 97 % of records.

This note characterizes *where and what* those six events are.

## Headline

**A twist is a defect-transposition event.** In 841/841 records with
min Case-C = 6, every single C-edge changes both `q` (defect position)
**and** `i` (cycle index). They are not two classes of events; they
are the same event viewed from two projections.

## Invariants on the 6 twists

Aggregated across 841 records (n = 6: 647; n = 7: 149; n = 8: 45):

| Invariant | n=6 | n=7 | n=8 |
|---|---|---|---|
| `q_change` count per record | 6 (647/647) | 6 (149/149) | 6 (45/45) |
| `i_change` count per record | 6 (647/647) | 6 (149/149) | 6 (45/45) |
| Σ Δq ≡ 0 (mod n) | 647/647 | 149/149 | 45/45 |
| Σ Δi mod L = 6 | 604/647 | 139/149 | 45/45 |
| Σ Δi mod L ∈ {7, 8} | 43/647 | 10/149 | 0/45 |

Δq distribution is concentrated on cyclic-neighbour shifts (±1 mod n),
with a small tail at ±2 and occasional longer jumps. Defect migrates
locally per twist.

## Where twists fire

- **Signature multiplicity at C-edges.** `|Σ(c)|` before a C-edge is
  distributed as `{1: 1444, 2: 2421, 3: 2, 4: 15}` at n=6,
  `{1: 329, 2: 560, 3: 2, 4: 3}` at n=7,
  `{1: 97, 2: 173}` at n=8. Modal is |Σ| = 2. Twists concentrate at
  branch points where anchor choice is genuinely non-trivial.
- **Arity at firing position.** n=6:
  `{2: 2821, 3: 629, 4: 182, 5: 189, 6: 57, 7: 4}`. Binary movers
  dominate; higher-arity movers contribute a long tail. Same shape at
  n=7, n=8.
- **Adjacency.** Among the 6 twists, the count of cyclically-adjacent
  C-pairs per record is modal 2: n=6 `{0: 83, 1: 122, 2: 431, 3: 11}`,
  n=7 `{0: 12, 1: 33, 2: 102, 3: 2}`, n=8 `{0: 3, 1: 10, 2: 31, 3: 1}`.
  Suggests two typical pair-bundles among the six, but not a strict
  "3 pairs of 2."

## Defect-value changes

Unlike `q` and `i`, defect value `v` does not change at every C-edge:
n=6 `v_change` counts per record `{2: 35, 3: 7, 4: 44, 5: 28, 6: 533}`,
n=7 `{2: 13, 3: 4, 4: 18, 5: 3, 6: 111}`,
n=8 `{2: 6, 4: 1, 6: 38}`. Dominant mode is still 6 (all twists
change `v`), but 18 – 24 % of records have twists that move `q` and
`i` without changing `v`. So defect-position migration is the universal
signal; defect-value migration is almost-universal but not forced.

## Sharpened conjecture

The physically-correct transport `T_phys` (between T_strict and
T_loose) should satisfy:

> Every closed `T_phys`-lift of a base girth cycle in D_tube decomposes
> as `L − 6` strict (A/B) edges and **exactly 6 defect-transposition
> twists**, where each twist is a simultaneous (q, i) jump. The six
> twists satisfy `Σ Δq ≡ 0 mod n` and `Σ Δi ≈ 6 mod L`.

"At most 6" may be the cleanest theorem shape. "Exactly 6" is the
empirical floor; the upper bound floor collapse at n = 5 (distribution
spreads over 4–8) is a finite-L effect, not a counterexample.

## Why this matters for Lean

The previous "six twists" dependency slate was fuzzy on step 5
(`Closed-threading-from-six-twists theorem`). Twist-geometry sharpens
it:

- Step 3 (definition of Case-C edge) refines to: **defect-transposition
  edge** = step that changes `q` *and* `i` simultaneously.
- Step 5 (six-twists theorem) refines to: **closure forces exactly
  six defect transpositions on any base girth cycle of length L ≥ L_0**,
  where the `L_0` threshold accounts for the n=5 spread.

This is still conjectural and unproved. It does not reduce the sorry
count. It gives the next probe something concrete to falsify.

## Files

- Probe: `probes/probe_sk_twist_geometry_2026-04-19.py`
- JSON output: `probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.json`
- Log: `probes/sk_phase0_out/r4b_twist_geometry_2026-04-19.log`
