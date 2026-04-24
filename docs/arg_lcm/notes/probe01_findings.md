# probe01 findings: R1/R2/R3 across small-n multisets

**Script:** `probes/arg_lcm/probe01_enumerate_L.py`
**Date:** 2026-04-20.

## Method

For each target multiset, enumerate all distinct orientations (up to
cyclic rotation) on a ring of length $n$. Split into "non-adjacent"
(ARG's hypothesis applies) and "adjacent-binary" (ARG silent).

Compute three candidate quantities for L, matching the three readings
in `arg_statement.md` §4:

- **R1** (global LCM): $L = \mathrm{lcm}\{m_i : P_i \notin B\}$.
- **R2** (per-arc LCM): min and max over arcs of $\mathrm{lcm}\{m_i : P_i \in A_j\}$.
- **R3** (block-product LCM): $L = \mathrm{lcm}\{\prod_{P_i \in A_j} m_i\}$.

## Key results (k=3 binaries, non-adjacent subset)

| Case | n | Valid? | non-adj count | R1 | R2 min | R2 max | R3 |
|---|---|---|---|---|---|---|---|
| `{2³, 3³, 4}` | 7 | valid | 4 | {12} | {3} | {4, 12} | **{12, 36}** |
| `{2³, 3⁴, 4}` | 8 | valid | 10 | {12} | {3} | {4, 12} | **{36, 108}** |
| `{2³, 3⁵, 4}` | 9 | invalid | 20 | {12} | {3} | {4, 12} | **{36, 108, 324}** |

## Interpretation

1. **R1, R2min, R2max are identical across n=7, 8, 9.** Any bound of
   the form $L \geq f(k, n)$ using R1/R2 is literally blind to the
   transition — the input to $f$ is the same at n=8 (valid) and n=9
   (invalid).

2. **R3 values at n=9 are a strict superset of n=8's.** Specifically:
   - n=8 non-adj R3 values: {36, 108}.
   - n=9 non-adj R3 values: {36, 108, **324**}.
   - The 324 appears only in n=9 orientations with partition (1,1,4)
     and the 4-state processor placed in a length-1 arc.

3. **Implication for R3 bounds.** Any bound "R3 ≤ threshold" that:
   - **Passes all n=8 orientations** must have threshold ≥ 108.
   - **Fails all n=9 orientations** must have threshold < 36.
   These two are incompatible (108 > 36). **No R3-based threshold
   can separate n=8 valid from n=9 invalid on this multiset.**

4. **The 324 orientations at n=9 are only a minority.** n=9 has 20
   non-adj orientations total. Partition counts:
   - (1,1,4): some subset has R3 = 324 (4 in length-1 arc) or 108 (4 in length-4 arc).
   - (1,2,3), (2,2,2): R3 ∈ {36, 108} — overlaps n=8 values.
   So most n=9 orientations have R3 values that also appear in
   (presumably some) valid n=8 arrangement.

## Other cases

- **n=9 {2⁴, 3⁴, 6}** (5 non-adj orientations): k=4 = 2N, ARG DIRECTLY
  applies. N=2, bound L ≥ 3. R1 = 6 ≥ 3 ✓. **ARG's bound is met; system
  is still invalid.** Confirms ARG is necessary but insufficient even
  on its own turf.

- **n=9 {2⁵, 3³, 9}** (0 non-adj orientations): k=5 binaries in n=9
  forces adjacency in every orientation. ARG silent; invalidity by
  adjacency mechanism.

- **n=6 {2, 4, 2, 4, 2, 4}** (1 non-adj orientation): k=3, R1 = 4.
  System is invalid (bad cycle of length 32, transcript p. 75). Any
  natural odd-k extension of ARG with bound $L \geq N+1$ under $k = 2N+1$
  would give $N=1$, $L \geq 2$, trivially satisfied. **ARG-extended
  cannot rule out this known-invalid system either.**

## Verdict

**A-KILL (equivalently B-OBSTRUCT-on-arrival).**

No reading of ARG's L quantity (R1, R2, R3) — and hence no naïve
odd-k extension of ARG's bound that stays within the L-quantity family
— can distinguish the n=8 valid case from the n=9 invalid case on
the target multiset `{2³, 3^(n-3), 4}`.

The n=9 phase transition is NOT induced by ARG's LCM bound. It has a
different structural source.

## What this does NOT say

- ARG's bound is still TRUE and still useful for:
  - All-binary / most-binary systems (L=1 or small, bound fails).
  - Mixed systems where the LCM IS small (e.g., all non-binaries = 3
    forces L = 3, bounding k ≤ 4).
- The bound is a genuine 1985 result, not paraphrase error.

The thesis tested was "ARG extended to odd-k explains n=9." Result:
**FALSE.** The n=9 transition requires a different invariant — likely
one that is n-dependent (scaling with ring length) or couples the arc
structure to the binary-placement in a way not captured by any LCM
functional on state counts.

## Forward implication

Per research plan §0.B: dispatch ship as *"ARG-LCM does not induce the
n=9 phase transition."* Contribution: kills a plausible-looking thread
and forces the search for the real cause elsewhere.
