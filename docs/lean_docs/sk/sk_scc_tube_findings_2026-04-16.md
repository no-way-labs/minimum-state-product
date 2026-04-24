# SK non-emptiness via SCC tube — findings 2026-04-16

> **STATUS UPDATE (end of 2026-04-16 session)**: `SlabBridge.lean`
> has been **deleted** — it provided only the weaker `|SK| ≥ 1`
> statement and was never imported by the clouds route. The work
> below (peel(N_1) / dominant-pair) is now aimed at the **stronger**
> Lemma C statement `|SK| ≥ 2^(n-1)` in `SK/CloudsTheorem.lean`,
> which is the actual critical path.

## Critical-path sorry audit (LB proof, 2026-04-16)

After deleting two dead files (`LargeN/ClassicalLB.lean` with its
4-case `M_n_lower` sorry, and `SK/SlabBridge.lean` with its
`sk_nonempty_of_slab_counting` sorry — neither imported by the
clouds route), the LB proof's critical path is **8 sorrys, all in
`LowerBound/SK/CloudsTheorem.lean`**. They are NOT equal in difficulty:

| # | Line | Sorry | Type | Honest complexity |
|---|---|---|---|---|
| 1 | 210 | `valueSet_card_le_two_at_min_length` | Lean-port | **~50–150 lines**: trajectory argument between the 2 fires + closure. Self-contained. |
| 2 | 239 | `SK_subset_binaryCompatible` | Lean-port | **~200–400 lines**: characterize `detOf` on off-cycle contexts. Structural, not combinatorial. |
| 3 | 263 | `binaryCompatible_card_eq` | Lean-port | **~100–200 lines**: lower bound on valueSet (≥2, not just ≤2) + product cardinality. |
| 4 | 281 | `lemma_a_generalized` | **Exact equality**, Lean-port | **~500+ lines**: `|SK| = 2^n - 2n - 2·[n odd]` at L=2n. Both directions, plus characterizing the alternating-parity residue Z. |
| 5 | 290 | `lemma_b` | **Exact equality**, Lean-port | Similar to #4 at L=2n+1 with a `+2^(n−3)−1` correction. Probably worse. |
| 6 | 317 | **`lemma_c_small_n`** | **OPEN RESEARCH** | `|SK| ≥ 2^(n−1)` at L≥2n+2, n∈{5..8}. The docstring itself says "Open research question." |
| 7 | 329 | **`lemma_c_large_n`** | **OPEN RESEARCH** | Same as #6 for n≥9. |
| 8 | 400 | fringe L<2n | Small Lean-port | "every fair cycle has L ≥ 2n." |

### Where the woe is hard

- **#6 / #7 (Lemma C)**: this is the load-bearing research gap.
  `clouds_floor_small_n` and `clouds_floor_large_n` both route
  through Lemma C; without it, the entire clouds route has no
  `M_n_lower` closer. Everything in this document (peel(N_1),
  dominant-pair theorem, zig-zag L-cycle, slab counting) is
  aimed at proving Lemma C.
  - Empirical evidence: `|peel(N_1(C) ∩ VC-NG)| ≥ 2^(n−1)` at
    n=5..8 in 656/656 records; **exactly** `2^(n−1)` at n=7 in
    all 96 records.
  - Strongest candidate lemma: `N_1^dom_all(C)` (dominant-pair
    restriction) = peel exactly at n=7 (96/96), partial match at
    n=5,6,8. **No single closed-form works across all n.**
  - The peel is a zig-zag L-cycle (not a rigid shadow) — 85% of
    steps lockstep the good cycle, 15% are "jump" steps that
    re-index the anchor. This combinatorial instability is the
    block.
  - Pivoted Lean target: `peel_N1_nonempty` (weak form) or
    `peel_N1_card_ge_pow` (strong form, subsumes Lemma C).

- **#4 / #5 (Lemma A/B)**: classical from Cloud's paper, but
  exact equalities (not bounds) on finite-set cardinalities with
  parity case-splits. Lean-porting this is ~weeks of careful
  work, not an open question — but it is NOT a one-page sorry.

- **#1 / #2 / #3 / #8**: provable, days each, structural.

### Deleted dead files (no longer in the sorry count)

- `LowerBound/LargeN/ClassicalLB.lean` — pre-clouds 4-case
  `M_n_lower` assembly; depended on `SK/Attic/{TailTheorem,
  Witness, PhaseChange}`. Never imported; sorry at :68.
- `LowerBound/SK/SlabBridge.lean` — gave `|SK| ≥ 1` (weak form)
  via slab counting. Never imported by the clouds route. Its
  sorry at :127 was `sk_nonempty_of_slab_counting`. SlabCounting's
  abstract math (§1–5) survives in `SlabCounting.lean` for
  possible future reuse, but the bridge to SK nonemptiness
  through self-maps has been retired.

## Target

Close the load-bearing sorrys in `SK/CloudsTheorem.lean`:
**#6/#7 (Lemma C, open research)**, or — if those prove too hard —
build enough weaker machinery that the `|SK| ≥ 2^(n-1)` conclusion
can be weakened to `|SK| ≥ 1` and the overall LB still closes (this
would require restructuring `SmallN/CloudsLB.lean` and
`LargeN/CloudsLB.lean`, and does NOT currently compile). The
peel(N_1)/SCC-tube work below is aimed at Lemma C directly.

## Empirical results (n = 5..8, pooled across all records)

| Probe | Result |
|---|---|
| Single-slab `Slab(q,v)` self-closed in NG | 0/1649 (dead) |
| Shortest directed cycle in VC-NG | ≥ 2n+2 (no short cycle) |
| Shadow-lift from N_1(C) (rigid) | 0/655 closed walks (dead) |
| Relaxed-lift from N_1(C) (BFS) | 100% closed ≤ 3L, max-Hamming ≤ 3 |
| Non-trivial SCC in VC-NG | **100% exists, size ≥ 2^(n-1)** |
| SCC ⊆ N_1 | 0% |
| SCC ⊆ N_2 | 100% at n=5,6; 0% at n=7,8 |
| SCC ⊆ N_3 | **100% at n=5..8** |
| Canonical-first-NG successor total on SCC | 100% |
| Canonical orbit covers SCC | 0% (orbit ≠ SCC) |
| Every VC-NG config has NG successor | 0% (some "sinks" exist) |
| Fraction of VC-NG with NG successor | 0.78 → 0.93 (increases with n) |

## Key takeaways

1. **SCC exists and lives in a tight Hamming-3 tube**. This is the
   self-closed object we need for `sk_nonempty_of_self_map`.
2. **N_3 tube is tight**: N_2 fails at n ≥ 7.
3. **No naive single-slab self-map**. The slab counting argument gives
   one NG-edge but not a cycle — the gap is real.
4. **Canonical first-NG map** is total on SCC — so once we *know* the
   SCC is nonempty, the self-map is trivially obtained.
5. **Sinks exist**: 7–22% of VC-NG configs have NO NG-successor, so
   VC-NG itself is not the self-map domain.

## The Lean-ready construction

Replace `S = Slab(q, v) ∩ peel(...)` with
`S = peel(N_3(C) ∩ VC-NG)`.

Since `peel` is monotone and the non-trivial SCC is self-closed and
⊆ N_3(C) ∩ VC-NG, we have `SCC ⊆ peel(N_3(C) ∩ VC-NG)`. So proving
`peel(N_3(C) ∩ VC-NG) ≠ ∅` is equivalent (modulo empirics) to the
target.

But this just relocates the sorry: now we need a counting/constructive
argument that `peel(N_3(C))` is nonempty.

## Candidate analytical route

**Tube pigeonhole (VERIFIED)**: peel(N_k(C) ∩ VC-NG) is nonempty
for k ∈ {1, 2, 3} across all sampled records (656/656):

| n | k=1 |peel| avg | k=3 |peel| avg | nonempty rate |
|---|---|---|---|
| 5 | 25.3 (min 18) | 28.5 | 100% |
| 6 | 43.6 (min 36) | 66.4 | 100% |
| 7 | **64 exactly** | 142.7 | 100% |
| 8 | 92.5 (min 84) | 320.3 | 100% |

At n=7, peel(N_1 ∩ VC-NG) = **exactly 2^(n-1) = 64** in all 96 records.

**Edge-vs-sink margin** for N_1 tube:
 - n=5: avg margin 9.5 (|E|−(|T|−|sinks|))
 - n=6: avg margin 12.3
 - n=7: avg margin 12.4
 - n=8: avg margin 14.5

This margin is always ≥ 6 — a pigeonhole argument might yield
peel ≥ 1 analytically.

## Non-routes (ruled out)

- Single slab: does not self-close even with weakest NG-based criterion
- Shortest cycle: too long for direct construction (≥ 2n+2)
- Rigid shadow-lift: too many break-points
- Canonical map on all VC-NG: not total (sinks exist)

## **L-cycle theorem** (new empirical result)

For every record (n=5..7, 641/641), the shortest directed cycle in
peel(N_1(C) ∩ VC-NG) has length **exactly L** (the cycle length of C).

| n | L range | shortest cycle range | equality rate |
|---|---|---|---|
| 5 | 12..15 | 12..15 | 100% (294/294) |
| 6 | 14..16 | 14..16 | 100% (251/251) |
| 7 | 16 | 16 | 100% (96/96) |

The cycle is **not** a rigid shadow {c_i[q←v] : i ∈ Z/L} for any single
(q, v) — verified 0/641 records have such rigid shadow. The cycle is a
"zig-zag": different (q, v) anchors at different steps. Firing positions
in the zig-zag are mostly (~68% at n=7) **outside** the {q−1, q, q+1}
neighborhood of the current anchor.

Interpretation: for each i there's a "companion" config in N_1, and the
L-cycle walks through companions of c_0, c_1, ..., c_{L−1} in order,
changing anchor when the firing position demands.

### Concrete example

ms=(2,2,2,2,3), n=5, L=14. Good cycle:
```
i=0  (0,0,0,0,0) fires p=0
i=1  (1,0,0,0,0) fires p=1
...
i=13 (0,0,0,0,1) fires p=4  (closes back to c_0)
```
L-cycle in peel(N_1) (length 14, |peel|=28):
```
(1,0,0,0,2) → (1,1,0,0,2) → (0,1,0,0,2) → (0,1,0,1,2)
  → (0,1,0,1,1) → (0,1,0,0,1) → (0,1,1,0,1) → (0,0,1,0,1)
  → (0,0,1,0,0) → (1,0,1,0,0) → (1,0,1,1,0) → (1,0,1,1,1)
  → (1,0,1,0,1) → (1,0,0,0,1) → (back to (1,0,0,0,2))
```
Anchor (i, q, v) of each shadow config jumps: 1→2→8→11→12→13→6→9→0→1→4→5→6→1.
Not monotonic. Some configs have multiple N_1 anchors (e.g. j=0 has
(1, 4, 2) and (10, 0, 1)). Firing sequence: 1,0,3,4,3,2,1,4,0,3,4,3,2,4.

## **Pivoted Lean target**

Replace `sk_nonempty_of_slab_counting` with:

```lean
theorem peel_N1_nonempty (gc : GoodCycle sys)
    (hn : 5 ≤ sys.rs.n)
    (hL : 2 * sys.rs.n + 2 ≤ cycleLength gc) :
    (peel (N1_intersect_VCNG gc)).Nonempty
```

where
- `N1_intersect_VCNG gc = {c ∈ VC gc : hammingDistance c (cycle gc) = 1}`
- `peel T` iteratively removes sinks (no NG-successor in T)

Then `SK.Nonempty` follows from `closed_subset_le_SK` applied to `peel T`.

## **n=7 exact theorem (new 2026-04-16, evening)**

**Theorem (empirical, 96/96 records)**: At n=7, for L ≥ 2n+2,
```
  peel(N_1(C) ∩ VC-NG) = N_1^dom_all(C)
```
where
```
  dom_pair(q) := top-2 values of V_q by residence time (∑_i [c_i[q] = v])
  N_1^dom_all(C) := { c_i[q ← v] ∈ N_1 : every Hamming-1 anchor of c has v ∈ dom_pair(q) }.
```

- |N_1^dom_all| = exactly 64 = 2^(n-1) in all 96 records.
- N_1^dom_all is closed under forced NG-successor in all 96 records.
- So the slab_counting sorry reduces at n=7 to proving N_1^dom_all is
  forced-NG-closed — a single analytical lemma with no case splits.

**Why dominant-pair, not {min,max}**: At each q, peel has EXACTLY 2 anchor
v-values (672/672). These are the 2 values q spends the MOST TOTAL TIME at.
The {min, max} framing is a shadow — it's correct 96.7% of the time because
min and max tend to be the longest-residence values, but fails when a "mid"
value dominates (e.g. V_q={0,1,2}, residence times {8,7,1}: dom_pair={0,1},
not {0,2}).

**Open lemma**: prove analytically that at n=7 (or more generally), N_1^dom_all
is closed under the forced NG-successor relation.

At n=5, n=6: peel can be larger OR smaller than N_1^dom_all (dom_all is
sometimes a strict subset, sometimes a strict superset). The exact theorem
is an n=7+ phenomenon — smaller n has looser residence-time separation.

## **Extreme-anchor structure of peel(N_1)** (superseded by dominant-pair)

Follow-up probes pin down the structure of peel(N_1) precisely:

| Invariant | n=5 | n=6 | n=7 |
|---|---|---|---|
| |peel| | 18..31 | 36..50 | **exactly 64 = 2^(n−1)** |
| # distinct anchor pairs (q, v) | avg 9.9 (2n=10) | avg 11.6 (2n=12) | **exactly 14 = 2n** |
| # v-values per q in anchors | avg 2.1 | avg 1.9 | **exactly 2, 672/672** |
| anchors v always ∈ V_q | 100% | 100% | 100% |
| anchors v always both fire-input AND fire-output of q | 100% | 100% | 100% |
| anchors = {min(V_q), max(V_q)} | — | — | **96.7% (650/672)** |

At n=7, define
```
  N_1^ext_all = { c ∈ N_1(C) ∩ VC-NG : every Hamming-1 anchor (q, v) of c has v ∈ {min(V_q), max(V_q)} }.
```

- **74/96 records**: `peel(N_1) = N_1^ext_all` exactly, |N_1^ext_all| = 64, closed under forced NG-successor.
- **22/96 records**: `peel ⊊ N_1^ext_all` (|N_1^ext_all| = 69..71), peeling trims to 64.

The GOOD/BAD split depends on **cycle mid-coverage**:
 - GOOD: `n_mid_config = 2` (only 2 of L cycle positions touch a mid value of any V_q)
 - BAD: `n_mid_config = 7..8` (mid-values persist across many cycle steps)

In the GOOD case, the peel has a clean closed form determined purely by `V_q` boundary and cycle indices. In the BAD case, a second peel round is needed.

## Open analytical lemma

**(A)** Prove `N_1^ext_all` is closed under forced NG-successor whenever the cycle's mid-value coverage is at most O(1).

**(B)** For cycles with large mid-value coverage, identify a second-order closed subset
       (candidate: extreme anchors minus a small "mid-induced" sink family).

Either (A) or (B) would feed directly into `closed_subset_le_SK` and close
`sk_nonempty_of_self_map`.

## Files (probes this session)

- `probe_sk_cw_homology_2026-04-16.py`
- `probe_sk_abc_combined_2026-04-16.py`
- `probe_sk_slab_pair_2026-04-16.py`
- `probe_sk_slab_distance_2026-04-16.py`
- `probe_sk_slab_every_pair_2026-04-16.py`
- `probe_sk_slab_closed_2026-04-16.py`
- `probe_sk_slab_ng_closed_2026-04-16.py`
- `probe_sk_short_cycle_2026-04-16.py`
- `probe_sk_shadow_lift_2026-04-16.py`
- `probe_sk_relaxed_lift_2026-04-16.py`
- `probe_sk_scc_structure_2026-04-16.py`
- `probe_sk_edge_count_2026-04-16.py`
- `probe_sk_tube_closure_2026-04-16.py`
- `probe_sk_tube_pigeonhole_2026-04-16.py`
- `probe_sk_peel_n1_structure_2026-04-16.py`
- `probe_sk_n1_cycle_shape_2026-04-16.py`
- `probe_sk_shadow_qv_2026-04-16.py`
- `probe_sk_concrete_Lcycle_2026-04-16.py`
- `probe_sk_peel_bijection_2026-04-16.py`
- `probe_sk_peel_qv_structure_2026-04-16.py`
- `probe_sk_peel_qv_pair_2026-04-16.py`
- `probe_sk_peel_bijection_v2_2026-04-16.py`
- `probe_sk_peel_extreme_anchor_2026-04-16.py`
- `probe_sk_peel_ext_split_2026-04-16.py`
