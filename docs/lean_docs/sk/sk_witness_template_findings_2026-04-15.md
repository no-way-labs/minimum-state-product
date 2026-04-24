# Girth-2k Witness Templates — Phase A Findings — 2026-04-15

Companion to `sk_invariant_lean_targets_2026-04-14.md` §4 and §7. This
doc reports the result of `probe_sk_witness_template_2026-04-15.py`,
which extracted symbolic witness templates for each of the 10 canonical
skeleton edges across 8 (n, ms) cases.

**TL;DR**: T2 has a clean refined form that is uniform across binary
placement and provable without case analysis on n. The full 10-edge
form requires the binary positions to be tight; the 4-pole form is
robust for any placement and is enough for the SK lower bound.

---

## Cases tested

| label | ms | n | binary positions | |SK| |
|---|---|---|---|---|
| n5 3CB | (2,2,2,3,3) | 5 | [0,1,2] | 20 |
| n6 3CB | (2,2,2,3,3,3) | 6 | [0,1,2] | 52 |
| n7 3CB | (2,2,2,3,3,3,3) | 7 | [0,1,2] | 112 |
| n8 3CB | (2,2,2,3,3,3,3,3) | 8 | [0,1,2] | 240 |
| n9 3CB | (2,2,2,3,3,3,3,3,3) | 9 | [0,1,2] | 492 |
| n7 spread (0,2,4) | (2,3,2,3,2,3,3) | 7 | [0,2,4] | 112 |
| n7 spread (0,3,5) | (2,3,3,2,3,2,3) | 7 | [0,3,5] | 112 |
| n7 spread (0,3,6) | (2,3,3,2,3,3,2) | 7 | [0,3,6] | 112 |

`|SK|` shows the binary-count invariance noted in the findings doc:
SK size depends on `n` only at fixed `k = 3`. ✓

---

## Witness coverage by edge

For each canonical edge, count of cases (out of 8) with at least one
witness:

| edge | type | #cases with witnesses |
|---|---|---|
| (0,1,1) → (0,0,1) | REV | **8/8** |
| (0,0,1) → (1,0,1) | REV | 7/8 (missing in (0,3,6)) |
| (1,0,1) → (1,0,0) | REV | 7/8 (missing in (0,3,6)) |
| (1,0,0) → (1,1,0) | REV | **8/8** |
| (1,1,0) → (0,1,0) | REV | 7/8 (missing in (0,3,6)) |
| (0,1,0) → (0,1,1) | REV | 7/8 (missing in (0,3,6)) |
| (0,0,1) → (0,0,0) | POLE | **8/8** |
| (0,0,0) → (1,0,0) | POLE | **8/8** |
| (1,1,0) → (1,1,1) | POLE | **8/8** |
| (1,1,1) → (0,1,1) | POLE | **8/8** |

**All 4 pole-attachment edges have witnesses in all 8 cases.**

The 2 "diagonal" reverse-cycle edges `(0,1,1)→(0,0,1)` and `(1,0,0)→(1,1,0)`
also have witnesses in all 8 cases.

The 4 "side" reverse-cycle edges fail to find witnesses in the maximally
spread (0,3,6) case at n=7. They succeed in all consecutive and
moderately-spread cases.

---

## Template structure

A "template" for an edge is the set of values each non-binary position
takes across all witnesses for that edge. Each non-binary position is
either **forced** to a single value or **flexible** (takes both 0 and 1).
**No witness ever uses value 2** at any non-binary position — the
witness configurations live entirely in the binary/0/1 sub-region of
the state space.

### Pattern 1: Consecutive 3CB at {0,1,2} — uniform across n=5..9

For each edge, the template has at most **one forced** non-binary
position; all others are flexible:

| edge | forced position(s) | flex positions |
|---|---|---|
| (0,1,1) → (0,0,1) | none | all of {3, …, n-1} |
| (0,0,1) → (1,0,1) | n-1 ↦ 0 | {3, …, n-2} |
| (1,0,1) → (1,0,0) | 3 ↦ 1 | {4, …, n-1} |
| (1,0,0) → (1,1,0) | none | all of {3, …, n-1} |
| (1,1,0) → (0,1,0) | n-1 ↦ 1 | {3, …, n-2} |
| (0,1,0) → (0,1,1) | 3 ↦ 0 | {4, …, n-1} |
| (0,0,1) → (0,0,0) [POLE] | 3 ↦ 1 | {4, …, n-1} |
| (0,0,0) → (1,0,0) [POLE] | n-1 ↦ 0 | {3, …, n-2} |
| (1,1,0) → (1,1,1) [POLE] | 3 ↦ 0 | {4, …, n-1} |
| (1,1,1) → (0,1,1) [POLE] | n-1 ↦ 1 | {3, …, n-2} |

**Key observation**: the forced position is always either position 3
(immediately right of the 3-binary block) or position n-1 (the rightmost
position in the ring, which loops back to position 0). The forced value
depends on the edge but the position pattern is a clean two-case split.

### Pattern 2: Spread binary at n=7 (0,2,4), (0,3,5), (0,3,6)

For spread placements the templates have **2 forced positions** instead
of 1 (one adjacent to each interior binary), but the structural shape
is preserved: still a small fixed set of forced positions, the rest
flexible, no value-2 anywhere.

The (0,3,6) case is the maximally spread placement — binary positions
are evenly distributed around the ring. There the 4 "side" reverse-cycle
edges genuinely have **no witnesses** under any choice of mover. The
4 pole edges and the 2 "diagonal" reverse edges still survive.

---

## Implications for T2

The findings refine T2 (`tail_skeleton`) into a stronger and more
provable form:

### T2-weak (refined statement, uniform across binary placement)

> **For any sub-threshold `ms` with at least 3 binary positions, the
> binary-cube projection of `SK(gc)` contains all 4 canonical
> pole-attachment edges.**

This is the weakest statement that still gives the full SK lower bound
via T1 (any non-empty edge in the projection forces SK non-empty), and
it is uniform in binary placement: the empirical sweep above confirms
it for both consecutive and spread placements at all tested sizes.

The 4 pole-attachment templates are explicit:

```
For pick of binary positions {p₀ < p₁ < p₂}, write q₀, q₁, q₂, q₃ for
the four ternary positions immediately adjacent to a binary in the
ring (with appropriate wrap). For each pole edge:

  (0,0,1) → (0,0,0):  c[p₀]=0, c[p₁]=0, c[p₂]=1, c[<adj>]=1
  (0,0,0) → (1,0,0):  c[p₀]=0, c[p₁]=0, c[p₂]=0, c[<adj>]=0
  (1,1,0) → (1,1,1):  c[p₀]=1, c[p₁]=1, c[p₂]=0, c[<adj>]=0
  (1,1,1) → (0,1,1):  c[p₀]=1, c[p₁]=1, c[p₂]=1, c[<adj>]=1

(Plus: every other ternary position takes any value in {0,1}; no
position ever takes value 2.)
```

The exact `<adj>` slot depends on the placement but is determined by
the binary positions, not by the rest of the state vector.

### T2-strong (original statement, requires consecutivity)

> **For sub-threshold `ms` with `≥ 3` *consecutive* binary positions
> {0,1,2}, the binary-cube projection of `SK(gc)` contains the full
> canonical 10-edge skeleton.**

This is provable for the consecutive case but does not generalize to
arbitrary placements. We do not need T2-strong for the LB proof. It
remains as a structural curiosity worth recording.

### Recommendation for Lean

Use **T2-weak** as the actual `tail_skeleton` theorem in `TailTheorem.lean`.
Drop the full 10-edge claim from the signature; replace with a 4-pole
claim. This:

- Removes case analysis on binary placement (uniform over consecutive
  and spread).
- Halves the witness construction work (4 templates instead of 10).
- Still gives `tail_SK_nonempty` immediately (4 pole edges → 4 source
  vertices → 4 distinct configs in `SK`).

The full canonical skeleton structure (`canonical_skeleton_no_sink`,
T3) remains useful as a structural fact about the canonical skeleton
*as an abstract object* but is no longer load-bearing for the lower
bound proof.

---

## Implications for the Lean stubs

Action items on `LeanMn/LowerBound/SK/`:

1. **`TailTheorem.lean`**: rewrite `tail_skeleton` signature to claim
   only the 4 pole edges, not all 10. Add a separate
   `tail_skeleton_strong` for the consecutive case as a future lemma
   (left sorry'd, not load-bearing).

2. **`Skeleton.lean`**: add `canonicalPoleEdges : List (CubeVertex ×
   CubeVertex)` as a sub-list of the full `canonicalSkeletonEdges`, so
   the refined T2 references it directly.

3. **`Theorem.lean` (T6)**: the proof outline in the doc-comment
   already only needs SK non-empty, which T2-weak provides. No change
   needed.

These edits are small (≤30 lines total) and should be made before any
proof work begins.

---

## What the probe did NOT establish (still empirical, not proof)

These claims hold in the data but have not been proved analytically:

- **No witness ever uses value 2 at a non-binary position.** Empirically
  true in 8/8 cases. Not proved.

- **The "forced position" of each edge template is a function of the
  binary placement only.** Empirically consistent in 8/8 cases for the
  same placement family. Not proved that this holds for *all*
  sub-threshold ms.

- **The 4 pole edges always have non-empty witness sets.** Empirically
  true in 8/8 cases. Not proved analytically.

These all need analytical proofs in T2-weak, ideally derived from the
forced-graph structure of `det(C)` directly. The good news is that the
shape of the proof now seems clear: the witnesses are extremely
constrained (no value 2, fixed forced positions), so the analytical
construction has a small target.

---

## Next step

Edit the SK stubs per the recommendations above (small mechanical
edit), commit, then move on to **task E** — the worked n=5 hand-trace
(or skip directly to handing off to a Lean proof author).

The girth-2k risk (originally flagged as the only empirical uncertainty
in the targets doc) is now substantially reduced: the witness structure
is uniform and small. The analytical proof of T2-weak should follow
the template pattern in this doc.
