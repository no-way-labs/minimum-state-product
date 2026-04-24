# Proof: CPhiStep Well-Foundedness

## Status

One sorry remains: `psiRank_segment_drop` at ConstLayerDAG.lean:184.
This document provides the analytical proof argument and Lean formalization
spec to eliminate it.

---

## 1. Problem Diagnosis

The current ConstLayerDAG.lean decomposes `cup2SyntheticOuterStep_wf` via
inner/segment:
- Inner: boundary-fixed steps, WF via `(fc, deep)` lex. PROVED (sorry-free).
- Segment: chain of boundary-fixed steps then one boundary-changing step.
- Segment measure: psiRank (Psi). **FAILS** because Psi can increase by
  up to 10 on boundary-fixed interior steps. The sorry is at
  `psiRank_segment_drop` (line 184).

**Root cause:** Psi drops on every boundary-CHANGING bad step (proved in
`bad_boundary_all_Psi_drop`). But Psi is NOT monotone on boundary-FIXED
(interior) steps, so the segment composition fails.

---

## 2. Solution: Direct 4-Component Lex on CPhiStep

Replace the inner/segment decomposition with a direct proof that every
single CPhiStep decreases a 4-component lex measure:

```
cphiMeasure(c) = ( condensationRank(boundary(c)),
                   fc(c),
                   sccSubRank(boundary(c)),
                   deepMidHopPotential(c) )
```

ordered lexicographically on Nat^4.

**Why this works:** Every individual CPhiStep (not just segments) decreases
this measure. No inner/segment composition is needed. No Psi is involved.

---

## 3. The SCC {239, 245, 251}

Encoding: `((((c0*3 + c1)*3 + c2)*3 + cN3)*3 + cN2)*2 + cN1`.

| State | c0 | c1 | c2 | c[n-3] | c[n-2] | c[n-1] |
|-------|----|----|----|--------|--------|--------|
| 239   | 1  | 1  | 1  | 0      | 2      | 1      |
| 245   | 1  | 1  | 1  | 1      | 2      | 1      |
| 251   | 1  | 1  | 1  | 2      | 2      | 1      |

All three differ only in c[n-3]. Proved: `scc_shared_fields` (native_decide).

---

## 4. SCC Edge Analysis

All SCC edges are moves at position n-3 (deep interior for n >= 9).
Position n-3 uses TMidVal. Right neighbor c[n-2] = 2 (boundary).

### 239 -> 245: c[n-3] changes 0 -> 1

TMidVal(c[n-4], 0, 2) must equal 1.
Table: TMidVal(0,0,2)=0, TMidVal(1,0,2)=1, TMidVal(2,0,2)=2.
Forces c[n-4] = 1.

Local fc: Before = [1!=0]+[0!=2] = 2. After = [1!=1]+[1!=2] = 1.
**fc drops by 1.**

### 245 -> 251: c[n-3] changes 1 -> 2

TMidVal(c[n-4], 1, 2) must equal 2.
TMidVal(1,1,2)=2 (c[n-4]=1, fc constant), TMidVal(2,1,2)=2 (c[n-4]=2, fc drops by 2).
fc non-increasing. sccSubRank drops: 2 -> 1.

### 251 -> 239: c[n-3] changes 2 -> 0

TMidVal(c[n-4], 2, 2) must equal 0.
TMidVal(0,2,2)=0. Forces c[n-4] = 0. fc constant.
sccSubRank drops: 1 -> 0.

---

## 5. Lemma: scc_edge_239_245_fc_strict_drop

**Statement.** For n >= 9, if a TP-preserving bad step transitions
boundary state from 239 to 245, then fc strictly drops.

**Proof.**

1. Boundary 239: c[n-3]=0, c[n-2]=2. Boundary 245: c[n-3]=1.
   Only c[n-3] changes, so mover is at position n-3.

2. Position n-3 uses TMidVal (`cup2OutVal_boundaryIdxN3`).
   TMidVal(c[n-4], 0, 2) = 1 forces c[n-4] = 1.

3. localFcBefore(1, 0, 2) = 2.
   localFcAfter(1, 0, 2, 1) = 1.
   Delta = -1.

4. By `cup2Fc_move_split` + `cup2Fc_rest_move_eq`:
   fc(c') = fc(c) - 1 < fc(c).

**Lean proof:** Analytical using existing fc-splitting lemmas. The table
lookup can be `native_decide` or unfolded.

---

## 6. Main Theorem: CPhiStep Decreases cphiMeasure

**Case A: Boundary fixed.**
Components 1 (condensationRank) and 3 (sccSubRank) depend only on
boundary, so unchanged.
By `fixed_boundary_fc_or_deep_drop`: either fc drops (comp 2) or
(fc same AND deep drops, comp 4). Done.

**Case B: Boundary changes, in sixTupleEdge.**

Apply `sixTuple_edge_lex_decrease` (native_decide, SixTuple.lean):

- **B1: condensationRank drops.** Component 1 drops. Done.

- **B2: condensationRank same, sccSubRank drops.**
  Both in SCC. Mover at n-3 (deep interior). fc non-increasing by
  copy-neighbor. If fc drops: comp 2 drops. If fc same: comp 3 drops.

- **B3: edge is 239->245.**
  fc strictly drops (Lemma, Section 5). Comp 2 drops. Done.

**Case C: Boundary changes, NOT in sixTupleEdge.**
This case must be shown to be impossible for CPhiSteps.
This is the **Bridge Lemma** (Section 7).

---

## 7. Bridge Lemma

**Statement.** Every boundary-changing CPhiStep has its boundary
transition in the sixTupleEdge relation (617 edges).

**Why needed.** The 4-component lex relies on `sixTuple_edge_lex_decrease`,
which only applies to edges in sixTupleEdge. A boundary-changing CPhiStep
whose boundary transition is NOT in sixTupleEdge would escape the lex
argument.

**Context.** `cup2SyntheticOuterStep_cases` (SyntheticPotential.lean:1048)
proves: every TP-preserving boundary-changing bad step either IS in
sixTupleEdge, or Psi drops. But Psi drop alone is insufficient for the
4-component lex because condensationRank/fc might simultaneously increase.

**Two approaches to prove the bridge:**

### Approach 1: Expand sixTupleEdge to all TP-preserving transitions -- RULED OUT

Verified computationally (verify_expanded_edge.py): 391 of 480 extra
TP-preserving edges have condensationRank INCREASING, not dropping.
The condensation ranking from the 617-edge CPhiStep graph does not
extend to the full 1098-edge graph. This approach is not viable.

### Approach 2: Prove via PhiFull computability (RECOMMENDED)

1. Make `cup2PhiFull` fully computable at n=9 (decidable TP-reachability
   already exists in PhiFullTP.lean).
2. Prove by native_decide at n=9 that every CPhiStep boundary transition
   is in sixTupleEdge.
3. Extend to n >= 10 via n-independence: boundary transitions depend on
   at most one interior value, and PhiFull behavior at the boundary is
   determined by the boundary 6-tuple + that one interior value.

---

## 8. Complete Proof Architecture

### What to delete from ConstLayerDAG.lean:
- `cup2BoundaryDropSegment` and related definitions
- `psiRank`, `psiRank_lt_of_Psi_lt`, `psiRank_segment_drop` (the sorry)
- `cup2BoundaryDropSegment_wf`
- `boundaryFixed_extends_segment`
- `outerStep_fixed_or_segment`
- `cup2SyntheticOuterStep_wf`
- `bad_boundary_Psi_drop` (local wrapper, not the underlying theorem)

### What to keep in ConstLayerDAG.lean:
- `wf_of_inner_segment` (used by PhiFullTP.lean for CF decomposition)
- `cup2BoundaryFixedOuterStep` definition
- `fixed_boundary_fc_or_deep_drop` (sorry-free, used in new proof)
- `cup2BoundaryFixedOuterStep_wf` (sorry-free, but may become unused)

### What to add to ConstLayerDAG.lean:

```lean
private def cphiMeasure (n : Nat) (hn4 : 4 <= n) (hn9 : 9 <= n)
    (c : Config (cup2Spec n hn4)) : Nat x Nat x Nat x Nat :=
  (condensationRank (cup2BoundaryState n hn4 hn9 c),
   cup2Fc n hn4 c,
   sccSubRank (cup2BoundaryState n hn4 hn9 c),
   deepMidHopPotential n hn4 c)

private def lex4 : Nat x Nat x Nat x Nat -> Nat x Nat x Nat x Nat -> Prop :=
  Prod.Lex (. < .) (Prod.Lex (. < .) (Prod.Lex (. < .) (. < .)))

private theorem lex4_wf : WellFounded lex4 :=
  WellFounded.prod_lex Nat.lt_wfRel.wf
    (WellFounded.prod_lex Nat.lt_wfRel.wf
      (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf))

private theorem cphi_step_measure_decrease (n : Nat) (hn4 : 4 <= n) (hn9 : 9 <= n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c) :
    lex4 (cphiMeasure n hn4 hn9 c') (cphiMeasure n hn4 hn9 c) := by
  -- Case split on boundary change
  ...

theorem cup2CPhiStep_wf (n : Nat) (hn4 : 4 <= n) (hn9 : 9 <= n) :
    WellFounded (cup2CPhiStep n hn4) :=
  Subrelation.wf
    (fun {c' c} h => cphi_step_measure_decrease n hn4 hn9 h)
    (InvImage.wf (cphiMeasure n hn4 hn9) lex4_wf)
```

### What to add to SixTuple.lean:

The bridge lemma connects CPhiStep boundary transitions to sixTupleEdge.
The proof strategy (Approach 2) requires:

1. Making `cup2PhiFull` computable at n=9 (decidable TP-reachability
   is already in PhiFullTP.lean).
2. Defining the CPhiStep boundary transition as a decidable relation.
3. Proving by native_decide at n=9 that every CPhiStep boundary
   transition is in sixTupleEdge.
4. Proving n-independence: the CPhiStep boundary edge set is the
   same for all n >= 9 (boundary transitions depend on at most one
   interior value; PhiFull behavior at boundary depends only on the
   boundary 6-tuple + that one interior value, not on n).

### Files unchanged:
- PhiFullTP.lean (wf_of_inner_segment for CF->CPhiStep decomposition)
- SyntheticPotential.lean
- Interior.lean, CopyDAG.lean

---

## 9. New Theorems Summary

| # | Theorem | File | Method | Difficulty |
|---|---------|------|--------|------------|
| 1 | Bridge lemma | SixTuple.lean | native_decide n=9 + n-indep | HARD |
| 2 | `scc_edge_239_245_fc_drop` | ConstLayerDAG.lean | TMidVal + fc arith | EASY |
| 3 | `scc_fc_nonincreasing` | ConstLayerDAG.lean | deep interior copy | EASY |
| 4 | `cphi_step_measure_decrease` | ConstLayerDAG.lean | case split | MEDIUM |
| 5 | `cup2CPhiStep_wf` | ConstLayerDAG.lean | InvImage + lex4_wf | EASY |

**Result:** 1 sorry eliminated, 0 new sorrys introduced.
The bridge (Theorem 1) is the critical path.

---

## 10. Key Findings

1. **Expanded-edge approach FAILS.** Verified: 391 of 480 non-CPhiStep
   TP-preserving boundary transitions have condensationRank increasing.
   Cannot expand sixTupleEdge to cover all TP-preserving transitions.
   (Script: `verify_expanded_edge.py`.)

2. **Bridge lemma is required.** Must prove that every boundary-changing
   CPhiStep has its boundary transition in the 617-edge sixTupleEdge list.
   The 480 non-sixTupleEdge TP-preserving transitions always change PhiFull.

3. **The 4-component lex is correct.** Once the bridge is proved, the
   cphiMeasure = (condensationRank, fc, sccSubRank, deep) strictly decreases
   on every CPhiStep. The SCC fc-edge 239->245 is handled analytically
   (TMidVal forces c[n-4]=1, local fc drops by 1).

4. **Immediate next step:** Make `cup2PhiFull` computable in Lean
   (decidable TP-reachability already in PhiFullTP.lean). Then
   native_decide the bridge at n=9. Prove n-independence analytically.
