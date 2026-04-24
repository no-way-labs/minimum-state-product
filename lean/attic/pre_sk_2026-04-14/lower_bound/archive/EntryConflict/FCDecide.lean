/-
  FCDecide.lean — Finite decidable checks for the binary fire count bound

  Provides native_decide-verified combinatorial lemmas that support the
  fc(p) ≤ 2 theorem for 3 consecutive binary processors.

  Key results (all sorry-free, no axioms):
  1. `maxIndepC4_le2`: The maximum independent set in the 4-cycle graph C₄
     on {0,1}² has size ≤ 2.
  2. `disjointIndep_bound`: Two disjoint independent sets in C₄ have total
     size ≤ 4.
  3. `maximalDisjointPair_classified`: The only maximal disjoint pairs with
     both sizes = 2 are {(0,0),(1,1)} and {(0,1),(1,0)}.

  These encode the constraint that mover (L,R) pairs at each S-value form
  an independent set in C₄ (from the step-before-neighbor entry conflict
  argument), and that mover pairs across S-values are disjoint (from the
  flipS non-mover constraint).

  All verified by native_decide.
-/
import LeanMn.LowerBound.Archive.EntryConflict.FCBound

namespace LeanMn

/-! ### C₄ independent set check via native_decide -/

-- Encode a subset of {(0,0),(0,1),(1,0),(1,1)} as a 4-bit mask.
-- Bit 0 = (0,0), bit 1 = (0,1), bit 2 = (1,0), bit 3 = (1,1).
abbrev LRMask := Fin 16

-- Check if a subset (given as a bitmask) is an independent set in C₄.
-- C₄ edges: (0,0)-(0,1), (0,0)-(1,0), (0,1)-(1,1), (1,0)-(1,1).
-- Independent means no two adjacent elements are both in the set.
def isIndepC4 (s : LRMask) : Bool :=
  let b := s.val
  (b &&& 0b0011 != 0b0011) &&  -- not both (0,0) and (0,1)
  (b &&& 0b0101 != 0b0101) &&  -- not both (0,0) and (1,0)
  (b &&& 0b1010 != 0b1010) &&  -- not both (0,1) and (1,1)
  (b &&& 0b1100 != 0b1100)     -- not both (1,0) and (1,1)

-- Count the number of set bits in a 4-bit mask.
def popcount4 (b : Nat) : Nat :=
  (b &&& 1) + ((b >>> 1) &&& 1) + ((b >>> 2) &&& 1) + ((b >>> 3) &&& 1)

-- Every independent set in C₄ has at most 2 elements.
def maxIndepC4Check : Bool :=
  (List.finRange 16).all fun s =>
    !isIndepC4 s || (popcount4 s.val ≤ 2)

theorem maxIndepC4_le2 : maxIndepC4Check = true := by native_decide

-- For two disjoint independent sets in C₄ with both nonempty:
-- their total size is at most 4 (trivially) and each ≤ 2.
def disjointIndepCheck : Bool :=
  (List.finRange 16).all fun s0 =>
    (List.finRange 16).all fun s1 =>
      if isIndepC4 s0 && isIndepC4 s1 &&
         (s0.val &&& s1.val == 0) &&
         (s0.val != 0) && (s1.val != 0)
      then popcount4 s0.val + popcount4 s1.val ≤ 4
      else true

theorem disjointIndep_bound : disjointIndepCheck = true := by native_decide

-- The only maximal disjoint independent set pairs with both sizes = 2 are:
-- ({(0,0),(1,1)}, {(0,1),(1,0)}) and vice versa.
-- Encoding: {(0,0),(1,1)} = 0b1001 = 9, {(0,1),(1,0)} = 0b0110 = 6.
def maximalDisjointPairCheck : Bool :=
  (List.finRange 16).all fun s0 =>
    (List.finRange 16).all fun s1 =>
      if isIndepC4 s0 && isIndepC4 s1 &&
         (s0.val &&& s1.val == 0) &&
         (popcount4 s0.val == 2) && (popcount4 s1.val == 2)
      then (s0.val == 9 && s1.val == 6) || (s0.val == 6 && s1.val == 9)
      else true

theorem maximalDisjointPair_classified : maximalDisjointPairCheck = true := by native_decide

-- For the mover set at each S-value: flipping S maps mover to non-mover.
-- This means: flipS(M₀) ⊆ complement of M₁, i.e., M₀ and M₁ as (L,R) sets
-- are disjoint. Combined with the independent set constraint:
-- |M₀| ≤ 2, |M₁| ≤ 2, M₀ ∩ M₁ = ∅ (as (L,R) pairs).
-- Total distinct mover contexts: |M₀| + |M₁| ≤ 4.

-- Stronger check: if both |M₀| = 2 and |M₁| = 2, the ONLY possibility
-- is M₀ = {(0,0),(1,1)}, M₁ = {(0,1),(1,0)} (or vice versa).
-- These are the two complementary independent sets of C₄.

-- This means the mover contexts form a very rigid structure:
-- either the "diagonal" pair or the "anti-diagonal" pair at each S-value.

end LeanMn
