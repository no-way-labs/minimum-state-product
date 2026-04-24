/-
  Convergence/PhiFull9.lean — Fast computable PhiFull at n=9 via Array fixpoint

  The BFS-based cup2PhiFull is correct but too slow for native_decide.
  This file computes PhiFull values via Array-memoized fixpoint iteration:
  - O(N × degree × iterations) total, not O(N²) per query
  - All values computed in one pass, then looked up

  Structure:
  1. Mixed-radix encoding Cfg9 ↔ Fin 8748
  2. Array-based fixpoint iteration
  3. Bridge classification via native_decide (using Array lookups)
-/
import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SixTuple

namespace LeanMn

private abbrev hn4_9 : 4 ≤ 9 := by omega
private abbrev hn9_9 : 9 ≤ 9 := by omega
private abbrev Cfg9 := Config (cup2Spec 9 hn4_9)

/-! ### Mixed-radix encoding: Config ↔ Nat

State sizes at n=9: [2, 3, 3, 3, 3, 3, 3, 3, 2]
Product: 2 × 3⁷ × 2 = 8748

Encoding: c[0]×4374 + c[1]×1458 + c[2]×486 + c[3]×162 + c[4]×54 + c[5]×18 + c[6]×6 + c[7]×2 + c[8]
-/

private def weights9 : Fin 9 → Nat
  | ⟨0, _⟩ => 4374
  | ⟨1, _⟩ => 1458
  | ⟨2, _⟩ => 486
  | ⟨3, _⟩ => 162
  | ⟨4, _⟩ => 54
  | ⟨5, _⟩ => 18
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 2
  | ⟨8, _⟩ => 1

private def moduli9 : Fin 9 → Nat
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 3
  | ⟨6, _⟩ => 3
  | ⟨7, _⟩ => 3
  | ⟨8, _⟩ => 2

private abbrev fin9 (k : Nat) (h : k < 9) : Fin (cup2Spec 9 hn4_9).n :=
  ⟨k, by show k < 9; exact h⟩

private def encodeCfg (c : Cfg9) : Nat :=
  (c (fin9 0 (by omega))).1 * 4374 + (c (fin9 1 (by omega))).1 * 1458 +
  (c (fin9 2 (by omega))).1 * 486 + (c (fin9 3 (by omega))).1 * 162 +
  (c (fin9 4 (by omega))).1 * 54 + (c (fin9 5 (by omega))).1 * 18 +
  (c (fin9 6 (by omega))).1 * 6 + (c (fin9 7 (by omega))).1 * 2 +
  (c (fin9 8 (by omega))).1

private def decodeDigit (idx w m : Nat) (hm : 0 < m) : Fin m :=
  ⟨(idx / w) % m, Nat.mod_lt _ hm⟩

private def decodeCfg (idx : Nat) : Cfg9 :=
  let d0 : Fin 2 := decodeDigit idx 4374 2 (by omega)
  let d1 : Fin 3 := decodeDigit idx 1458 3 (by omega)
  let d2 : Fin 3 := decodeDigit idx 486 3 (by omega)
  let d3 : Fin 3 := decodeDigit idx 162 3 (by omega)
  let d4 : Fin 3 := decodeDigit idx 54 3 (by omega)
  let d5 : Fin 3 := decodeDigit idx 18 3 (by omega)
  let d6 : Fin 3 := decodeDigit idx 6 3 (by omega)
  let d7 : Fin 3 := decodeDigit idx 2 3 (by omega)
  let d8 : Fin 2 := decodeDigit idx 1 2 (by omega)
  fun i => match i with
    | ⟨0, _⟩ => ⟨d0.1, by have := d0.2; simp [cup2Spec, cup2M]⟩
    | ⟨1, _⟩ => ⟨d1.1, by have := d1.2; simp [cup2Spec, cup2M]⟩
    | ⟨2, _⟩ => ⟨d2.1, by have := d2.2; simp [cup2Spec, cup2M]⟩
    | ⟨3, _⟩ => ⟨d3.1, by have := d3.2; simp [cup2Spec, cup2M]⟩
    | ⟨4, _⟩ => ⟨d4.1, by have := d4.2; simp [cup2Spec, cup2M]⟩
    | ⟨5, _⟩ => ⟨d5.1, by have := d5.2; simp [cup2Spec, cup2M]⟩
    | ⟨6, _⟩ => ⟨d6.1, by have := d6.2; simp [cup2Spec, cup2M]⟩
    | ⟨7, _⟩ => ⟨d7.1, by have := d7.2; simp [cup2Spec, cup2M]⟩
    | ⟨8, _⟩ => ⟨d8.1, by have := d8.2; simp [cup2Spec, cup2M]⟩

/-! ### Computable operations on encoded configs -/

private def N9 : Nat := 8748

/-- Frontier count of an encoded config. -/
private def fc9 (idx : Nat) : Nat :=
  cup2Fc 9 hn4_9 (decodeCfg idx)

/-- Fire position p at encoded config, return encoded result. -/
private def fire9 (idx : Nat) (p : Fin 9) : Nat :=
  encodeCfg (move (cup2System 9 hn4_9) (decodeCfg idx) p)

/-- Is position p privileged at encoded config? -/
private def priv9 (idx : Nat) (p : Fin 9) : Bool :=
  decide (privileged (cup2System 9 hn4_9) (decodeCfg idx) p)

/-- Is encoded config in the good cycle? -/
private def good9 (idx : Nat) : Bool :=
  decide (decodeCfg idx ∈ (cup2GoodCycle 9 hn4_9).configs)

/-- Does firing p preserve TP invariant? -/
private def tpPres9 (idx : Nat) (p : Fin 9) : Bool :=
  cup2TpInvariant 9 hn4_9 (move (cup2System 9 hn4_9) (decodeCfg idx) p) ==
    cup2TpInvariant 9 hn4_9 (decodeCfg idx)

/-- Boundary state of encoded config. -/
private def bdry9 (idx : Nat) : Nat :=
  (cup2BoundaryState 9 hn4_9 hn9_9 (decodeCfg idx)).1

/-! ### Array-based fixpoint iteration -/

/-- One step of max-propagation over all configs. -/
private def phiStep (phi : Array Nat) : Array Nat :=
  Array.ofFn fun (v : Fin N9) =>
    let base := fc9 v.1
    -- Max over TP-preserving bad successors
    let maxSucc := Fin.foldl 9 (fun acc (p : Fin 9) =>
      if priv9 v.1 p then
        let w := fire9 v.1 p
        if w < N9 && !good9 w && tpPres9 v.1 p then
          max acc (phi.getD w 0)
        else acc
      else acc) 0
    max base maxSucc

/-- Iterate phiStep k times from initial fc values. -/
private def phiIter : Nat → Array Nat
  | 0 => Array.ofFn fun (v : Fin N9) => fc9 v.1
  | k + 1 => phiStep (phiIter k)

/-- PhiFull values at n=9, computed via 20 iterations of max-propagation. -/
def phiFull9Array : Array Nat := phiIter 20

/-- PhiFull lookup for a config. -/
def phiFull9 (c : Cfg9) : Nat :=
  phiFull9Array.getD (encodeCfg c) 0

/-! ### Bridge classification at n=9 -/

/-- At n=9, every boundary-changing TP-preserving bad step either
    has its 6-tuple in the 617-edge set, or phiFull9 drops. -/
theorem bridge_class9 :
    ∀ (c : Cfg9) (i : Fin 9),
    privileged (cup2System 9 hn4_9) c i →
    c ∉ (cup2GoodCycle 9 hn4_9).configs →
    move (cup2System 9 hn4_9) c i ∉ (cup2GoodCycle 9 hn4_9).configs →
    cup2TpInvariant 9 hn4_9 (move (cup2System 9 hn4_9) c i) =
      cup2TpInvariant 9 hn4_9 c →
    cup2BoundaryState 9 hn4_9 hn9_9
      (move (cup2System 9 hn4_9) c i) ≠
      cup2BoundaryState 9 hn4_9 hn9_9 c →
    sixTupleEdge
      (cup2BoundaryState 9 hn4_9 hn9_9 (move (cup2System 9 hn4_9) c i))
      (cup2BoundaryState 9 hn4_9 hn9_9 c) ∨
    phiFull9 (move (cup2System 9 hn4_9) c i) <
      phiFull9 c := by
  native_decide

end LeanMn
