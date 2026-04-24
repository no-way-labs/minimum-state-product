import LeanMn.Convergence.TP
import LeanMn.Convergence.SixTuple

namespace LeanMn

private def cup2Idx3 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨3, by omega⟩

private def cup2IdxN4 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨n - 4, by omega⟩

private def p002ExceptionalMidIdx
    (n : Nat) (hn9 : 9 ≤ n) (k : Nat) (hk : k < n - 6) : Fin n :=
  ⟨3 + k, by omega⟩

private theorem p002ExceptionalMidIdx_zero
    (n : Nat) (hn9 : 9 ≤ n) :
    p002ExceptionalMidIdx n hn9 0 (by omega) = cup2Idx3 n hn9 := by
  apply Fin.ext
  simp [p002ExceptionalMidIdx, cup2Idx3]

private theorem p002ExceptionalMidIdx_last
    (n : Nat) (hn9 : 9 ≤ n) :
    p002ExceptionalMidIdx n hn9 (n - 7) (by omega) = cup2IdxN4 n hn9 := by
  apply Fin.ext
  simp [p002ExceptionalMidIdx, cup2IdxN4]
  omega

private theorem right_p002ExceptionalMidIdx
    (n : Nat) (hn9 : 9 ≤ n)
    (k : Nat) (hk : k + 1 < n - 6) :
    right (p002ExceptionalMidIdx n hn9 k (by omega)) =
      p002ExceptionalMidIdx n hn9 (k + 1) hk := by
  have htop : (p002ExceptionalMidIdx n hn9 k (by omega)).1 + 1 ≠ n := by
    simp [p002ExceptionalMidIdx]
    omega
  apply Fin.ext
  rw [right_val_of_not_top (i := p002ExceptionalMidIdx n hn9 k (by omega)) htop]
  simp [p002ExceptionalMidIdx]
  omega

private def p002ExceptionalBoundaryA0B0Vals : List Nat :=
  [6, 7, 8, 9, 11, 42, 43, 44, 45, 47, 153, 155, 168, 170, 171, 173, 204, 206, 207,
    209, 222, 224, 225, 227, 240, 242, 243, 245, 258, 260, 261, 263, 312, 314, 315, 317]

private def p002ExceptionalBoundaryA0BpVals : List Nat :=
  [6, 7, 8, 9, 11, 168, 170, 171, 173, 222, 224, 225, 227, 240, 242, 243, 245]

private def p002ExceptionalBoundaryAPosVals : List Nat :=
  [240, 242, 243, 245]

private def p002ExceptionalBoundaryA0B0 (s : SixBoundary) : Prop :=
  s.encode.1 ∈ p002ExceptionalBoundaryA0B0Vals

private def p002ExceptionalBoundaryA0Bp (s : SixBoundary) : Prop :=
  s.encode.1 ∈ p002ExceptionalBoundaryA0BpVals

private def p002ExceptionalBoundaryAPos (s : SixBoundary) : Prop :=
  s.encode.1 ∈ p002ExceptionalBoundaryAPosVals

private instance (s : SixBoundary) : Decidable (p002ExceptionalBoundaryA0B0 s) := by
  unfold p002ExceptionalBoundaryA0B0
  infer_instance

private instance (s : SixBoundary) : Decidable (p002ExceptionalBoundaryA0Bp s) := by
  unfold p002ExceptionalBoundaryA0Bp
  infer_instance

private instance (s : SixBoundary) : Decidable (p002ExceptionalBoundaryAPos s) := by
  unfold p002ExceptionalBoundaryAPos
  infer_instance

private def p002ExceptionalBoundaryForAB
    (s : SixBoundary) (a b : Nat) : Prop :=
  if 0 < a then
    p002ExceptionalBoundaryAPos s
  else if 0 < b then
    p002ExceptionalBoundaryA0Bp s
  else
    p002ExceptionalBoundaryA0B0 s

private theorem p002Exceptional_left_idx_lt
    (n a b cLen k : Nat)
    (hlen : a + b + cLen = n - 6)
    (hk : k < a) :
    3 + k < n := by
  omega

private theorem p002Exceptional_mid_idx_lt
    (n a b cLen k : Nat)
    (hlen : a + b + cLen = n - 6)
    (hk : k < b) :
    3 + a + k < n := by
  omega

private theorem p002Exceptional_right_idx_lt
    (n a b cLen k : Nat)
    (hlen : a + b + cLen = n - 6)
    (hk : k < cLen) :
    3 + a + b + k < n := by
  omega

private def p002ExceptionalMidABC
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (cfg : Config (cup2Spec n hn4))
    (a b cLen : Nat) : Prop :=
  ∃ hlen : a + b + cLen = n - 6,
    1 ≤ cLen ∧
      (∀ k : Nat, ∀ hk : k < a,
        (cfg ⟨3 + k, p002Exceptional_left_idx_lt n a b cLen k hlen hk⟩).1 = 1) ∧
      (∀ k : Nat, ∀ hk : k < b,
        (cfg ⟨3 + a + k, p002Exceptional_mid_idx_lt n a b cLen k hlen hk⟩).1 = 0) ∧
      (∀ k : Nat, ∀ hk : k < cLen,
        (cfg ⟨3 + a + b + k, p002Exceptional_right_idx_lt n a b cLen k hlen hk⟩).1 = 2)

def p002ExceptionalMidShape
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (cfg : Config (cup2Spec n hn4)) : Prop :=
  ∃ a b cLen, p002ExceptionalMidABC n hn4 hn9 cfg a b cLen

def p002ExceptionalFamily
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (cfg : Config (cup2Spec n hn4)) : Prop :=
  ∃ a b cLen,
    p002ExceptionalMidABC n hn4 hn9 cfg a b cLen ∧
      p002ExceptionalBoundaryForAB (cup2Boundary6 n hn4 hn9 cfg) a b

theorem p002ExceptionalMidShape_witness
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a b cLen : Nat}
    (hshape : p002ExceptionalMidABC n hn4 hn9 cfg a b cLen) :
    p002ExceptionalMidShape n hn4 hn9 cfg := by
  exact ⟨a, b, cLen, hshape⟩

theorem p002ExceptionalFamily_of_mid_boundary
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a b cLen : Nat}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a b cLen)
    (hboundary : p002ExceptionalBoundaryForAB (cup2Boundary6 n hn4 hn9 cfg) a b) :
    p002ExceptionalFamily n hn4 hn9 cfg := by
  exact ⟨a, b, cLen, hmid, hboundary⟩

theorem p002ExceptionalBoundaryA0B0_count :
    p002ExceptionalBoundaryA0B0Vals.length = 36 := by native_decide

theorem p002ExceptionalBoundaryA0Bp_count :
    p002ExceptionalBoundaryA0BpVals.length = 17 := by native_decide

theorem p002ExceptionalBoundaryAPos_count :
    p002ExceptionalBoundaryAPosVals.length = 4 := by native_decide

private theorem p002ExceptionalBoundaryA0B0_cN3_one
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryA0B0 s) :
    s.cN3.1 = 1 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryA0B0 s → s.cN3.1 = 1 := by
    native_decide
  exact hclosed s hmem

private theorem p002ExceptionalBoundaryA0Bp_cN3_one
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryA0Bp s) :
    s.cN3.1 = 1 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryA0Bp s → s.cN3.1 = 1 := by
    native_decide
  exact hclosed s hmem

private theorem p002ExceptionalBoundaryA0Bp_c2_ne_two
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryA0Bp s) :
    s.c2.1 ≠ 2 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryA0Bp s → s.c2.1 ≠ 2 := by
    native_decide
  exact hclosed s hmem

private theorem p002ExceptionalBoundaryAPos_cN3_one
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryAPos s) :
    s.cN3.1 = 1 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryAPos s → s.cN3.1 = 1 := by
    native_decide
  exact hclosed s hmem

private theorem p002ExceptionalBoundaryAPos_c2_one
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryAPos s) :
    s.c2.1 = 1 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryAPos s → s.c2.1 = 1 := by
    native_decide
  exact hclosed s hmem

private def p002ExceptionalBoundaryBudgetA0B0 (s : SixBoundary) : Nat :=
  frontierBitVal s.c0.1 s.c1.1 +
    frontierBitVal s.c1.1 s.c2.1 +
    frontierBitVal s.c2.1 2 +
    frontierBitVal s.cN3.1 s.cN2.1 +
    frontierBitVal s.cN2.1 s.cN1.1 +
    frontierBitVal s.cN1.1 s.c0.1

private def p002ExceptionalBoundaryBudgetA0Bp (s : SixBoundary) : Nat :=
  frontierBitVal s.c0.1 s.c1.1 +
    frontierBitVal s.c1.1 s.c2.1 +
    frontierBitVal s.c2.1 0 +
    frontierBitVal s.cN3.1 s.cN2.1 +
    frontierBitVal s.cN2.1 s.cN1.1 +
    frontierBitVal s.cN1.1 s.c0.1

private def p002ExceptionalBoundaryBudgetAPos (s : SixBoundary) : Nat :=
  frontierBitVal s.c0.1 s.c1.1 +
    frontierBitVal s.c1.1 s.c2.1 +
    frontierBitVal s.c2.1 1 +
    frontierBitVal s.cN3.1 s.cN2.1 +
    frontierBitVal s.cN2.1 s.cN1.1 +
    frontierBitVal s.cN1.1 s.c0.1

private theorem p002ExceptionalBoundaryBudgetA0B0_le_four
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryA0B0 s) :
    p002ExceptionalBoundaryBudgetA0B0 s ≤ 4 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryA0B0 s →
        p002ExceptionalBoundaryBudgetA0B0 s ≤ 4 := by
    native_decide
  exact hclosed s hmem

private theorem p002ExceptionalBoundaryBudgetA0Bp_le_three
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryA0Bp s) :
    p002ExceptionalBoundaryBudgetA0Bp s ≤ 3 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryA0Bp s →
        p002ExceptionalBoundaryBudgetA0Bp s ≤ 3 := by
    native_decide
  exact hclosed s hmem

private theorem p002ExceptionalBoundaryBudgetAPos_le_two
    (s : SixBoundary)
    (hmem : p002ExceptionalBoundaryAPos s) :
    p002ExceptionalBoundaryBudgetAPos s ≤ 2 := by
  have hclosed :
      ∀ s : SixBoundary, p002ExceptionalBoundaryAPos s →
        p002ExceptionalBoundaryBudgetAPos s ≤ 2 := by
    native_decide
  exact hclosed s hmem

private def p002ExceptionalFcTerm
    (n : Nat) (hn4 : 4 ≤ n)
    (cfg : Config (cup2Spec n hn4)) (j : Nat) (hj : j < n) : Nat :=
  cup2FrontierBit n hn4 cfg ⟨j, hj⟩

theorem p002Exceptional_allTwos_start_family
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (cfg : Config (cup2Spec n hn4))
    (hc0 : (cfg (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (cfg (cup2BoundaryIdx1 n hn9)).1 = 0)
    (hc2 : (cfg (cup2BoundaryIdx2 n hn9)).1 = 2)
    (hcN3 : (cfg (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hcN2 : (cfg (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (cfg (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hmid : ∀ k : Nat, ∀ hk : k < n - 6,
      (cfg ⟨3 + k, p002Exceptional_right_idx_lt n 0 0 (n - 6) k (by omega) hk⟩).1 = 2) :
    p002ExceptionalFamily n hn4 hn9 cfg := by
  have hmidABC : p002ExceptionalMidABC n hn4 hn9 cfg 0 0 (n - 6) := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro k hk
      omega
    · intro k hk
      omega
    · intro k hk
      simpa using hmid k hk
  have hboundaryEq :
      cup2Boundary6 n hn4 hn9 cfg =
        { c0 := (⟨0, by decide⟩ : Fin 2)
          c1 := (⟨0, by decide⟩ : Fin 3)
          c2 := (⟨2, by decide⟩ : Fin 3)
          cN3 := (⟨1, by decide⟩ : Fin 3)
          cN2 := (⟨0, by decide⟩ : Fin 3)
          cN1 := (⟨1, by decide⟩ : Fin 2) } := by
    ext <;> simp [cup2Boundary6, hc0, hc1, hc2, hcN3, hcN2, hcN1]
  have hboundary : p002ExceptionalBoundaryForAB (cup2Boundary6 n hn4 hn9 cfg) 0 0 := by
    have henc :
        ({ c0 := (⟨0, by decide⟩ : Fin 2)
           c1 := (⟨0, by decide⟩ : Fin 3)
           c2 := (⟨2, by decide⟩ : Fin 3)
           cN3 := (⟨1, by decide⟩ : Fin 3)
           cN2 := (⟨0, by decide⟩ : Fin 3)
           cN1 := (⟨1, by decide⟩ : Fin 2) } : SixBoundary).encode.1 = 43 := by
      native_decide
    rw [p002ExceptionalBoundaryForAB]
    simp
    rw [hboundaryEq, p002ExceptionalBoundaryA0B0, henc]
    native_decide
  exact p002ExceptionalFamily_of_mid_boundary n hn4 hn9 hmidABC hboundary

theorem p002ExceptionalFamily_cN3_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hfamily : p002ExceptionalFamily n hn4 hn9 cfg) :
    (cfg (cup2BoundaryIdxN3 n hn9)).1 = 1 := by
  rcases hfamily with ⟨a, b, cLen, _hmid, hboundary⟩
  by_cases ha : 0 < a
  · simp [p002ExceptionalBoundaryForAB, ha] at hboundary
    simpa [cup2Boundary6] using
      p002ExceptionalBoundaryAPos_cN3_one (cup2Boundary6 n hn4 hn9 cfg) hboundary
  · by_cases hb : 0 < b
    · simp [p002ExceptionalBoundaryForAB, ha, hb] at hboundary
      simpa [cup2Boundary6] using
        p002ExceptionalBoundaryA0Bp_cN3_one (cup2Boundary6 n hn4 hn9 cfg) hboundary
    · simp [p002ExceptionalBoundaryForAB, ha, hb] at hboundary
      simpa [cup2Boundary6] using
        p002ExceptionalBoundaryA0B0_cN3_one (cup2Boundary6 n hn4 hn9 cfg) hboundary

theorem p002ExceptionalBoundaryForAB_c2_ne_two_of_prefix
    (s : SixBoundary) {a b : Nat}
    (hboundary : p002ExceptionalBoundaryForAB s a b)
    (hprefix : 0 < a ∨ 0 < b) :
    s.c2.1 ≠ 2 := by
  by_cases ha : 0 < a
  · simp [p002ExceptionalBoundaryForAB, ha, p002ExceptionalBoundaryAPos] at hboundary
    have hc2 := p002ExceptionalBoundaryAPos_c2_one s hboundary
    omega
  · have hb : 0 < b := by
      rcases hprefix with ha' | hb'
      · exact False.elim (ha ha')
      · exact hb'
    simp [p002ExceptionalBoundaryForAB, ha, hb] at hboundary
    exact p002ExceptionalBoundaryA0Bp_c2_ne_two s hboundary

theorem p002ExceptionalMidABC_last_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a b cLen : Nat}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a b cLen) :
    (cfg (cup2IdxN4 n hn9)).1 = 2 := by
  rcases hmid with ⟨hlen, hcpos, _hones, _hzeros, htwos⟩
  have hk : cLen - 1 < cLen := by
    omega
  have hidx :
      3 + a + b + (cLen - 1) = n - 4 := by
    omega
  have hfin :
      (⟨3 + a + b + (cLen - 1),
          p002Exceptional_right_idx_lt n a b cLen (cLen - 1) hlen hk⟩ : Fin n) =
        cup2IdxN4 n hn9 := by
    apply Fin.ext
    simp [cup2IdxN4, hidx]
  rw [← hfin]
  exact htwos (cLen - 1) hk

theorem p002ExceptionalMidABC_idx3_ne_two_of_prefix
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a b cLen : Nat}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a b cLen)
    (hprefix : 0 < a ∨ 0 < b) :
    (cfg (cup2Idx3 n hn9)).1 ≠ 2 := by
  rcases hmid with ⟨hlen, _hcpos, hones, hzeros, _htwos⟩
  by_cases ha : 0 < a
  · have h3 : (cfg (cup2Idx3 n hn9)).1 = 1 := by
      simpa using hones 0 ha
    omega
  · have hb : 0 < b := by
      rcases hprefix with ha' | hb'
      · exact False.elim (ha ha')
      · exact hb'
    have hzeroa : a = 0 := by omega
    have hidx3 :
        (⟨3 + a + 0, p002Exceptional_mid_idx_lt n a b cLen 0 hlen hb⟩ : Fin n) =
          cup2Idx3 n hn9 := by
      apply Fin.ext
      simp [cup2Idx3, hzeroa]
    have h3 : (cfg (cup2Idx3 n hn9)).1 = 0 := by
      rw [← hidx3]
      exact hzeros 0 hb
    omega

theorem p002ExceptionalA0B0_midIdx_eq_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 0 (n - 6))
    (k : Nat) (hk : k < n - 6) :
    (cfg (p002ExceptionalMidIdx n hn9 k hk)).1 = 2 := by
  rcases hmid with ⟨hlen, _hcpos, _hones, _hzeros, htwos⟩
  simpa [p002ExceptionalMidIdx] using htwos k hk

theorem p002ExceptionalA0B0_mid_frontier_zero
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 0 (n - 6))
    (k : Nat) (hk : k + 1 < n - 6) :
    cup2FrontierBit n hn4 cfg (p002ExceptionalMidIdx n hn9 k (by omega)) = 0 := by
  have hcur := p002ExceptionalA0B0_midIdx_eq_two n hn4 hn9 hmid k (by omega)
  have hnext := p002ExceptionalA0B0_midIdx_eq_two n hn4 hn9 hmid (k + 1) hk
  have hright := right_p002ExceptionalMidIdx n hn9 k hk
  unfold cup2FrontierBit frontierBitVal
  rw [hright, hcur, hnext]
  decide

theorem p002ExceptionalFamily_frontier_at_n4
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hfamily : p002ExceptionalFamily n hn4 hn9 cfg) :
    cup2FrontierBit n hn4 cfg (cup2IdxN4 n hn9) = 1 := by
  rcases hfamily with ⟨a, b, cLen, hmid, hboundary⟩
  have hfamily' : p002ExceptionalFamily n hn4 hn9 cfg := by
    exact ⟨a, b, cLen, hmid, hboundary⟩
  have hlast : (cfg (cup2IdxN4 n hn9)).1 = 2 :=
    p002ExceptionalMidABC_last_two n hn4 hn9 hmid
  have hN3 : (cfg (cup2BoundaryIdxN3 n hn9)).1 = 1 :=
    p002ExceptionalFamily_cN3_one n hn4 hn9 hfamily'
  have hright : right (cup2IdxN4 n hn9) = cup2BoundaryIdxN3 n hn9 := by
    have htop : (cup2IdxN4 n hn9).1 + 1 ≠ n := by
      simp [cup2IdxN4]
      omega
    apply Fin.ext
    rw [right_val_of_not_top (i := cup2IdxN4 n hn9) htop]
    simp [cup2IdxN4, cup2BoundaryIdxN3]
    omega
  unfold cup2FrontierBit frontierBitVal
  rw [hright]
  rw [hlast, hN3]
  decide

theorem p002ExceptionalA0B0_prefix_bit_sum
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 0 (n - 6))
    :
    cup2FrontierBit n hn4 cfg (cup2BoundaryIdx0 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdx1 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdx2 n hn9) =
      frontierBitVal (cfg (cup2BoundaryIdx0 n hn9)).1 (cfg (cup2BoundaryIdx1 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdx1 n hn9)).1 (cfg (cup2BoundaryIdx2 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdx2 n hn9)).1 2 := by
  have h3 : (cfg (cup2Idx3 n hn9)).1 = 2 := by
    rcases hmid with ⟨hlen, _hcpos, _hones, _hzeros, htwos⟩
    have hk : 0 < n - 6 := by omega
    have h := htwos 0 hk
    have hfin :
        (⟨3 + 0 + 0 + 0, p002Exceptional_right_idx_lt n 0 0 (n - 6) 0 hlen hk⟩ : Fin n) =
          cup2Idx3 n hn9 := by
      apply Fin.ext
      simp [cup2Idx3]
    simpa [hfin] using h
  have hright2 :
      right (cup2BoundaryIdx2 n hn9) = cup2Idx3 n hn9 := by
    have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdx2]; omega
    apply Fin.ext
    rw [right_val_of_not_top (i := cup2BoundaryIdx2 n hn9) htop]
    simp [cup2BoundaryIdx2, cup2Idx3]
  have hr0 : right (cup2BoundaryIdx0 n hn9) = cup2BoundaryIdx1 n hn9 :=
    right_cup2BoundaryIdx0 n hn9
  have hr1 : right (cup2BoundaryIdx1 n hn9) = cup2BoundaryIdx2 n hn9 :=
    right_cup2BoundaryIdx1 n hn9
  have hv0 : (cfg (right (cup2BoundaryIdx0 n hn9))).1 = (cfg (cup2BoundaryIdx1 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hr0
  have hv1 : (cfg (right (cup2BoundaryIdx1 n hn9))).1 = (cfg (cup2BoundaryIdx2 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hr1
  have hv2 : (cfg (right (cup2BoundaryIdx2 n hn9))).1 = (cfg (cup2Idx3 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hright2
  simp only [cup2FrontierBit, hv0, hv1, hv2, h3]

theorem p002ExceptionalA0B0_suffix_bit_sum
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (cfg : Config (cup2Spec n hn4)) :
    cup2FrontierBit n hn4 cfg (cup2BoundaryIdxN3 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdxN2 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdxN1 n hn9) =
      frontierBitVal (cfg (cup2BoundaryIdxN3 n hn9)).1 (cfg (cup2BoundaryIdxN2 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdxN2 n hn9)).1 (cfg (cup2BoundaryIdxN1 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdxN1 n hn9)).1 (cfg (cup2BoundaryIdx0 n hn9)).1 := by
  have hrN3 : right (cup2BoundaryIdxN3 n hn9) = cup2BoundaryIdxN2 n hn9 :=
    right_cup2BoundaryIdxN3 n hn9
  have hrN2 : right (cup2BoundaryIdxN2 n hn9) = cup2BoundaryIdxN1 n hn9 :=
    right_cup2BoundaryIdxN2 n hn9
  have hrN1 : right (cup2BoundaryIdxN1 n hn9) = cup2BoundaryIdx0 n hn9 :=
    right_cup2BoundaryIdxN1 n hn9
  have hvN3 : (cfg (right (cup2BoundaryIdxN3 n hn9))).1 = (cfg (cup2BoundaryIdxN2 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hrN3
  have hvN2 : (cfg (right (cup2BoundaryIdxN2 n hn9))).1 = (cfg (cup2BoundaryIdxN1 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hrN2
  have hvN1 : (cfg (right (cup2BoundaryIdxN1 n hn9))).1 = (cfg (cup2BoundaryIdx0 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hrN1
  simp only [cup2FrontierBit, hvN3, hvN2, hvN1]

private def p002MidFinset (n : Nat) (hn9 : 9 ≤ n) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => 3 ≤ j.val ∧ j.val + 4 < n)

private theorem p002_univ_decompose (n : Nat) (hn9 : 9 ≤ n) (f : Fin n → Nat) :
    (∑ j : Fin n, f j) =
      f (cup2BoundaryIdx0 n hn9) + f (cup2BoundaryIdx1 n hn9) + f (cup2BoundaryIdx2 n hn9) +
        (∑ j ∈ p002MidFinset n hn9, f j) +
        f (cup2IdxN4 n hn9) +
        f (cup2BoundaryIdxN3 n hn9) + f (cup2BoundaryIdxN2 n hn9) +
        f (cup2BoundaryIdxN1 n hn9) := by
  have hsplit :
      (Finset.univ : Finset (Fin n)) =
        ({cup2BoundaryIdx0 n hn9, cup2BoundaryIdx1 n hn9, cup2BoundaryIdx2 n hn9,
          cup2IdxN4 n hn9, cup2BoundaryIdxN3 n hn9, cup2BoundaryIdxN2 n hn9,
          cup2BoundaryIdxN1 n hn9} : Finset (Fin n)) ∪ p002MidFinset n hn9 := by
    apply Finset.ext
    intro j
    have hj : j.val < n := j.2
    constructor
    · intro _
      rw [Finset.mem_union]
      rcases Nat.lt_or_ge j.val 3 with hlo | hlo
      · rcases Nat.lt_or_ge j.val 1 with hlo2 | hlo2
        · -- j.val = 0
          have hveq : j.val = 0 := by omega
          have hj_eq : j = cup2BoundaryIdx0 n hn9 := Fin.ext (by simp [cup2BoundaryIdx0, hveq])
          exact Or.inl (by simp [hj_eq])
        · rcases Nat.lt_or_ge j.val 2 with hlo3 | hlo3
          · have hveq : j.val = 1 := by omega
            have hj_eq : j = cup2BoundaryIdx1 n hn9 := Fin.ext (by simp [cup2BoundaryIdx1, hveq])
            exact Or.inl (by simp [hj_eq])
          · have hveq : j.val = 2 := by omega
            have hj_eq : j = cup2BoundaryIdx2 n hn9 := Fin.ext (by simp [cup2BoundaryIdx2, hveq])
            exact Or.inl (by simp [hj_eq])
      · rcases Nat.lt_or_ge j.val (n - 4) with hmidlo | hmidhi
        · refine Or.inr ?_
          simp only [p002MidFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hlo, by omega⟩
        · rcases Nat.lt_or_ge j.val (n - 3) with hhi1 | hhi1
          · have hveq : j.val = n - 4 := by omega
            have hj_eq : j = cup2IdxN4 n hn9 := Fin.ext (by simp [cup2IdxN4, hveq])
            exact Or.inl (by simp [hj_eq])
          · rcases Nat.lt_or_ge j.val (n - 2) with hhi2 | hhi2
            · have hveq : j.val = n - 3 := by omega
              have hj_eq : j = cup2BoundaryIdxN3 n hn9 := Fin.ext (by simp [cup2BoundaryIdxN3, hveq])
              exact Or.inl (by simp [hj_eq])
            · rcases Nat.lt_or_ge j.val (n - 1) with hhi3 | hhi3
              · have hveq : j.val = n - 2 := by omega
                have hj_eq : j = cup2BoundaryIdxN2 n hn9 := Fin.ext (by simp [cup2BoundaryIdxN2, hveq])
                exact Or.inl (by simp [hj_eq])
              · have hveq : j.val = n - 1 := by omega
                have hj_eq : j = cup2BoundaryIdxN1 n hn9 := Fin.ext (by simp [cup2BoundaryIdxN1, hveq])
                exact Or.inl (by simp [hj_eq])
    · intro _; exact Finset.mem_univ _
  have hdisj :
      Disjoint ({cup2BoundaryIdx0 n hn9, cup2BoundaryIdx1 n hn9, cup2BoundaryIdx2 n hn9,
          cup2IdxN4 n hn9, cup2BoundaryIdxN3 n hn9, cup2BoundaryIdxN2 n hn9,
          cup2BoundaryIdxN1 n hn9} : Finset (Fin n))
        (p002MidFinset n hn9) := by
    rw [Finset.disjoint_left]
    intro j hj hmid
    simp only [p002MidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hmid
    simp only [Finset.mem_insert, Finset.mem_singleton, cup2BoundaryIdx0, cup2BoundaryIdx1,
      cup2BoundaryIdx2, cup2IdxN4, cup2BoundaryIdxN3, cup2BoundaryIdxN2,
      cup2BoundaryIdxN1] at hj
    rcases hj with h | h | h | h | h | h | h <;>
      · subst h
        simp only [Fin.val_mk] at hmid
        omega
  rw [show (∑ j : Fin n, f j) = ∑ j ∈ Finset.univ, f j from rfl, hsplit, Finset.sum_union hdisj]
  have h01 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro h; exact absurd (Fin.mk.inj_iff.mp h) (by simp [cup2BoundaryIdx0, cup2BoundaryIdx1])
  have h02 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
    intro h; exact absurd (Fin.mk.inj_iff.mp h) (by simp [cup2BoundaryIdx0, cup2BoundaryIdx2])
  have h0N4 : cup2BoundaryIdx0 n hn9 ≠ cup2IdxN4 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h; simp [cup2BoundaryIdx0, cup2IdxN4] at this; omega
  have h0N3 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN3] at this; omega
  have h0N2 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN2] at this; omega
  have h0N1 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at this; omega
  have h12 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
    intro h; exact absurd (Fin.mk.inj_iff.mp h) (by simp [cup2BoundaryIdx1, cup2BoundaryIdx2])
  have h1N4 : cup2BoundaryIdx1 n hn9 ≠ cup2IdxN4 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h; simp [cup2BoundaryIdx1, cup2IdxN4] at this; omega
  have h1N3 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN3] at this; omega
  have h1N2 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN2] at this; omega
  have h1N1 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at this; omega
  have h2N4 : cup2BoundaryIdx2 n hn9 ≠ cup2IdxN4 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h; simp [cup2BoundaryIdx2, cup2IdxN4] at this; omega
  have h2N3 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN3] at this; omega
  have h2N2 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN2] at this; omega
  have h2N1 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at this; omega
  have hN4N3 : cup2IdxN4 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2IdxN4, cup2BoundaryIdxN3] at this; omega
  have hN4N2 : cup2IdxN4 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2IdxN4, cup2BoundaryIdxN2] at this; omega
  have hN4N1 : cup2IdxN4 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2IdxN4, cup2BoundaryIdxN1] at this; omega
  have hN3N2 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdxN3, cup2BoundaryIdxN2] at this; omega
  have hN3N1 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdxN3, cup2BoundaryIdxN1] at this; omega
  have hN2N1 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h; have := Fin.mk.inj_iff.mp h
    simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at this; omega
  rw [Finset.sum_insert (by simp [h01, h02, h0N4, h0N3, h0N2, h0N1]),
      Finset.sum_insert (by simp [h12, h1N4, h1N3, h1N2, h1N1]),
      Finset.sum_insert (by simp [h2N4, h2N3, h2N2, h2N1]),
      Finset.sum_insert (by simp [hN4N3, hN4N2, hN4N1]),
      Finset.sum_insert (by simp [hN3N2, hN3N1]),
      Finset.sum_insert (by simp [hN2N1]),
      Finset.sum_singleton]
  ring

theorem p002ExceptionalA0B0_mid_sum_zero
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 0 (n - 6)) :
    (∑ j ∈ p002MidFinset n hn9, cup2FrontierBit n hn4 cfg j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [p002MidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨hjge, hjlt⟩ := hj
  rcases hmid with ⟨hlen, _hcpos, _hones, _hzeros, htwos⟩
  have hj1 : j.val - 3 < n - 6 := by omega
  have hj2 : j.val + 1 - 3 < n - 6 := by omega
  have hcur : (cfg j).1 = 2 := by
    have hfin :
        (⟨3 + (j.val - 3),
          p002Exceptional_right_idx_lt n 0 0 (n - 6) (j.val - 3) hlen hj1⟩ : Fin n) = j := by
      apply Fin.ext
      simp
      omega
    rw [← hfin]
    exact htwos (j.val - 3) hj1
  have hvright : (cfg (right j)).1 = 2 := by
    have htop : j.val + 1 ≠ n := by omega
    have hr : right j = ⟨j.val + 1, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := j) htop]
    have hfin :
        (⟨3 + (j.val + 1 - 3),
          p002Exceptional_right_idx_lt n 0 0 (n - 6) (j.val + 1 - 3) hlen hj2⟩ : Fin n) =
            (⟨j.val + 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp
      omega
    rw [hr, ← hfin]
    exact htwos (j.val + 1 - 3) hj2
  unfold cup2FrontierBit frontierBitVal
  rw [hcur, hvright]
  decide

theorem p002ExceptionalA0B0_fc_eq_budget_plus_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 0 (n - 6))
    (hfamily : p002ExceptionalFamily n hn4 hn9 cfg) :
    cup2Fc n hn4 cfg =
      p002ExceptionalBoundaryBudgetA0B0 (cup2Boundary6 n hn4 hn9 cfg) + 1 := by
  have hmidABC :
      p002ExceptionalMidABC n hn4 hn9 cfg 0 0 (n - 6) := hmid
  have hprefix :=
    p002ExceptionalA0B0_prefix_bit_sum n hn4 hn9 (cfg := cfg) hmidABC
  have hsuffix :=
    p002ExceptionalA0B0_suffix_bit_sum n hn4 hn9 cfg
  have hmidsum :=
    p002ExceptionalA0B0_mid_sum_zero n hn4 hn9 (cfg := cfg) hmidABC
  have htrans :=
    p002ExceptionalFamily_frontier_at_n4 n hn4 hn9 (cfg := cfg) hfamily
  have hsplit := p002_univ_decompose n hn9 (cup2FrontierBit n hn4 cfg)
  unfold cup2Fc
  rw [hsplit, hmidsum, htrans]
  -- Now LHS = prefix_bits + 0 + 1 + suffix_bits; combine prefix/suffix
  simp only [Nat.add_zero]
  have hbudget :
      p002ExceptionalBoundaryBudgetA0B0 (cup2Boundary6 n hn4 hn9 cfg) =
        frontierBitVal (cfg (cup2BoundaryIdx0 n hn9)).1 (cfg (cup2BoundaryIdx1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx1 n hn9)).1 (cfg (cup2BoundaryIdx2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx2 n hn9)).1 2 +
          frontierBitVal (cfg (cup2BoundaryIdxN3 n hn9)).1 (cfg (cup2BoundaryIdxN2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN2 n hn9)).1 (cfg (cup2BoundaryIdxN1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN1 n hn9)).1 (cfg (cup2BoundaryIdx0 n hn9)).1 := by
    unfold p002ExceptionalBoundaryBudgetA0B0 cup2Boundary6
    simp
  rw [hbudget]
  linarith [hprefix, hsuffix]

theorem p002ExceptionalA0Bp_prefix_bit_sum
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {b cLen : Nat} (hb : 1 ≤ b)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 b cLen) :
    cup2FrontierBit n hn4 cfg (cup2BoundaryIdx0 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdx1 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdx2 n hn9) =
      frontierBitVal (cfg (cup2BoundaryIdx0 n hn9)).1 (cfg (cup2BoundaryIdx1 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdx1 n hn9)).1 (cfg (cup2BoundaryIdx2 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdx2 n hn9)).1 0 := by
  have h3 : (cfg (cup2Idx3 n hn9)).1 = 0 := by
    rcases hmid with ⟨hlen, _hcpos, _hones, hzeros, _htwos⟩
    have h := hzeros 0 hb
    have hfin :
        (⟨3 + 0 + 0, p002Exceptional_mid_idx_lt n 0 b cLen 0 hlen hb⟩ : Fin n) =
          cup2Idx3 n hn9 := by
      apply Fin.ext
      simp [cup2Idx3]
    simpa [hfin] using h
  have hright2 : right (cup2BoundaryIdx2 n hn9) = cup2Idx3 n hn9 := by
    have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdx2]; omega
    apply Fin.ext
    rw [right_val_of_not_top (i := cup2BoundaryIdx2 n hn9) htop]
    simp [cup2BoundaryIdx2, cup2Idx3]
  have hr0 : right (cup2BoundaryIdx0 n hn9) = cup2BoundaryIdx1 n hn9 :=
    right_cup2BoundaryIdx0 n hn9
  have hr1 : right (cup2BoundaryIdx1 n hn9) = cup2BoundaryIdx2 n hn9 :=
    right_cup2BoundaryIdx1 n hn9
  have hv0 : (cfg (right (cup2BoundaryIdx0 n hn9))).1 = (cfg (cup2BoundaryIdx1 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hr0
  have hv1 : (cfg (right (cup2BoundaryIdx1 n hn9))).1 = (cfg (cup2BoundaryIdx2 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hr1
  have hv2 : (cfg (right (cup2BoundaryIdx2 n hn9))).1 = (cfg (cup2Idx3 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hright2
  simp only [cup2FrontierBit, hv0, hv1, hv2, h3]

theorem p002ExceptionalA0Bp_mid_sum_eq_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {b cLen : Nat} (hb : 1 ≤ b)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 b cLen) :
    (∑ j ∈ p002MidFinset n hn9, cup2FrontierBit n hn4 cfg j) = 1 := by
  rcases hmid with ⟨hlen, hcpos, _hones, hzeros, htwos⟩
  have hb2_lt_n : b + 2 < n := by omega
  let transPos : Fin n := ⟨b + 2, hb2_lt_n⟩
  have htrans_mem : transPos ∈ p002MidFinset n hn9 := by
    simp only [p002MidFinset, Finset.mem_filter, Finset.mem_univ, true_and, transPos]
    refine ⟨by omega, by omega⟩
  have hval_trans : cup2FrontierBit n hn4 cfg transPos = 1 := by
    have htop : transPos.val + 1 ≠ n := by
      show b + 2 + 1 ≠ n; omega
    have hr : right transPos = ⟨b + 3, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := transPos) htop]
    have hbm1 : b - 1 < b := by omega
    have hcur_eq :
        (⟨3 + 0 + (b - 1),
            p002Exceptional_mid_idx_lt n 0 b cLen (b - 1) hlen hbm1⟩ : Fin n) = transPos := by
      apply Fin.ext
      show 3 + 0 + (b - 1) = b + 2
      omega
    have hcur : (cfg transPos).1 = 0 := by
      rw [← hcur_eq]
      exact hzeros (b - 1) hbm1
    have hcz : 0 < cLen := hcpos
    have hright_eq :
        (⟨3 + 0 + b + 0,
            p002Exceptional_right_idx_lt n 0 b cLen 0 hlen hcz⟩ : Fin n) =
          (⟨b + 3, by omega⟩ : Fin n) := by
      apply Fin.ext
      show 3 + 0 + b + 0 = b + 3
      omega
    have hvright : (cfg (right transPos)).1 = 2 := by
      rw [hr, ← hright_eq]
      exact htwos 0 hcz
    unfold cup2FrontierBit frontierBitVal
    rw [hcur, hvright]
    decide
  have herase_zero :
      (∑ j ∈ (p002MidFinset n hn9).erase transPos,
          cup2FrontierBit n hn4 cfg j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, p002MidFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    obtain ⟨hjne, hjge, hjlt⟩ := hj
    have hjval_ne : j.val ≠ b + 2 := by
      intro h
      apply hjne
      apply Fin.ext
      show j.val = (transPos : Fin n).val
      simp [transPos, h]
    have htop : j.val + 1 ≠ n := by omega
    have hr : right j = ⟨j.val + 1, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := j) htop]
    rcases Nat.lt_or_gt_of_ne hjval_ne with hjlt2 | hjgt2
    · have hk1 : j.val - 3 < b := by omega
      have hk2 : j.val + 1 - 3 < b := by omega
      have heq1 :
          (⟨3 + 0 + (j.val - 3),
              p002Exceptional_mid_idx_lt n 0 b cLen (j.val - 3) hlen hk1⟩ : Fin n) = j := by
        apply Fin.ext
        show 3 + 0 + (j.val - 3) = j.val
        omega
      have hcur : (cfg j).1 = 0 := by
        rw [← heq1]
        exact hzeros (j.val - 3) hk1
      have heq2 :
          (⟨3 + 0 + (j.val + 1 - 3),
              p002Exceptional_mid_idx_lt n 0 b cLen (j.val + 1 - 3) hlen hk2⟩ : Fin n) =
            (⟨j.val + 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        show 3 + 0 + (j.val + 1 - 3) = j.val + 1
        omega
      have hvright : (cfg (right j)).1 = 0 := by
        rw [hr, ← heq2]
        exact hzeros (j.val + 1 - 3) hk2
      unfold cup2FrontierBit frontierBitVal
      rw [hcur, hvright]
      decide
    · have hk1 : j.val - 3 - b < cLen := by omega
      have hk2 : j.val + 1 - 3 - b < cLen := by omega
      have heq1 :
          (⟨3 + 0 + b + (j.val - 3 - b),
              p002Exceptional_right_idx_lt n 0 b cLen (j.val - 3 - b) hlen hk1⟩ : Fin n) = j := by
        apply Fin.ext
        show 3 + 0 + b + (j.val - 3 - b) = j.val
        omega
      have hcur : (cfg j).1 = 2 := by
        rw [← heq1]
        exact htwos (j.val - 3 - b) hk1
      have heq2 :
          (⟨3 + 0 + b + (j.val + 1 - 3 - b),
              p002Exceptional_right_idx_lt n 0 b cLen (j.val + 1 - 3 - b) hlen hk2⟩ : Fin n) =
            (⟨j.val + 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        show 3 + 0 + b + (j.val + 1 - 3 - b) = j.val + 1
        omega
      have hvright : (cfg (right j)).1 = 2 := by
        rw [hr, ← heq2]
        exact htwos (j.val + 1 - 3 - b) hk2
      unfold cup2FrontierBit frontierBitVal
      rw [hcur, hvright]
      decide
  rw [← Finset.add_sum_erase _ _ htrans_mem, hval_trans, herase_zero]

theorem p002ExceptionalA0Bp_fc_eq_budget_plus_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {b cLen : Nat} (hb : 1 ≤ b)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg 0 b cLen)
    (hfamily : p002ExceptionalFamily n hn4 hn9 cfg) :
    cup2Fc n hn4 cfg =
      p002ExceptionalBoundaryBudgetA0Bp (cup2Boundary6 n hn4 hn9 cfg) + 2 := by
  have hprefix :=
    p002ExceptionalA0Bp_prefix_bit_sum n hn4 hn9 (cfg := cfg) hb hmid
  have hsuffix :=
    p002ExceptionalA0B0_suffix_bit_sum n hn4 hn9 cfg
  have hmidsum :=
    p002ExceptionalA0Bp_mid_sum_eq_one n hn4 hn9 (cfg := cfg) hb hmid
  have htrans :=
    p002ExceptionalFamily_frontier_at_n4 n hn4 hn9 (cfg := cfg) hfamily
  have hsplit := p002_univ_decompose n hn9 (cup2FrontierBit n hn4 cfg)
  unfold cup2Fc
  rw [hsplit, hmidsum, htrans]
  have hbudget :
      p002ExceptionalBoundaryBudgetA0Bp (cup2Boundary6 n hn4 hn9 cfg) =
        frontierBitVal (cfg (cup2BoundaryIdx0 n hn9)).1 (cfg (cup2BoundaryIdx1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx1 n hn9)).1 (cfg (cup2BoundaryIdx2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx2 n hn9)).1 0 +
          frontierBitVal (cfg (cup2BoundaryIdxN3 n hn9)).1 (cfg (cup2BoundaryIdxN2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN2 n hn9)).1 (cfg (cup2BoundaryIdxN1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN1 n hn9)).1 (cfg (cup2BoundaryIdx0 n hn9)).1 := by
    unfold p002ExceptionalBoundaryBudgetA0Bp cup2Boundary6
    simp
  rw [hbudget]
  linarith [hprefix, hsuffix]

theorem p002ExceptionalAPos_prefix_bit_sum
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a b cLen : Nat} (ha : 1 ≤ a)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a b cLen) :
    cup2FrontierBit n hn4 cfg (cup2BoundaryIdx0 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdx1 n hn9) +
        cup2FrontierBit n hn4 cfg (cup2BoundaryIdx2 n hn9) =
      frontierBitVal (cfg (cup2BoundaryIdx0 n hn9)).1 (cfg (cup2BoundaryIdx1 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdx1 n hn9)).1 (cfg (cup2BoundaryIdx2 n hn9)).1 +
        frontierBitVal (cfg (cup2BoundaryIdx2 n hn9)).1 1 := by
  have h3 : (cfg (cup2Idx3 n hn9)).1 = 1 := by
    rcases hmid with ⟨hlen, _hcpos, hones, _hzeros, _htwos⟩
    have h := hones 0 ha
    have hfin :
        (⟨3 + 0, p002Exceptional_left_idx_lt n a b cLen 0 hlen ha⟩ : Fin n) =
          cup2Idx3 n hn9 := by
      apply Fin.ext
      simp [cup2Idx3]
    simpa [hfin] using h
  have hright2 : right (cup2BoundaryIdx2 n hn9) = cup2Idx3 n hn9 := by
    have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdx2]; omega
    apply Fin.ext
    rw [right_val_of_not_top (i := cup2BoundaryIdx2 n hn9) htop]
    simp [cup2BoundaryIdx2, cup2Idx3]
  have hr0 : right (cup2BoundaryIdx0 n hn9) = cup2BoundaryIdx1 n hn9 :=
    right_cup2BoundaryIdx0 n hn9
  have hr1 : right (cup2BoundaryIdx1 n hn9) = cup2BoundaryIdx2 n hn9 :=
    right_cup2BoundaryIdx1 n hn9
  have hv0 : (cfg (right (cup2BoundaryIdx0 n hn9))).1 = (cfg (cup2BoundaryIdx1 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hr0
  have hv1 : (cfg (right (cup2BoundaryIdx1 n hn9))).1 = (cfg (cup2BoundaryIdx2 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hr1
  have hv2 : (cfg (right (cup2BoundaryIdx2 n hn9))).1 = (cfg (cup2Idx3 n hn9)).1 :=
    congrArg (fun i => (cfg i).1) hright2
  simp only [cup2FrontierBit, hv0, hv1, hv2, h3]

theorem p002ExceptionalAPosB0_mid_sum_eq_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a cLen : Nat} (ha : 1 ≤ a)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a 0 cLen) :
    (∑ j ∈ p002MidFinset n hn9, cup2FrontierBit n hn4 cfg j) = 1 := by
  rcases hmid with ⟨hlen, hcpos, hones, _hzeros, htwos⟩
  have ha2_lt_n : a + 2 < n := by omega
  let transPos : Fin n := ⟨a + 2, ha2_lt_n⟩
  have htrans_mem : transPos ∈ p002MidFinset n hn9 := by
    simp only [p002MidFinset, Finset.mem_filter, Finset.mem_univ, true_and, transPos]
    refine ⟨by omega, by omega⟩
  have hval_trans : cup2FrontierBit n hn4 cfg transPos = 1 := by
    have htop : transPos.val + 1 ≠ n := by
      show a + 2 + 1 ≠ n; omega
    have hr : right transPos = ⟨a + 3, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := transPos) htop]
    have ham1 : a - 1 < a := by omega
    have hcur_eq :
        (⟨3 + (a - 1),
            p002Exceptional_left_idx_lt n a 0 cLen (a - 1) hlen ham1⟩ : Fin n) = transPos := by
      apply Fin.ext
      show 3 + (a - 1) = a + 2
      omega
    have hcur : (cfg transPos).1 = 1 := by
      rw [← hcur_eq]
      exact hones (a - 1) ham1
    have hcz : 0 < cLen := hcpos
    have hright_eq :
        (⟨3 + a + 0 + 0,
            p002Exceptional_right_idx_lt n a 0 cLen 0 hlen hcz⟩ : Fin n) =
          (⟨a + 3, by omega⟩ : Fin n) := by
      apply Fin.ext
      show 3 + a + 0 + 0 = a + 3
      omega
    have hvright : (cfg (right transPos)).1 = 2 := by
      rw [hr, ← hright_eq]
      exact htwos 0 hcz
    unfold cup2FrontierBit frontierBitVal
    rw [hcur, hvright]
    decide
  have herase_zero :
      (∑ j ∈ (p002MidFinset n hn9).erase transPos,
          cup2FrontierBit n hn4 cfg j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, p002MidFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    obtain ⟨hjne, hjge, hjlt⟩ := hj
    have hjval_ne : j.val ≠ a + 2 := by
      intro h
      apply hjne
      apply Fin.ext
      show j.val = (transPos : Fin n).val
      simp [transPos, h]
    have htop : j.val + 1 ≠ n := by omega
    have hr : right j = ⟨j.val + 1, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := j) htop]
    rcases Nat.lt_or_gt_of_ne hjval_ne with hjlt2 | hjgt2
    · have hk1 : j.val - 3 < a := by omega
      have hk2 : j.val + 1 - 3 < a := by omega
      have heq1 :
          (⟨3 + (j.val - 3),
              p002Exceptional_left_idx_lt n a 0 cLen (j.val - 3) hlen hk1⟩ : Fin n) = j := by
        apply Fin.ext
        show 3 + (j.val - 3) = j.val
        omega
      have hcur : (cfg j).1 = 1 := by
        rw [← heq1]
        exact hones (j.val - 3) hk1
      have heq2 :
          (⟨3 + (j.val + 1 - 3),
              p002Exceptional_left_idx_lt n a 0 cLen (j.val + 1 - 3) hlen hk2⟩ : Fin n) =
            (⟨j.val + 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        show 3 + (j.val + 1 - 3) = j.val + 1
        omega
      have hvright : (cfg (right j)).1 = 1 := by
        rw [hr, ← heq2]
        exact hones (j.val + 1 - 3) hk2
      unfold cup2FrontierBit frontierBitVal
      rw [hcur, hvright]
      decide
    · have hk1 : j.val - 3 - a < cLen := by omega
      have hk2 : j.val + 1 - 3 - a < cLen := by omega
      have heq1 :
          (⟨3 + a + 0 + (j.val - 3 - a),
              p002Exceptional_right_idx_lt n a 0 cLen (j.val - 3 - a) hlen hk1⟩ : Fin n) = j := by
        apply Fin.ext
        show 3 + a + 0 + (j.val - 3 - a) = j.val
        omega
      have hcur : (cfg j).1 = 2 := by
        rw [← heq1]
        exact htwos (j.val - 3 - a) hk1
      have heq2 :
          (⟨3 + a + 0 + (j.val + 1 - 3 - a),
              p002Exceptional_right_idx_lt n a 0 cLen (j.val + 1 - 3 - a) hlen hk2⟩ : Fin n) =
            (⟨j.val + 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        show 3 + a + 0 + (j.val + 1 - 3 - a) = j.val + 1
        omega
      have hvright : (cfg (right j)).1 = 2 := by
        rw [hr, ← heq2]
        exact htwos (j.val + 1 - 3 - a) hk2
      unfold cup2FrontierBit frontierBitVal
      rw [hcur, hvright]
      decide
  rw [← Finset.add_sum_erase _ _ htrans_mem, hval_trans, herase_zero]

theorem p002ExceptionalAPosB0_fc_eq_budget_plus_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a cLen : Nat} (ha : 1 ≤ a)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a 0 cLen)
    (hfamily : p002ExceptionalFamily n hn4 hn9 cfg) :
    cup2Fc n hn4 cfg =
      p002ExceptionalBoundaryBudgetAPos (cup2Boundary6 n hn4 hn9 cfg) + 2 := by
  have hprefix :=
    p002ExceptionalAPos_prefix_bit_sum n hn4 hn9 (cfg := cfg) ha hmid
  have hsuffix :=
    p002ExceptionalA0B0_suffix_bit_sum n hn4 hn9 cfg
  have hmidsum :=
    p002ExceptionalAPosB0_mid_sum_eq_one n hn4 hn9 (cfg := cfg) ha hmid
  have htrans :=
    p002ExceptionalFamily_frontier_at_n4 n hn4 hn9 (cfg := cfg) hfamily
  have hsplit := p002_univ_decompose n hn9 (cup2FrontierBit n hn4 cfg)
  unfold cup2Fc
  rw [hsplit, hmidsum, htrans]
  have hbudget :
      p002ExceptionalBoundaryBudgetAPos (cup2Boundary6 n hn4 hn9 cfg) =
        frontierBitVal (cfg (cup2BoundaryIdx0 n hn9)).1 (cfg (cup2BoundaryIdx1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx1 n hn9)).1 (cfg (cup2BoundaryIdx2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx2 n hn9)).1 1 +
          frontierBitVal (cfg (cup2BoundaryIdxN3 n hn9)).1 (cfg (cup2BoundaryIdxN2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN2 n hn9)).1 (cfg (cup2BoundaryIdxN1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN1 n hn9)).1 (cfg (cup2BoundaryIdx0 n hn9)).1 := by
    unfold p002ExceptionalBoundaryBudgetAPos cup2Boundary6
    simp
  rw [hbudget]
  linarith [hprefix, hsuffix]

theorem p002ExceptionalAPosBp_mid_sum_eq_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a b cLen : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a b cLen) :
    (∑ j ∈ p002MidFinset n hn9, cup2FrontierBit n hn4 cfg j) = 2 := by
  rcases hmid with ⟨hlen, hcpos, hones, hzeros, htwos⟩
  have ha2_lt_n : a + 2 < n := by omega
  have hab2_lt_n : a + b + 2 < n := by omega
  let t1 : Fin n := ⟨a + 2, ha2_lt_n⟩
  let t2 : Fin n := ⟨a + b + 2, hab2_lt_n⟩
  have h_t1_t2 : t1 ≠ t2 := by
    intro h
    have : (t1 : Fin n).val = (t2 : Fin n).val := by rw [h]
    simp [t1, t2] at this
    omega
  have ht1_mem : t1 ∈ p002MidFinset n hn9 := by
    simp only [p002MidFinset, Finset.mem_filter, Finset.mem_univ, true_and, t1]
    refine ⟨by omega, by omega⟩
  have ht2_mem : t2 ∈ p002MidFinset n hn9 := by
    simp only [p002MidFinset, Finset.mem_filter, Finset.mem_univ, true_and, t2]
    refine ⟨by omega, by omega⟩
  have ht2_mem_erase : t2 ∈ (p002MidFinset n hn9).erase t1 := by
    rw [Finset.mem_erase]
    exact ⟨fun h => h_t1_t2 h.symm, ht2_mem⟩
  -- value at t1: 1 → 0 transition (a-1 is 1, a is 0)
  have hval_t1 : cup2FrontierBit n hn4 cfg t1 = 1 := by
    have htop : t1.val + 1 ≠ n := by show a + 2 + 1 ≠ n; omega
    have hr : right t1 = ⟨a + 3, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := t1) htop]
    have ham1 : a - 1 < a := by omega
    have hcur_eq :
        (⟨3 + (a - 1),
            p002Exceptional_left_idx_lt n a b cLen (a - 1) hlen ham1⟩ : Fin n) = t1 := by
      apply Fin.ext
      show 3 + (a - 1) = a + 2
      omega
    have hcur : (cfg t1).1 = 1 := by
      rw [← hcur_eq]
      exact hones (a - 1) ham1
    have hbpos : 0 < b := hb
    have hright_eq :
        (⟨3 + a + 0,
            p002Exceptional_mid_idx_lt n a b cLen 0 hlen hbpos⟩ : Fin n) =
          (⟨a + 3, by omega⟩ : Fin n) := by
      apply Fin.ext
      show 3 + a + 0 = a + 3
      omega
    have hvright : (cfg (right t1)).1 = 0 := by
      rw [hr, ← hright_eq]
      exact hzeros 0 hbpos
    unfold cup2FrontierBit frontierBitVal
    rw [hcur, hvright]
    decide
  -- value at t2: 0 → 2 transition (b-1 is 0, c[0] is 2)
  have hval_t2 : cup2FrontierBit n hn4 cfg t2 = 1 := by
    have htop : t2.val + 1 ≠ n := by show a + b + 2 + 1 ≠ n; omega
    have hr : right t2 = ⟨a + b + 3, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := t2) htop]
    have hbm1 : b - 1 < b := by omega
    have hcur_eq :
        (⟨3 + a + (b - 1),
            p002Exceptional_mid_idx_lt n a b cLen (b - 1) hlen hbm1⟩ : Fin n) = t2 := by
      apply Fin.ext
      show 3 + a + (b - 1) = a + b + 2
      omega
    have hcur : (cfg t2).1 = 0 := by
      rw [← hcur_eq]
      exact hzeros (b - 1) hbm1
    have hcz : 0 < cLen := hcpos
    have hright_eq :
        (⟨3 + a + b + 0,
            p002Exceptional_right_idx_lt n a b cLen 0 hlen hcz⟩ : Fin n) =
          (⟨a + b + 3, by omega⟩ : Fin n) := by
      apply Fin.ext
      show 3 + a + b + 0 = a + b + 3
      omega
    have hvright : (cfg (right t2)).1 = 2 := by
      rw [hr, ← hright_eq]
      exact htwos 0 hcz
    unfold cup2FrontierBit frontierBitVal
    rw [hcur, hvright]
    decide
  have herase_zero :
      (∑ j ∈ ((p002MidFinset n hn9).erase t1).erase t2,
          cup2FrontierBit n hn4 cfg j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, p002MidFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    obtain ⟨hjnet2, hjnet1, hjge, hjlt⟩ := hj
    have hjval_ne_t1 : j.val ≠ a + 2 := by
      intro h
      apply hjnet1
      apply Fin.ext
      show j.val = (t1 : Fin n).val
      simp [t1, h]
    have hjval_ne_t2 : j.val ≠ a + b + 2 := by
      intro h
      apply hjnet2
      apply Fin.ext
      show j.val = (t2 : Fin n).val
      simp [t2, h]
    have htop : j.val + 1 ≠ n := by omega
    have hr : right j = ⟨j.val + 1, by omega⟩ := by
      apply Fin.ext
      rw [right_val_of_not_top (i := j) htop]
    -- three zones: < a+2, in [a+3, a+b+1], > a+b+2
    rcases Nat.lt_or_gt_of_ne hjval_ne_t1 with hlt_a | hgt_a
    · -- j.val < a + 2, so j.val ∈ [3, a+1], value 1
      have hk1 : j.val - 3 < a := by omega
      have hk2 : j.val + 1 - 3 < a := by omega
      have heq1 :
          (⟨3 + (j.val - 3),
              p002Exceptional_left_idx_lt n a b cLen (j.val - 3) hlen hk1⟩ : Fin n) = j := by
        apply Fin.ext
        show 3 + (j.val - 3) = j.val
        omega
      have hcur : (cfg j).1 = 1 := by
        rw [← heq1]
        exact hones (j.val - 3) hk1
      have heq2 :
          (⟨3 + (j.val + 1 - 3),
              p002Exceptional_left_idx_lt n a b cLen (j.val + 1 - 3) hlen hk2⟩ : Fin n) =
            (⟨j.val + 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        show 3 + (j.val + 1 - 3) = j.val + 1
        omega
      have hvright : (cfg (right j)).1 = 1 := by
        rw [hr, ← heq2]
        exact hones (j.val + 1 - 3) hk2
      unfold cup2FrontierBit frontierBitVal
      rw [hcur, hvright]
      decide
    · -- j.val > a + 2
      rcases Nat.lt_or_gt_of_ne hjval_ne_t2 with hlt_ab | hgt_ab
      · -- a+2 < j.val < a+b+2, so j.val ∈ [a+3, a+b+1], value 0
        have hk1 : j.val - 3 - a < b := by omega
        have hk2 : j.val + 1 - 3 - a < b := by omega
        have heq1 :
            (⟨3 + a + (j.val - 3 - a),
                p002Exceptional_mid_idx_lt n a b cLen (j.val - 3 - a) hlen hk1⟩ : Fin n) = j := by
          apply Fin.ext
          show 3 + a + (j.val - 3 - a) = j.val
          omega
        have hcur : (cfg j).1 = 0 := by
          rw [← heq1]
          exact hzeros (j.val - 3 - a) hk1
        have heq2 :
            (⟨3 + a + (j.val + 1 - 3 - a),
                p002Exceptional_mid_idx_lt n a b cLen (j.val + 1 - 3 - a) hlen hk2⟩ : Fin n) =
              (⟨j.val + 1, by omega⟩ : Fin n) := by
          apply Fin.ext
          show 3 + a + (j.val + 1 - 3 - a) = j.val + 1
          omega
        have hvright : (cfg (right j)).1 = 0 := by
          rw [hr, ← heq2]
          exact hzeros (j.val + 1 - 3 - a) hk2
        unfold cup2FrontierBit frontierBitVal
        rw [hcur, hvright]
        decide
      · -- j.val > a + b + 2, value 2
        have hk1 : j.val - 3 - a - b < cLen := by omega
        have hk2 : j.val + 1 - 3 - a - b < cLen := by omega
        have heq1 :
            (⟨3 + a + b + (j.val - 3 - a - b),
                p002Exceptional_right_idx_lt n a b cLen (j.val - 3 - a - b) hlen hk1⟩ :
              Fin n) = j := by
          apply Fin.ext
          show 3 + a + b + (j.val - 3 - a - b) = j.val
          omega
        have hcur : (cfg j).1 = 2 := by
          rw [← heq1]
          exact htwos (j.val - 3 - a - b) hk1
        have heq2 :
            (⟨3 + a + b + (j.val + 1 - 3 - a - b),
                p002Exceptional_right_idx_lt n a b cLen (j.val + 1 - 3 - a - b) hlen hk2⟩ :
              Fin n) = (⟨j.val + 1, by omega⟩ : Fin n) := by
          apply Fin.ext
          show 3 + a + b + (j.val + 1 - 3 - a - b) = j.val + 1
          omega
        have hvright : (cfg (right j)).1 = 2 := by
          rw [hr, ← heq2]
          exact htwos (j.val + 1 - 3 - a - b) hk2
        unfold cup2FrontierBit frontierBitVal
        rw [hcur, hvright]
        decide
  rw [← Finset.add_sum_erase _ _ ht1_mem,
      ← Finset.add_sum_erase _ _ ht2_mem_erase,
      hval_t1, hval_t2, herase_zero]
  rfl

theorem p002ExceptionalAPosBp_fc_eq_budget_plus_three
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    {a b cLen : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hmid : p002ExceptionalMidABC n hn4 hn9 cfg a b cLen)
    (hfamily : p002ExceptionalFamily n hn4 hn9 cfg) :
    cup2Fc n hn4 cfg =
      p002ExceptionalBoundaryBudgetAPos (cup2Boundary6 n hn4 hn9 cfg) + 3 := by
  have hprefix :=
    p002ExceptionalAPos_prefix_bit_sum n hn4 hn9 (cfg := cfg) ha hmid
  have hsuffix :=
    p002ExceptionalA0B0_suffix_bit_sum n hn4 hn9 cfg
  have hmidsum :=
    p002ExceptionalAPosBp_mid_sum_eq_two n hn4 hn9 (cfg := cfg) ha hb hmid
  have htrans :=
    p002ExceptionalFamily_frontier_at_n4 n hn4 hn9 (cfg := cfg) hfamily
  have hsplit := p002_univ_decompose n hn9 (cup2FrontierBit n hn4 cfg)
  unfold cup2Fc
  rw [hsplit, hmidsum, htrans]
  have hbudget :
      p002ExceptionalBoundaryBudgetAPos (cup2Boundary6 n hn4 hn9 cfg) =
        frontierBitVal (cfg (cup2BoundaryIdx0 n hn9)).1 (cfg (cup2BoundaryIdx1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx1 n hn9)).1 (cfg (cup2BoundaryIdx2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdx2 n hn9)).1 1 +
          frontierBitVal (cfg (cup2BoundaryIdxN3 n hn9)).1 (cfg (cup2BoundaryIdxN2 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN2 n hn9)).1 (cfg (cup2BoundaryIdxN1 n hn9)).1 +
          frontierBitVal (cfg (cup2BoundaryIdxN1 n hn9)).1 (cfg (cup2BoundaryIdx0 n hn9)).1 := by
    unfold p002ExceptionalBoundaryBudgetAPos cup2Boundary6
    simp
  rw [hbudget]
  linarith [hprefix, hsuffix]

theorem p002ExceptionalFamily_fc_le_five
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {cfg : Config (cup2Spec n hn4)}
    (hfamily : p002ExceptionalFamily n hn4 hn9 cfg) :
    cup2Fc n hn4 cfg ≤ 5 := by
  obtain ⟨a, b, cLen, hmid, hboundary⟩ := hfamily
  have hfam : p002ExceptionalFamily n hn4 hn9 cfg :=
    ⟨a, b, cLen, hmid, hboundary⟩
  by_cases ha : 1 ≤ a
  · -- APos: a ≥ 1
    have h0a : 0 < a := ha
    have hboundAPos : p002ExceptionalBoundaryAPos (cup2Boundary6 n hn4 hn9 cfg) := by
      simp only [p002ExceptionalBoundaryForAB, if_pos h0a] at hboundary
      exact hboundary
    have hbudget :=
      p002ExceptionalBoundaryBudgetAPos_le_two (cup2Boundary6 n hn4 hn9 cfg) hboundAPos
    by_cases hb : 1 ≤ b
    · have hfc :=
        p002ExceptionalAPosBp_fc_eq_budget_plus_three n hn4 hn9 ha hb hmid hfam
      omega
    · have hb0 : b = 0 := by omega
      subst hb0
      have hfc :=
        p002ExceptionalAPosB0_fc_eq_budget_plus_two n hn4 hn9 ha hmid hfam
      omega
  · have ha0 : a = 0 := by omega
    subst ha0
    have h00 : ¬ (0 < 0) := Nat.lt_irrefl 0
    by_cases hb : 1 ≤ b
    · -- A0Bp
      have h0b : 0 < b := hb
      have hboundA0Bp : p002ExceptionalBoundaryA0Bp (cup2Boundary6 n hn4 hn9 cfg) := by
        simp only [p002ExceptionalBoundaryForAB, if_neg h00, if_pos h0b] at hboundary
        exact hboundary
      have hbudget :=
        p002ExceptionalBoundaryBudgetA0Bp_le_three
          (cup2Boundary6 n hn4 hn9 cfg) hboundA0Bp
      have hfc :=
        p002ExceptionalA0Bp_fc_eq_budget_plus_two n hn4 hn9 hb hmid hfam
      omega
    · -- A0B0
      have hb0 : b = 0 := by omega
      subst hb0
      have hcLenEq : cLen = n - 6 := by
        rcases hmid with ⟨hlen, _⟩
        omega
      subst hcLenEq
      have hboundA0B0 : p002ExceptionalBoundaryA0B0 (cup2Boundary6 n hn4 hn9 cfg) := by
        simp only [p002ExceptionalBoundaryForAB, if_neg h00] at hboundary
        exact hboundary
      have hbudget :=
        p002ExceptionalBoundaryBudgetA0B0_le_four
          (cup2Boundary6 n hn4 hn9 cfg) hboundA0B0
      have hfc :=
        p002ExceptionalA0B0_fc_eq_budget_plus_one n hn4 hn9 hmid hfam
      omega

theorem p002ExceptionalScratch_smoke : True := by
  have _ := p002ExceptionalMidShape
  have _ := p002ExceptionalMidShape_witness
  have _ := p002ExceptionalFamily
  have _ := p002ExceptionalFamily_of_mid_boundary
  have _ := p002Exceptional_allTwos_start_family
  have _ := p002ExceptionalFamily_cN3_one
  have _ := p002ExceptionalBoundaryForAB_c2_ne_two_of_prefix
  have _ := p002ExceptionalMidABC_last_two
  have _ := p002ExceptionalMidABC_idx3_ne_two_of_prefix
  have _ := p002ExceptionalFamily_frontier_at_n4
  have _ := p002ExceptionalBoundaryA0B0_count
  have _ := p002ExceptionalBoundaryA0Bp_count
  have _ := p002ExceptionalBoundaryAPos_count
  have _ := p002ExceptionalBoundaryA0B0_cN3_one
  have _ := p002ExceptionalBoundaryA0Bp_cN3_one
  have _ := p002ExceptionalBoundaryA0Bp_c2_ne_two
  have _ := p002ExceptionalBoundaryAPos_cN3_one
  have _ := p002ExceptionalBoundaryAPos_c2_one
  have _ := p002ExceptionalBoundaryBudgetA0B0_le_four
  have _ := p002ExceptionalBoundaryBudgetA0Bp_le_three
  have _ := p002ExceptionalBoundaryBudgetAPos_le_two
  trivial

end LeanMn
