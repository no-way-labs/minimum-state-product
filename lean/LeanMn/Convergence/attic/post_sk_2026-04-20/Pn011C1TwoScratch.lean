import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SyntheticPotential
import LeanMn.Convergence.SixTuple

namespace LeanMn

private structure Pn011C1TwoSig where
  cN3 : Fin 3
  cN2 : Fin 3
  cN1 : Fin 2
  c0 : Fin 2
  c1 : Fin 3
  c2 : Fin 3
deriving DecidableEq, Fintype, Repr

@[ext] private theorem Pn011C1TwoSig.ext {s t : Pn011C1TwoSig}
    (hN3 : s.cN3 = t.cN3) (hN2 : s.cN2 = t.cN2) (hN1 : s.cN1 = t.cN1)
    (h0 : s.c0 = t.c0) (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2) :
    s = t := by
  cases s
  cases t
  cases hN3
  cases hN2
  cases hN1
  cases h0
  cases h1
  cases h2
  rfl

private def pn011c1two_sigOfBoundary (s : SixBoundary) : Pn011C1TwoSig :=
  { cN3 := s.cN3, cN2 := s.cN2, cN1 := s.cN1, c0 := s.c0, c1 := s.c1, c2 := s.c2 }

private def pn011c1two_sigOfConfig
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Pn011C1TwoSig :=
  pn011c1two_sigOfBoundary (cup2Boundary6 n hn4 hn9 c)

private theorem pn011c1two_sigOfConfig_eq_boundary
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    pn011c1two_sigOfConfig n hn4 hn9 c =
      pn011c1two_sigOfBoundary (cup2Boundary6 n hn4 hn9 c) := by
  rfl

private theorem pn011c1two_sigOfConfig_eq_of_boundaryState_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hbdry : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c) :
    pn011c1two_sigOfConfig n hn4 hn9 c' = pn011c1two_sigOfConfig n hn4 hn9 c := by
  have hdecode := congrArg (fun s : SixState => decodeSixBoundary s.1) hbdry
  have hb6 : cup2Boundary6 n hn4 hn9 c' = cup2Boundary6 n hn4 hn9 c := by
    simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdecode
  simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c',
    pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c] using congrArg pn011c1two_sigOfBoundary hb6

private def pn011c1two_sigSuccP0 (s : Pn011C1TwoSig) : Pn011C1TwoSig :=
  { s with c0 := ⟨TBotVal s.cN1.1 s.c0.1 s.c1.1,
      TBotVal_lt s.cN1.2 s.c0.2 s.c1.2⟩ }

private def pn011c1two_sigSuccP1 (s : Pn011C1TwoSig) : Pn011C1TwoSig :=
  { s with c1 := ⟨TLowVal s.c0.1 s.c1.1 s.c2.1,
      TLowVal_lt s.c0.2 s.c1.2 s.c2.2⟩ }

private def pn011c1two_sigSuccP2 (s : Pn011C1TwoSig) (c3 : Fin 3) : Pn011C1TwoSig :=
  { s with c2 := ⟨TMidVal s.c1.1 s.c2.1 c3.1, TMidVal_lt s.c1.2 s.c2.2 c3.2⟩ }

private def pn011c1two_sigSuccPN2 (s : Pn011C1TwoSig) (cN3 : Fin 3) : Pn011C1TwoSig :=
  { s with cN2 := ⟨THighVal cN3.1 s.cN2.1 s.cN1.1,
      THighVal_lt cN3.2 s.cN2.2 s.cN1.2⟩ }

private def pn011c1two_sigSuccPN1 (s : Pn011C1TwoSig) : Pn011C1TwoSig :=
  { s with cN1 := ⟨TTopVal s.cN2.1 s.cN1.1 s.c0.1,
      TTopVal_lt s.cN2.2 s.cN1.2 s.c0.2⟩ }

private def pn011c1two_sigSuccPN3 (s : Pn011C1TwoSig) (cN4 : Fin 3) : Pn011C1TwoSig :=
  { s with cN3 := ⟨TMidVal cN4.1 s.cN3.1 s.cN2.1,
      TMidVal_lt cN4.2 s.cN3.2 s.cN2.2⟩ }

private def pn011c1two_sigIdx (s : Pn011C1TwoSig) : Nat :=
  ((((s.c0.1 * 3 + s.c1.1) * 3 + s.c2.1) * 3 + s.cN3.1) * 3 + s.cN2.1) * 2 + s.cN1.1

private def pn011c1two_sigRank (s : Pn011C1TwoSig) : Int :=
  if pn011c1two_sigIdx s = 174 ∨
      pn011c1two_sigIdx s = 228 ∨
      pn011c1two_sigIdx s = 246 ∨
      pn011c1two_sigIdx s = 264 ∨
      pn011c1two_sigIdx s = 282 ∨
      pn011c1two_sigIdx s = 318 then
    0
  else
    -1

private abbrev p2TpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R = 1 then 1 else 0) = (if S = 2 ∧ R = 1 then 1 else 0)

private abbrev pn2TpLocal (L S R : Nat) : Prop :=
  let out := THighVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if L = 2 ∧ out = 1 then 1 else 0) = (if L = 2 ∧ S = 1 then 1 else 0)

private abbrev pn3TpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    ((if L = 2 ∧ out = 1 then 1 else 0) + (if out = 2 ∧ R = 1 then 1 else 0) =
      (if L = 2 ∧ S = 1 then 1 else 0) + (if S = 2 ∧ R = 1 then 1 else 0))

private theorem pn011c1two_sig_step_P0 (s : Pn011C1TwoSig)
    (hrank : 0 ≤ pn011c1two_sigRank s) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccP0 s) ∧
      localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
        pn011c1two_sigRank (pn011c1two_sigSuccP0 s) ≤
      pn011c1two_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoSig,
        0 ≤ pn011c1two_sigRank s →
          0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccP0 s) ∧
            localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
              pn011c1two_sigRank (pn011c1two_sigSuccP0 s) ≤
            pn011c1two_sigRank s := by
    native_decide
  exact h s hrank

private theorem pn011c1two_sig_step_P1 (s : Pn011C1TwoSig)
    (hrank : 0 ≤ pn011c1two_sigRank s) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccP1 s) ∧
      localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
        pn011c1two_sigRank (pn011c1two_sigSuccP1 s) ≤
      pn011c1two_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoSig,
        0 ≤ pn011c1two_sigRank s →
          0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccP1 s) ∧
            localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
              pn011c1two_sigRank (pn011c1two_sigSuccP1 s) ≤
            pn011c1two_sigRank s := by
    native_decide
  exact h s hrank

private theorem pn011c1two_sig_step_P2 (s : Pn011C1TwoSig) (c3 : Fin 3)
    (hrank : 0 ≤ pn011c1two_sigRank s)
    (htp : p2TpLocal s.c1.1 s.c2.1 c3.1) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccP2 s c3) ∧
      localFcDelta s.c1.1 s.c2.1 c3.1 (TMidVal s.c1.1 s.c2.1 c3.1) +
        pn011c1two_sigRank (pn011c1two_sigSuccP2 s c3) ≤
      pn011c1two_sigRank s := by
  have h :
      ∀ (s : Pn011C1TwoSig) (c3 : Fin 3),
        0 ≤ pn011c1two_sigRank s →
          p2TpLocal s.c1.1 s.c2.1 c3.1 →
            0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccP2 s c3) ∧
              localFcDelta s.c1.1 s.c2.1 c3.1 (TMidVal s.c1.1 s.c2.1 c3.1) +
                pn011c1two_sigRank (pn011c1two_sigSuccP2 s c3) ≤
              pn011c1two_sigRank s := by
    native_decide
  exact h s c3 hrank htp

private theorem pn011c1two_sig_step_PN2 (s : Pn011C1TwoSig)
    (hrank : 0 ≤ pn011c1two_sigRank s)
    (htp : pn2TpLocal s.cN3.1 s.cN2.1 s.cN1.1) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccPN2 s s.cN3) ∧
      localFcDelta s.cN3.1 s.cN2.1 s.cN1.1 (THighVal s.cN3.1 s.cN2.1 s.cN1.1) +
        pn011c1two_sigRank (pn011c1two_sigSuccPN2 s s.cN3) ≤
      pn011c1two_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoSig,
        0 ≤ pn011c1two_sigRank s →
          pn2TpLocal s.cN3.1 s.cN2.1 s.cN1.1 →
            0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccPN2 s s.cN3) ∧
              localFcDelta s.cN3.1 s.cN2.1 s.cN1.1 (THighVal s.cN3.1 s.cN2.1 s.cN1.1) +
                pn011c1two_sigRank (pn011c1two_sigSuccPN2 s s.cN3) ≤
              pn011c1two_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem pn011c1two_sig_step_PN1 (s : Pn011C1TwoSig)
    (hrank : 0 ≤ pn011c1two_sigRank s) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccPN1 s) ∧
      localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
        pn011c1two_sigRank (pn011c1two_sigSuccPN1 s) ≤
      pn011c1two_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoSig,
        0 ≤ pn011c1two_sigRank s →
          0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccPN1 s) ∧
            localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
              pn011c1two_sigRank (pn011c1two_sigSuccPN1 s) ≤
            pn011c1two_sigRank s := by
    native_decide
  exact h s hrank

private theorem pn011c1two_sig_step_PN3 (s : Pn011C1TwoSig) (cN4 : Fin 3)
    (hrank : 0 ≤ pn011c1two_sigRank s)
    (htp : pn3TpLocal cN4.1 s.cN3.1 s.cN2.1) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccPN3 s cN4) ∧
      localFcDelta cN4.1 s.cN3.1 s.cN2.1 (TMidVal cN4.1 s.cN3.1 s.cN2.1) +
        pn011c1two_sigRank (pn011c1two_sigSuccPN3 s cN4) ≤
      pn011c1two_sigRank s := by
  have h :
      ∀ (s : Pn011C1TwoSig) (cN4 : Fin 3),
        0 ≤ pn011c1two_sigRank s →
          pn3TpLocal cN4.1 s.cN3.1 s.cN2.1 →
            0 ≤ pn011c1two_sigRank (pn011c1two_sigSuccPN3 s cN4) ∧
              localFcDelta cN4.1 s.cN3.1 s.cN2.1 (TMidVal cN4.1 s.cN3.1 s.cN2.1) +
                pn011c1two_sigRank (pn011c1two_sigSuccPN3 s cN4) ≤
              pn011c1two_sigRank s := by
    native_decide
  exact h s cN4 hrank htp

private theorem pn011c1two_start_rank_zero_of_source (s : SixBoundary)
    (hN3 : s.cN3.1 = 2)
    (hN2 : s.cN2.1 = 0)
    (hN1 : s.cN1.1 = 1)
    (h0 : s.c0.1 = 1)
    (h1 : s.c1.1 = 2)
    (h2 : s.c2.1 = 0 ∨ s.c2.1 = 2) :
    pn011c1two_sigRank (pn011c1two_sigOfBoundary (boundarySuccPN1 s)) = 0 := by
  have htop011 : TTopVal 0 1 1 = 0 := by native_decide
  rw [pn011c1two_sigRank, pn011c1two_sigIdx, pn011c1two_sigOfBoundary, boundarySuccPN1]
  rcases h2 with hs2 | hs2 <;>
    simp [hN3, hN2, hN1, h0, h1, hs2, htop011]

private theorem p2TpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9)) :
    p2TpLocal (c (cup2BoundaryIdx1 n hn9)).1 (c (cup2BoundaryIdx2 n hn9)).1
      (c (right (cup2BoundaryIdx2 n hn9))).1 := by
  obtain ⟨hexp2, hi21, _hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdx2 n hn9) htp
  have hout :
      cup2OutVal n (cup2BoundaryIdx2 n hn9)
        (c (left (cup2BoundaryIdx2 n hn9))).1
        (c (cup2BoundaryIdx2 n hn9)).1
        (c (right (cup2BoundaryIdx2 n hn9))).1 =
          TMidVal (c (cup2BoundaryIdx1 n hn9)).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1 := by
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9]
  have h4 : 4 < n := by omega
  rw [hout] at hexp2 hi21
  constructor
  · rw [localExp2After, localExp2Before] at hexp2
    simpa [p2TpLocal, cup2Exp2BitVal, hout, left_cup2BoundaryIdx2 n hn9,
      cup2BoundaryIdx2, h4, Nat.mod_eq_of_lt (show 1 < n by omega)] using hexp2
  · rw [localInt21After, localInt21Before] at hi21
    simpa [p2TpLocal, cup2Int21BitVal, hout, left_cup2BoundaryIdx2 n hn9,
      cup2BoundaryIdx2, h4, Nat.mod_eq_of_lt (show 1 < n by omega)] using hi21

private theorem pn2TpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN2 n hn9)) :
    pn2TpLocal (c (cup2BoundaryIdxN3 n hn9)).1
      (c (cup2BoundaryIdxN2 n hn9)).1
      (c (cup2BoundaryIdxN1 n hn9)).1 := by
  obtain ⟨hexp2, hi21, _hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdxN2 n hn9) htp
  have hout :
      cup2OutVal n (cup2BoundaryIdxN2 n hn9)
        (c (left (cup2BoundaryIdxN2 n hn9))).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 =
          THighVal (c (cup2BoundaryIdxN3 n hn9)).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (cup2BoundaryIdxN1 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN2 n hn9, left_cup2BoundaryIdxN2 n hn9,
      right_cup2BoundaryIdxN2 n hn9]
  have hzero_before_exp2 :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_after_exp2 :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_before_i21 :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_before_exp2' :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_before_exp2
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_after_exp2' :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_after_exp2
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_before_i21' :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_before_i21
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_after_i21 :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_after_i21' :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_after_i21
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hinner_lo : 2 ≤ (cup2BoundaryIdxN3 n hn9).1 := by
    simp [cup2BoundaryIdxN3]
    omega
  have hinner_hi : (cup2BoundaryIdxN3 n hn9).1 + 2 < n := by
    simp [cup2BoundaryIdxN3]
    omega
  rw [localExp2After, localExp2Before] at hexp2
  rw [hout] at hexp2
  rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9] at hexp2
  rw [hzero_after_exp2', hzero_before_exp2'] at hexp2
  rw [cup2Exp2BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi,
    cup2Exp2BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi] at hexp2
  rw [localInt21After, localInt21Before] at hi21
  rw [hout] at hi21
  rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9] at hi21
  rw [hzero_after_i21', hzero_before_i21'] at hi21
  rw [cup2Int21BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi,
    cup2Int21BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi] at hi21
  simpa [pn2TpLocal] using And.intro hexp2 hi21

private theorem eq_bits_of_sum_and_weight_local
    {w a b c d : Nat}
    (hsum : a + b = c + d)
    (hweight : w * a + (w + 1) * b = w * c + (w + 1) * d) :
    a = c ∧ b = d := by
  have hbd : b = d := by
    nlinarith [hsum, hweight]
  have hac : a = c := by
    nlinarith [hsum, hbd]
  exact ⟨hac, hbd⟩

private theorem pn3TpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9)) :
    pn3TpLocal (c (left (cup2BoundaryIdxN3 n hn9))).1
      (c (cup2BoundaryIdxN3 n hn9)).1
      (c (cup2BoundaryIdxN2 n hn9)).1 := by
  let i := cup2BoundaryIdxN3 n hn9
  have hi_eq : i.1 = n - 3 := by
    change (cup2BoundaryIdxN3 n hn9).1 = n - 3
    simp [cup2BoundaryIdxN3]
  have h0 : i.1 ≠ 0 := by
    rw [hi_eq]
    omega
  have hleft_val : (left i).1 = n - 4 := by
    rw [left_val_of_ne_zero h0, hi_eq]
    omega
  have hi_succ : i.1 = (left i).1 + 1 := by
    rw [hleft_val]
    omega
  have hleft_in : 2 ≤ (left i).1 := by
    rw [hleft_val]
    omega
  have hleft_top : (left i).1 + 2 < n := by
    rw [hleft_val]
    omega
  have hi_in : 2 ≤ i.1 := by
    rw [hi_eq]
    omega
  have hi_top : i.1 + 2 < n := by
    rw [hi_eq]
    omega
  obtain ⟨hexp2, hi21, hweight⟩ := cup2TpPreserving_local_eqs n hn4 c i htp
  have hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
        TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
  have hexp2' :
      (if (c (left i)).1 = 2 ∧
            TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) +
        (if TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) =
      (if (c (left i)).1 = 2 ∧ (c i).1 ≠ 2 then 1 else 0) +
        (if (c i).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2After, localExp2Before] at hexp2
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hexp2
    rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top] at hexp2
    exact hexp2
  have hweight' :
      (left i).1 *
          (if (c (left i)).1 = 2 ∧
                TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) +
        ((left i).1 + 1) *
          (if TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
              (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) =
      (left i).1 *
          (if (c (left i)).1 = 2 ∧ (c i).1 ≠ 2 then 1 else 0) +
        ((left i).1 + 1) *
          (if (c i).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2WeightAfter, localExp2WeightBefore] at hweight
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hweight
    rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top] at hweight
    have htmp := hweight
    rw [hi_succ] at htmp
    exact htmp
  have hbits := eq_bits_of_sum_and_weight_local hexp2' hweight'
  have hi21' :
      (if (c (left i)).1 = 2 ∧
            TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) +
        (if TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) =
      (if (c (left i)).1 = 2 ∧ (c i).1 = 1 then 1 else 0) +
        (if (c i).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) := by
    rw [localInt21After, localInt21Before] at hi21
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hi21
    rw [cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n i.1 _ _ hi_in hi_top,
      cup2Int21BitVal_eq_inner n i.1 _ _ hi_in hi_top] at hi21
    exact hi21
  simpa [pn3TpLocal] using And.intro hbits.1 (And.intro hbits.2 hi21')

private theorem p2TpLocal_c1_one_or_two_c2_two_implies_out_two
    (c1 c3 : Fin 3)
    (hc1 : c1.1 = 1 ∨ c1.1 = 2)
    (htp : p2TpLocal c1.1 2 c3.1) :
    TMidVal c1.1 2 c3.1 = 2 := by
  have h :
      ∀ (c1 c3 : Fin 3),
        (c1.1 = 1 ∨ c1.1 = 2) →
        p2TpLocal c1.1 2 c3.1 →
        TMidVal c1.1 2 c3.1 = 2 := by
    native_decide
  exact h c1 c3 hc1 htp

private theorem pn3TpLocal_cN3_two_cN2_zero_implies_out_two
    (cN4 : Fin 3)
    (htp : pn3TpLocal cN4.1 2 0) :
    TMidVal cN4.1 2 0 = 2 := by
  have h :
      ∀ cN4 : Fin 3,
        pn3TpLocal cN4.1 2 0 →
        TMidVal cN4.1 2 0 = 2 := by
    native_decide
  exact h cN4 htp

private theorem pn011c1two_fc_noninc_of_boundary_fixed_tpStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c) :
    cup2Fc n hn4 c' ≤ cup2Fc n hn4 c := by
  rcases hstep.1.2.2 with ⟨i, hpriv, hmove⟩
  subst c'
  have htpMove : cup2TpPreservingMove n hn4 c i := by
    simpa [cup2TpPreservingMove] using hstep.2
  have hdecode := congrArg (fun s : SixState => decodeSixBoundary s.1) hfixed
  have hfixed6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i) =
        cup2Boundary6 n hn4 hn9 c := by
    simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdecode
  have hnotboundary : ¬ (i.1 ≤ 2 ∨ n - 3 ≤ i.1) := by
    intro hboundary
    exact (cup2Boundary6_changed_of_boundary_move n hn4 hn9 c i hpriv hboundary) hfixed6
  have h3 : 3 ≤ i.1 := by omega
  have htop : i.1 + 2 < n := by omega
  have hcopy :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (left i)).1 ∨
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (right i)).1 := by
    exact cup2TpPreserving_mid_copyNeighbor_val n hn4 c i h3 htop htpMove hpriv
  rw [cup2Fc_move_split n hn4 c i, cup2Fc_split n hn4 c i, cup2Fc_rest_move_eq n hn4 c i]
  have hlocal :=
    localFcAfter_le_of_copyNeighbor
      (c (left i)).1 (c i).1 (c (right i)).1
      (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) hcopy
  omega

private theorem localFcAfter_eq_localFcBefore_add_localFcDelta
    (L S R out : Nat) :
    (localFcAfter L S R out : Int) =
      localFcBefore L S R + localFcDelta L S R out := by
  unfold localFcBefore localFcAfter localFcDelta frontierBitVal
  by_cases h1 : L = out <;>
    by_cases h2 : L = S <;>
    by_cases h3 : out = R <;>
    by_cases h4 : S = R <;>
    simp [h1, h2, h3, h4] <;> omega

private theorem pn011c1two_sig_step_noninc_of_boundary_fixed
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c)
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c') ∧
      (cup2Fc n hn4 c' : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c') ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  have hsig : pn011c1two_sigOfConfig n hn4 hn9 c' = pn011c1two_sigOfConfig n hn4 hn9 c :=
    pn011c1two_sigOfConfig_eq_of_boundaryState_eq n hn4 hn9 hfixed
  constructor
  · simpa [hsig] using hrank
  · have hfc_le := pn011c1two_fc_noninc_of_boundary_fixed_tpStep n hn4 hn9 hstep hfixed
    have hfc_le' : (cup2Fc n hn4 c' : Int) ≤ cup2Fc n hn4 c := by
      exact_mod_cast hfc_le
    rw [hsig]
    omega

private theorem pn011c1two_sig_boundarySuccP0 (s : SixBoundary) :
    pn011c1two_sigOfBoundary (boundarySuccP0 s) =
      pn011c1two_sigSuccP0 (pn011c1two_sigOfBoundary s) := by
  ext <;> rfl

private theorem pn011c1two_sig_boundarySuccP1 (s : SixBoundary) :
    pn011c1two_sigOfBoundary (boundarySuccP1 s) =
      pn011c1two_sigSuccP1 (pn011c1two_sigOfBoundary s) := by
  ext <;> rfl

private theorem pn011c1two_sig_boundarySuccP2 (s : SixBoundary) (c3 : Fin 3) :
    pn011c1two_sigOfBoundary (boundarySuccP2 s c3) =
      pn011c1two_sigSuccP2 (pn011c1two_sigOfBoundary s) c3 := by
  ext <;> rfl

private theorem pn011c1two_sig_boundarySuccPN2 (s : SixBoundary) :
    pn011c1two_sigOfBoundary (boundarySuccPN2 s) =
      pn011c1two_sigSuccPN2 (pn011c1two_sigOfBoundary s) s.cN3 := by
  ext <;> rfl

private theorem pn011c1two_sig_boundarySuccPN1 (s : SixBoundary) :
    pn011c1two_sigOfBoundary (boundarySuccPN1 s) =
      pn011c1two_sigSuccPN1 (pn011c1two_sigOfBoundary s) := by
  ext <;> rfl

private theorem pn011c1two_sig_boundarySuccPN3 (s : SixBoundary) (cn4 : Fin 3) :
    pn011c1two_sigOfBoundary (boundarySuccPN3 s cn4) =
      pn011c1two_sigSuccPN3 (pn011c1two_sigOfBoundary s) cn4 := by
  ext <;> rfl

private lemma cup2Boundary6_move_eq_boundarySuccP0
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
      boundarySuccP0 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idx0 n hn4 hn9 c]
  ext
  · simp [boundarySuccP0, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx0 n hn9)
    have hright : (c (right (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx0 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]

private lemma cup2Boundary6_move_eq_boundarySuccP1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
      boundarySuccP1 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idx1 n hn4 hn9 c]
  ext
  · simp [boundarySuccP1]
  · simp [boundarySuccP1, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx1 n hn9)
    have hright : (c (right (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx1 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]

private lemma cup2Boundary6_move_eq_boundarySuccP2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
      boundarySuccP2 (cup2Boundary6 n hn4 hn9 c)
        (stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))) := by
  rw [cup2Boundary6_move_idx2 n hn4 hn9 c]
  ext
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2, stateAsFin3, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx2 n hn9)
    rw [hleft]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]

private lemma cup2Boundary6_move_eq_boundarySuccPN2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
      boundarySuccPN2 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idxN2 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN2 n hn9)
    have hright : (c (right (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN2 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccPN2]

private lemma cup2Boundary6_move_eq_boundarySuccPN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
      boundarySuccPN1 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idxN1 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN1 n hn9)
    have hright : (c (right (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN1 n hn9)
    rw [hleft, hright]

private theorem pn011c1two_sig_step_noninc_idx0
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) : Int) +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn011c1two_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        pn011c1two_sigSuccP0 (pn011c1two_sigOfConfig n hn4 hn9 c) := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)),
      pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn011c1two_sigSuccP0] using
      congrArg pn011c1two_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccP0 n hn4 hn9 c)
  have hlocal := pn011c1two_sig_step_P0 (pn011c1two_sigOfConfig n hn4 hn9 c) hrank
  constructor
  · simpa [hsig] using hlocal.1
  · have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx0 n hn9)
              (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1) : Int) +
          pn011c1two_sigRank (pn011c1two_sigSuccP0 (pn011c1two_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      have h := hlocal.2
      have hleft : (c (left (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx0 n hn9)
      have hright : (c (right (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx0 n hn9)
      have h' :
          localFcDelta (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1
              (TBotVal (c (left (cup2BoundaryIdx0 n hn9))).1
                (c (cup2BoundaryIdx0 n hn9)).1
                (c (right (cup2BoundaryIdx0 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccP0 (pn011c1two_sigOfConfig n hn4 hn9 c)) ≤
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
        simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c, pn011c1two_sigOfBoundary, hleft, hright] using h
      calc
        (localFcAfter (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx0 n hn9)
              (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1) : Int) +
            pn011c1two_sigRank (pn011c1two_sigSuccP0 (pn011c1two_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdx0 n hn9)
                (c (left (cup2BoundaryIdx0 n hn9))).1
                (c (cup2BoundaryIdx0 n hn9)).1
                (c (right (cup2BoundaryIdx0 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccP0 (pn011c1two_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1 +
            pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
                (c (cup2BoundaryIdx0 n hn9)).1
                (c (right (cup2BoundaryIdx0 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdx0 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_sig_step_noninc_idx1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) : Int) +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn011c1two_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        pn011c1two_sigSuccP1 (pn011c1two_sigOfConfig n hn4 hn9 c) := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)),
      pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn011c1two_sigSuccP1] using
      congrArg pn011c1two_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccP1 n hn4 hn9 c)
  have hlocal := pn011c1two_sig_step_P1 (pn011c1two_sigOfConfig n hn4 hn9 c) hrank
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hleft : (c (left (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx1 n hn9)
    have hright : (c (right (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx1 n hn9)
    have h' :
        localFcDelta (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (TLowVal (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) +
          pn011c1two_sigRank (pn011c1two_sigSuccP1 (pn011c1two_sigOfConfig n hn4 hn9 c)) ≤
        pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c, pn011c1two_sigOfBoundary, hleft, hright] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
          pn011c1two_sigRank (pn011c1two_sigSuccP1 (pn011c1two_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
            pn011c1two_sigRank (pn011c1two_sigSuccP1 (pn011c1two_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdx1 n hn9)
                (c (left (cup2BoundaryIdx1 n hn9))).1
                (c (cup2BoundaryIdx1 n hn9)).1
                (c (right (cup2BoundaryIdx1 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccP1 (pn011c1two_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1 +
            pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
                (c (cup2BoundaryIdx1 n hn9)).1
                (c (right (cup2BoundaryIdx1 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdx1 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_sig_step_noninc_idxN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN1 n hn9)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) : Int) +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn011c1two_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        pn011c1two_sigSuccPN1 (pn011c1two_sigOfConfig n hn4 hn9 c) := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)),
      pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn011c1two_sigSuccPN1] using
      congrArg pn011c1two_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c)
  have hlocal := pn011c1two_sig_step_PN1 (pn011c1two_sigOfConfig n hn4 hn9 c) hrank
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hleft : (c (left (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN1 n hn9)
    have hright : (c (right (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN1 n hn9)
    have h' :
        localFcDelta (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (TTopVal (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) +
          pn011c1two_sigRank (pn011c1two_sigSuccPN1 (pn011c1two_sigOfConfig n hn4 hn9 c)) ≤
        pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c, pn011c1two_sigOfBoundary, hleft, hright] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
          pn011c1two_sigRank (pn011c1two_sigSuccPN1 (pn011c1two_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
            pn011c1two_sigRank (pn011c1two_sigSuccPN1 (pn011c1two_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
                (c (left (cup2BoundaryIdxN1 n hn9))).1
                (c (cup2BoundaryIdxN1 n hn9)).1
                (c (right (cup2BoundaryIdxN1 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccPN1 (pn011c1two_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1 +
            pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
                (c (cup2BoundaryIdxN1 n hn9)).1
                (c (right (cup2BoundaryIdxN1 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdxN1 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_sig_step_noninc_idx2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) : Int) +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
  have hsig :
      pn011c1two_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        pn011c1two_sigSuccP2 (pn011c1two_sigOfConfig n hn4 hn9 c) c3 := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)),
      pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn011c1two_sigSuccP2, c3] using
      congrArg pn011c1two_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccP2 n hn4 hn9 c)
  have hlocal := pn011c1two_sig_step_P2 (pn011c1two_sigOfConfig n hn4 hn9 c) c3 hrank
    (by simpa [c3] using p2TpLocal_of_tpPreserving n hn4 hn9 c htp)
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hleft : (c (left (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx2 n hn9)
    have h' :
        localFcDelta (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (TMidVal (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccP2 (pn011c1two_sigOfConfig n hn4 hn9 c) c3) ≤
        pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c, pn011c1two_sigOfBoundary,
        c3, hleft] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
          pn011c1two_sigRank (pn011c1two_sigSuccP2 (pn011c1two_sigOfConfig n hn4 hn9 c) c3) ≤
        localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
            pn011c1two_sigRank (pn011c1two_sigSuccP2 (pn011c1two_sigOfConfig n hn4 hn9 c) c3) =
          localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdx2 n hn9)
                (c (left (cup2BoundaryIdx2 n hn9))).1
                (c (cup2BoundaryIdx2 n hn9)).1
                (c (right (cup2BoundaryIdx2 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccP2 (pn011c1two_sigOfConfig n hn4 hn9 c) c3)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1 +
            pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
                (c (cup2BoundaryIdx2 n hn9)).1
                (c (right (cup2BoundaryIdx2 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdx2 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_sig_step_noninc_idxN2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN2 n hn9)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) : Int) +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  let s := cup2Boundary6 n hn4 hn9 c
  have hsig :
      pn011c1two_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
        pn011c1two_sigSuccPN2 (pn011c1two_sigOfConfig n hn4 hn9 c) s.cN3 := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)),
      pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn011c1two_sigSuccPN2, s] using
      congrArg pn011c1two_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccPN2 n hn4 hn9 c)
  have hlocal := pn011c1two_sig_step_PN2 (pn011c1two_sigOfConfig n hn4 hn9 c) hrank
    (by simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c, pn011c1two_sigOfBoundary, s]
      using pn2TpLocal_of_tpPreserving n hn4 hn9 c htp)
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hleft : (c (left (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN2 n hn9)
    have hright : (c (right (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN2 n hn9)
    have h' :
        localFcDelta (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (THighVal (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) +
          pn011c1two_sigRank (pn011c1two_sigSuccPN2 (pn011c1two_sigOfConfig n hn4 hn9 c) s.cN3) ≤
        pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c, pn011c1two_sigOfBoundary, s, hleft, hright] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
          pn011c1two_sigRank (pn011c1two_sigSuccPN2 (pn011c1two_sigOfConfig n hn4 hn9 c) s.cN3) ≤
        localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
            pn011c1two_sigRank (pn011c1two_sigSuccPN2 (pn011c1two_sigOfConfig n hn4 hn9 c) s.cN3) =
          localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
                (c (left (cup2BoundaryIdxN2 n hn9))).1
                (c (cup2BoundaryIdxN2 n hn9)).1
                (c (right (cup2BoundaryIdxN2 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccPN2 (pn011c1two_sigOfConfig n hn4 hn9 c) s.cN3)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1 +
            pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
                (c (cup2BoundaryIdxN2 n hn9)).1
                (c (right (cup2BoundaryIdxN2 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN2 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN2 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN2 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdxN2 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private lemma cup2Boundary6_move_eq_boundarySuccPN3_aux
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
      boundarySuccPN3 (cup2Boundary6 n hn4 hn9 c)
        (stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))) := by
  rw [cup2Boundary6_move_idxN3 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3, stateAsFin3, cup2Boundary6, move_apply_self_val]
    have hright : (c (right (cup2BoundaryIdxN3 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN3 n hn9)
    rw [hright]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]

private theorem pn011c1two_sig_step_noninc_idxN3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9))
    (hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) : Int) +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  let cN4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
  have hsig :
      pn011c1two_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
        pn011c1two_sigSuccPN3 (pn011c1two_sigOfConfig n hn4 hn9 c) cN4 := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)),
      pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn011c1two_sigSuccPN3, cN4] using
      congrArg pn011c1two_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccPN3_aux n hn4 hn9 c)
  have hlocal := pn011c1two_sig_step_PN3 (pn011c1two_sigOfConfig n hn4 hn9 c) cN4 hrank
    (by simpa [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c, pn011c1two_sigOfBoundary, cN4,
      stateAsFin3] using pn3TpLocal_of_tpPreserving n hn4 hn9 c htp)
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hleft : (c (left (cup2BoundaryIdxN3 n hn9))).1 = cN4.1 := by
      simp [cN4, stateAsFin3]
    have hright : (c (right (cup2BoundaryIdxN3 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN3 n hn9)
    have h' :
        localFcDelta (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1
            (TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1) +
          pn011c1two_sigRank (pn011c1two_sigSuccPN3 (pn011c1two_sigOfConfig n hn4 hn9 c) cN4) ≤
        pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      dsimp [pn011c1two_sigOfConfig, pn011c1two_sigOfBoundary] at h ⊢
      rw [hleft, hright]
      exact h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
              (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1) : Int) +
          pn011c1two_sigRank (pn011c1two_sigSuccPN3 (pn011c1two_sigOfConfig n hn4 hn9 c) cN4) ≤
        localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 +
          pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
              (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1) : Int) +
            pn011c1two_sigRank (pn011c1two_sigSuccPN3 (pn011c1two_sigOfConfig n hn4 hn9 c) cN4) =
          localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
                (c (left (cup2BoundaryIdxN3 n hn9))).1
                (c (cup2BoundaryIdxN3 n hn9)).1
                (c (right (cup2BoundaryIdxN3 n hn9))).1) +
              pn011c1two_sigRank (pn011c1two_sigSuccPN3 (pn011c1two_sigOfConfig n hn4 hn9 c) cN4)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1 +
            pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
                (c (cup2BoundaryIdxN3 n hn9)).1
                (c (right (cup2BoundaryIdxN3 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN3 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN3 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN3 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdxN3 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_sig_step_noninc
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hrank : 0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c)) :
    0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c') ∧
      (cup2Fc n hn4 c' : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c') ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) := by
  by_cases hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c
  · exact pn011c1two_sig_step_noninc_of_boundary_fixed n hn4 hn9 hstep hfixed hrank
  · rcases hstep.1.2.2 with ⟨i, hpriv, hmove⟩
    subst c'
    have htpMove : cup2TpPreservingMove n hn4 c i := by
      simpa [cup2TpPreservingMove] using hstep.2
    have hbdry : i.1 ≤ 2 ∨ n - 3 ≤ i.1 :=
      cup2BoundaryState_changed_implies_boundary_index n hn4 hn9 c i hfixed
    rcases hbdry with hsmall | hlarge
    · by_cases hi0 : i.1 = 0
      · have hi : i = cup2BoundaryIdx0 n hn9 := by
          apply Fin.ext
          simpa [cup2BoundaryIdx0] using hi0
        subst i
        exact pn011c1two_sig_step_noninc_idx0 n hn4 hn9 c hrank htpMove
      · by_cases hi1 : i.1 = 1
        · have hi : i = cup2BoundaryIdx1 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx1] using hi1
          subst i
          exact pn011c1two_sig_step_noninc_idx1 n hn4 hn9 c hrank htpMove
        · have hi2 : i.1 = 2 := by omega
          have hi : i = cup2BoundaryIdx2 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx2] using hi2
          subst i
          exact pn011c1two_sig_step_noninc_idx2 n hn4 hn9 c hrank htpMove
    · by_cases hiN1 : i.1 + 1 = n
      · have hi : i = cup2BoundaryIdxN1 n hn9 := by
          have hi_val : i.1 = n - 1 := by omega
          apply Fin.ext
          simp [cup2BoundaryIdxN1, hi_val]
        subst i
        exact pn011c1two_sig_step_noninc_idxN1 n hn4 hn9 c hrank htpMove
      · by_cases hiN2 : i.1 + 2 = n
        · have hi : i = cup2BoundaryIdxN2 n hn9 := by
            have hi_val : i.1 = n - 2 := by omega
            apply Fin.ext
            simp [cup2BoundaryIdxN2, hi_val]
          subst i
          exact pn011c1two_sig_step_noninc_idxN2 n hn4 hn9 c hrank htpMove
        · have hi_lt : i.1 < n := i.2
          have hiN3 : i.1 = n - 3 := by omega
          have hi : i = cup2BoundaryIdxN3 n hn9 := by
            apply Fin.ext
            simp [cup2BoundaryIdxN3, hiN3]
          subst i
          exact pn011c1two_sig_step_noninc_idxN3 n hn4 hn9 c hrank htpMove hpriv

theorem pn1_011_c1_two_c2_zero_or_two_tpReachable_fc_le_core
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
      (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) d) :
    cup2Fc n hn4 d ≤
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
  let c' := move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
  have hsig0 : pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c') = 0 := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c',
      show c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) by rfl,
      cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c]
    let s := cup2Boundary6 n hn4 hn9 c
    have hsN3 : s.cN3.1 = 2 := by
      show ((cup2Boundary6 n hn4 hn9 c).cN3).1 = 2
      change (c (cup2BoundaryIdxN3 n hn9)).1 = 2
      exact hcN3
    have hsN2 : s.cN2.1 = 0 := by
      show ((cup2Boundary6 n hn4 hn9 c).cN2).1 = 0
      change (c (cup2BoundaryIdxN2 n hn9)).1 = 0
      exact hcN2
    have hsN1 : s.cN1.1 = 1 := by
      show ((cup2Boundary6 n hn4 hn9 c).cN1).1 = 1
      change (c (cup2BoundaryIdxN1 n hn9)).1 = 1
      exact hcN1
    have hs0 : s.c0.1 = 1 := by
      show ((cup2Boundary6 n hn4 hn9 c).c0).1 = 1
      change (c (cup2BoundaryIdx0 n hn9)).1 = 1
      exact hc0
    have hs1 : s.c1.1 = 2 := by
      show ((cup2Boundary6 n hn4 hn9 c).c1).1 = 2
      change (c (cup2BoundaryIdx1 n hn9)).1 = 2
      exact hc1
    exact pn011c1two_start_rank_zero_of_source s
      hsN3 hsN2 hsN1 hs0 hs1
      (by simpa [s, cup2Boundary6] using hc2)
  have hstrong :
      ∀ {x : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c' x →
          0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 x) ∧
            (cup2Fc n hn4 x : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 x) ≤
              (cup2Fc n hn4 c' : Int) := by
    intro x hreach'
    induction hreach' with
    | refl =>
      exact ⟨by simpa [hsig0], by simpa [hsig0]⟩
    | tail _ hstep ih =>
      rcases pn011c1two_sig_step_noninc n hn4 hn9 hstep ih.1 with ⟨hrank', hstep'⟩
      exact ⟨hrank', le_trans hstep' ih.2⟩
  have hbound := hstrong hreach
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c' := by
    omega
  exact Int.ofNat_le.mp hfc_le'

theorem p1_102_cN3_two_cN2_zero_tpReachable_fc_le_core
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤ cup2Fc n hn4 c := by
  have hsig0 : pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 c) = 0 := by
    rw [pn011c1two_sigOfConfig_eq_boundary n hn4 hn9 c]
    let s := cup2Boundary6 n hn4 hn9 c
    have hsN3 : s.cN3.1 = 2 := by
      show ((cup2Boundary6 n hn4 hn9 c).cN3).1 = 2
      change (c (cup2BoundaryIdxN3 n hn9)).1 = 2
      exact hcN3
    have hsN2 : s.cN2.1 = 0 := by
      show ((cup2Boundary6 n hn4 hn9 c).cN2).1 = 0
      change (c (cup2BoundaryIdxN2 n hn9)).1 = 0
      exact hcN2
    have hsN1 : s.cN1.1 = 0 := by
      show ((cup2Boundary6 n hn4 hn9 c).cN1).1 = 0
      change (c (cup2BoundaryIdxN1 n hn9)).1 = 0
      exact hcN1
    have hs0 : s.c0.1 = 1 := by
      show ((cup2Boundary6 n hn4 hn9 c).c0).1 = 1
      change (c (cup2BoundaryIdx0 n hn9)).1 = 1
      exact hc0
    have hs1 : s.c1.1 = 1 := by
      show ((cup2Boundary6 n hn4 hn9 c).c1).1 = 1
      change (c (cup2BoundaryIdx1 n hn9)).1 = 1
      exact hc1
    have hs2 : s.c2.1 = 2 := by
      show ((cup2Boundary6 n hn4 hn9 c).c2).1 = 2
      change (c (cup2BoundaryIdx2 n hn9)).1 = 2
      exact hc2
    rw [pn011c1two_sigRank, pn011c1two_sigIdx, pn011c1two_sigOfBoundary]
    simp [s, hsN3, hsN2, hsN1, hs0, hs1, hs2]
  have hstrong :
      ∀ {x : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c x →
          0 ≤ pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 x) ∧
            (cup2Fc n hn4 x : Int) + pn011c1two_sigRank (pn011c1two_sigOfConfig n hn4 hn9 x) ≤
              (cup2Fc n hn4 c : Int) := by
    intro x hreach'
    induction hreach' with
    | refl =>
      exact ⟨by simpa [hsig0], by simpa [hsig0]⟩
    | tail _ hstep ih =>
      rcases pn011c1two_sig_step_noninc n hn4 hn9 hstep ih.1 with ⟨hrank', hstep'⟩
      exact ⟨hrank', le_trans hstep' ih.2⟩
  have hbound := hstrong hreach
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c := by
    omega
  exact Int.ofNat_le.mp hfc_le'

private structure Pn011C1TwoC2OneSig where
  c1 : Fin 3
  c2 : Fin 3
  c3 : Fin 3
  c4 : Fin 3
  c5 : Fin 3
deriving DecidableEq, Fintype, Repr

@[ext] private theorem Pn011C1TwoC2OneSig.ext
    {s t : Pn011C1TwoC2OneSig}
    (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2) (h3 : s.c3 = t.c3)
    (h4 : s.c4 = t.c4) (h5 : s.c5 = t.c5) :
    s = t := by
  cases s
  cases t
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  rfl

private def pn011c1two_c2one_sigIdx (s : Pn011C1TwoC2OneSig) : Nat :=
  ((((s.c1.1 * 3 + s.c2.1) * 3 + s.c3.1) * 3 + s.c4.1) * 3 + s.c5.1)

private def pn011c1two_c2one_reachableVals : List Nat :=
  [0, 1, 2, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 81, 82, 83, 87, 88,
    89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 108, 109, 110, 111, 112, 113, 114,
    115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129,
    130, 131, 132, 133, 134, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162,
    163, 164, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 189,
    190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
    205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 234, 235, 236, 237,
    238, 239, 240, 241, 242]

private def pn011c1two_c2one_rankOneVals : List Nat :=
  [189, 190, 191, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]

private def pn011c1two_c2one_sigRank (s : Pn011C1TwoC2OneSig) : Int :=
  let idx := pn011c1two_c2one_sigIdx s
  if idx ∈ pn011c1two_c2one_rankOneVals then
    1
  else if idx ∈ pn011c1two_c2one_reachableVals then
    0
  else
    -1

private def pn011c1two_c2one_sigSuccIdx1 (s : Pn011C1TwoC2OneSig) : Pn011C1TwoC2OneSig :=
  { s with c1 := ⟨TLowVal 1 s.c1.1 s.c2.1, TLowVal_lt (by decide) s.c1.2 s.c2.2⟩ }

private def pn011c1two_c2one_sigSuccIdx2 (s : Pn011C1TwoC2OneSig) : Pn011C1TwoC2OneSig :=
  { s with c2 := ⟨TMidVal s.c1.1 s.c2.1 s.c3.1, TMidVal_lt s.c1.2 s.c2.2 s.c3.2⟩ }

private def pn011c1two_c2one_sigSuccIdx3 (s : Pn011C1TwoC2OneSig) : Pn011C1TwoC2OneSig :=
  { s with c3 := ⟨TMidVal s.c2.1 s.c3.1 s.c4.1, TMidVal_lt s.c2.2 s.c3.2 s.c4.2⟩ }

private def pn011c1two_c2one_sigSuccIdx4 (s : Pn011C1TwoC2OneSig) : Pn011C1TwoC2OneSig :=
  { s with c4 := ⟨TMidVal s.c3.1 s.c4.1 s.c5.1, TMidVal_lt s.c3.2 s.c4.2 s.c5.2⟩ }

private def pn011c1two_c2one_sigSuccIdx5
    (s : Pn011C1TwoC2OneSig) (c6 : Fin 3) : Pn011C1TwoC2OneSig :=
  { s with c5 := ⟨TMidVal s.c4.1 s.c5.1 c6.1, TMidVal_lt s.c4.2 s.c5.2 c6.2⟩ }

private abbrev midTpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    ((if L = 2 ∧ out = 1 then 1 else 0) + (if out = 2 ∧ R = 1 then 1 else 0) =
      (if L = 2 ∧ S = 1 then 1 else 0) + (if S = 2 ∧ R = 1 then 1 else 0))

private theorem pn011c1two_c2one_sig_step_idx1
    (s : Pn011C1TwoC2OneSig)
    (hrank : 0 ≤ pn011c1two_c2one_sigRank s) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx1 s) ∧
      localFcDelta 1 s.c1.1 s.c2.1 (TLowVal 1 s.c1.1 s.c2.1) +
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx1 s) ≤
      pn011c1two_c2one_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoC2OneSig,
        0 ≤ pn011c1two_c2one_sigRank s →
          0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx1 s) ∧
            localFcDelta 1 s.c1.1 s.c2.1 (TLowVal 1 s.c1.1 s.c2.1) +
              pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx1 s) ≤
            pn011c1two_c2one_sigRank s := by
    native_decide
  exact h s hrank

private theorem pn011c1two_c2one_sig_step_idx2
    (s : Pn011C1TwoC2OneSig)
    (hrank : 0 ≤ pn011c1two_c2one_sigRank s)
    (htp : p2TpLocal s.c1.1 s.c2.1 s.c3.1) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx2 s) ∧
      localFcDelta s.c1.1 s.c2.1 s.c3.1 (TMidVal s.c1.1 s.c2.1 s.c3.1) +
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx2 s) ≤
      pn011c1two_c2one_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoC2OneSig,
        0 ≤ pn011c1two_c2one_sigRank s →
          p2TpLocal s.c1.1 s.c2.1 s.c3.1 →
            0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx2 s) ∧
              localFcDelta s.c1.1 s.c2.1 s.c3.1 (TMidVal s.c1.1 s.c2.1 s.c3.1) +
                pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx2 s) ≤
              pn011c1two_c2one_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem pn011c1two_c2one_sig_step_idx3
    (s : Pn011C1TwoC2OneSig)
    (hrank : 0 ≤ pn011c1two_c2one_sigRank s)
    (htp : midTpLocal s.c2.1 s.c3.1 s.c4.1) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx3 s) ∧
      localFcDelta s.c2.1 s.c3.1 s.c4.1 (TMidVal s.c2.1 s.c3.1 s.c4.1) +
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx3 s) ≤
      pn011c1two_c2one_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoC2OneSig,
        0 ≤ pn011c1two_c2one_sigRank s →
          midTpLocal s.c2.1 s.c3.1 s.c4.1 →
            0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx3 s) ∧
              localFcDelta s.c2.1 s.c3.1 s.c4.1 (TMidVal s.c2.1 s.c3.1 s.c4.1) +
                pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx3 s) ≤
              pn011c1two_c2one_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem pn011c1two_c2one_sig_step_idx4
    (s : Pn011C1TwoC2OneSig)
    (hrank : 0 ≤ pn011c1two_c2one_sigRank s)
    (htp : midTpLocal s.c3.1 s.c4.1 s.c5.1) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx4 s) ∧
      localFcDelta s.c3.1 s.c4.1 s.c5.1 (TMidVal s.c3.1 s.c4.1 s.c5.1) +
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx4 s) ≤
      pn011c1two_c2one_sigRank s := by
  have h :
      ∀ s : Pn011C1TwoC2OneSig,
        0 ≤ pn011c1two_c2one_sigRank s →
          midTpLocal s.c3.1 s.c4.1 s.c5.1 →
            0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx4 s) ∧
              localFcDelta s.c3.1 s.c4.1 s.c5.1 (TMidVal s.c3.1 s.c4.1 s.c5.1) +
                pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx4 s) ≤
              pn011c1two_c2one_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem pn011c1two_c2one_sig_step_idx5
    (s : Pn011C1TwoC2OneSig) (c6 : Fin 3)
    (hrank : 0 ≤ pn011c1two_c2one_sigRank s)
    (htp : midTpLocal s.c4.1 s.c5.1 c6.1) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx5 s c6) ∧
      localFcDelta s.c4.1 s.c5.1 c6.1 (TMidVal s.c4.1 s.c5.1 c6.1) +
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx5 s c6) ≤
      pn011c1two_c2one_sigRank s := by
  have h :
      ∀ (s : Pn011C1TwoC2OneSig) (c6 : Fin 3),
        0 ≤ pn011c1two_c2one_sigRank s →
          midTpLocal s.c4.1 s.c5.1 c6.1 →
            0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx5 s c6) ∧
              localFcDelta s.c4.1 s.c5.1 c6.1 (TMidVal s.c4.1 s.c5.1 c6.1) +
                pn011c1two_c2one_sigRank (pn011c1two_c2one_sigSuccIdx5 s c6) ≤
              pn011c1two_c2one_sigRank s := by
    native_decide
  exact h s c6 hrank htp

private theorem pn011c1two_c2one_start_rank
    (c3 c4 c5 : Fin 3) :
    pn011c1two_c2one_sigRank
        { c1 := (⟨2, by decide⟩ : Fin 3)
          c2 := (⟨1, by decide⟩ : Fin 3)
          c3 := c3
          c4 := c4
          c5 := c5 } =
      if c3.1 = 1 ∨
          (c3.1 = 0 ∧ c4.1 = 0) ∨
          (c3.1 = 0 ∧ c4.1 = 2 ∧ c5.1 = 2) then
        1
      else
        0 := by
  fin_cases c3 <;> fin_cases c4 <;> fin_cases c5 <;> native_decide

private theorem midTpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) {i : Fin n}
    (h3 : 3 ≤ i.1) (htop : i.1 + 2 < n)
    (htp : cup2TpPreservingMove n hn4 c i) :
    midTpLocal (c (left i)).1 (c i).1 (c (right i)).1 := by
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have h2 : 2 ≤ i.1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh' : i.1 + 2 ≠ n := by omega
  have hleft_val : (left i).1 = i.1 - 1 := by
    simpa using left_val_of_ne_zero h0
  have hleft_in : 2 ≤ (left i).1 := by
    rw [hleft_val]
    omega
  have hleft_top : (left i).1 + 2 < n := by
    rw [hleft_val]
    omega
  obtain ⟨hexp2, hi21, hweight⟩ := cup2TpPreserving_local_eqs n hn4 c i htp
  have hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
        TMidVal (c (left i)).1 (c i).1 (c (right i)).1 := by
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop', if_neg hhigh']
  have hexp2' :
      (if (c (left i)).1 = 2 ∧
            TMidVal (c (left i)).1 (c i).1 (c (right i)).1 ≠ 2 then 1 else 0) +
        (if TMidVal (c (left i)).1 (c i).1 (c (right i)).1 = 2 ∧
            (c (right i)).1 ≠ 2 then 1 else 0) =
      (if (c (left i)).1 = 2 ∧ (c i).1 ≠ 2 then 1 else 0) +
        (if (c i).1 = 2 ∧ (c (right i)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2After, localExp2Before] at hexp2
    rw [hout] at hexp2
    rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ h2 htop,
      cup2Exp2BitVal_eq_inner n i.1 _ _ h2 htop] at hexp2
    exact hexp2
  have hweight' :
      (left i).1 *
          (if (c (left i)).1 = 2 ∧
                TMidVal (c (left i)).1 (c i).1 (c (right i)).1 ≠ 2 then 1 else 0) +
        ((left i).1 + 1) *
          (if TMidVal (c (left i)).1 (c i).1 (c (right i)).1 = 2 ∧
              (c (right i)).1 ≠ 2 then 1 else 0) =
      (left i).1 *
          (if (c (left i)).1 = 2 ∧ (c i).1 ≠ 2 then 1 else 0) +
        ((left i).1 + 1) *
          (if (c i).1 = 2 ∧ (c (right i)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2WeightAfter, localExp2WeightBefore] at hweight
    rw [hout] at hweight
    rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ h2 htop,
      cup2Exp2BitVal_eq_inner n i.1 _ _ h2 htop] at hweight
    have htmp := hweight
    have hi_succ : i.1 = (left i).1 + 1 := by
      rw [hleft_val]
      omega
    rw [hi_succ] at htmp
    exact htmp
  have hbits := eq_bits_of_sum_and_weight_local hexp2' hweight'
  have hi21' :
      (if (c (left i)).1 = 2 ∧
            TMidVal (c (left i)).1 (c i).1 (c (right i)).1 = 1 then 1 else 0) +
        (if TMidVal (c (left i)).1 (c i).1 (c (right i)).1 = 2 ∧
            (c (right i)).1 = 1 then 1 else 0) =
      (if (c (left i)).1 = 2 ∧ (c i).1 = 1 then 1 else 0) +
        (if (c i).1 = 2 ∧ (c (right i)).1 = 1 then 1 else 0) := by
    rw [localInt21After, localInt21Before] at hi21
    rw [hout] at hi21
    rw [cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n i.1 _ _ h2 htop,
      cup2Int21BitVal_eq_inner n i.1 _ _ h2 htop] at hi21
    exact hi21
  simpa [midTpLocal] using And.intro hbits.1 (And.intro hbits.2 hi21')

private def cup2Idx3 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨3, by omega⟩

private def cup2Idx4 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨4, by omega⟩

private def cup2Idx5 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨5, by omega⟩

private def cup2Idx6 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨6, by omega⟩

private theorem right_cup2BoundaryIdx2_eq_idx3
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2BoundaryIdx2 n hn9) = cup2Idx3 n hn9 := by
  apply Fin.ext
  have hlt : 3 < n := by omega
  simp [right_val, cup2BoundaryIdx2, cup2Idx3, Nat.mod_eq_of_lt hlt]

private theorem left_cup2Idx3_eq_boundaryIdx2
    (n : Nat) (hn9 : 9 ≤ n) :
    left (cup2Idx3 n hn9) = cup2BoundaryIdx2 n hn9 := by
  apply Fin.ext
  have hlt : 2 < n := by omega
  simp [cup2Idx3, cup2BoundaryIdx2, left_val, Nat.mod_eq_of_lt hlt]

private theorem right_cup2Idx3_eq_idx4
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2Idx3 n hn9) = cup2Idx4 n hn9 := by
  apply Fin.ext
  have hlt : 4 < n := by omega
  simp [right_val, cup2Idx3, cup2Idx4, Nat.mod_eq_of_lt hlt]

private theorem left_cup2Idx4_eq_idx3
    (n : Nat) (hn9 : 9 ≤ n) :
    left (cup2Idx4 n hn9) = cup2Idx3 n hn9 := by
  apply Fin.ext
  have hlt : 3 < n := by omega
  simp [cup2Idx4, cup2Idx3, left_val, Nat.mod_eq_of_lt hlt]

private theorem right_cup2Idx4_eq_idx5
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2Idx4 n hn9) = cup2Idx5 n hn9 := by
  apply Fin.ext
  have hlt : 5 < n := by omega
  simp [cup2Idx4, cup2Idx5, right_val, Nat.mod_eq_of_lt hlt]

private theorem left_cup2Idx5_eq_idx4
    (n : Nat) (hn9 : 9 ≤ n) :
    left (cup2Idx5 n hn9) = cup2Idx4 n hn9 := by
  apply Fin.ext
  have hlt : 4 < n := by omega
  simp [cup2Idx5, cup2Idx4, left_val, Nat.mod_eq_of_lt hlt]

private theorem right_cup2Idx5_eq_idx6
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2Idx5 n hn9) = cup2Idx6 n hn9 := by
  apply Fin.ext
  have hlt : 6 < n := by omega
  simp [cup2Idx5, cup2Idx6, right_val, Nat.mod_eq_of_lt hlt]

private def pn011c1two_c2one_sigOfConfig
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Pn011C1TwoC2OneSig :=
  { c1 := stateAsFin3 n hn4 c (cup2BoundaryIdx1 n hn9)
    c2 := stateAsFin3 n hn4 c (cup2BoundaryIdx2 n hn9)
    c3 := stateAsFin3 n hn4 c (cup2Idx3 n hn9)
    c4 := stateAsFin3 n hn4 c (cup2Idx4 n hn9)
    c5 := stateAsFin3 n hn4 c (cup2Idx5 n hn9) }

private theorem pn011c1two_c2one_start_rank_of_config
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1) :
    pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) =
      if (c (cup2Idx3 n hn9)).1 = 1 ∨
          ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
          ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
            (c (cup2Idx5 n hn9)).1 = 2) then
        1
      else
        0 := by
  let c3 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx3 n hn9)
  let c4 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx4 n hn9)
  let c5 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx5 n hn9)
  have hc3 : (c (cup2Idx3 n hn9)).1 = c3.1 := by simp [c3, stateAsFin3]
  have hc4 : (c (cup2Idx4 n hn9)).1 = c4.1 := by simp [c4, stateAsFin3]
  have hc5 : (c (cup2Idx5 n hn9)).1 = c5.1 := by simp [c5, stateAsFin3]
  have hsig :
      pn011c1two_c2one_sigOfConfig n hn4 hn9 c =
        { c1 := (⟨2, by decide⟩ : Fin 3)
          c2 := (⟨1, by decide⟩ : Fin 3)
          c3 := c3
          c4 := c4
          c5 := c5 } := by
    ext <;> simp [pn011c1two_c2one_sigOfConfig, hc1, hc2, c3, c4, c5, stateAsFin3]
  rw [hsig, pn011c1two_c2one_start_rank c3 c4 c5]
  simp [hc3, hc4, hc5]

private theorem tbot_zero_one_eq_one (r : Fin 3) :
    TBotVal 0 1 r.1 = 1 := by
  fin_cases r <;> native_decide

private theorem thigh_two_zero_zero_eq_zero :
    THighVal 2 0 0 = 0 := by native_decide

private theorem ttop_zero_zero_one_eq_zero :
    TTopVal 0 0 1 = 0 := by native_decide

private theorem not_privileged_idx0_of_cN1_zero_c0_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1) :
    ¬ privileged (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) := by
  intro hpriv
  unfold privileged cup2System at hpriv
  rw [Fin.ne_iff_vne, cup2Trans_val,
    cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9] at hpriv
  have hc1 : TBotVal 0 1 (c (cup2BoundaryIdx1 n hn9)).1 = 1 := by
    let r : Fin 3 := stateAsFin3 n hn4 c (cup2BoundaryIdx1 n hn9)
    have hr : r.1 = (c (cup2BoundaryIdx1 n hn9)).1 := by rfl
    simpa [hr] using tbot_zero_one_eq_one r
  simpa [hcN1, hc0, hc1] using hpriv

private theorem not_privileged_idxN2_of_cN3_two_cN2_zero_cN1_zero
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0) :
    ¬ privileged (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9) := by
  intro hpriv
  unfold privileged cup2System at hpriv
  rw [Fin.ne_iff_vne, cup2Trans_val,
    cup2OutVal_boundaryIdxN2 n hn9, left_cup2BoundaryIdxN2 n hn9,
    right_cup2BoundaryIdxN2 n hn9] at hpriv
  simpa [hcN3, hcN2, hcN1, thigh_two_zero_zero_eq_zero] using hpriv

private theorem not_privileged_idxN1_of_cN2_zero_cN1_zero_c0_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1) :
    ¬ privileged (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) := by
  intro hpriv
  unfold privileged cup2System at hpriv
  rw [Fin.ne_iff_vne, cup2Trans_val,
    cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
    right_cup2BoundaryIdxN1 n hn9] at hpriv
  simpa [hcN2, hcN1, hc0, ttop_zero_zero_one_eq_zero] using hpriv

private theorem not_privileged_idxN3_of_cN3_two_cN2_zero
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9)) :
    ¬ privileged (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9) := by
  intro hpriv
  have htpLocal := pn3TpLocal_of_tpPreserving n hn4 hn9 c htp
  let cN4 : Fin 3 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
  have hmid :
      TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
    have htwo := pn3TpLocal_cN3_two_cN2_zero_implies_out_two cN4
      (by simpa [cN4, stateAsFin3, hcN3, hcN2] using htpLocal)
    simpa [cN4, stateAsFin3, hcN3, hcN2] using htwo
  have hout :
      cup2OutVal n (cup2BoundaryIdxN3 n hn9)
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
    rw [cup2OutVal_boundaryIdxN3 n hn9]
    exact hmid
  unfold privileged cup2System at hpriv
  rw [Fin.ne_iff_vne, cup2Trans_val] at hpriv
  rw [right_cup2BoundaryIdxN3 n hn9, hout, hcN3] at hpriv
  exact hpriv rfl

private theorem pn011c1two_c2one_sig_eq_of_move_off_window
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi1 : i ≠ cup2BoundaryIdx1 n hn9)
    (hi2 : i ≠ cup2BoundaryIdx2 n hn9)
    (hi3 : i ≠ cup2Idx3 n hn9)
    (hi4 : i ≠ cup2Idx4 n hn9)
    (hi5 : i ≠ cup2Idx5 n hn9) :
    pn011c1two_c2one_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c i) =
      pn011c1two_c2one_sigOfConfig n hn4 hn9 c := by
  ext <;> simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
  · rw [move_apply_ne n hn4 c i (cup2BoundaryIdx1 n hn9) (by intro hEq; exact hi1 hEq.symm)]
  · rw [move_apply_ne n hn4 c i (cup2BoundaryIdx2 n hn9) (by intro hEq; exact hi2 hEq.symm)]
  · rw [move_apply_ne n hn4 c i (cup2Idx3 n hn9) (by intro hEq; exact hi3 hEq.symm)]
  · rw [move_apply_ne n hn4 c i (cup2Idx4 n hn9) (by intro hEq; exact hi4 hEq.symm)]
  · rw [move_apply_ne n hn4 c i (cup2Idx5 n hn9) (by intro hEq; exact hi5 hEq.symm)]

private theorem pn011c1two_c2one_leftFrame_preserved_of_move_off
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hiN3 : i ≠ cup2BoundaryIdxN3 n hn9)
    (hiN2 : i ≠ cup2BoundaryIdxN2 n hn9)
    (hiN1 : i ≠ cup2BoundaryIdxN1 n hn9)
    (hi0 : i ≠ cup2BoundaryIdx0 n hn9)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1) :
    ((move (cup2System n hn4) c i) (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
      ((move (cup2System n hn4) c i) (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      ((move (cup2System n hn4) c i) (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      ((move (cup2System n hn4) c i) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
  have hcN3' :
      ((move (cup2System n hn4) c i) (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdxN3 n hn9) (by intro hEq; exact hiN3 hEq.symm)]
    exact hcN3
  have hcN2' :
      ((move (cup2System n hn4) c i) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdxN2 n hn9) (by intro hEq; exact hiN2 hEq.symm)]
    exact hcN2
  have hcN1' :
      ((move (cup2System n hn4) c i) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdxN1 n hn9) (by intro hEq; exact hiN1 hEq.symm)]
    exact hcN1
  have hc0' :
      ((move (cup2System n hn4) c i) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdx0 n hn9) (by intro hEq; exact hi0 hEq.symm)]
    exact hc0
  exact ⟨hcN3', hcN2', hcN1', hc0'⟩

private theorem pn011c1two_c2one_sig_step_noninc_idx1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hrank : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9)) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) : Int) +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn011c1two_c2one_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        pn011c1two_c2one_sigSuccIdx1 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
    ext <;> simp [pn011c1two_c2one_sigOfConfig, pn011c1two_c2one_sigSuccIdx1, stateAsFin3]
    · rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
      simp [hc0]
    · have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    · have hne : cup2Idx3 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx3, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2Idx3 n hn9) hne]
    · have hne : cup2Idx4 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx4, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2Idx4 n hn9) hne]
    · have hne : cup2Idx5 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx5, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2Idx5 n hn9) hne]
  have hlocal :=
    pn011c1two_c2one_sig_step_idx1 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) hrank
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hc2 : (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c2.1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have h' :
        localFcDelta 1 (c (cup2BoundaryIdx1 n hn9)).1 (c (cup2BoundaryIdx2 n hn9)).1
            (TLowVal 1 (c (cup2BoundaryIdx1 n hn9)).1 (c (cup2BoundaryIdx2 n hn9)).1) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx1 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_c2one_sigOfConfig, hc2, stateAsFin3] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx1 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      have hleft : (c (left (cup2BoundaryIdx1 n hn9))).1 = 1 := by
        rw [left_cup2BoundaryIdx1 n hn9]
        exact hc0
      have hright : (c (right (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx1 n hn9)
      calc
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
            pn011c1two_c2one_sigRank
              (pn011c1two_c2one_sigSuccIdx1 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdx1 n hn9)
                (c (left (cup2BoundaryIdx1 n hn9))).1
                (c (cup2BoundaryIdx1 n hn9)).1
                (c (right (cup2BoundaryIdx1 n hn9))).1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx1 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1 +
            pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
          simpa [hleft, hright, add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdx1 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_c2one_sig_step_noninc_idx2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9)) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) : Int) +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn011c1two_c2one_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        pn011c1two_c2one_sigSuccIdx2 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
    ext <;> simp [pn011c1two_c2one_sigOfConfig, pn011c1two_c2one_sigSuccIdx2, stateAsFin3]
    · have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    · rw [left_cup2BoundaryIdx2 n hn9, right_cup2BoundaryIdx2_eq_idx3 n hn9]
    · have hne : cup2Idx3 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx3, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2Idx3 n hn9) hne]
    · have hne : cup2Idx4 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx4, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2Idx4 n hn9) hne]
    · have hne : cup2Idx5 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx5, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2Idx5 n hn9) hne]
  have hlocal :=
    pn011c1two_c2one_sig_step_idx2 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) hrank
      (by
        have htpLocal := p2TpLocal_of_tpPreserving n hn4 hn9 c htp
        rw [right_cup2BoundaryIdx2_eq_idx3 n hn9] at htpLocal
        simpa [pn011c1two_c2one_sigOfConfig, stateAsFin3] using htpLocal)
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hc1 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c1.1 =
          (c (cup2BoundaryIdx1 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have hc3 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c3.1 =
          (c (cup2Idx3 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have h' :
        localFcDelta (c (cup2BoundaryIdx1 n hn9)).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (cup2Idx3 n hn9)).1
            (TMidVal (c (cup2BoundaryIdx1 n hn9)).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx2 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_c2one_sigOfConfig, hc1, hc3, stateAsFin3] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx2 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      have hleft : (c (left (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx2 n hn9)
      have hright : (c (right (cup2BoundaryIdx2 n hn9))).1 = (c (cup2Idx3 n hn9)).1 := by
        rw [right_cup2BoundaryIdx2_eq_idx3 n hn9]
      calc
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
            pn011c1two_c2one_sigRank
              (pn011c1two_c2one_sigSuccIdx2 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1 +
            (localFcDelta (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1
              (cup2OutVal n (cup2BoundaryIdx2 n hn9)
                (c (left (cup2BoundaryIdx2 n hn9))).1
                (c (cup2BoundaryIdx2 n hn9)).1
                (c (right (cup2BoundaryIdx2 n hn9))).1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx2 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1 +
            pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
          simpa [hleft, hright, add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdx2 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_c2one_sig_step_noninc_idx3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2Idx3 n hn9)) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2Idx3 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9)) : Int) +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2Idx3 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn011c1two_c2one_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2Idx3 n hn9)) =
        pn011c1two_c2one_sigSuccIdx3 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
    ext <;> simp [pn011c1two_c2one_sigOfConfig, pn011c1two_c2one_sigSuccIdx3, stateAsFin3]
    · have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx3] at hval
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    · have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2Idx3] at hval
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    · have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
      have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
      have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
        simp [cup2Idx3]
        omega
      have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
        simp [cup2Idx3]
        omega
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh,
        left_cup2Idx3_eq_boundaryIdx2 n hn9, right_cup2Idx3_eq_idx4 n hn9]
    · have hne : cup2Idx4 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx4, cup2Idx3] at hval
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2Idx4 n hn9) hne]
    · have hne : cup2Idx5 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx5, cup2Idx3] at hval
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2Idx5 n hn9) hne]
  have htpLocal :
      midTpLocal (c (cup2BoundaryIdx2 n hn9)).1 (c (cup2Idx3 n hn9)).1
        (c (cup2Idx4 n hn9)).1 := by
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2Idx3 n hn9)
      (by simp [cup2Idx3]) (by simp [cup2Idx3]; omega) htp
    rw [left_cup2Idx3_eq_boundaryIdx2 n hn9, right_cup2Idx3_eq_idx4 n hn9] at hlocal
    exact hlocal
  have hlocal :=
    pn011c1two_c2one_sig_step_idx3 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hc2 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c2.1 =
          (c (cup2BoundaryIdx2 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have hc4 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c4.1 =
          (c (cup2Idx4 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have h' :
        localFcDelta (c (cup2BoundaryIdx2 n hn9)).1
            (c (cup2Idx3 n hn9)).1
            (c (cup2Idx4 n hn9)).1
            (TMidVal (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx3 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_c2one_sigOfConfig, hc2, hc4, stateAsFin3] using h
    have hleft : (c (left (cup2Idx3 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
    have hright : (c (right (cup2Idx3 n hn9))).1 = (c (cup2Idx4 n hn9)).1 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
    have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
    have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
    have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx3]
      omega
    have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx3]
      omega
    have hout' :
        cup2OutVal n (cup2Idx3 n hn9)
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (cup2Idx3 n hn9)).1
          (c (cup2Idx4 n hn9)).1 =
            TMidVal (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hdelta :
        (localFcAfter (c (left (cup2Idx3 n hn9))).1
            (c (cup2Idx3 n hn9)).1
            (c (right (cup2Idx3 n hn9))).1
            (cup2OutVal n (cup2Idx3 n hn9)
              (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1) : Int) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx3 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2Idx3 n hn9))).1
          (c (cup2Idx3 n hn9)).1
            (c (right (cup2Idx3 n hn9))).1 +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      rw [hleft, hright]
      calc
        (localFcAfter (c (cup2BoundaryIdx2 n hn9)).1
            (c (cup2Idx3 n hn9)).1
            (c (cup2Idx4 n hn9)).1
            (cup2OutVal n (cup2Idx3 n hn9)
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1) : Int) +
            pn011c1two_c2one_sigRank
              (pn011c1two_c2one_sigSuccIdx3 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 +
            (localFcDelta (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (cup2OutVal n (cup2Idx3 n hn9)
                (c (cup2BoundaryIdx2 n hn9)).1
                (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx3 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ = localFcBefore (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 +
            (localFcDelta (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (TMidVal (c (cup2BoundaryIdx2 n hn9)).1
                (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx3 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))) := by
          rw [hout']
        _ ≤ localFcBefore (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 +
            pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (cup2BoundaryIdx2 n hn9)).1
                (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2Idx3 n hn9),
      cup2Fc_split n hn4 c (cup2Idx3 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2Idx3 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2Idx3 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_c2one_sig_step_noninc_idx4
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2Idx4 n hn9)) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2Idx4 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9)) : Int) +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2Idx4 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn011c1two_c2one_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2Idx4 n hn9)) =
        pn011c1two_c2one_sigSuccIdx4 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
    ext <;> simp [pn011c1two_c2one_sigOfConfig, pn011c1two_c2one_sigSuccIdx4, stateAsFin3]
    · have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx4] at hval
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    · have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2Idx4] at hval
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    · have hne : cup2Idx3 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx3, cup2Idx4] at hval
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2Idx3 n hn9) hne]
    · have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
      have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
      have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
        simp [cup2Idx4]
        omega
      have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
        simp [cup2Idx4]
        omega
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh,
        left_cup2Idx4_eq_idx3 n hn9, right_cup2Idx4_eq_idx5 n hn9]
    · have hne : cup2Idx5 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx5, cup2Idx4] at hval
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2Idx5 n hn9) hne]
  have htpLocal :
      midTpLocal (c (cup2Idx3 n hn9)).1 (c (cup2Idx4 n hn9)).1
        (c (cup2Idx5 n hn9)).1 := by
    have h4 : 3 ≤ (cup2Idx4 n hn9).1 := by simp [cup2Idx4]
    have htop4 : (cup2Idx4 n hn9).1 + 2 < n := by simp [cup2Idx4]; omega
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2Idx4 n hn9)
      h4 htop4 htp
    rw [left_cup2Idx4_eq_idx3 n hn9, right_cup2Idx4_eq_idx5 n hn9] at hlocal
    exact hlocal
  have hlocal :=
    pn011c1two_c2one_sig_step_idx4 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hc3 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c3.1 =
          (c (cup2Idx3 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have hc5 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c5.1 =
          (c (cup2Idx5 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have h' :
        localFcDelta (c (cup2Idx3 n hn9)).1
            (c (cup2Idx4 n hn9)).1
            (c (cup2Idx5 n hn9)).1
            (TMidVal (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx4 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_c2one_sigOfConfig, hc3, hc5, stateAsFin3] using h
    have hleft : (c (left (cup2Idx4 n hn9))).1 = (c (cup2Idx3 n hn9)).1 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
    have hright : (c (right (cup2Idx4 n hn9))).1 = (c (cup2Idx5 n hn9)).1 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
    have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
    have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
    have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx4]
      omega
    have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx4]
      omega
    have hout' :
        cup2OutVal n (cup2Idx4 n hn9)
          (c (cup2Idx3 n hn9)).1
          (c (cup2Idx4 n hn9)).1
          (c (cup2Idx5 n hn9)).1 =
            TMidVal (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hdelta :
        (localFcAfter (c (left (cup2Idx4 n hn9))).1
            (c (cup2Idx4 n hn9)).1
            (c (right (cup2Idx4 n hn9))).1
            (cup2OutVal n (cup2Idx4 n hn9)
              (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1) : Int) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx4 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2Idx4 n hn9))).1
          (c (cup2Idx4 n hn9)).1
          (c (right (cup2Idx4 n hn9))).1 +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      rw [hleft, hright]
      calc
        (localFcAfter (c (cup2Idx3 n hn9)).1
            (c (cup2Idx4 n hn9)).1
            (c (cup2Idx5 n hn9)).1
            (cup2OutVal n (cup2Idx4 n hn9)
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1) : Int) +
            pn011c1two_c2one_sigRank
              (pn011c1two_c2one_sigSuccIdx4 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 +
            (localFcDelta (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1
              (cup2OutVal n (cup2Idx4 n hn9)
                (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1
                (c (cup2Idx5 n hn9)).1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx4 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ = localFcBefore (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 +
            (localFcDelta (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1
              (TMidVal (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1
                (c (cup2Idx5 n hn9)).1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx4 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))) := by
          rw [hout']
        _ ≤ localFcBefore (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 +
            pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1
                (c (cup2Idx5 n hn9)).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2Idx4 n hn9),
      cup2Fc_split n hn4 c (cup2Idx4 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2Idx4 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2Idx4 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_c2one_sig_step_noninc_idx5
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2Idx5 n hn9)) :
    0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2Idx5 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx5 n hn9)) : Int) +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2Idx5 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
  let c6 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx6 n hn9)
  have hsig :
      pn011c1two_c2one_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2Idx5 n hn9)) =
        pn011c1two_c2one_sigSuccIdx5 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) c6 := by
    ext <;> simp [pn011c1two_c2one_sigOfConfig, pn011c1two_c2one_sigSuccIdx5, stateAsFin3]
    · have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx5 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx5] at hval
      rw [move_apply_ne n hn4 c (cup2Idx5 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    · have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx5 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2Idx5] at hval
      rw [move_apply_ne n hn4 c (cup2Idx5 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    · have hne : cup2Idx3 n hn9 ≠ cup2Idx5 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx3, cup2Idx5] at hval
      rw [move_apply_ne n hn4 c (cup2Idx5 n hn9) (cup2Idx3 n hn9) hne]
    · have hne : cup2Idx4 n hn9 ≠ cup2Idx5 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx4, cup2Idx5] at hval
      rw [move_apply_ne n hn4 c (cup2Idx5 n hn9) (cup2Idx4 n hn9) hne]
    · have h0 : (cup2Idx5 n hn9).1 ≠ 0 := by simp [cup2Idx5]
      have h1 : (cup2Idx5 n hn9).1 ≠ 1 := by simp [cup2Idx5]
      have htop : (cup2Idx5 n hn9).1 + 1 ≠ n := by
        simp [cup2Idx5]
        omega
      have hhigh : (cup2Idx5 n hn9).1 + 2 ≠ n := by
        simp [cup2Idx5]
        omega
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh,
        left_cup2Idx5_eq_idx4 n hn9, right_cup2Idx5_eq_idx6 n hn9]
      simp [c6, stateAsFin3]
  have htpLocal :
      midTpLocal (c (cup2Idx4 n hn9)).1 (c (cup2Idx5 n hn9)).1 c6.1 := by
    have h5 : 3 ≤ (cup2Idx5 n hn9).1 := by simp [cup2Idx5]
    have htop5 : (cup2Idx5 n hn9).1 + 2 < n := by simp [cup2Idx5]; omega
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2Idx5 n hn9)
      h5 htop5 htp
    rw [left_cup2Idx5_eq_idx4 n hn9, right_cup2Idx5_eq_idx6 n hn9] at hlocal
    simpa [c6, stateAsFin3] using hlocal
  have hlocal :=
    pn011c1two_c2one_sig_step_idx5 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) c6 hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have h := hlocal.2
    have hc4 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c4.1 =
          (c (cup2Idx4 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have hc5 :
        (pn011c1two_c2one_sigOfConfig n hn4 hn9 c).c5.1 =
          (c (cup2Idx5 n hn9)).1 := by
      simp [pn011c1two_c2one_sigOfConfig, stateAsFin3]
    have h' :
        localFcDelta (c (cup2Idx4 n hn9)).1
            (c (cup2Idx5 n hn9)).1 c6.1
            (TMidVal (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx5 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) c6) ≤
        pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      simpa [pn011c1two_c2one_sigOfConfig, hc4, hc5, c6, stateAsFin3] using h
    have hleft : (c (left (cup2Idx5 n hn9))).1 = (c (cup2Idx4 n hn9)).1 := by
      rw [left_cup2Idx5_eq_idx4 n hn9]
    have hright : (c (right (cup2Idx5 n hn9))).1 = c6.1 := by
      rw [right_cup2Idx5_eq_idx6 n hn9]
      simp [c6, stateAsFin3]
    have h0 : (cup2Idx5 n hn9).1 ≠ 0 := by simp [cup2Idx5]
    have h1 : (cup2Idx5 n hn9).1 ≠ 1 := by simp [cup2Idx5]
    have htop : (cup2Idx5 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx5]
      omega
    have hhigh : (cup2Idx5 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx5]
      omega
    have hout' :
        cup2OutVal n (cup2Idx5 n hn9)
          (c (cup2Idx4 n hn9)).1
          (c (cup2Idx5 n hn9)).1 c6.1 =
            TMidVal (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hdelta :
        (localFcAfter (c (left (cup2Idx5 n hn9))).1
            (c (cup2Idx5 n hn9)).1
            (c (right (cup2Idx5 n hn9))).1
            (cup2OutVal n (cup2Idx5 n hn9)
              (c (left (cup2Idx5 n hn9))).1
              (c (cup2Idx5 n hn9)).1
              (c (right (cup2Idx5 n hn9))).1) : Int) +
          pn011c1two_c2one_sigRank
            (pn011c1two_c2one_sigSuccIdx5 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) c6) ≤
        localFcBefore (c (left (cup2Idx5 n hn9))).1
          (c (cup2Idx5 n hn9)).1
          (c (right (cup2Idx5 n hn9))).1 +
          pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
      rw [hleft, hright]
      calc
        (localFcAfter (c (cup2Idx4 n hn9)).1
            (c (cup2Idx5 n hn9)).1 c6.1
            (cup2OutVal n (cup2Idx5 n hn9)
              (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1) : Int) +
            pn011c1two_c2one_sigRank
              (pn011c1two_c2one_sigSuccIdx5 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) c6) =
          localFcBefore (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1 +
            (localFcDelta (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1
              (cup2OutVal n (cup2Idx5 n hn9)
                (c (cup2Idx4 n hn9)).1
                (c (cup2Idx5 n hn9)).1 c6.1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx5 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) c6)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ = localFcBefore (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1 +
            (localFcDelta (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1
              (TMidVal (c (cup2Idx4 n hn9)).1
                (c (cup2Idx5 n hn9)).1 c6.1) +
              pn011c1two_c2one_sigRank
                (pn011c1two_c2one_sigSuccIdx5 (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) c6)) := by
          rw [hout']
        _ ≤ localFcBefore (c (cup2Idx4 n hn9)).1
              (c (cup2Idx5 n hn9)).1 c6.1 +
            pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (cup2Idx4 n hn9)).1
                (c (cup2Idx5 n hn9)).1 c6.1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2Idx5 n hn9),
      cup2Fc_split n hn4 c (cup2Idx5 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2Idx5 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2Idx5 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem pn011c1two_c2one_step
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hrank : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c)) :
    (c' (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
      (c' (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (c' (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      (c' (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c') ∧
      (cup2Fc n hn4 c' : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c') ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
  rcases hstep.1.2.2 with ⟨i, hpriv, hmove⟩
  subst c'
  have htpMove : cup2TpPreservingMove n hn4 c i := by
    simpa [cup2TpPreservingMove] using hstep.2
  by_cases hfixed :
      cup2BoundaryState n hn4 hn9 (move (cup2System n hn4) c i) =
        cup2BoundaryState n hn4 hn9 c
  · by_cases hi3 : i = cup2Idx3 n hn9
    · subst i
      rcases pn011c1two_c2one_leftFrame_preserved_of_move_off n hn4 hn9 c (cup2Idx3 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN3, cup2Idx3] at hval
            omega)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN2, cup2Idx3] at hval
            omega)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN1, cup2Idx3] at hval
            omega)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2Idx3] at hval)
          hcN3 hcN2 hcN1 hc0 with ⟨hcN3', hcN2', hcN1', hc0'⟩
      rcases pn011c1two_c2one_sig_step_noninc_idx3 n hn4 hn9 c hrank htpMove with ⟨hrank', hle⟩
      exact ⟨hcN3', hcN2', hcN1', hc0', hrank', hle⟩
    · by_cases hi4 : i = cup2Idx4 n hn9
      · subst i
        rcases pn011c1two_c2one_leftFrame_preserved_of_move_off n hn4 hn9 c (cup2Idx4 n hn9)
            (by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN3, cup2Idx4] at hval
              omega)
            (by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN2, cup2Idx4] at hval
              omega)
            (by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN1, cup2Idx4] at hval
              omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdx0, cup2Idx4] at hval)
            hcN3 hcN2 hcN1 hc0 with ⟨hcN3', hcN2', hcN1', hc0'⟩
        rcases pn011c1two_c2one_sig_step_noninc_idx4 n hn4 hn9 c hrank htpMove with ⟨hrank', hle⟩
        exact ⟨hcN3', hcN2', hcN1', hc0', hrank', hle⟩
      · by_cases hi5 : i = cup2Idx5 n hn9
        · subst i
          rcases pn011c1two_c2one_leftFrame_preserved_of_move_off n hn4 hn9 c (cup2Idx5 n hn9)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN3, cup2Idx5] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN2, cup2Idx5] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN1, cup2Idx5] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdx0, cup2Idx5] at hval)
              hcN3 hcN2 hcN1 hc0 with ⟨hcN3', hcN2', hcN1', hc0'⟩
          rcases pn011c1two_c2one_sig_step_noninc_idx5 n hn4 hn9 c hrank htpMove with ⟨hrank', hle⟩
          exact ⟨hcN3', hcN2', hcN1', hc0', hrank', hle⟩
        · have hnotboundary : ¬ (i.1 ≤ 2 ∨ n - 3 ≤ i.1) := by
            intro hboundary
            exact (cup2Boundary6_changed_of_boundary_move n hn4 hn9 c i hpriv hboundary) (by
              have hdecode := congrArg (fun s : SixState => decodeSixBoundary s.1) hfixed
              simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdecode)
          have hiN3 : i ≠ cup2BoundaryIdxN3 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN3] at hval
            exact hnotboundary (Or.inr (by omega))
          have hiN2 : i ≠ cup2BoundaryIdxN2 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN2] at hval
            exact hnotboundary (Or.inr (by omega))
          have hiN1 : i ≠ cup2BoundaryIdxN1 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN1] at hval
            exact hnotboundary (Or.inr (by omega))
          have hi0 : i ≠ cup2BoundaryIdx0 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0] at hval
            exact hnotboundary (Or.inl (by omega))
          have hi1 : i ≠ cup2BoundaryIdx1 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1] at hval
            exact hnotboundary (Or.inl (by omega))
          have hi2 : i ≠ cup2BoundaryIdx2 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2] at hval
            exact hnotboundary (Or.inl (by omega))
          rcases pn011c1two_c2one_leftFrame_preserved_of_move_off n hn4 hn9 c i hiN3 hiN2 hiN1 hi0
              hcN3 hcN2 hcN1 hc0 with ⟨hcN3', hcN2', hcN1', hc0'⟩
          have hsig := pn011c1two_c2one_sig_eq_of_move_off_window n hn4 hn9 c i hi1 hi2 hi3 hi4 hi5
          have hfc_le := pn011c1two_fc_noninc_of_boundary_fixed_tpStep n hn4 hn9 hstep hfixed
          have hfc_le' : (cup2Fc n hn4 (move (cup2System n hn4) c i) : Int) ≤ cup2Fc n hn4 c := by
            exact_mod_cast hfc_le
          have hrank' : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
              (move (cup2System n hn4) c i)) := by
            simpa [hsig] using hrank
          have hle :
              (cup2Fc n hn4 (move (cup2System n hn4) c i) : Int) +
                pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9
                  (move (cup2System n hn4) c i)) ≤
              (cup2Fc n hn4 c : Int) +
                pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
            rw [hsig]
            omega
          exact ⟨hcN3', hcN2', hcN1', hc0', hrank', hle⟩
  · have hbdry : i.1 ≤ 2 ∨ n - 3 ≤ i.1 :=
        cup2BoundaryState_changed_implies_boundary_index n hn4 hn9 c i hfixed
    rcases hbdry with hsmall | hlarge
    · by_cases hi0v : i.1 = 0
      · have hi : i = cup2BoundaryIdx0 n hn9 := by
          apply Fin.ext
          simpa [cup2BoundaryIdx0] using hi0v
        subst i
        exact False.elim ((not_privileged_idx0_of_cN1_zero_c0_one n hn4 hn9 c hcN1 hc0) hpriv)
      · by_cases hi1v : i.1 = 1
        · have hi : i = cup2BoundaryIdx1 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx1] using hi1v
          subst i
          rcases pn011c1two_c2one_leftFrame_preserved_of_move_off n hn4 hn9 c (cup2BoundaryIdx1 n hn9)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN3, cup2BoundaryIdx1] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval)
              hcN3 hcN2 hcN1 hc0 with ⟨hcN3', hcN2', hcN1', hc0'⟩
          rcases pn011c1two_c2one_sig_step_noninc_idx1 n hn4 hn9 c hc0 hrank htpMove with ⟨hrank', hle⟩
          exact ⟨hcN3', hcN2', hcN1', hc0', hrank', hle⟩
        · have hi2v : i.1 = 2 := by omega
          have hi : i = cup2BoundaryIdx2 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx2] using hi2v
          subst i
          rcases pn011c1two_c2one_leftFrame_preserved_of_move_off n hn4 hn9 c (cup2BoundaryIdx2 n hn9)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN3, cup2BoundaryIdx2] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN2, cup2BoundaryIdx2] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdxN1, cup2BoundaryIdx2] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval)
              hcN3 hcN2 hcN1 hc0 with ⟨hcN3', hcN2', hcN1', hc0'⟩
          rcases pn011c1two_c2one_sig_step_noninc_idx2 n hn4 hn9 c hrank htpMove with ⟨hrank', hle⟩
          exact ⟨hcN3', hcN2', hcN1', hc0', hrank', hle⟩
    · by_cases hiN1v : i.1 + 1 = n
      · have hi : i = cup2BoundaryIdxN1 n hn9 := by
          have hi_val : i.1 = n - 1 := by omega
          apply Fin.ext
          simp [cup2BoundaryIdxN1, hi_val]
        subst i
        exact False.elim ((not_privileged_idxN1_of_cN2_zero_cN1_zero_c0_one n hn4 hn9 c hcN2 hcN1 hc0) hpriv)
      · by_cases hiN2v : i.1 + 2 = n
        · have hi : i = cup2BoundaryIdxN2 n hn9 := by
            have hi_val : i.1 = n - 2 := by omega
            apply Fin.ext
            simp [cup2BoundaryIdxN2, hi_val]
          subst i
          exact False.elim ((not_privileged_idxN2_of_cN3_two_cN2_zero_cN1_zero n hn4 hn9 c hcN3 hcN2 hcN1) hpriv)
        · have hi : i = cup2BoundaryIdxN3 n hn9 := by
            have hi_lt : i.1 < n := i.2
            have hi_val : i.1 = n - 3 := by omega
            apply Fin.ext
            simp [cup2BoundaryIdxN3, hi_val]
          subst i
          exact False.elim ((not_privileged_idxN3_of_cN3_two_cN2_zero n hn4 hn9 c hcN3 hcN2 htpMove) hpriv)

def pn011c1two_c2one_activeWindow
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Prop :=
  (c (cup2Idx3 n hn9)).1 = 1 ∨
    ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
    ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
      (c (cup2Idx5 n hn9)).1 = 2)

private theorem pn011c1two_c2one_tpReachable_bound
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    (d (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
      (d (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (d (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      (d (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 d) ∧
      (cup2Fc n hn4 d : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 d) ≤
        (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
  have hrank0 : 0 ≤ pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := by
    rw [pn011c1two_c2one_start_rank_of_config n hn4 hn9 c hc1 hc2]
    by_cases hactive : pn011c1two_c2one_activeWindow n hn4 hn9 c
    · have hactive' :
          (c (cup2Idx3 n hn9)).1 = 1 ∨
            ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
            ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
              (c (cup2Idx5 n hn9)).1 = 2) := by
        simpa [pn011c1two_c2one_activeWindow] using hactive
      simp [hactive']
    · have hpassive' :
          ¬ ((c (cup2Idx3 n hn9)).1 = 1 ∨
              ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
              ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
                (c (cup2Idx5 n hn9)).1 = 2)) := by
        simpa [pn011c1two_c2one_activeWindow] using hactive
      simp [hpassive']
  induction hreach with
  | refl =>
      exact ⟨hcN3, hcN2, hcN1, hc0, hrank0, by omega⟩
  | tail _ hstep ih =>
      rcases ih with ⟨hN3, hN2, hN1, h0, hrank, hle⟩
      rcases pn011c1two_c2one_step n hn4 hn9 hstep hN3 hN2 hN1 h0 hrank with
        ⟨hN3', hN2', hN1', h0', hrank', hle'⟩
      exact ⟨hN3', hN2', hN1', h0', hrank', le_trans hle' hle⟩

theorem pn1_011_c1_two_c2_one_tpReachable_fc_le_active
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hactive : pn011c1two_c2one_activeWindow n hn4 hn9 c)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤ cup2Fc n hn4 c + 1 := by
  have hbound := pn011c1two_c2one_tpReachable_bound n hn4 hn9 c hcN3 hcN2 hcN1 hc0 hc1 hc2 hreach
  rcases hbound with ⟨_, _, _, _, _hrankd, hlebound⟩
  have hrankc : pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) = 1 := by
    have hactive' :
        (c (cup2Idx3 n hn9)).1 = 1 ∨
          ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
          ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
            (c (cup2Idx5 n hn9)).1 = 2) := by
      simpa [pn011c1two_c2one_activeWindow] using hactive
    rw [pn011c1two_c2one_start_rank_of_config n hn4 hn9 c hc1 hc2]
    simp [hactive']
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c + 1 := by
    calc
      (cup2Fc n hn4 d : Int) ≤
          (cup2Fc n hn4 d : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 d) := by
        omega
      _ ≤ (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := hlebound
      _ = cup2Fc n hn4 c + 1 := by simpa [hrankc]
  exact Int.ofNat_le.mp hfc_le'

theorem pn1_011_c1_two_c2_one_tpReachable_fc_le_passive
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hpassive : ¬ pn011c1two_c2one_activeWindow n hn4 hn9 c)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤ cup2Fc n hn4 c := by
  have hbound := pn011c1two_c2one_tpReachable_bound n hn4 hn9 c hcN3 hcN2 hcN1 hc0 hc1 hc2 hreach
  rcases hbound with ⟨_, _, _, _, _hrankd, hlebound⟩
  have hrankc : pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) = 0 := by
    have hpassive' :
        ¬ ((c (cup2Idx3 n hn9)).1 = 1 ∨
            ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
            ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
              (c (cup2Idx5 n hn9)).1 = 2)) := by
      simpa [pn011c1two_c2one_activeWindow] using hpassive
    rw [pn011c1two_c2one_start_rank_of_config n hn4 hn9 c hc1 hc2]
    simp [hpassive']
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c := by
    calc
      (cup2Fc n hn4 d : Int) ≤
          (cup2Fc n hn4 d : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 d) := by
        omega
      _ ≤ (cup2Fc n hn4 c : Int) + pn011c1two_c2one_sigRank (pn011c1two_c2one_sigOfConfig n hn4 hn9 c) := hlebound
      _ = cup2Fc n hn4 c := by simpa [hrankc]
  exact Int.ofNat_le.mp hfc_le'

theorem pn1_011_c1_two_scratch_smoke : True := by
  have _ := pn011c1two_sigIdx
  have _ := pn011c1two_c2one_reachableVals.length
  have _ := pn011c1two_c2one_rankOneVals.length
  trivial

end LeanMn
