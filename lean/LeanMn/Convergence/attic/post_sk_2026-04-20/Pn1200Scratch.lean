import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SyntheticPotential
import LeanMn.Convergence.SixTuple

namespace LeanMn

private def up2' (x : Fin 2) : Fin 3 :=
  ⟨x.1, by omega⟩

private structure Pn1200Sig where
  cN2 : Fin 3
  cN1 : Fin 2
  c0 : Fin 2
  c1 : Fin 3
  c2 : Fin 3
deriving DecidableEq, Fintype, Repr

@[ext] private theorem Pn1200Sig.ext {s t : Pn1200Sig}
    (hN2 : s.cN2 = t.cN2) (hN1 : s.cN1 = t.cN1)
    (h0 : s.c0 = t.c0) (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2) :
    s = t := by
  cases s
  cases t
  cases hN2
  cases hN1
  cases h0
  cases h1
  cases h2
  rfl

private def pn1_200_sigOfBoundary (s : SixBoundary) : Pn1200Sig :=
  { cN2 := s.cN2, cN1 := s.cN1, c0 := s.c0, c1 := s.c1, c2 := s.c2 }

private def pn1_200_sigOfConfig
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Pn1200Sig :=
  pn1_200_sigOfBoundary (cup2Boundary6 n hn4 hn9 c)

private theorem pn1_200_sigOfConfig_eq_boundary
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    pn1_200_sigOfConfig n hn4 hn9 c =
      pn1_200_sigOfBoundary (cup2Boundary6 n hn4 hn9 c) := by
  rfl

private theorem pn1_200_sigOfConfig_eq_of_boundaryState_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hbdry : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c) :
    pn1_200_sigOfConfig n hn4 hn9 c' = pn1_200_sigOfConfig n hn4 hn9 c := by
  have hdecode := congrArg (fun s : SixState => decodeSixBoundary s.1) hbdry
  have hb6 : cup2Boundary6 n hn4 hn9 c' = cup2Boundary6 n hn4 hn9 c := by
    simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdecode
  simpa [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c',
    pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c] using congrArg pn1_200_sigOfBoundary hb6

private def pn1_200_sigSuccP0 (s : Pn1200Sig) : Pn1200Sig :=
  { s with c0 := ⟨TBotVal s.cN1.1 s.c0.1 s.c1.1,
      TBotVal_lt s.cN1.2 s.c0.2 s.c1.2⟩ }

private def pn1_200_sigSuccP1 (s : Pn1200Sig) : Pn1200Sig :=
  { s with c1 := ⟨TLowVal s.c0.1 s.c1.1 s.c2.1,
      TLowVal_lt s.c0.2 s.c1.2 s.c2.2⟩ }

private def pn1_200_sigSuccP2 (s : Pn1200Sig) (c3 : Fin 3) : Pn1200Sig :=
  { s with c2 := ⟨TMidVal s.c1.1 s.c2.1 c3.1, TMidVal_lt s.c1.2 s.c2.2 c3.2⟩ }

private def pn1_200_sigSuccPN2 (s : Pn1200Sig) (cN3 : Fin 3) : Pn1200Sig :=
  { s with cN2 := ⟨THighVal cN3.1 s.cN2.1 s.cN1.1,
      THighVal_lt cN3.2 s.cN2.2 s.cN1.2⟩ }

private def pn1_200_sigSuccPN1 (s : Pn1200Sig) : Pn1200Sig :=
  { s with cN1 := ⟨TTopVal s.cN2.1 s.cN1.1 s.c0.1,
      TTopVal_lt s.cN2.2 s.cN1.2 s.c0.2⟩ }

private def pn1_200_sigRankVals : List Int :=
  [
    3, 2, 3, -1, -1, -1, -1, -1, 3, 1, 0, 1, 1, 1, 1, -1, -1, 1,
    1, 0, 1, -1, -1, -1, -1, -1, 1, 2, 1, 2, 2, 2, 2, -1, -1, 2,
    3, 2, 3, -1, -1, -1, -1, -1, 3, 1, 0, 1, 1, 1, 1, -1, -1, 1,
    2, 2, 2, -1, -1, -1, -1, -1, 2, 3, 2, 3, 3, 3, 3, -1, -1, 3,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    0, 0, 0, -1, -1, -1, -1, -1, 0, 1, 0, 1, 1, 1, 1, -1, -1, 1
  ]

private def pn1_200_sigRank (s : Pn1200Sig) : Int :=
  match pn1_200_sigRankVals[s.cN2.1 * 36 + s.cN1.1 * 18 + s.c0.1 * 9 + s.c1.1 * 3 + s.c2.1]? with
  | some r => r
  | none => -1

private abbrev p2TpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R = 1 then 1 else 0) = (if S = 2 ∧ R = 1 then 1 else 0)

private abbrev pn2TpLocal (L S R : Nat) : Prop :=
  let out := THighVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if L = 2 ∧ out = 1 then 1 else 0) = (if L = 2 ∧ S = 1 then 1 else 0)

private theorem pn1_200_sig_step_P0 (s : Pn1200Sig)
    (hrank : 0 ≤ pn1_200_sigRank s) :
    0 ≤ pn1_200_sigRank (pn1_200_sigSuccP0 s) ∧
      localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
        pn1_200_sigRank (pn1_200_sigSuccP0 s) ≤
      pn1_200_sigRank s := by
  have h :
      ∀ s : Pn1200Sig,
        0 ≤ pn1_200_sigRank s →
          0 ≤ pn1_200_sigRank (pn1_200_sigSuccP0 s) ∧
            localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
              pn1_200_sigRank (pn1_200_sigSuccP0 s) ≤
            pn1_200_sigRank s := by
    native_decide
  exact h s hrank

private theorem pn1_200_sig_step_P1 (s : Pn1200Sig)
    (hrank : 0 ≤ pn1_200_sigRank s) :
    0 ≤ pn1_200_sigRank (pn1_200_sigSuccP1 s) ∧
      localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
        pn1_200_sigRank (pn1_200_sigSuccP1 s) ≤
      pn1_200_sigRank s := by
  have h :
      ∀ s : Pn1200Sig,
        0 ≤ pn1_200_sigRank s →
          0 ≤ pn1_200_sigRank (pn1_200_sigSuccP1 s) ∧
            localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
              pn1_200_sigRank (pn1_200_sigSuccP1 s) ≤
            pn1_200_sigRank s := by
    native_decide
  exact h s hrank

private theorem pn1_200_sig_step_P2 (s : Pn1200Sig) (c3 : Fin 3)
    (hrank : 0 ≤ pn1_200_sigRank s)
    (htp : p2TpLocal s.c1.1 s.c2.1 c3.1) :
    0 ≤ pn1_200_sigRank (pn1_200_sigSuccP2 s c3) ∧
      localFcDelta s.c1.1 s.c2.1 c3.1 (TMidVal s.c1.1 s.c2.1 c3.1) +
        pn1_200_sigRank (pn1_200_sigSuccP2 s c3) ≤
      pn1_200_sigRank s := by
  have h :
      ∀ (s : Pn1200Sig) (c3 : Fin 3),
        0 ≤ pn1_200_sigRank s →
          p2TpLocal s.c1.1 s.c2.1 c3.1 →
            0 ≤ pn1_200_sigRank (pn1_200_sigSuccP2 s c3) ∧
              localFcDelta s.c1.1 s.c2.1 c3.1 (TMidVal s.c1.1 s.c2.1 c3.1) +
                pn1_200_sigRank (pn1_200_sigSuccP2 s c3) ≤
              pn1_200_sigRank s := by
    native_decide
  exact h s c3 hrank htp

private theorem pn1_200_sig_step_PN2 (s : Pn1200Sig) (cN3 : Fin 3)
    (hrank : 0 ≤ pn1_200_sigRank s)
    (htp : pn2TpLocal cN3.1 s.cN2.1 s.cN1.1) :
    0 ≤ pn1_200_sigRank (pn1_200_sigSuccPN2 s cN3) ∧
      localFcDelta cN3.1 s.cN2.1 s.cN1.1 (THighVal cN3.1 s.cN2.1 s.cN1.1) +
        pn1_200_sigRank (pn1_200_sigSuccPN2 s cN3) ≤
      pn1_200_sigRank s := by
  have h :
      ∀ (s : Pn1200Sig) (cN3 : Fin 3),
        0 ≤ pn1_200_sigRank s →
          pn2TpLocal cN3.1 s.cN2.1 s.cN1.1 →
            0 ≤ pn1_200_sigRank (pn1_200_sigSuccPN2 s cN3) ∧
              localFcDelta cN3.1 s.cN2.1 s.cN1.1 (THighVal cN3.1 s.cN2.1 s.cN1.1) +
                pn1_200_sigRank (pn1_200_sigSuccPN2 s cN3) ≤
              pn1_200_sigRank s := by
    native_decide
  exact h s cN3 hrank htp

private theorem pn1_200_sig_step_PN1 (s : Pn1200Sig)
    (hrank : 0 ≤ pn1_200_sigRank s) :
    0 ≤ pn1_200_sigRank (pn1_200_sigSuccPN1 s) ∧
      localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
        pn1_200_sigRank (pn1_200_sigSuccPN1 s) ≤
      pn1_200_sigRank s := by
  have h :
      ∀ s : Pn1200Sig,
        0 ≤ pn1_200_sigRank s →
          0 ≤ pn1_200_sigRank (pn1_200_sigSuccPN1 s) ∧
            localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
              pn1_200_sigRank (pn1_200_sigSuccPN1 s) ≤
            pn1_200_sigRank s := by
    native_decide
  exact h s hrank

private theorem pn1_200_sig_c1_two_implies_c2_two (s : Pn1200Sig)
    (hrank : 0 ≤ pn1_200_sigRank s)
    (hc1 : s.c1.1 = 2) :
    s.c2.1 = 2 := by
  have h :
      ∀ s : Pn1200Sig, 0 ≤ pn1_200_sigRank s → s.c1.1 = 2 → s.c2.1 = 2 := by
    native_decide
  exact h s hrank hc1

private theorem pn1_200_sig_start_rank_zero (c2 : Fin 3) :
    pn1_200_sigRank
      { cN2 := (⟨2, by decide⟩ : Fin 3)
        cN1 := (⟨1, by decide⟩ : Fin 2)
        c0 := (⟨0, by decide⟩ : Fin 2)
        c1 := (⟨0, by decide⟩ : Fin 3)
        c2 := c2 } = 0 := by
  fin_cases c2 <;> native_decide

private theorem pn1_200_sig_start_rank_zero_c1_two :
    pn1_200_sigRank
      { cN2 := (⟨2, by decide⟩ : Fin 3)
        cN1 := (⟨1, by decide⟩ : Fin 2)
        c0 := (⟨0, by decide⟩ : Fin 2)
        c1 := (⟨2, by decide⟩ : Fin 3)
        c2 := (⟨2, by decide⟩ : Fin 3) } = 0 := by
  native_decide

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

private theorem pn1_200_fc_noninc_of_boundary_fixed_tpStep
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

private theorem pn1_200_sig_step_noninc_of_boundary_fixed
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c)
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c') ∧
      (cup2Fc n hn4 c' : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c') ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  have hsig : pn1_200_sigOfConfig n hn4 hn9 c' = pn1_200_sigOfConfig n hn4 hn9 c :=
    pn1_200_sigOfConfig_eq_of_boundaryState_eq n hn4 hn9 hfixed
  constructor
  · simpa [hsig] using hrank
  · have hfc_le := pn1_200_fc_noninc_of_boundary_fixed_tpStep n hn4 hn9 hstep hfixed
    have hfc_le' : (cup2Fc n hn4 c' : Int) ≤ cup2Fc n hn4 c := by
      exact_mod_cast hfc_le
    rw [hsig]
    omega

private theorem pn1_200_sig_boundarySuccP0 (s : SixBoundary) :
    pn1_200_sigOfBoundary (boundarySuccP0 s) =
      pn1_200_sigSuccP0 (pn1_200_sigOfBoundary s) := by
  ext <;> rfl

private theorem pn1_200_sig_boundarySuccP1 (s : SixBoundary) :
    pn1_200_sigOfBoundary (boundarySuccP1 s) =
      pn1_200_sigSuccP1 (pn1_200_sigOfBoundary s) := by
  ext <;> rfl

private theorem pn1_200_sig_boundarySuccP2 (s : SixBoundary) (c3 : Fin 3) :
    pn1_200_sigOfBoundary (boundarySuccP2 s c3) =
      pn1_200_sigSuccP2 (pn1_200_sigOfBoundary s) c3 := by
  ext <;> rfl

private theorem pn1_200_sig_boundarySuccPN2 (s : SixBoundary) :
    pn1_200_sigOfBoundary (boundarySuccPN2 s) =
      pn1_200_sigSuccPN2 (pn1_200_sigOfBoundary s) s.cN3 := by
  ext <;> rfl

private theorem pn1_200_sig_boundarySuccPN1 (s : SixBoundary) :
    pn1_200_sigOfBoundary (boundarySuccPN1 s) =
      pn1_200_sigSuccPN1 (pn1_200_sigOfBoundary s) := by
  ext <;> rfl

private theorem pn1_200_sig_boundarySuccPN3 (s : SixBoundary) (cn4 : Fin 3) :
    pn1_200_sigOfBoundary (boundarySuccPN3 s cn4) =
      pn1_200_sigOfBoundary s := by
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

private theorem pn1_200_sig_step_noninc_idx0
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) : Int) +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn1_200_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        pn1_200_sigSuccP0 (pn1_200_sigOfConfig n hn4 hn9 c) := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)),
      pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn1_200_sigSuccP0] using
      congrArg pn1_200_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccP0 n hn4 hn9 c)
  have hlocal := pn1_200_sig_step_P0 (pn1_200_sigOfConfig n hn4 hn9 c) hrank
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
          pn1_200_sigRank (pn1_200_sigSuccP0 (pn1_200_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
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
              pn1_200_sigRank (pn1_200_sigSuccP0 (pn1_200_sigOfConfig n hn4 hn9 c)) ≤
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
        simpa [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c, pn1_200_sigOfBoundary, hleft, hright] using h
      calc
        (localFcAfter (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx0 n hn9)
              (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1) : Int) +
            pn1_200_sigRank (pn1_200_sigSuccP0 (pn1_200_sigOfConfig n hn4 hn9 c)) =
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
              pn1_200_sigRank (pn1_200_sigSuccP0 (pn1_200_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1 +
            pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
                (c (cup2BoundaryIdx0 n hn9)).1
                (c (right (cup2BoundaryIdx0 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdx0 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn1_200_sig_step_noninc_idx1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) : Int) +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn1_200_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        pn1_200_sigSuccP1 (pn1_200_sigOfConfig n hn4 hn9 c) := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)),
      pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn1_200_sigSuccP1] using
      congrArg pn1_200_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccP1 n hn4 hn9 c)
  have hlocal := pn1_200_sig_step_P1 (pn1_200_sigOfConfig n hn4 hn9 c) hrank
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
          pn1_200_sigRank (pn1_200_sigSuccP1 (pn1_200_sigOfConfig n hn4 hn9 c)) ≤
        pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      simpa [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c, pn1_200_sigOfBoundary, hleft, hright] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
          pn1_200_sigRank (pn1_200_sigSuccP1 (pn1_200_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
            pn1_200_sigRank (pn1_200_sigSuccP1 (pn1_200_sigOfConfig n hn4 hn9 c)) =
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
              pn1_200_sigRank (pn1_200_sigSuccP1 (pn1_200_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1 +
            pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
                (c (cup2BoundaryIdx1 n hn9)).1
                (c (right (cup2BoundaryIdx1 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdx1 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn1_200_sig_step_noninc_idxN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN1 n hn9)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) : Int) +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn1_200_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        pn1_200_sigSuccPN1 (pn1_200_sigOfConfig n hn4 hn9 c) := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)),
      pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn1_200_sigSuccPN1] using
      congrArg pn1_200_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c)
  have hlocal := pn1_200_sig_step_PN1 (pn1_200_sigOfConfig n hn4 hn9 c) hrank
  constructor
  · simpa [hsig] using hlocal.1
  · have h :=
        hlocal.2
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
          pn1_200_sigRank (pn1_200_sigSuccPN1 (pn1_200_sigOfConfig n hn4 hn9 c)) ≤
        pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      simpa [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c, pn1_200_sigOfBoundary, hleft, hright] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
          pn1_200_sigRank (pn1_200_sigSuccPN1 (pn1_200_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
            pn1_200_sigRank (pn1_200_sigSuccPN1 (pn1_200_sigOfConfig n hn4 hn9 c)) =
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
              pn1_200_sigRank (pn1_200_sigSuccPN1 (pn1_200_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1 +
            pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
                (c (cup2BoundaryIdxN1 n hn9)).1
                (c (right (cup2BoundaryIdxN1 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdxN1 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn1_200_sig_step_noninc_idx2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) : Int) +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
  have hsig :
      pn1_200_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        pn1_200_sigSuccP2 (pn1_200_sigOfConfig n hn4 hn9 c) c3 := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)),
      pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn1_200_sigSuccP2, c3] using
      congrArg pn1_200_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccP2 n hn4 hn9 c)
  have hlocal := pn1_200_sig_step_P2 (pn1_200_sigOfConfig n hn4 hn9 c) c3 hrank
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
              pn1_200_sigRank (pn1_200_sigSuccP2 (pn1_200_sigOfConfig n hn4 hn9 c) c3) ≤
        pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      simpa [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c, pn1_200_sigOfBoundary,
        c3, hleft] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
          pn1_200_sigRank (pn1_200_sigSuccP2 (pn1_200_sigOfConfig n hn4 hn9 c) c3) ≤
        localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
            pn1_200_sigRank (pn1_200_sigSuccP2 (pn1_200_sigOfConfig n hn4 hn9 c) c3) =
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
              pn1_200_sigRank (pn1_200_sigSuccP2 (pn1_200_sigOfConfig n hn4 hn9 c) c3)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1 +
            pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h' (localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
                (c (cup2BoundaryIdx2 n hn9)).1
                (c (right (cup2BoundaryIdx2 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdx2 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn1_200_sig_step_noninc_idxN2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN2 n hn9)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) : Int) +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  let s := cup2Boundary6 n hn4 hn9 c
  have hsig :
      pn1_200_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
        pn1_200_sigSuccPN2 (pn1_200_sigOfConfig n hn4 hn9 c) s.cN3 := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)),
      pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa [pn1_200_sigSuccPN2, s] using
      congrArg pn1_200_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccPN2 n hn4 hn9 c)
  have hlocal := pn1_200_sig_step_PN2 (pn1_200_sigOfConfig n hn4 hn9 c) s.cN3 hrank
    (by simpa [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c, pn1_200_sigOfBoundary, s]
      using pn2TpLocal_of_tpPreserving n hn4 hn9 c htp)
  constructor
  · simpa [hsig] using hlocal.1
  · have h :=
        hlocal.2
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
          pn1_200_sigRank (pn1_200_sigSuccPN2 (pn1_200_sigOfConfig n hn4 hn9 c) s.cN3) ≤
        pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      simpa [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c, pn1_200_sigOfBoundary, s, hleft, hright] using h
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
          pn1_200_sigRank (pn1_200_sigSuccPN2 (pn1_200_sigOfConfig n hn4 hn9 c) s.cN3) ≤
        localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
            pn1_200_sigRank (pn1_200_sigSuccPN2 (pn1_200_sigOfConfig n hn4 hn9 c) s.cN3) =
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
              pn1_200_sigRank (pn1_200_sigSuccPN2 (pn1_200_sigOfConfig n hn4 hn9 c) s.cN3)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1 +
            pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
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

private theorem pn1_200_sig_step_noninc_idxN3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9))
    (hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) : Int) +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      pn1_200_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
        pn1_200_sigOfConfig n hn4 hn9 c := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)),
      pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c]
    simpa using
      congrArg pn1_200_sigOfBoundary (cup2Boundary6_move_eq_boundarySuccPN3_aux n hn4 hn9 c)
  have h3 : 3 ≤ (cup2BoundaryIdxN3 n hn9).1 := by
    simp [cup2BoundaryIdxN3]
    omega
  have htop : (cup2BoundaryIdxN3 n hn9).1 + 2 < n := by
    simp [cup2BoundaryIdxN3]
    omega
  have hcopy :
      cup2OutVal n (cup2BoundaryIdxN3 n hn9)
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (right (cup2BoundaryIdxN3 n hn9))).1 =
          (c (left (cup2BoundaryIdxN3 n hn9))).1 ∨
        cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 =
            (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
    exact cup2TpPreserving_mid_copyNeighbor_val n hn4 c (cup2BoundaryIdxN3 n hn9) h3 htop htp hpriv
  constructor
  · simpa [hsig] using hrank
  · rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN3 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN3 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN3 n hn9)]
    have hlocal :=
      localFcAfter_le_of_copyNeighbor
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (right (cup2BoundaryIdxN3 n hn9))).1
        (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1) hcopy
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
              (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1) : Int) +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) ≤
        localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 +
          pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
      have hlocal' : (localFcAfter (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1
          (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
            (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1) : Int) ≤
        localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
        exact_mod_cast hlocal
      omega
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta (Finset.sum (adjacentComplement (cup2BoundaryIdxN3 n hn9)) (cup2FrontierBit n hn4 c) : Nat)

private theorem pn1_200_sig_step_noninc
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hrank : 0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c)) :
    0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c') ∧
      (cup2Fc n hn4 c' : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c') ≤
        (cup2Fc n hn4 c : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) := by
  by_cases hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c
  · exact pn1_200_sig_step_noninc_of_boundary_fixed n hn4 hn9 hstep hfixed hrank
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
        exact pn1_200_sig_step_noninc_idx0 n hn4 hn9 c hrank htpMove
      · by_cases hi1 : i.1 = 1
        · have hi : i = cup2BoundaryIdx1 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx1] using hi1
          subst i
          exact pn1_200_sig_step_noninc_idx1 n hn4 hn9 c hrank htpMove
        · have hi2 : i.1 = 2 := by omega
          have hi : i = cup2BoundaryIdx2 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx2] using hi2
          subst i
          exact pn1_200_sig_step_noninc_idx2 n hn4 hn9 c hrank htpMove
    · by_cases hiN1 : i.1 + 1 = n
      · have hi : i = cup2BoundaryIdxN1 n hn9 := by
          have hi_val : i.1 = n - 1 := by omega
          apply Fin.ext
          simp [cup2BoundaryIdxN1, hi_val]
        subst i
        exact pn1_200_sig_step_noninc_idxN1 n hn4 hn9 c hrank htpMove
      · by_cases hiN2 : i.1 + 2 = n
        · have hi : i = cup2BoundaryIdxN2 n hn9 := by
            have hi_val : i.1 = n - 2 := by omega
            apply Fin.ext
            simp [cup2BoundaryIdxN2, hi_val]
          subst i
          exact pn1_200_sig_step_noninc_idxN2 n hn4 hn9 c hrank htpMove
        · have hi_lt : i.1 < n := i.2
          have hiN3 : i.1 = n - 3 := by omega
          have hi : i = cup2BoundaryIdxN3 n hn9 := by
            apply Fin.ext
            simp [cup2BoundaryIdxN3, hiN3]
          subst i
          exact pn1_200_sig_step_noninc_idxN3 n hn4 hn9 c hrank htpMove hpriv

theorem pn1_200_c1_zero_tpReachable_fc_le_core
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) d) :
    cup2Fc n hn4 d ≤
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
  let c' := move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
  have hsig0 : pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c') = 0 := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c',
      show c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) by rfl,
      cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c]
    let s := cup2Boundary6 n hn4 hn9 c
    rw [pn1_200_sig_boundarySuccPN1 s]
    have hsN2 : s.cN2 = (⟨2, by decide⟩ : Fin 3) := by
      apply Fin.ext
      exact hcN2
    have hsN1 : s.cN1 = (⟨0, by decide⟩ : Fin 2) := by
      apply Fin.ext
      exact hcN1
    have hs0 : s.c0 = (⟨0, by decide⟩ : Fin 2) := by
      apply Fin.ext
      exact hc0
    have hs1 : s.c1 = (⟨0, by decide⟩ : Fin 3) := by
      apply Fin.ext
      exact hc1
    simpa [pn1_200_sigOfBoundary, pn1_200_sigSuccPN1, s, hsN2, hsN1, hs0, hs1] using
      pn1_200_sig_start_rank_zero s.c2
  have hstrong :
      ∀ {x : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c' x →
          0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 x) ∧
            (cup2Fc n hn4 x : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 x) ≤
              (cup2Fc n hn4 c' : Int) := by
    intro x hreach'
    induction hreach' with
    | refl =>
      exact ⟨by simpa [hsig0], by simpa [hsig0]⟩
    | tail _ hstep ih =>
      rcases pn1_200_sig_step_noninc n hn4 hn9 hstep ih.1 with ⟨hrank', hstep'⟩
      exact ⟨hrank', le_trans hstep' ih.2⟩
  have hbound := hstrong hreach
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c' := by
    omega
  exact Int.ofNat_le.mp hfc_le'

theorem pn1_200_c1_two_tpReachable_fc_le_core
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤ cup2Fc n hn4 c := by
  have hsig0 : pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 c) = 0 := by
    rw [pn1_200_sigOfConfig_eq_boundary n hn4 hn9 c]
    let s := cup2Boundary6 n hn4 hn9 c
    have hsN2 : s.cN2 = (⟨2, by decide⟩ : Fin 3) := by
      apply Fin.ext
      exact hcN2
    have hsN1 : s.cN1 = (⟨1, by decide⟩ : Fin 2) := by
      apply Fin.ext
      exact hcN1
    have hs0 : s.c0 = (⟨0, by decide⟩ : Fin 2) := by
      apply Fin.ext
      exact hc0
    have hs1 : s.c1 = (⟨2, by decide⟩ : Fin 3) := by
      apply Fin.ext
      exact hc1
    have hs2 : s.c2 = (⟨2, by decide⟩ : Fin 3) := by
      apply Fin.ext
      exact hc2
    simpa [pn1_200_sigOfBoundary, s, hsN2, hsN1, hs0, hs1, hs2] using
      pn1_200_sig_start_rank_zero_c1_two
  have hstrong :
      ∀ {x : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c x →
          0 ≤ pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 x) ∧
            (cup2Fc n hn4 x : Int) + pn1_200_sigRank (pn1_200_sigOfConfig n hn4 hn9 x) ≤
              (cup2Fc n hn4 c : Int) := by
    intro x hreach'
    induction hreach' with
    | refl =>
      exact ⟨by simpa [hsig0], by simpa [hsig0]⟩
    | tail _ hstep ih =>
      rcases pn1_200_sig_step_noninc n hn4 hn9 hstep ih.1 with ⟨hrank', hstep'⟩
      exact ⟨hrank', le_trans hstep' ih.2⟩
  have hbound := hstrong hreach
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c := by
    omega
  exact Int.ofNat_le.mp hfc_le'

private lemma cup2Boundary6_move_eq_boundarySuccPN3
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

theorem pn1_200_scratch_smoke : True := by
  have _ := pn1_200_sigRankVals.length
  trivial

end LeanMn
