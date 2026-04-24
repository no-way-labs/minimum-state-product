import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SyntheticPotential
import LeanMn.Convergence.SixTuple

namespace LeanMn

private structure P012SourceSig where
  c0 : Fin 2
  c1 : Fin 3
  c2 : Fin 3
  c3 : Fin 3
  c4 : Fin 3
  cN2 : Fin 3
  cN1 : Fin 2
deriving DecidableEq, Repr

@[ext] private theorem P012SourceSig.ext {s t : P012SourceSig}
    (h0 : s.c0 = t.c0) (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2)
    (h3 : s.c3 = t.c3) (h4 : s.c4 = t.c4)
    (hN2 : s.cN2 = t.cN2) (hN1 : s.cN1 = t.cN1) :
    s = t := by
  cases s
  cases t
  cases h0
  cases h1
  cases h2
  cases h3
  cases h4
  cases hN2
  cases hN1
  rfl

private abbrev P012SourceSigTuple :=
  Fin 2 × (Fin 3 × (Fin 3 × (Fin 3 × (Fin 3 × (Fin 3 × Fin 2)))))

private def p012sourceSigToTuple (s : P012SourceSig) : P012SourceSigTuple :=
  ⟨s.c0, ⟨s.c1, ⟨s.c2, ⟨s.c3, ⟨s.c4, ⟨s.cN2, s.cN1⟩⟩⟩⟩⟩⟩

private def p012sourceSigOfTuple : P012SourceSigTuple → P012SourceSig
  | ⟨c0, ⟨c1, ⟨c2, ⟨c3, ⟨c4, ⟨cN2, cN1⟩⟩⟩⟩⟩⟩ =>
      { c0 := c0, c1 := c1, c2 := c2, c3 := c3, c4 := c4, cN2 := cN2, cN1 := cN1 }

private theorem p012sourceSig_left_inv : Function.LeftInverse p012sourceSigToTuple p012sourceSigOfTuple := by
  intro t
  rcases t with ⟨c0, ⟨c1, ⟨c2, ⟨c3, ⟨c4, ⟨cN2, cN1⟩⟩⟩⟩⟩⟩
  rfl

private theorem p012sourceSig_right_inv : Function.RightInverse p012sourceSigToTuple p012sourceSigOfTuple := by
  intro s
  cases s
  rfl

private instance : Fintype P012SourceSig :=
  Fintype.ofEquiv P012SourceSigTuple
    { toFun := p012sourceSigOfTuple
      invFun := p012sourceSigToTuple
      left_inv := p012sourceSig_left_inv
      right_inv := p012sourceSig_right_inv }

private def p012source_sigIdx (s : P012SourceSig) : Nat :=
  ((((((s.c0.1 * 3 + s.c1.1) * 3 + s.c2.1) * 3 + s.c3.1) * 3 + s.c4.1) * 3 + s.cN2.1) * 2 + s.cN1.1)

private def p012source_rankZeroVals : List Nat :=
  [
    1, 3, 13, 15, 37, 39, 43, 45, 49, 51, 109, 111, 115, 117, 121, 123, 127, 129, 133, 135,
    139, 141, 145, 147, 151, 153, 157, 159, 271, 273, 277, 279, 283, 285, 289, 291, 295, 297, 301, 303,
    307, 309, 313, 315, 319, 321, 324, 325, 326, 327, 330, 331, 332, 333, 336, 337, 338, 339, 433, 435,
    439, 441, 445, 447, 451, 453, 457, 459, 463, 465, 469, 471, 475, 477, 481, 483, 486, 488, 498, 500,
    522, 524, 525, 528, 530, 531, 534, 536, 594, 596, 597, 600, 602, 603, 606, 608, 609, 612, 614, 615,
    618, 620, 621, 624, 626, 627, 630, 632, 633, 636, 638, 639, 642, 644, 648, 650, 660, 662, 684, 686,
    687, 690, 692, 693, 696, 698, 702, 704, 714, 716, 720, 722, 726, 728, 732, 734, 738, 740, 744, 746,
    750, 752, 756, 758, 762, 764, 768, 770, 774, 776, 780, 782, 786, 788, 792, 794, 798, 800, 804, 806,
    810, 812, 816, 818, 822, 824, 918, 920, 924, 926, 930, 932, 936, 938, 942, 944, 948, 950, 954, 956,
    960, 962, 966, 968
  ]

private def p012source_rankOneVals : List Nat :=
  [
    270, 272, 276, 278, 282, 284, 288, 290, 294, 296, 300, 302, 306, 308, 312, 314, 318, 320, 489, 501,
    537, 645, 651, 663, 699, 705, 717, 723, 729, 735, 741, 747, 753, 757, 759, 763, 765, 769, 771, 775,
    777, 781, 783, 787, 789, 793, 795, 799, 801, 805, 807, 811, 813, 817, 819, 823, 825, 919, 921, 925,
    927, 931, 933, 937, 939, 943, 945, 949, 951, 955, 957, 961, 963, 967, 969
  ]

private def p012source_rankTwoVals : List Nat :=
  [
    0, 2, 12, 14, 36, 38, 42, 44, 48, 50, 108, 110, 114, 116, 120, 122, 126, 128, 132, 134,
    138, 140, 144, 146, 150, 152, 156, 158, 432, 434, 438, 440, 444, 446, 450, 452, 456, 458, 462, 464,
    468, 470, 474, 476, 480, 482
  ]

private def p012source_sigRank (s : P012SourceSig) : Int :=
  let idx := p012source_sigIdx s
  if idx ∈ p012source_rankTwoVals then
    2
  else if idx ∈ p012source_rankOneVals then
    1
  else if idx ∈ p012source_rankZeroVals then
    0
  else
    -1

private def p012source_sigSuccP0 (s : P012SourceSig) : P012SourceSig :=
  { s with c0 := ⟨TBotVal s.cN1.1 s.c0.1 s.c1.1, TBotVal_lt s.cN1.2 s.c0.2 s.c1.2⟩ }

private def p012source_sigSuccP1 (s : P012SourceSig) : P012SourceSig :=
  { s with c1 := ⟨TLowVal s.c0.1 s.c1.1 s.c2.1, TLowVal_lt s.c0.2 s.c1.2 s.c2.2⟩ }

private def p012source_sigSuccP2 (s : P012SourceSig) : P012SourceSig :=
  { s with c2 := ⟨TMidVal s.c1.1 s.c2.1 s.c3.1, TMidVal_lt s.c1.2 s.c2.2 s.c3.2⟩ }

private def p012source_sigSuccIdx3 (s : P012SourceSig) : P012SourceSig :=
  { s with c3 := ⟨TMidVal s.c2.1 s.c3.1 s.c4.1, TMidVal_lt s.c2.2 s.c3.2 s.c4.2⟩ }

private def p012source_sigSuccIdx4 (s : P012SourceSig) (c5 : Fin 3) : P012SourceSig :=
  { s with c4 := ⟨TMidVal s.c3.1 s.c4.1 c5.1, TMidVal_lt s.c3.2 s.c4.2 c5.2⟩ }

private def p012source_sigSuccPN2 (s : P012SourceSig) : P012SourceSig :=
  { s with cN2 := ⟨THighVal 1 s.cN2.1 s.cN1.1, THighVal_lt (by decide) s.cN2.2 s.cN1.2⟩ }

private def p012source_sigSuccPN1 (s : P012SourceSig) : P012SourceSig :=
  { s with cN1 := ⟨TTopVal s.cN2.1 s.cN1.1 s.c0.1, TTopVal_lt s.cN2.2 s.cN1.2 s.c0.2⟩ }

private abbrev p2TpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R = 1 then 1 else 0) = (if S = 2 ∧ R = 1 then 1 else 0)

private abbrev midTpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    ((if L = 2 ∧ out = 1 then 1 else 0) + (if out = 2 ∧ R = 1 then 1 else 0) =
      (if L = 2 ∧ S = 1 then 1 else 0) + (if S = 2 ∧ R = 1 then 1 else 0))

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

private abbrev p012source_p1_live (s : P012SourceSig) : Prop :=
  (s.c0.1 = 0 ∧ s.c1.1 = 1 ∧ s.c2.1 = 2) ∨
    (s.c0.1 = 0 ∧ s.c1.1 = 2 ∧ s.c2.1 = 2) ∨
    (s.c0.1 = 1 ∧ s.c1.1 = 1 ∧ s.c2.1 = 2) ∨
    (s.c0.1 = 1 ∧ s.c1.1 = 0 ∧ s.c2.1 = 2) ∨
    (s.c0.1 = 1 ∧ s.c1.1 = 0 ∧ s.c2.1 = 0)

private theorem p012source_p1_failure_core (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s)
    (hpriv : TLowVal s.c0.1 s.c1.1 s.c2.1 ≠ s.c1.1)
    (hnotlive : ¬ p012source_p1_live s) :
    s.c1.1 = 2 ∧ s.c2.1 = 0 ∧ s.c3.1 = 0 := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          TLowVal s.c0.1 s.c1.1 s.c2.1 ≠ s.c1.1 →
          ¬ p012source_p1_live s →
          s.c1.1 = 2 ∧ s.c2.1 = 0 ∧ s.c3.1 = 0 := by
    native_decide
  exact h s hrank hpriv hnotlive

private theorem p012source_pn2_failure_core (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s)
    (hpriv : THighVal 1 s.cN2.1 s.cN1.1 ≠ s.cN2.1)
    (hnonzero : s.cN2.1 ≠ 0) :
    s.cN2.1 = 1 ∧ s.cN1.1 = 1 := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          THighVal 1 s.cN2.1 s.cN1.1 ≠ s.cN2.1 →
          s.cN2.1 ≠ 0 →
          s.cN2.1 = 1 ∧ s.cN1.1 = 1 := by
    native_decide
  exact h s hrank hpriv hnonzero

private theorem p012source_pn2_core_succ_rank_neg (s : P012SourceSig)
    (hcN2 : s.cN2.1 = 1)
    (hcN1 : s.cN1.1 = 1) :
    p012source_sigRank (p012source_sigSuccPN2 s) = -1 := by
  have h :
      ∀ s : P012SourceSig,
        s.cN2.1 = 1 →
          s.cN1.1 = 1 →
            p012source_sigRank (p012source_sigSuccPN2 s) = -1 := by
    native_decide
  exact h s hcN2 hcN1

private theorem p012source_pn2_failure_succ_rank_neg (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s)
    (hpriv : THighVal 1 s.cN2.1 s.cN1.1 ≠ s.cN2.1)
    (hnonzero : s.cN2.1 ≠ 0) :
    p012source_sigRank (p012source_sigSuccPN2 s) = -1 := by
  rcases p012source_pn2_failure_core s hrank hpriv hnonzero with ⟨hcN2, hcN1⟩
  exact p012source_pn2_core_succ_rank_neg s hcN2 hcN1

private theorem p012source_sig_step_P0 (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s) :
    0 ≤ p012source_sigRank (p012source_sigSuccP0 s) ∧
      localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
        p012source_sigRank (p012source_sigSuccP0 s) ≤
      p012source_sigRank s := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          0 ≤ p012source_sigRank (p012source_sigSuccP0 s) ∧
            localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
              p012source_sigRank (p012source_sigSuccP0 s) ≤
            p012source_sigRank s := by
    native_decide
  exact h s hrank

private theorem p012source_sig_step_P1 (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s)
    (hlive : p012source_p1_live s) :
    0 ≤ p012source_sigRank (p012source_sigSuccP1 s) ∧
      localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
        p012source_sigRank (p012source_sigSuccP1 s) ≤
      p012source_sigRank s := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          p012source_p1_live s →
          0 ≤ p012source_sigRank (p012source_sigSuccP1 s) ∧
            localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
              p012source_sigRank (p012source_sigSuccP1 s) ≤
            p012source_sigRank s := by
    native_decide
  exact h s hrank hlive

private theorem p012source_sig_step_P2 (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s)
    (htp : p2TpLocal s.c1.1 s.c2.1 s.c3.1) :
    0 ≤ p012source_sigRank (p012source_sigSuccP2 s) ∧
      localFcDelta s.c1.1 s.c2.1 s.c3.1 (TMidVal s.c1.1 s.c2.1 s.c3.1) +
        p012source_sigRank (p012source_sigSuccP2 s) ≤
      p012source_sigRank s := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          p2TpLocal s.c1.1 s.c2.1 s.c3.1 →
            0 ≤ p012source_sigRank (p012source_sigSuccP2 s) ∧
              localFcDelta s.c1.1 s.c2.1 s.c3.1 (TMidVal s.c1.1 s.c2.1 s.c3.1) +
                p012source_sigRank (p012source_sigSuccP2 s) ≤
              p012source_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem p012source_sig_step_Idx3 (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s)
    (htp : midTpLocal s.c2.1 s.c3.1 s.c4.1) :
    0 ≤ p012source_sigRank (p012source_sigSuccIdx3 s) ∧
      localFcDelta s.c2.1 s.c3.1 s.c4.1 (TMidVal s.c2.1 s.c3.1 s.c4.1) +
        p012source_sigRank (p012source_sigSuccIdx3 s) ≤
      p012source_sigRank s := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          midTpLocal s.c2.1 s.c3.1 s.c4.1 →
            0 ≤ p012source_sigRank (p012source_sigSuccIdx3 s) ∧
              localFcDelta s.c2.1 s.c3.1 s.c4.1 (TMidVal s.c2.1 s.c3.1 s.c4.1) +
                p012source_sigRank (p012source_sigSuccIdx3 s) ≤
              p012source_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem p012source_sig_step_Idx4 (s : P012SourceSig) (c5 : Fin 3)
    (hrank : 0 ≤ p012source_sigRank s)
    (htp : midTpLocal s.c3.1 s.c4.1 c5.1) :
    0 ≤ p012source_sigRank (p012source_sigSuccIdx4 s c5) ∧
      localFcDelta s.c3.1 s.c4.1 c5.1 (TMidVal s.c3.1 s.c4.1 c5.1) +
        p012source_sigRank (p012source_sigSuccIdx4 s c5) ≤
      p012source_sigRank s := by
  have h :
      ∀ (s : P012SourceSig) (c5 : Fin 3),
        0 ≤ p012source_sigRank s →
          midTpLocal s.c3.1 s.c4.1 c5.1 →
            0 ≤ p012source_sigRank (p012source_sigSuccIdx4 s c5) ∧
              localFcDelta s.c3.1 s.c4.1 c5.1 (TMidVal s.c3.1 s.c4.1 c5.1) +
                p012source_sigRank (p012source_sigSuccIdx4 s c5) ≤
              p012source_sigRank s := by
    native_decide
  exact h s c5 hrank htp

private theorem p012source_sig_step_PN2 (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s)
    (hzero : s.cN2.1 = 0) :
    0 ≤ p012source_sigRank (p012source_sigSuccPN2 s) ∧
      localFcDelta 1 s.cN2.1 s.cN1.1 (THighVal 1 s.cN2.1 s.cN1.1) +
        p012source_sigRank (p012source_sigSuccPN2 s) ≤
      p012source_sigRank s := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          s.cN2.1 = 0 →
            0 ≤ p012source_sigRank (p012source_sigSuccPN2 s) ∧
              localFcDelta 1 s.cN2.1 s.cN1.1 (THighVal 1 s.cN2.1 s.cN1.1) +
                p012source_sigRank (p012source_sigSuccPN2 s) ≤
              p012source_sigRank s := by
    native_decide
  exact h s hrank hzero

private theorem p012source_sig_step_PN1 (s : P012SourceSig)
    (hrank : 0 ≤ p012source_sigRank s) :
    0 ≤ p012source_sigRank (p012source_sigSuccPN1 s) ∧
      localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
        p012source_sigRank (p012source_sigSuccPN1 s) ≤
      p012source_sigRank s := by
  have h :
      ∀ s : P012SourceSig,
        0 ≤ p012source_sigRank s →
          0 ≤ p012source_sigRank (p012source_sigSuccPN1 s) ∧
            localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
              p012source_sigRank (p012source_sigSuccPN1 s) ≤
            p012source_sigRank s := by
    native_decide
  exact h s hrank

private theorem p012source_src_start_rank_zero (c3 c4 : Fin 3) :
    p012source_sigRank
      { c0 := (⟨0, by decide⟩ : Fin 2)
        c1 := (⟨1, by decide⟩ : Fin 3)
        c2 := (⟨2, by decide⟩ : Fin 3)
        c3 := c3
        c4 := c4
        cN2 := (⟨0, by decide⟩ : Fin 3)
        cN1 := (⟨1, by decide⟩ : Fin 2) } = 0 := by
  fin_cases c3 <;> fin_cases c4 <;> native_decide

private theorem p012source_dst_start_rank_zero (c3 c4 : Fin 3) :
    p012source_sigRank
      { c0 := (⟨0, by decide⟩ : Fin 2)
        c1 := (⟨0, by decide⟩ : Fin 3)
        c2 := (⟨2, by decide⟩ : Fin 3)
        c3 := c3
        c4 := c4
        cN2 := (⟨0, by decide⟩ : Fin 3)
        cN1 := (⟨1, by decide⟩ : Fin 2) } = 0 := by
  fin_cases c3 <;> fin_cases c4 <;> native_decide

private theorem midTpLocal_one_two_one_false :
    ¬ midTpLocal 1 2 1 := by
  native_decide

private theorem midTpLocal_two_one_one_false :
    ¬ midTpLocal 2 1 1 := by
  native_decide

private def cup2Idx3 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨3, by omega⟩

private def cup2Idx4 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨4, by omega⟩

private def p012source_sigOfConfig
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : P012SourceSig :=
  { c0 := c (cup2BoundaryIdx0 n hn9)
    c1 := stateAsFin3 n hn4 c (cup2BoundaryIdx1 n hn9)
    c2 := stateAsFin3 n hn4 c (cup2BoundaryIdx2 n hn9)
    c3 := stateAsFin3 n hn4 c (cup2Idx3 n hn9)
    c4 := stateAsFin3 n hn4 c (cup2Idx4 n hn9)
    cN2 := stateAsFin3 n hn4 c (cup2BoundaryIdxN2 n hn9)
    cN1 := Fin.cast
      (by
        have htop : (cup2BoundaryIdxN1 n hn9).1 + 1 = n := by
          simp [cup2BoundaryIdxN1]
          omega
        simpa [cup2Spec] using
          (cup2M_eq_two_of_endpoint (n := n) (i := cup2BoundaryIdxN1 n hn9)
            (Or.inr htop)))
      (c (cup2BoundaryIdxN1 n hn9)) }

private theorem p012source_src_start_rank_of_config
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1) :
    p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) = 0 := by
  let c3 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx3 n hn9)
  let c4 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx4 n hn9)
  have hsig :
      p012source_sigOfConfig n hn4 hn9 c =
        { c0 := (⟨0, by decide⟩ : Fin 2)
          c1 := (⟨1, by decide⟩ : Fin 3)
          c2 := (⟨2, by decide⟩ : Fin 3)
          c3 := c3
          c4 := c4
          cN2 := (⟨0, by decide⟩ : Fin 3)
          cN1 := (⟨1, by decide⟩ : Fin 2) } := by
    ext <;> simp [p012source_sigOfConfig, hc0, hc1, hc2, hcN2, hcN1, c3, c4, stateAsFin3]
  rw [hsig, p012source_src_start_rank_zero c3 c4]

private theorem p012source_dst_start_rank_of_config
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1) :
    p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) = 0 := by
  let c3 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx3 n hn9)
  let c4 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx4 n hn9)
  have hsig :
      p012source_sigOfConfig n hn4 hn9 c =
        { c0 := (⟨0, by decide⟩ : Fin 2)
          c1 := (⟨0, by decide⟩ : Fin 3)
          c2 := (⟨2, by decide⟩ : Fin 3)
          c3 := c3
          c4 := c4
          cN2 := (⟨0, by decide⟩ : Fin 3)
          cN1 := (⟨1, by decide⟩ : Fin 2) } := by
    ext <;> simp [p012source_sigOfConfig, hc0, hc1, hc2, hcN2, hcN1, c3, c4, stateAsFin3]
  rw [hsig, p012source_dst_start_rank_zero c3 c4]

private def cup2Idx5 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨5, by omega⟩

private def cup2IdxN5 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨n - 5, by omega⟩

private def cup2IdxN4 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨n - 4, by omega⟩

private theorem left_cup2IdxN4_eq_idxN5
    (n : Nat) (hn9 : 9 ≤ n) :
    left (cup2IdxN4 n hn9) = cup2IdxN5 n hn9 := by
  apply Fin.ext
  have h0 : (cup2IdxN4 n hn9).1 ≠ 0 := by
    simp [cup2IdxN4]
    omega
  rw [left_val_of_ne_zero h0]
  simp [cup2IdxN4, cup2IdxN5]
  omega

private theorem right_cup2IdxN4_eq_boundaryIdxN3
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2IdxN4 n hn9) = cup2BoundaryIdxN3 n hn9 := by
  apply Fin.ext
  rw [right_val]
  have hlt : n - 4 + 1 < n := by omega
  simp [cup2IdxN4, cup2BoundaryIdxN3, Nat.mod_eq_of_lt hlt]
  omega

private theorem left_cup2BoundaryIdxN3_eq_idxN4
    (n : Nat) (hn9 : 9 ≤ n) :
    left (cup2BoundaryIdxN3 n hn9) = cup2IdxN4 n hn9 := by
  apply Fin.ext
  have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
    simp [cup2BoundaryIdxN3]
    omega
  rw [left_val_of_ne_zero h0]
  simp [cup2BoundaryIdxN3, cup2IdxN4]
  omega

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
  simp [right_val, cup2Idx4, cup2Idx5, Nat.mod_eq_of_lt hlt]

@[simp] private theorem stateAsFin3_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) (i j : Fin n)
    (hji : j ≠ i) :
    stateAsFin3 n hn4 (move (cup2System n hn4) c i) j =
      stateAsFin3 n hn4 c j := by
  apply Fin.eq_of_val_eq
  simp [stateAsFin3, move_apply_ne n hn4 c i j hji]

@[simp] private theorem stateAsFin3_val_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) (i j : Fin n)
    (hji : j ≠ i) :
    (stateAsFin3 n hn4 (move (cup2System n hn4) c i) j).1 =
      (stateAsFin3 n hn4 c j).1 := by
  simpa using congrArg Fin.val (stateAsFin3_move_eq_of_ne n hn4 c i j hji)

@[simp] private theorem move_val_apply_ne
    (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) (i j : Fin n)
    (hji : j ≠ i) :
    (move (cup2System n hn4) c i j).1 = (c j).1 := by
  simpa using congrArg Fin.val (move_apply_ne n hn4 c i j hji)

private theorem p012source_sig_eq_of_move_off_window
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi0 : i ≠ cup2BoundaryIdx0 n hn9)
    (hi1 : i ≠ cup2BoundaryIdx1 n hn9)
    (hi2 : i ≠ cup2BoundaryIdx2 n hn9)
    (hi3 : i ≠ cup2Idx3 n hn9)
    (hi4 : i ≠ cup2Idx4 n hn9)
    (hiN2 : i ≠ cup2BoundaryIdxN2 n hn9)
    (hiN1 : i ≠ cup2BoundaryIdxN1 n hn9) :
    p012source_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c i) =
      p012source_sigOfConfig n hn4 hn9 c := by
  ext <;> simp [p012source_sigOfConfig]
  · simpa using move_val_apply_ne n hn4 c i (cup2BoundaryIdx0 n hn9) hi0.symm
  · simpa using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2BoundaryIdx1 n hn9) hi1.symm
  · simpa using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2BoundaryIdx2 n hn9) hi2.symm
  · simpa using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2Idx3 n hn9) hi3.symm
  · simpa using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2Idx4 n hn9) hi4.symm
  · simpa using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2BoundaryIdxN2 n hn9) hiN2.symm
  · simpa using move_val_apply_ne n hn4 c i (cup2BoundaryIdxN1 n hn9) hiN1.symm

private theorem p012source_rightFrame_preserved_of_move_off
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hiN4 : i ≠ cup2IdxN4 n hn9)
    (hiN3 : i ≠ cup2BoundaryIdxN3 n hn9)
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1) :
    ((move (cup2System n hn4) c i) (cup2IdxN4 n hn9)).1 = 2 ∧
      ((move (cup2System n hn4) c i) (cup2BoundaryIdxN3 n hn9)).1 = 1 := by
  constructor
  · rw [move_apply_ne n hn4 c i (cup2IdxN4 n hn9) hiN4.symm]
    exact hcN4
  · rw [move_apply_ne n hn4 c i (cup2BoundaryIdxN3 n hn9) hiN3.symm]
    exact hcN3

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

private theorem tmid_left_priv_two_one_implies_left_one
    {L : Nat}
    (hL : L < 3)
    (hpriv : TMidVal L 2 1 ≠ 2) :
    L = 1 := by
  interval_cases L <;> simp [TMidVal] at hpriv ⊢

private theorem tmid_priv_two_one_implies_right_ne_zero
    {R : Nat}
    (hR : R < 3)
    (hpriv : TMidVal 2 1 R ≠ 1) :
    R ≠ 0 := by
  interval_cases R <;> simp [TMidVal] at hpriv ⊢

private theorem pn3TpLocal_two_one_one_false :
    ¬ pn3TpLocal 2 1 1 := by
  native_decide

private theorem pn3TpLocal_two_one_two_false :
    ¬ pn3TpLocal 2 1 2 := by
  native_decide

private theorem not_tpPreserving_idxN4_of_sourceFrame
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hpriv : privileged (cup2System n hn4) c (cup2IdxN4 n hn9))
    (htp : cup2TpPreservingMove n hn4 c (cup2IdxN4 n hn9)) :
    False := by
  let cN5 : Fin 3 := stateAsFin3 n hn4 c (cup2IdxN5 n hn9)
  have h0 : (cup2IdxN4 n hn9).1 ≠ 0 := by
    simp [cup2IdxN4]
    omega
  have h1 : (cup2IdxN4 n hn9).1 ≠ 1 := by
    simp [cup2IdxN4]
    omega
  have htop : (cup2IdxN4 n hn9).1 + 1 ≠ n := by
    simp [cup2IdxN4]
    omega
  have hhigh : (cup2IdxN4 n hn9).1 + 2 ≠ n := by
    simp [cup2IdxN4]
    omega
  have hpriv' : TMidVal cN5.1 2 1 ≠ 2 := by
    unfold privileged cup2System at hpriv
    rw [Fin.ne_iff_vne, cup2Trans_val] at hpriv
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh,
      left_cup2IdxN4_eq_idxN5 n hn9, right_cup2IdxN4_eq_boundaryIdxN3 n hn9] at hpriv
    simp [cN5, stateAsFin3, hcN4, hcN3] at hpriv
    exact hpriv
  have hcN5 : cN5.1 = 1 := tmid_left_priv_two_one_implies_left_one cN5.2 hpriv'
  have hcN5' : (c (cup2IdxN5 n hn9)).1 = 1 := by
    simpa [cN5, stateAsFin3] using hcN5
  have htpLocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2IdxN4 n hn9)
    (by
      simp [cup2IdxN4]
      omega)
    (by
      simp [cup2IdxN4]
      omega)
    htp
  rw [left_cup2IdxN4_eq_idxN5 n hn9, right_cup2IdxN4_eq_boundaryIdxN3 n hn9] at htpLocal
  have : midTpLocal 1 2 1 := by
    simpa [hcN5', hcN4, hcN3] using htpLocal
  exact midTpLocal_one_two_one_false this

private theorem not_tpPreserving_idxN3_of_sourceFrame
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9)) :
    False := by
  have hpriv' :
      TMidVal 2 1 (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 1 := by
    unfold privileged cup2System at hpriv
    rw [Fin.ne_iff_vne, cup2Trans_val] at hpriv
    rw [cup2OutVal_boundaryIdxN3 n hn9, left_cup2BoundaryIdxN3_eq_idxN4 n hn9,
      right_cup2BoundaryIdxN3 n hn9] at hpriv
    simpa [hcN4, hcN3] using hpriv
  let cN2 : Fin 3 := stateAsFin3 n hn4 c (cup2BoundaryIdxN2 n hn9)
  have hcN2_ne_zero : cN2.1 ≠ 0 := by
    exact tmid_priv_two_one_implies_right_ne_zero cN2.2 (by simpa [cN2, stateAsFin3] using hpriv')
  have htpLocal := pn3TpLocal_of_tpPreserving n hn4 hn9 c htp
  rw [left_cup2BoundaryIdxN3_eq_idxN4 n hn9] at htpLocal
  have hcN2_is_one_or_two :
      cN2.1 = 1 ∨ cN2.1 = 2 := by
    have hlt : cN2.1 < 3 := cN2.2
    omega
  rcases hcN2_is_one_or_two with hcN2 | hcN2
  · have hcN2' : (c (cup2BoundaryIdxN2 n hn9)).1 = 1 := by
      simpa [cN2, stateAsFin3] using hcN2
    have : pn3TpLocal 2 1 1 := by
      simpa [hcN4, hcN3, hcN2'] using htpLocal
    exact pn3TpLocal_two_one_one_false this
  · have hcN2' : (c (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
      simpa [cN2, stateAsFin3] using hcN2
    have : pn3TpLocal 2 1 2 := by
      simpa [hcN4, hcN3, hcN2'] using htpLocal
    exact pn3TpLocal_two_one_two_false this

private theorem p012source_fc_noninc_of_boundary_fixed_tpStep
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

private theorem p012source_sig_step_noninc_idx0
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9)) :
    0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) : Int) +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012source_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        p012source_sigSuccP0 (p012source_sigOfConfig n hn4 hn9 c) := by
    ext
    · have hleft : (c (left (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx0 n hn9)
      have hright : (c (right (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx0 n hn9)
      simpa [p012source_sigOfConfig, p012source_sigSuccP0, cup2Boundary6, hleft, hright]
    · simpa [p012source_sigOfConfig, p012source_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx3 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2Idx3] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx4 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2Idx4] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP0] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
            omega)
  have hlocal := p012source_sig_step_P0 (p012source_sigOfConfig n hn4 hn9 c) hrank
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
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
          p012source_sigRank (p012source_sigSuccP0 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      simpa [p012source_sigOfConfig, p012source_sigSuccP0, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx0 n hn9)
              (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1) : Int) +
          p012source_sigRank (p012source_sigSuccP0 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx0 n hn9)
              (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1) : Int) +
            p012source_sigRank (p012source_sigSuccP0 (p012source_sigOfConfig n hn4 hn9 c)) =
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
              p012source_sigRank (p012source_sigSuccP0 (p012source_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1 +
            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
                (c (cup2BoundaryIdx0 n hn9)).1
                (c (right (cup2BoundaryIdx0 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdx0 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012source_sig_step_noninc_idx1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (hlive : p012source_p1_live (p012source_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9)) :
    0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) : Int) +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012source_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        p012source_sigSuccP1 (p012source_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012source_sigOfConfig, p012source_sigSuccP1] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval)
    · have hleft : (c (left (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx1 n hn9)
      have hright : (c (right (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx1 n hn9)
      simpa [p012source_sigOfConfig, p012source_sigSuccP1, cup2Boundary6, hleft, hright]
    · simpa [p012source_sigOfConfig, p012source_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2Idx3 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2Idx3] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2Idx4 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2Idx4] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP1] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
            omega)
  have hlocal := p012source_sig_step_P1 (p012source_sigOfConfig n hn4 hn9 c) hrank hlive
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
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
          p012source_sigRank (p012source_sigSuccP1 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      simpa [p012source_sigOfConfig, p012source_sigSuccP1, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
          p012source_sigRank (p012source_sigSuccP1 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
            p012source_sigRank (p012source_sigSuccP1 (p012source_sigOfConfig n hn4 hn9 c)) =
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
              p012source_sigRank (p012source_sigSuccP1 (p012source_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1 +
            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
                (c (cup2BoundaryIdx1 n hn9)).1
                (c (right (cup2BoundaryIdx1 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdx1 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012source_sig_step_noninc_idx2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9)) :
    0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) : Int) +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012source_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        p012source_sigSuccP2 (p012source_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012source_sigOfConfig, p012source_sigSuccP2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval)
    · have hleft : (c (left (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx2 n hn9)
      have hright : (c (right (cup2BoundaryIdx2 n hn9))).1 = (c (cup2Idx3 n hn9)).1 := by
        rw [right_cup2BoundaryIdx2_eq_idx3 n hn9]
      have hc3 : (stateAsFin3 n hn4 c (cup2Idx3 n hn9)).1 = (c (cup2Idx3 n hn9)).1 := by
        simp [stateAsFin3]
      simp [p012source_sigOfConfig, p012source_sigSuccP2, cup2Boundary6, hleft, hright, hc3]
    · simpa [p012source_sigOfConfig, p012source_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2Idx3 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2Idx3] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2Idx4 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2Idx4] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccP2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
            omega)
  have htpLocal :
      p2TpLocal (c (cup2BoundaryIdx1 n hn9)).1 (c (cup2BoundaryIdx2 n hn9)).1
        (c (cup2Idx3 n hn9)).1 := by
    have hlocal := p2TpLocal_of_tpPreserving n hn4 hn9 c htp
    rw [right_cup2BoundaryIdx2_eq_idx3 n hn9] at hlocal
    exact hlocal
  have hlocal := p012source_sig_step_P2 (p012source_sigOfConfig n hn4 hn9 c) hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx2 n hn9)
    have hright : (c (right (cup2BoundaryIdx2 n hn9))).1 = (c (cup2Idx3 n hn9)).1 := by
      rw [right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have h' :
        localFcDelta (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (TMidVal (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) +
          p012source_sigRank (p012source_sigSuccP2 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      simpa [p012source_sigOfConfig, p012source_sigSuccP2, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
          p012source_sigRank (p012source_sigSuccP2 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
            p012source_sigRank (p012source_sigSuccP2 (p012source_sigOfConfig n hn4 hn9 c)) =
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
              p012source_sigRank (p012source_sigSuccP2 (p012source_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1 +
            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
                (c (cup2BoundaryIdx2 n hn9)).1
                (c (right (cup2BoundaryIdx2 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdx2 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012source_sig_step_noninc_idx3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2Idx3 n hn9)) :
    0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2Idx3 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9)) : Int) +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2Idx3 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
  have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
  have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx3]
    omega
  have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx3]
    omega
  have hsig :
      p012source_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2Idx3 n hn9)) =
        p012source_sigSuccIdx3 (p012source_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx3] using
        move_val_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2Idx3] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2Idx3] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2Idx3] at hval)
    · have hleft : (c (left (cup2Idx3 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
        rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      have hright : (c (right (cup2Idx3 n hn9))).1 = (c (cup2Idx4 n hn9)).1 := by
        rw [right_cup2Idx3_eq_idx4 n hn9]
      simp [p012source_sigOfConfig, p012source_sigSuccIdx3, stateAsFin3]
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh, hleft, hright]
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2Idx4 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx3, cup2Idx4] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx3, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx3] using
        move_val_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx3, cup2BoundaryIdxN1] at hval
            omega)
  have htpLocal :
      midTpLocal (c (cup2BoundaryIdx2 n hn9)).1 (c (cup2Idx3 n hn9)).1
        (c (cup2Idx4 n hn9)).1 := by
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2Idx3 n hn9)
      (by simp [cup2Idx3]) (by simp [cup2Idx3]; omega) htp
    rw [left_cup2Idx3_eq_boundaryIdx2 n hn9, right_cup2Idx3_eq_idx4 n hn9] at hlocal
    exact hlocal
  have hlocal := p012source_sig_step_Idx3 (p012source_sigOfConfig n hn4 hn9 c) hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2Idx3 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
    have hright : (c (right (cup2Idx3 n hn9))).1 = (c (cup2Idx4 n hn9)).1 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
    have hout' :
        cup2OutVal n (cup2Idx3 n hn9)
          (c (left (cup2Idx3 n hn9))).1
          (c (cup2Idx3 n hn9)).1
          (c (right (cup2Idx3 n hn9))).1 =
            TMidVal (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have h' :
        localFcDelta (c (left (cup2Idx3 n hn9))).1
            (c (cup2Idx3 n hn9)).1
            (c (right (cup2Idx3 n hn9))).1
            (TMidVal (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1) +
          p012source_sigRank (p012source_sigSuccIdx3 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      simpa [p012source_sigOfConfig, p012source_sigSuccIdx3, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2Idx3 n hn9))).1
            (c (cup2Idx3 n hn9)).1
            (c (right (cup2Idx3 n hn9))).1
            (cup2OutVal n (cup2Idx3 n hn9)
              (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1) : Int) +
          p012source_sigRank (p012source_sigSuccIdx3 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2Idx3 n hn9))).1
          (c (cup2Idx3 n hn9)).1
          (c (right (cup2Idx3 n hn9))).1 +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2Idx3 n hn9))).1
            (c (cup2Idx3 n hn9)).1
            (c (right (cup2Idx3 n hn9))).1
            (cup2OutVal n (cup2Idx3 n hn9)
              (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1) : Int) +
            p012source_sigRank (p012source_sigSuccIdx3 (p012source_sigOfConfig n hn4 hn9 c)) =
          localFcBefore (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1 +
            (localFcDelta (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1
              (cup2OutVal n (cup2Idx3 n hn9)
                (c (left (cup2Idx3 n hn9))).1
                (c (cup2Idx3 n hn9)).1
                (c (right (cup2Idx3 n hn9))).1) +
              p012source_sigRank (p012source_sigSuccIdx3 (p012source_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ = localFcBefore (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1 +
            (localFcDelta (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1
              (TMidVal (c (left (cup2Idx3 n hn9))).1
                (c (cup2Idx3 n hn9)).1
                (c (right (cup2Idx3 n hn9))).1) +
              p012source_sigRank (p012source_sigSuccIdx3 (p012source_sigOfConfig n hn4 hn9 c))) := by
          rw [hout']
        _ ≤ localFcBefore (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1 +
            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2Idx3 n hn9))).1
                (c (cup2Idx3 n hn9)).1
                (c (right (cup2Idx3 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2Idx3 n hn9),
      cup2Fc_split n hn4 c (cup2Idx3 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2Idx3 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2Idx3 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012source_sig_step_noninc_idxN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN1 n hn9)) :
    0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) : Int) +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012source_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        p012source_sigSuccPN1 (p012source_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN1] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx3 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx3, cup2BoundaryIdxN1] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx4 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx4, cup2BoundaryIdxN1] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
            omega)
    · have hleft : (c (left (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN1 n hn9)
      have hright : (c (right (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN1 n hn9)
      simpa [p012source_sigOfConfig, p012source_sigSuccPN1, cup2Boundary6, hleft, hright]
  have hlocal := p012source_sig_step_PN1 (p012source_sigOfConfig n hn4 hn9 c) hrank
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
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
          p012source_sigRank (p012source_sigSuccPN1 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      simpa [p012source_sigOfConfig, p012source_sigSuccPN1, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
          p012source_sigRank (p012source_sigSuccPN1 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
            p012source_sigRank (p012source_sigSuccPN1 (p012source_sigOfConfig n hn4 hn9 c)) =
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
              p012source_sigRank (p012source_sigSuccPN1 (p012source_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1 +
            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
                (c (cup2BoundaryIdxN1 n hn9)).1
                (c (right (cup2BoundaryIdxN1 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdxN1 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012source_sig_step_noninc_idxN2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hzero : (p012source_sigOfConfig n hn4 hn9 c).cN2.1 = 0)
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN2 n hn9)) :
    0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) : Int) +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012source_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
        p012source_sigSuccPN2 (p012source_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx0 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2Idx3 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx3, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2Idx4 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx4, cup2BoundaryIdxN2] at hval
            omega)
    · have hleft : (c (left (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN2 n hn9)
      have hright : (c (right (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
        simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN2 n hn9)
      simp [p012source_sigOfConfig, p012source_sigSuccPN2, cup2Boundary6, hleft, hright, hcN3]
    · simpa [p012source_sigOfConfig, p012source_sigSuccPN2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdxN1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN1, cup2BoundaryIdxN2] at hval
            omega)
  have hlocal := p012source_sig_step_PN2 (p012source_sigOfConfig n hn4 hn9 c) hrank hzero
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
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
          p012source_sigRank (p012source_sigSuccPN2 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      simpa [p012source_sigOfConfig, p012source_sigSuccPN2, stateAsFin3, hleft, hright, hcN3] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
          p012source_sigRank (p012source_sigSuccPN2 (p012source_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
            p012source_sigRank (p012source_sigSuccPN2 (p012source_sigOfConfig n hn4 hn9 c)) =
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
              p012source_sigRank (p012source_sigSuccPN2 (p012source_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1 +
            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
                (c (cup2BoundaryIdxN2 n hn9)).1
                (c (right (cup2BoundaryIdxN2 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN2 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN2 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN2 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdxN2 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012source_sig_step_noninc_idx4
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2Idx4 n hn9)) :
    0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2Idx4 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9)) : Int) +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2Idx4 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  let c5 : Fin 3 := stateAsFin3 n hn4 c (cup2Idx5 n hn9)
  have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
  have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
  have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx4]
    omega
  have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx4]
    omega
  have hsig :
      p012source_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2Idx4 n hn9)) =
        p012source_sigSuccIdx4 (p012source_sigOfConfig n hn4 hn9 c) c5 := by
    ext
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx4] using
        move_val_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2Idx4] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx4] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2Idx4] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx4] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2Idx4] at hval)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx4] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2Idx3 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx3, cup2Idx4] at hval)
    · have hleft : (c (left (cup2Idx4 n hn9))).1 = (c (cup2Idx3 n hn9)).1 := by
        rw [left_cup2Idx4_eq_idx3 n hn9]
      have hright : (c (right (cup2Idx4 n hn9))).1 = (c (cup2Idx5 n hn9)).1 := by
        rw [right_cup2Idx4_eq_idx5 n hn9]
      have hc5 : (stateAsFin3 n hn4 c (cup2Idx5 n hn9)).1 = (c (cup2Idx5 n hn9)).1 := by
        simp [stateAsFin3]
      have hc5' : (c (cup2Idx5 n hn9)).1 = c5.1 := by
        simpa [c5, stateAsFin3] using hc5.symm
      simp [p012source_sigOfConfig, p012source_sigSuccIdx4, stateAsFin3, hleft, hright, hc5']
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx4] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx4, cup2BoundaryIdxN2] at hval
            omega)
    · simpa [p012source_sigOfConfig, p012source_sigSuccIdx4] using
        move_val_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2Idx4, cup2BoundaryIdxN1] at hval
            omega)
  have htpLocal :
      midTpLocal (c (cup2Idx3 n hn9)).1 (c (cup2Idx4 n hn9)).1 c5.1 := by
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2Idx4 n hn9)
      (by simp [cup2Idx4]) (by simp [cup2Idx4]; omega) htp
    rw [left_cup2Idx4_eq_idx3 n hn9, right_cup2Idx4_eq_idx5 n hn9] at hlocal
    simpa [c5, stateAsFin3] using hlocal
  have hlocal := p012source_sig_step_Idx4 (p012source_sigOfConfig n hn4 hn9 c) c5 hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2Idx4 n hn9))).1 = (c (cup2Idx3 n hn9)).1 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
    have hright : (c (right (cup2Idx4 n hn9))).1 = (c (cup2Idx5 n hn9)).1 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
    have hout' :
        cup2OutVal n (cup2Idx4 n hn9)
          (c (left (cup2Idx4 n hn9))).1
          (c (cup2Idx4 n hn9)).1
          (c (right (cup2Idx4 n hn9))).1 =
            TMidVal (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have h' :
        localFcDelta (c (left (cup2Idx4 n hn9))).1
            (c (cup2Idx4 n hn9)).1
            (c (right (cup2Idx4 n hn9))).1
            (TMidVal (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1) +
          p012source_sigRank (p012source_sigSuccIdx4 (p012source_sigOfConfig n hn4 hn9 c) c5) ≤
        p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      simpa [p012source_sigOfConfig, p012source_sigSuccIdx4, stateAsFin3, c5, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2Idx4 n hn9))).1
            (c (cup2Idx4 n hn9)).1
            (c (right (cup2Idx4 n hn9))).1
            (cup2OutVal n (cup2Idx4 n hn9)
              (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1) : Int) +
          p012source_sigRank (p012source_sigSuccIdx4 (p012source_sigOfConfig n hn4 hn9 c) c5) ≤
        localFcBefore (c (left (cup2Idx4 n hn9))).1
          (c (cup2Idx4 n hn9)).1
          (c (right (cup2Idx4 n hn9))).1 +
          p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2Idx4 n hn9))).1
            (c (cup2Idx4 n hn9)).1
            (c (right (cup2Idx4 n hn9))).1
            (cup2OutVal n (cup2Idx4 n hn9)
              (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1) : Int) +
            p012source_sigRank (p012source_sigSuccIdx4 (p012source_sigOfConfig n hn4 hn9 c) c5) =
          localFcBefore (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1 +
            (localFcDelta (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1
              (cup2OutVal n (cup2Idx4 n hn9)
                (c (left (cup2Idx4 n hn9))).1
                (c (cup2Idx4 n hn9)).1
                (c (right (cup2Idx4 n hn9))).1) +
              p012source_sigRank (p012source_sigSuccIdx4 (p012source_sigOfConfig n hn4 hn9 c) c5)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ = localFcBefore (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1 +
            (localFcDelta (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1
              (TMidVal (c (left (cup2Idx4 n hn9))).1
                (c (cup2Idx4 n hn9)).1
                (c (right (cup2Idx4 n hn9))).1) +
              p012source_sigRank (p012source_sigSuccIdx4 (p012source_sigOfConfig n hn4 hn9 c) c5)) := by
          rw [hout']
        _ ≤ localFcBefore (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1 +
            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2Idx4 n hn9))).1
                (c (cup2Idx4 n hn9)).1
                (c (right (cup2Idx4 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2Idx4 n hn9),
      cup2Fc_split n hn4 c (cup2Idx4 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2Idx4 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2Idx4 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012source_step
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hrank : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c))
    (hp1 :
      privileged (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) →
        p012source_p1_live (p012source_sigOfConfig n hn4 hn9 c))
    (hpn2 :
      privileged (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9) →
        (c (cup2BoundaryIdxN2 n hn9)).1 = 0) :
    (c' (cup2IdxN4 n hn9)).1 = 2 ∧
      (c' (cup2BoundaryIdxN3 n hn9)).1 = 1 ∧
      0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c') ∧
      (cup2Fc n hn4 c' : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c') ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  rcases hstep.1.2.2 with ⟨i, hpriv, hmove⟩
  subst c'
  have htpMove : cup2TpPreservingMove n hn4 c i := by
    simpa [cup2TpPreservingMove] using hstep.2
  by_cases hi0 : i = cup2BoundaryIdx0 n hn9
  · subst i
    rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c
        (cup2BoundaryIdx0 n hn9)
        (by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx0, cup2IdxN4] at hval
          omega)
        (by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx0, cup2BoundaryIdxN3] at hval
          omega)
        hcN4 hcN3 with ⟨hcN4', hcN3'⟩
    rcases p012source_sig_step_noninc_idx0 n hn4 hn9 c hrank htpMove with ⟨hrank', hle⟩
    exact ⟨hcN4', hcN3', hrank', hle⟩
  · by_cases hi1 : i = cup2BoundaryIdx1 n hn9
    · subst i
      rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c
          (cup2BoundaryIdx1 n hn9)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2IdxN4] at hval
            omega)
          (by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN3] at hval
            omega)
          hcN4 hcN3 with ⟨hcN4', hcN3'⟩
      rcases p012source_sig_step_noninc_idx1 n hn4 hn9 c hrank (hp1 hpriv) htpMove with
        ⟨hrank', hle⟩
      exact ⟨hcN4', hcN3', hrank', hle⟩
    · by_cases hi2 : i = cup2BoundaryIdx2 n hn9
      · subst i
        rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c
            (cup2BoundaryIdx2 n hn9)
            (by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx2, cup2IdxN4] at hval
              omega)
            (by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx2, cup2BoundaryIdxN3] at hval
              omega)
            hcN4 hcN3 with ⟨hcN4', hcN3'⟩
        rcases p012source_sig_step_noninc_idx2 n hn4 hn9 c hrank htpMove with
          ⟨hrank', hle⟩
        exact ⟨hcN4', hcN3', hrank', hle⟩
      · by_cases hi3 : i = cup2Idx3 n hn9
        · subst i
          rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c
              (cup2Idx3 n hn9)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2Idx3, cup2IdxN4] at hval
                omega)
              (by
                intro hEq
                have hval := congrArg Fin.val hEq
                simp [cup2Idx3, cup2BoundaryIdxN3] at hval
                omega)
              hcN4 hcN3 with ⟨hcN4', hcN3'⟩
          rcases p012source_sig_step_noninc_idx3 n hn4 hn9 c hrank htpMove with
            ⟨hrank', hle⟩
          exact ⟨hcN4', hcN3', hrank', hle⟩
        · by_cases hi4 : i = cup2Idx4 n hn9
          · subst i
            rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c
                (cup2Idx4 n hn9)
                (by
                  intro hEq
                  have hval := congrArg Fin.val hEq
                  simp [cup2Idx4, cup2IdxN4] at hval
                  omega)
                (by
                  intro hEq
                  have hval := congrArg Fin.val hEq
                  simp [cup2Idx4, cup2BoundaryIdxN3] at hval
                  omega)
                hcN4 hcN3 with ⟨hcN4', hcN3'⟩
            rcases p012source_sig_step_noninc_idx4 n hn4 hn9 c hrank htpMove with
              ⟨hrank', hle⟩
            exact ⟨hcN4', hcN3', hrank', hle⟩
          · by_cases hiN1 : i = cup2BoundaryIdxN1 n hn9
            · subst i
              rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c
                  (cup2BoundaryIdxN1 n hn9)
                  (by
                    intro hEq
                    have hval := congrArg Fin.val hEq
                    simp [cup2BoundaryIdxN1, cup2IdxN4] at hval
                    omega)
                  (by
                    intro hEq
                    have hval := congrArg Fin.val hEq
                    simp [cup2BoundaryIdxN1, cup2BoundaryIdxN3] at hval
                    omega)
                  hcN4 hcN3 with ⟨hcN4', hcN3'⟩
              rcases p012source_sig_step_noninc_idxN1 n hn4 hn9 c hrank htpMove with
                ⟨hrank', hle⟩
              exact ⟨hcN4', hcN3', hrank', hle⟩
            · by_cases hiN2 : i = cup2BoundaryIdxN2 n hn9
              · subst i
                rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c
                    (cup2BoundaryIdxN2 n hn9)
                    (by
                      intro hEq
                      have hval := congrArg Fin.val hEq
                      simp [cup2BoundaryIdxN2, cup2IdxN4] at hval
                      omega)
                    (by
                      intro hEq
                      have hval := congrArg Fin.val hEq
                      simp [cup2BoundaryIdxN2, cup2BoundaryIdxN3] at hval
                      omega)
                    hcN4 hcN3 with ⟨hcN4', hcN3'⟩
                have hzero :
                    (p012source_sigOfConfig n hn4 hn9 c).cN2.1 = 0 := by
                  simpa [p012source_sigOfConfig, stateAsFin3] using hpn2 hpriv
                rcases p012source_sig_step_noninc_idxN2 n hn4 hn9 c hrank hcN3 hzero htpMove with
                  ⟨hrank', hle⟩
                exact ⟨hcN4', hcN3', hrank', hle⟩
              · by_cases hiN4 : i = cup2IdxN4 n hn9
                · subst i
                  exact False.elim
                    (not_tpPreserving_idxN4_of_sourceFrame n hn4 hn9 c hcN4 hcN3 hpriv htpMove)
                · by_cases hiN3 : i = cup2BoundaryIdxN3 n hn9
                  · subst i
                    exact False.elim
                      (not_tpPreserving_idxN3_of_sourceFrame n hn4 hn9 c hcN4 hcN3 hpriv htpMove)
                  ·
                    have hdeep_left : 2 < i.1 := by
                      have hi_ne0 : i.1 ≠ 0 := by
                        intro hEq
                        apply hi0
                        apply Fin.ext
                        simpa [cup2BoundaryIdx0] using hEq
                      have hi_ne1 : i.1 ≠ 1 := by
                        intro hEq
                        apply hi1
                        apply Fin.ext
                        simpa [cup2BoundaryIdx1] using hEq
                      have hi_ne2 : i.1 ≠ 2 := by
                        intro hEq
                        apply hi2
                        apply Fin.ext
                        simpa [cup2BoundaryIdx2] using hEq
                      omega
                    have hdeep_right : i.1 + 3 < n := by
                      have hi_ltN : i.1 < n := i.2
                      have hi_neN1 : i.1 ≠ n - 1 := by
                        intro hEq
                        apply hiN1
                        apply Fin.ext
                        simpa [cup2BoundaryIdxN1] using hEq
                      have hi_neN2 : i.1 ≠ n - 2 := by
                        intro hEq
                        apply hiN2
                        apply Fin.ext
                        simpa [cup2BoundaryIdxN2] using hEq
                      have hi_neN3 : i.1 ≠ n - 3 := by
                        intro hEq
                        apply hiN3
                        apply Fin.ext
                        simpa [cup2BoundaryIdxN3] using hEq
                      have hi_neN4 : i.1 ≠ n - 4 := by
                        intro hEq
                        apply hiN4
                        apply Fin.ext
                        simpa [cup2IdxN4] using hEq
                      have hi_ltN4 : i.1 < n - 4 := by
                        by_contra hnot
                        have hi_geN4 : n - 4 ≤ i.1 := by omega
                        have hcases0 : i.1 = n - 4 ∨ n - 3 ≤ i.1 := by
                          omega
                        rcases hcases0 with hEq | hi_geN3
                        · exact hi_neN4 hEq
                        have hcases1 : i.1 = n - 3 ∨ n - 2 ≤ i.1 := by
                          omega
                        rcases hcases1 with hEq | hi_geN2
                        · exact hi_neN3 hEq
                        have hcases2 : i.1 = n - 2 ∨ n - 1 ≤ i.1 := by
                          omega
                        rcases hcases2 with hEq | hi_geN1
                        · exact hi_neN2 hEq
                        have hEq : i.1 = n - 1 := by omega
                        exact hi_neN1 hEq
                      omega
                    have hfixed :
                        cup2BoundaryState n hn4 hn9 (move (cup2System n hn4) c i) =
                          cup2BoundaryState n hn4 hn9 c := by
                      exact cup2BoundaryState_move_eq_of_deep n hn4 hn9 c i hdeep_left hdeep_right
                    have hsig :=
                      p012source_sig_eq_of_move_off_window n hn4 hn9 c i
                        hi0 hi1 hi2 hi3 hi4 hiN2 hiN1
                    rcases p012source_rightFrame_preserved_of_move_off n hn4 hn9 c i hiN4 hiN3 hcN4 hcN3 with
                      ⟨hcN4', hcN3'⟩
                    have hfc_le := p012source_fc_noninc_of_boundary_fixed_tpStep n hn4 hn9 hstep hfixed
                    have hfc_le' : (cup2Fc n hn4 (move (cup2System n hn4) c i) : Int) ≤ cup2Fc n hn4 c := by
                      exact_mod_cast hfc_le
                    have hrank' :
                        0 ≤ p012source_sigRank
                          (p012source_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c i)) := by
                      simpa [hsig] using hrank
                    have hle :
                        (cup2Fc n hn4 (move (cup2System n hn4) c i) : Int) +
                            p012source_sigRank
                              (p012source_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c i)) ≤
                          (cup2Fc n hn4 c : Int) +
                            p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
                      rw [hsig]
                      omega
                    exact ⟨hcN4', hcN3', hrank', hle⟩

private theorem p012source_tpReachable_bound
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hp1 :
      ∀ {d : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c d →
          privileged (cup2System n hn4) d (cup2BoundaryIdx1 n hn9) →
            p012source_p1_live (p012source_sigOfConfig n hn4 hn9 d))
    (hpn2 :
      ∀ {d : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c d →
          privileged (cup2System n hn4) d (cup2BoundaryIdxN2 n hn9) →
            (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    (d (cup2IdxN4 n hn9)).1 = 2 ∧
      (d (cup2BoundaryIdxN3 n hn9)).1 = 1 ∧
      0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 d) ∧
      (cup2Fc n hn4 d : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 d) ≤
        (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
  have hrank0 : 0 ≤ p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := by
    simpa [p012source_src_start_rank_of_config n hn4 hn9 c hc0 hc1 hc2 hcN2 hcN1]
  induction hreach with
  | refl =>
      exact ⟨hcN4, hcN3, hrank0, by omega⟩
  | tail hreach_bd hstep ih =>
      rcases ih with ⟨hbN4, hbN3, hrankb, hleb⟩
      rcases p012source_step n hn4 hn9 hstep hbN4 hbN3 hrankb
          (fun hpriv => hp1 hreach_bd hpriv)
          (fun hpriv => hpn2 hreach_bd hpriv) with
        ⟨hdN4, hdN3, hrankd, hled⟩
      exact ⟨hdN4, hdN3, hrankd, le_trans hled hleb⟩

theorem p012source_tpReachable_fc_le_of_sideconds
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hp1 :
      ∀ {d : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c d →
          privileged (cup2System n hn4) d (cup2BoundaryIdx1 n hn9) →
            p012source_p1_live (p012source_sigOfConfig n hn4 hn9 d))
    (hpn2 :
      ∀ {d : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c d →
          privileged (cup2System n hn4) d (cup2BoundaryIdxN2 n hn9) →
            (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤ cup2Fc n hn4 c := by
  rcases p012source_tpReachable_bound n hn4 hn9 c hcN4 hcN3 hc0 hc1 hc2 hcN2 hcN1 hp1 hpn2 hreach with
    ⟨_, _, hrankd, hle⟩
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c := by
    calc
      (cup2Fc n hn4 d : Int) ≤
          (cup2Fc n hn4 d : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 d) := by
        omega
      _ ≤ (cup2Fc n hn4 c : Int) + p012source_sigRank (p012source_sigOfConfig n hn4 hn9 c) := hle
      _ = cup2Fc n hn4 c := by
        rw [p012source_src_start_rank_of_config n hn4 hn9 c hc0 hc1 hc2 hcN2 hcN1]
        omega
  exact_mod_cast hfc_le'

theorem p012source_scratch_smoke : True := by
  have _ := p012source_rankZeroVals.length
  have _ := p012source_rankOneVals.length
  have _ := p012source_rankTwoVals.length
  trivial

end LeanMn
