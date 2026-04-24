import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SyntheticPotential
import LeanMn.Convergence.SixTuple

namespace LeanMn

private structure P012ExactSig where
  c0 : Fin 2
  c1 : Fin 3
  c2 : Fin 3
  c3 : Fin 3
  c4 : Fin 3
  cN4 : Fin 3
  cN3 : Fin 3
  cN2 : Fin 3
  cN1 : Fin 2
deriving DecidableEq, Repr

@[ext] private theorem P012ExactSig.ext {s t : P012ExactSig}
    (h0 : s.c0 = t.c0) (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2)
    (h3 : s.c3 = t.c3) (h4 : s.c4 = t.c4)
    (hN4 : s.cN4 = t.cN4) (hN3 : s.cN3 = t.cN3)
    (hN2 : s.cN2 = t.cN2) (hN1 : s.cN1 = t.cN1) :
    s = t := by
  cases s
  cases t
  cases h0
  cases h1
  cases h2
  cases h3
  cases h4
  cases hN4
  cases hN3
  cases hN2
  cases hN1
  rfl

private abbrev P012ExactSigTuple :=
  Fin 2 × (Fin 3 × (Fin 3 × (Fin 3 × (Fin 3 ×
    (Fin 3 × (Fin 3 × (Fin 3 × Fin 2)))))))

private def p012exactSigToTuple (s : P012ExactSig) : P012ExactSigTuple :=
  ⟨s.c0, ⟨s.c1, ⟨s.c2, ⟨s.c3, ⟨s.c4, ⟨s.cN4, ⟨s.cN3, ⟨s.cN2, s.cN1⟩⟩⟩⟩⟩⟩⟩⟩

private def p012exactSigOfTuple : P012ExactSigTuple → P012ExactSig
  | ⟨c0, ⟨c1, ⟨c2, ⟨c3, ⟨c4, ⟨cN4, ⟨cN3, ⟨cN2, cN1⟩⟩⟩⟩⟩⟩⟩⟩ =>
      { c0 := c0, c1 := c1, c2 := c2, c3 := c3, c4 := c4
        cN4 := cN4, cN3 := cN3, cN2 := cN2, cN1 := cN1 }

private theorem p012exactSig_left_inv : Function.LeftInverse p012exactSigToTuple p012exactSigOfTuple := by
  intro t
  rcases t with ⟨c0, ⟨c1, ⟨c2, ⟨c3, ⟨c4, ⟨cN4, ⟨cN3, ⟨cN2, cN1⟩⟩⟩⟩⟩⟩⟩⟩
  rfl

private theorem p012exactSig_right_inv : Function.RightInverse p012exactSigToTuple p012exactSigOfTuple := by
  intro s
  cases s
  rfl

private instance : Fintype P012ExactSig :=
  Fintype.ofEquiv P012ExactSigTuple
    { toFun := p012exactSigOfTuple
      invFun := p012exactSigToTuple
      left_inv := p012exactSig_left_inv
      right_inv := p012exactSig_right_inv }

private def p012exact_sigOfConfig
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : P012ExactSig :=
  { c0 := c (cup2BoundaryIdx0 n hn9)
    c1 := stateAsFin3 n hn4 c (cup2BoundaryIdx1 n hn9)
    c2 := stateAsFin3 n hn4 c (cup2BoundaryIdx2 n hn9)
    c3 := stateAsFin3 n hn4 c (⟨3, by omega⟩ : Fin n)
    c4 := stateAsFin3 n hn4 c (⟨4, by omega⟩ : Fin n)
    cN4 := stateAsFin3 n hn4 c (⟨n - 4, by omega⟩ : Fin n)
    cN3 := stateAsFin3 n hn4 c (cup2BoundaryIdxN3 n hn9)
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

private def p012exact_sigIdx (s : P012ExactSig) : Nat :=
  ((((((((s.c0.1 * 3 + s.c1.1) * 3 + s.c2.1) * 3 + s.c3.1) * 3 + s.c4.1) * 3 + s.cN4.1) * 3 + s.cN3.1) * 3 + s.cN2.1) * 2 + s.cN1.1)

private def p012exact_rankZeroVals : List Nat :=
  [
    47, 155, 367, 371, 421, 425, 479, 1015, 1019, 1069, 1073, 1123, 1127, 1177, 1181, 1231, 1235, 1285, 1289, 1339,
    1343, 1393, 1397, 1451, 2473, 2477, 2527, 2531, 2581, 2585, 2635, 2639, 2689, 2693, 2743, 2747, 2797, 2801, 2851, 2855,
    2905, 2909, 3931, 3935, 3985, 3989, 4039, 4043, 4093, 4097, 4147, 4151, 4201, 4205, 4255, 4259, 4309, 4313, 4367, 4740,
    4742, 4745, 4794, 4796, 4799, 5388, 5390, 5393, 5442, 5444, 5447, 5496, 5498, 5501, 5550, 5552, 5555, 5604, 5606, 5609,
    5658, 5660, 5663, 5712, 5714, 5717, 5766, 5768, 5771, 6198, 6200, 6203, 6252, 6254, 6257
  ]

private def p012exact_rankOneVals : List Nat :=
  [
    43, 151, 475, 1447, 2472, 2474, 2526, 2528, 2580, 2582, 2634, 2636, 2688, 2690, 2742, 2744, 2796, 2798, 2850, 2852,
    4363, 4416, 4418, 4421, 4524, 4526, 4529, 4848, 4850, 4853, 5820, 5822, 5825, 5874, 5876, 5879, 5982, 5984, 5987, 6306,
    6308, 6311, 6360, 6362, 6365, 6468, 6470, 6473, 6522, 6524, 6527, 6576, 6578, 6581, 6630, 6632, 6635, 6684, 6686, 6689,
    6738, 6740, 6743, 6792, 6794, 6797, 6846, 6847, 6848, 6851, 6900, 6901, 6902, 6905, 6954, 6955, 6956, 6959, 7008, 7009,
    7010, 7013, 7062, 7063, 7064, 7067, 7116, 7117, 7118, 7121, 7170, 7171, 7172, 7175, 7224, 7225, 7226, 7229, 7278, 7280,
    7283, 8304, 8305, 8306, 8309, 8358, 8359, 8360, 8363, 8412, 8413, 8414, 8417, 8466, 8467, 8468, 8471, 8520, 8521, 8522,
    8525, 8574, 8575, 8576, 8579, 8628, 8629, 8630, 8633, 8682, 8683, 8684, 8687, 8736, 8738, 8741
  ]

private def p012exact_rankTwoVals : List Nat :=
  [
    45, 153, 366, 368, 369, 420, 422, 423, 477, 1014, 1016, 1017, 1068, 1070, 1071, 1122, 1124, 1125, 1176, 1178,
    1179, 1230, 1232, 1233, 1284, 1286, 1287, 1338, 1340, 1341, 1392, 1394, 1395, 1449, 2475, 2529, 2583, 2637, 2691, 2745,
    2799, 2853, 2904, 2906, 2907, 3930, 3932, 3933, 3984, 3986, 3987, 4038, 4040, 4041, 4092, 4094, 4095, 4146, 4148, 4149,
    4200, 4202, 4203, 4254, 4256, 4257, 4308, 4310, 4311, 4365, 4743, 4797, 5391, 5445, 5499, 5553, 5607, 5661, 5715, 5769,
    6201, 6255, 7279, 8737
  ]

private def p012exact_rankThreeVals : List Nat :=
  [
    42, 44, 150, 152, 474, 476, 1446, 1448, 4362, 4364, 4419, 4527, 4851, 5823, 5877, 5985, 6309, 6363, 6471, 6525,
    6579, 6633, 6687, 6741, 6795, 6849, 6903, 6957, 7011, 7065, 7119, 7173, 7227, 7281, 8307, 8361, 8415, 8469, 8523, 8577,
    8631, 8685, 8739
  ]

private def p012exact_sigRank (s : P012ExactSig) : Int :=
  let idx := p012exact_sigIdx s
  if idx ∈ p012exact_rankThreeVals then
    3
  else if idx ∈ p012exact_rankTwoVals then
    2
  else if idx ∈ p012exact_rankOneVals then
    1
  else if idx ∈ p012exact_rankZeroVals then
    0
  else
    -1

private theorem p012exact_src_start_rank_zero (c3 c4 : Fin 3) :
    p012exact_sigRank
      { c0 := (⟨0, by decide⟩ : Fin 2)
        c1 := (⟨1, by decide⟩ : Fin 3)
        c2 := (⟨2, by decide⟩ : Fin 3)
        c3 := c3
        c4 := c4
        cN4 := (⟨2, by decide⟩ : Fin 3)
        cN3 := (⟨1, by decide⟩ : Fin 3)
        cN2 := (⟨0, by decide⟩ : Fin 3)
        cN1 := (⟨1, by decide⟩ : Fin 2) } = 0 := by
  fin_cases c3 <;> fin_cases c4 <;> native_decide

private theorem p012exact_dst_start_rank (c3 c4 : Fin 3) :
    p012exact_sigRank
      { c0 := (⟨0, by decide⟩ : Fin 2)
        c1 := (⟨0, by decide⟩ : Fin 3)
        c2 := (⟨2, by decide⟩ : Fin 3)
        c3 := c3
        c4 := c4
        cN4 := (⟨2, by decide⟩ : Fin 3)
        cN3 := (⟨1, by decide⟩ : Fin 3)
        cN2 := (⟨0, by decide⟩ : Fin 3)
        cN1 := (⟨1, by decide⟩ : Fin 2) } =
      if c3.1 = 2 ∧ c4.1 = 2 then 1 else 0 := by
  fin_cases c3 <;> fin_cases c4 <;> native_decide

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

private abbrev midTpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    ((if L = 2 ∧ out = 1 then 1 else 0) + (if out = 2 ∧ R = 1 then 1 else 0) =
      (if L = 2 ∧ S = 1 then 1 else 0) + (if S = 2 ∧ R = 1 then 1 else 0))

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

private def cup2Idx3 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨3, by omega⟩

private def cup2Idx4 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨4, by omega⟩

private def cup2Idx5 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨5, by omega⟩

private def cup2IdxN5 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨n - 5, by omega⟩

private def cup2IdxN4 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨n - 4, by omega⟩

private def p012exact_sigSuccP0 (s : P012ExactSig) : P012ExactSig :=
  { s with c0 := ⟨TBotVal s.cN1.1 s.c0.1 s.c1.1,
      TBotVal_lt s.cN1.2 s.c0.2 s.c1.2⟩ }

private def p012exact_sigSuccP1 (s : P012ExactSig) : P012ExactSig :=
  { s with c1 := ⟨TLowVal s.c0.1 s.c1.1 s.c2.1,
      TLowVal_lt s.c0.2 s.c1.2 s.c2.2⟩ }

private def p012exact_sigSuccP2 (s : P012ExactSig) : P012ExactSig :=
  { s with c2 := ⟨TMidVal s.c1.1 s.c2.1 s.c3.1,
      TMidVal_lt s.c1.2 s.c2.2 s.c3.2⟩ }

private def p012exact_sigSuccIdx3 (s : P012ExactSig) : P012ExactSig :=
  { s with c3 := ⟨TMidVal s.c2.1 s.c3.1 s.c4.1,
      TMidVal_lt s.c2.2 s.c3.2 s.c4.2⟩ }

private def p012exact_sigSuccIdx4 (s : P012ExactSig) (c5 : Fin 3) : P012ExactSig :=
  { s with c4 := ⟨TMidVal s.c3.1 s.c4.1 c5.1,
      TMidVal_lt s.c3.2 s.c4.2 c5.2⟩ }

private def p012exact_sigSuccIdxN4 (s : P012ExactSig) (cN5 : Fin 3) : P012ExactSig :=
  { s with cN4 := ⟨TMidVal cN5.1 s.cN4.1 s.cN3.1,
      TMidVal_lt cN5.2 s.cN4.2 s.cN3.2⟩ }

private def p012exact_sigSuccPN3 (s : P012ExactSig) : P012ExactSig :=
  { s with cN3 := ⟨TMidVal s.cN4.1 s.cN3.1 s.cN2.1,
      TMidVal_lt s.cN4.2 s.cN3.2 s.cN2.2⟩ }

private def p012exact_sigSuccPN2 (s : P012ExactSig) : P012ExactSig :=
  { s with cN2 := ⟨THighVal s.cN3.1 s.cN2.1 s.cN1.1,
      THighVal_lt s.cN3.2 s.cN2.2 s.cN1.2⟩ }

private def p012exact_sigSuccPN1 (s : P012ExactSig) : P012ExactSig :=
  { s with cN1 := ⟨TTopVal s.cN2.1 s.cN1.1 s.c0.1,
      TTopVal_lt s.cN2.2 s.cN1.2 s.c0.2⟩ }

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
  change ((stateAsFin3 n hn4 (move (cup2System n hn4) c i) j : Fin 3).1 =
    (stateAsFin3 n hn4 c j : Fin 3).1)
  simpa using congrArg Fin.val (stateAsFin3_move_eq_of_ne n hn4 c i j hji)

@[simp] private theorem move_val_apply_ne
    (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) (i j : Fin n)
    (hji : j ≠ i) :
    (move (cup2System n hn4) c i j).1 = (c j).1 := by
  simpa using congrArg Fin.val (move_apply_ne n hn4 c i j hji)

@[simp] private theorem cup2Boundary6_c0_val_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi : i ≠ cup2BoundaryIdx0 n hn9) :
    (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i)).c0.1 =
      (cup2Boundary6 n hn4 hn9 c).c0.1 := by
  simpa [cup2Boundary6] using move_val_apply_ne n hn4 c i (cup2BoundaryIdx0 n hn9) hi.symm

@[simp] private theorem cup2Boundary6_c1_val_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi : i ≠ cup2BoundaryIdx1 n hn9) :
    (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i)).c1.1 =
      (cup2Boundary6 n hn4 hn9 c).c1.1 := by
  simpa [cup2Boundary6] using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2BoundaryIdx1 n hn9) hi.symm

@[simp] private theorem cup2Boundary6_c2_val_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi : i ≠ cup2BoundaryIdx2 n hn9) :
    (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i)).c2.1 =
      (cup2Boundary6 n hn4 hn9 c).c2.1 := by
  simpa [cup2Boundary6] using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2BoundaryIdx2 n hn9) hi.symm

@[simp] private theorem cup2Boundary6_cN3_val_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi : i ≠ cup2BoundaryIdxN3 n hn9) :
    (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i)).cN3.1 =
      (cup2Boundary6 n hn4 hn9 c).cN3.1 := by
  simpa [cup2Boundary6] using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2BoundaryIdxN3 n hn9) hi.symm

@[simp] private theorem cup2Boundary6_cN2_val_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi : i ≠ cup2BoundaryIdxN2 n hn9) :
    (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i)).cN2.1 =
      (cup2Boundary6 n hn4 hn9 c).cN2.1 := by
  simpa [cup2Boundary6] using stateAsFin3_val_move_eq_of_ne n hn4 c i (cup2BoundaryIdxN2 n hn9) hi.symm

@[simp] private theorem cup2Boundary6_cN1_val_move_eq_of_ne
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi : i ≠ cup2BoundaryIdxN1 n hn9) :
    (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i)).cN1.1 =
      (cup2Boundary6 n hn4 hn9 c).cN1.1 := by
  simpa [cup2Boundary6] using move_val_apply_ne n hn4 c i (cup2BoundaryIdxN1 n hn9) hi.symm

private theorem p012exact_sig_eq_of_move_off_window
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hi0 : i ≠ cup2BoundaryIdx0 n hn9)
    (hi1 : i ≠ cup2BoundaryIdx1 n hn9)
    (hi2 : i ≠ cup2BoundaryIdx2 n hn9)
    (hi3 : i ≠ cup2Idx3 n hn9)
    (hi4 : i ≠ cup2Idx4 n hn9)
    (hiN4 : i ≠ cup2IdxN4 n hn9)
    (hiN3 : i ≠ cup2BoundaryIdxN3 n hn9)
    (hiN2 : i ≠ cup2BoundaryIdxN2 n hn9)
    (hiN1 : i ≠ cup2BoundaryIdxN1 n hn9) :
    p012exact_sigOfConfig n hn4 hn9 (move (cup2System n hn4) c i) =
      p012exact_sigOfConfig n hn4 hn9 c := by
  ext <;> simp [p012exact_sigOfConfig]
  · simpa using congrArg Fin.val
      (move_apply_ne n hn4 c i (cup2BoundaryIdx0 n hn9) (by intro hEq; exact hi0 hEq.symm))
  · simpa using congrArg Fin.val
      (stateAsFin3_move_eq_of_ne n hn4 c i (cup2BoundaryIdx1 n hn9)
        (by intro hEq; exact hi1 hEq.symm))
  · simpa using congrArg Fin.val
      (stateAsFin3_move_eq_of_ne n hn4 c i (cup2BoundaryIdx2 n hn9)
        (by intro hEq; exact hi2 hEq.symm))
  · simpa using congrArg Fin.val
      (stateAsFin3_move_eq_of_ne n hn4 c i (cup2Idx3 n hn9)
        (by intro hEq; exact hi3 hEq.symm))
  · simpa using congrArg Fin.val
      (stateAsFin3_move_eq_of_ne n hn4 c i (cup2Idx4 n hn9)
        (by intro hEq; exact hi4 hEq.symm))
  · simpa using congrArg Fin.val
      (stateAsFin3_move_eq_of_ne n hn4 c i (cup2IdxN4 n hn9)
        (by intro hEq; exact hiN4 hEq.symm))
  · simpa using congrArg Fin.val
      (stateAsFin3_move_eq_of_ne n hn4 c i (cup2BoundaryIdxN3 n hn9)
        (by intro hEq; exact hiN3 hEq.symm))
  · simpa using congrArg Fin.val
      (stateAsFin3_move_eq_of_ne n hn4 c i (cup2BoundaryIdxN2 n hn9)
        (by intro hEq; exact hiN2 hEq.symm))
  · simpa using congrArg Fin.val
      (move_apply_ne n hn4 c i (cup2BoundaryIdxN1 n hn9) (by intro hEq; exact hiN1 hEq.symm))

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

private theorem p012exact_sig_step_P0 (s : P012ExactSig)
    (hrank : 0 ≤ p012exact_sigRank s) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccP0 s) ∧
      localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
        p012exact_sigRank (p012exact_sigSuccP0 s) ≤
      p012exact_sigRank s := by
  have h :
      ∀ s : P012ExactSig,
        0 ≤ p012exact_sigRank s →
          0 ≤ p012exact_sigRank (p012exact_sigSuccP0 s) ∧
            localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) +
              p012exact_sigRank (p012exact_sigSuccP0 s) ≤
            p012exact_sigRank s := by
    native_decide
  exact h s hrank

private theorem p012exact_sig_step_P1 (s : P012ExactSig)
    (hrank : 0 ≤ p012exact_sigRank s) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccP1 s) ∧
      localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
        p012exact_sigRank (p012exact_sigSuccP1 s) ≤
      p012exact_sigRank s := by
  have h :
      ∀ s : P012ExactSig,
        0 ≤ p012exact_sigRank s →
          0 ≤ p012exact_sigRank (p012exact_sigSuccP1 s) ∧
            localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) +
              p012exact_sigRank (p012exact_sigSuccP1 s) ≤
            p012exact_sigRank s := by
    native_decide
  exact h s hrank

private theorem p012exact_sig_step_P2 (s : P012ExactSig)
    (hrank : 0 ≤ p012exact_sigRank s)
    (htp : p2TpLocal s.c1.1 s.c2.1 s.c3.1) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccP2 s) ∧
      localFcDelta s.c1.1 s.c2.1 s.c3.1 (TMidVal s.c1.1 s.c2.1 s.c3.1) +
        p012exact_sigRank (p012exact_sigSuccP2 s) ≤
      p012exact_sigRank s := by
  have h :
      ∀ s : P012ExactSig,
        0 ≤ p012exact_sigRank s →
          p2TpLocal s.c1.1 s.c2.1 s.c3.1 →
            0 ≤ p012exact_sigRank (p012exact_sigSuccP2 s) ∧
              localFcDelta s.c1.1 s.c2.1 s.c3.1 (TMidVal s.c1.1 s.c2.1 s.c3.1) +
                p012exact_sigRank (p012exact_sigSuccP2 s) ≤
              p012exact_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem p012exact_sig_step_Idx3 (s : P012ExactSig)
    (hrank : 0 ≤ p012exact_sigRank s)
    (htp : midTpLocal s.c2.1 s.c3.1 s.c4.1) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccIdx3 s) ∧
      localFcDelta s.c2.1 s.c3.1 s.c4.1 (TMidVal s.c2.1 s.c3.1 s.c4.1) +
        p012exact_sigRank (p012exact_sigSuccIdx3 s) ≤
      p012exact_sigRank s := by
  have h :
      ∀ s : P012ExactSig,
        0 ≤ p012exact_sigRank s →
          midTpLocal s.c2.1 s.c3.1 s.c4.1 →
            0 ≤ p012exact_sigRank (p012exact_sigSuccIdx3 s) ∧
              localFcDelta s.c2.1 s.c3.1 s.c4.1 (TMidVal s.c2.1 s.c3.1 s.c4.1) +
                p012exact_sigRank (p012exact_sigSuccIdx3 s) ≤
              p012exact_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem p012exact_sig_step_Idx4 (s : P012ExactSig) (c5 : Fin 3)
    (hrank : 0 ≤ p012exact_sigRank s)
    (htp : midTpLocal s.c3.1 s.c4.1 c5.1) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccIdx4 s c5) ∧
      localFcDelta s.c3.1 s.c4.1 c5.1 (TMidVal s.c3.1 s.c4.1 c5.1) +
        p012exact_sigRank (p012exact_sigSuccIdx4 s c5) ≤
      p012exact_sigRank s := by
  have h :
      ∀ (s : P012ExactSig) (c5 : Fin 3),
        0 ≤ p012exact_sigRank s →
          midTpLocal s.c3.1 s.c4.1 c5.1 →
            0 ≤ p012exact_sigRank (p012exact_sigSuccIdx4 s c5) ∧
              localFcDelta s.c3.1 s.c4.1 c5.1 (TMidVal s.c3.1 s.c4.1 c5.1) +
                p012exact_sigRank (p012exact_sigSuccIdx4 s c5) ≤
              p012exact_sigRank s := by
    native_decide
  exact h s c5 hrank htp

private theorem p012exact_sig_step_IdxN4 (s : P012ExactSig) (cN5 : Fin 3)
    (hrank : 0 ≤ p012exact_sigRank s)
    (htp : midTpLocal cN5.1 s.cN4.1 s.cN3.1) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccIdxN4 s cN5) ∧
      localFcDelta cN5.1 s.cN4.1 s.cN3.1 (TMidVal cN5.1 s.cN4.1 s.cN3.1) +
        p012exact_sigRank (p012exact_sigSuccIdxN4 s cN5) ≤
      p012exact_sigRank s := by
  have h :
      ∀ (s : P012ExactSig) (cN5 : Fin 3),
        0 ≤ p012exact_sigRank s →
          midTpLocal cN5.1 s.cN4.1 s.cN3.1 →
            0 ≤ p012exact_sigRank (p012exact_sigSuccIdxN4 s cN5) ∧
              localFcDelta cN5.1 s.cN4.1 s.cN3.1 (TMidVal cN5.1 s.cN4.1 s.cN3.1) +
                p012exact_sigRank (p012exact_sigSuccIdxN4 s cN5) ≤
              p012exact_sigRank s := by
    native_decide
  exact h s cN5 hrank htp

private theorem p012exact_sig_step_PN3 (s : P012ExactSig)
    (hrank : 0 ≤ p012exact_sigRank s)
    (htp : pn3TpLocal s.cN4.1 s.cN3.1 s.cN2.1) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccPN3 s) ∧
      localFcDelta s.cN4.1 s.cN3.1 s.cN2.1 (TMidVal s.cN4.1 s.cN3.1 s.cN2.1) +
        p012exact_sigRank (p012exact_sigSuccPN3 s) ≤
      p012exact_sigRank s := by
  have h :
      ∀ s : P012ExactSig,
        0 ≤ p012exact_sigRank s →
          pn3TpLocal s.cN4.1 s.cN3.1 s.cN2.1 →
            0 ≤ p012exact_sigRank (p012exact_sigSuccPN3 s) ∧
              localFcDelta s.cN4.1 s.cN3.1 s.cN2.1 (TMidVal s.cN4.1 s.cN3.1 s.cN2.1) +
                p012exact_sigRank (p012exact_sigSuccPN3 s) ≤
              p012exact_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem p012exact_sig_step_PN2 (s : P012ExactSig)
    (hrank : 0 ≤ p012exact_sigRank s)
    (htp : pn2TpLocal s.cN3.1 s.cN2.1 s.cN1.1) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccPN2 s) ∧
      localFcDelta s.cN3.1 s.cN2.1 s.cN1.1 (THighVal s.cN3.1 s.cN2.1 s.cN1.1) +
        p012exact_sigRank (p012exact_sigSuccPN2 s) ≤
      p012exact_sigRank s := by
  have h :
      ∀ s : P012ExactSig,
        0 ≤ p012exact_sigRank s →
          pn2TpLocal s.cN3.1 s.cN2.1 s.cN1.1 →
            0 ≤ p012exact_sigRank (p012exact_sigSuccPN2 s) ∧
              localFcDelta s.cN3.1 s.cN2.1 s.cN1.1 (THighVal s.cN3.1 s.cN2.1 s.cN1.1) +
                p012exact_sigRank (p012exact_sigSuccPN2 s) ≤
              p012exact_sigRank s := by
    native_decide
  exact h s hrank htp

private theorem p012exact_sig_step_PN1 (s : P012ExactSig)
    (hrank : 0 ≤ p012exact_sigRank s) :
    0 ≤ p012exact_sigRank (p012exact_sigSuccPN1 s) ∧
      localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
        p012exact_sigRank (p012exact_sigSuccPN1 s) ≤
      p012exact_sigRank s := by
  have h :
      ∀ s : P012ExactSig,
        0 ≤ p012exact_sigRank s →
          0 ≤ p012exact_sigRank (p012exact_sigSuccPN1 s) ∧
            localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) +
              p012exact_sigRank (p012exact_sigSuccPN1 s) ≤
            p012exact_sigRank s := by
    native_decide
  exact h s hrank

private theorem p012exact_fc_noninc_of_boundary_fixed_tpStep
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

/-

private theorem fin_ne_of_val_ne {n : Nat} {i j : Fin n}
    (h : i.1 ≠ j.1) : i ≠ j := by
  intro hij
  exact h (congrArg Fin.val hij)

private theorem p012exact_sig_step_noninc_idx0
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        p012exact_sigSuccP0 (p012exact_sigOfConfig n hn4 hn9 c) := by
    ext
    · simp [p012exact_sigOfConfig, p012exact_sigSuccP0]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
        cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2BoundaryIdx1]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2BoundaryIdx2]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2Idx3]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2Idx4]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN2]
            omega))
      simpa [p012exact_sigOfConfig, p012exact_sigSuccP0] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN1]
            omega))
  have hlocal := p012exact_sig_step_P0 (p012exact_sigOfConfig n hn4 hn9 c) hrank
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
          p012exact_sigRank (p012exact_sigSuccP0 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccP0, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx0 n hn9)
              (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccP0 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx0 n hn9)
              (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccP0 (p012exact_sigOfConfig n hn4 hn9 c)) =
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
              p012exact_sigRank (p012exact_sigSuccP0 (p012exact_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx0 n hn9))).1
              (c (cup2BoundaryIdx0 n hn9)).1
              (c (right (cup2BoundaryIdx0 n hn9))).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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

private theorem p012exact_sig_step_noninc_idx1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        p012exact_sigSuccP1 (p012exact_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2BoundaryIdx1]))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccP1]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
        cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx1, cup2BoundaryIdx2]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx1, cup2Idx3]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx1, cup2Idx4]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN2]
            omega))
      simpa [p012exact_sigOfConfig, p012exact_sigSuccP1] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN1]
            omega))
  have hlocal := p012exact_sig_step_P1 (p012exact_sigOfConfig n hn4 hn9 c) hrank
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
          p012exact_sigRank (p012exact_sigSuccP1 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccP1, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccP1 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx1 n hn9)
              (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccP1 (p012exact_sigOfConfig n hn4 hn9 c)) =
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
              p012exact_sigRank (p012exact_sigSuccP1 (p012exact_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx1 n hn9))).1
              (c (cup2BoundaryIdx1 n hn9)).1
              (c (right (cup2BoundaryIdx1 n hn9))).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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

private theorem p012exact_sig_step_noninc_idx2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        p012exact_sigSuccP2 (p012exact_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2BoundaryIdx2]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx1, cup2BoundaryIdx2]))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccP2]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx2 n hn9),
        cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9, right_cup2BoundaryIdx2_eq_idx3 n hn9]
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx2, cup2Idx3]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx2, cup2Idx4]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN2]
            omega))
      simpa [p012exact_sigOfConfig, p012exact_sigSuccP2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN1]
            omega))
  have htpLocal :
      p2TpLocal (c (cup2BoundaryIdx1 n hn9)).1 (c (cup2BoundaryIdx2 n hn9)).1
        (c (cup2Idx3 n hn9)).1 := by
    have hlocal := p2TpLocal_of_tpPreserving n hn4 hn9 c htp
    rw [right_cup2BoundaryIdx2_eq_idx3 n hn9] at hlocal
    exact hlocal
  have hlocal := p012exact_sig_step_P2 (p012exact_sigOfConfig n hn4 hn9 c) hrank htpLocal
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
          p012exact_sigRank (p012exact_sigSuccP2 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccP2, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccP2 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdx2 n hn9)
              (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccP2 (p012exact_sigOfConfig n hn4 hn9 c)) =
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
              p012exact_sigRank (p012exact_sigSuccP2 (p012exact_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdx2 n hn9))).1
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (right (cup2BoundaryIdx2 n hn9))).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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

private theorem p012exact_sig_step_noninc_idx3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2Idx3 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2Idx3 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2Idx3 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
  have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
  have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx3]
    omega
  have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx3]
    omega
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2Idx3 n hn9)) =
        p012exact_sigSuccIdx3 (p012exact_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        move_val_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2Idx3]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx1, cup2Idx3]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx2, cup2Idx3]))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccIdx3]
      rw [move_apply_self_val n hn4 c (cup2Idx3 n hn9), cup2OutVal,
        if_neg h0, if_neg h1, if_neg htop, if_neg hhigh,
        left_cup2Idx3_eq_boundaryIdx2 n hn9, right_cup2Idx3_eq_idx4 n hn9]
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by simp [cup2Idx3, cup2Idx4]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2BoundaryIdxN2]
            omega))
      simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3] using
        move_val_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2BoundaryIdxN1]
            omega))
  have htpLocal :
      midTpLocal (c (cup2BoundaryIdx2 n hn9)).1 (c (cup2Idx3 n hn9)).1
        (c (cup2Idx4 n hn9)).1 := by
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2Idx3 n hn9)
      (by simp [cup2Idx3]) (by simp [cup2Idx3]; omega) htp
    rw [left_cup2Idx3_eq_boundaryIdx2 n hn9, right_cup2Idx3_eq_idx4 n hn9] at hlocal
    exact hlocal
  have hlocal := p012exact_sig_step_Idx3 (p012exact_sigOfConfig n hn4 hn9 c) hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2Idx3 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
    have hright : (c (right (cup2Idx3 n hn9))).1 = (c (cup2Idx4 n hn9)).1 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
    have hout' :
        cup2OutVal n (cup2Idx3 n hn9)
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (cup2Idx3 n hn9)).1
          (c (cup2Idx4 n hn9)).1 =
            TMidVal (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have h' :
        localFcDelta (c (left (cup2Idx3 n hn9))).1
            (c (cup2Idx3 n hn9)).1
            (c (right (cup2Idx3 n hn9))).1
            (TMidVal (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1) +
          p012exact_sigRank (p012exact_sigSuccIdx3 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx3, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2Idx3 n hn9))).1
            (c (cup2Idx3 n hn9)).1
            (c (right (cup2Idx3 n hn9))).1
            (cup2OutVal n (cup2Idx3 n hn9)
              (c (left (cup2Idx3 n hn9))).1
              (c (cup2Idx3 n hn9)).1
              (c (right (cup2Idx3 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccIdx3 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2Idx3 n hn9))).1
          (c (cup2Idx3 n hn9)).1
          (c (right (cup2Idx3 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      rw [hleft, hright]
      calc
        (localFcAfter (c (cup2BoundaryIdx2 n hn9)).1
            (c (cup2Idx3 n hn9)).1
            (c (cup2Idx4 n hn9)).1
            (cup2OutVal n (cup2Idx3 n hn9)
              (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccIdx3 (p012exact_sigOfConfig n hn4 hn9 c)) =
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
              p012exact_sigRank (p012exact_sigSuccIdx3 (p012exact_sigOfConfig n hn4 hn9 c))) := by
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
              p012exact_sigRank (p012exact_sigSuccIdx3 (p012exact_sigOfConfig n hn4 hn9 c))) := by
          rw [hout']
        _ ≤ localFcBefore (c (cup2BoundaryIdx2 n hn9)).1
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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

private theorem p012exact_sig_step_noninc_idx4
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2Idx4 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2Idx4 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2Idx4 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2Idx4 n hn9)) =
        p012exact_sigSuccIdx4 (p012exact_sigOfConfig n hn4 hn9 c) c5 := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        move_val_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx0, cup2Idx4]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx1, cup2Idx4]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by simp [cup2BoundaryIdx2, cup2Idx4]))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by simp [cup2Idx3, cup2Idx4]))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5]
      rw [move_apply_self_val n hn4 c (cup2Idx4 n hn9), cup2OutVal,
        if_neg h0, if_neg h1, if_neg htop, if_neg hhigh,
        left_cup2Idx4_eq_idx3 n hn9, right_cup2Idx4_eq_idx5 n hn9]
      simp [c5, stateAsFin3]
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2BoundaryIdxN2]
            omega))
      simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, c5] using
        move_val_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2BoundaryIdxN1]
            omega))
  have htpLocal :
      midTpLocal (c (cup2Idx3 n hn9)).1 (c (cup2Idx4 n hn9)).1 c5.1 := by
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2Idx4 n hn9)
      (by simp [cup2Idx4]) (by simp [cup2Idx4]; omega) htp
    rw [left_cup2Idx4_eq_idx3 n hn9, right_cup2Idx4_eq_idx5 n hn9] at hlocal
    simpa [c5, stateAsFin3] using hlocal
  have hlocal := p012exact_sig_step_Idx4 (p012exact_sigOfConfig n hn4 hn9 c) c5 hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2Idx4 n hn9))).1 = (c (cup2Idx3 n hn9)).1 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
    have hright : (c (right (cup2Idx4 n hn9))).1 = c5.1 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      simp [c5, stateAsFin3]
    have hout' :
        cup2OutVal n (cup2Idx4 n hn9)
          (c (cup2Idx3 n hn9)).1
          (c (cup2Idx4 n hn9)).1 c5.1 =
            TMidVal (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 c5.1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have h' :
        localFcDelta (c (left (cup2Idx4 n hn9))).1
            (c (cup2Idx4 n hn9)).1
            (c (right (cup2Idx4 n hn9))).1
            (TMidVal (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1) +
          p012exact_sigRank (p012exact_sigSuccIdx4 (p012exact_sigOfConfig n hn4 hn9 c) c5) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccIdx4, stateAsFin3, c5, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2Idx4 n hn9))).1
            (c (cup2Idx4 n hn9)).1
            (c (right (cup2Idx4 n hn9))).1
            (cup2OutVal n (cup2Idx4 n hn9)
              (c (left (cup2Idx4 n hn9))).1
              (c (cup2Idx4 n hn9)).1
              (c (right (cup2Idx4 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccIdx4 (p012exact_sigOfConfig n hn4 hn9 c) c5) ≤
        localFcBefore (c (left (cup2Idx4 n hn9))).1
          (c (cup2Idx4 n hn9)).1
          (c (right (cup2Idx4 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      rw [hleft, hright]
      calc
        (localFcAfter (c (cup2Idx3 n hn9)).1
            (c (cup2Idx4 n hn9)).1 c5.1
            (cup2OutVal n (cup2Idx4 n hn9)
              (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 c5.1) : Int) +
            p012exact_sigRank (p012exact_sigSuccIdx4 (p012exact_sigOfConfig n hn4 hn9 c) c5) =
          localFcBefore (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 c5.1 +
            (localFcDelta (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 c5.1
              (cup2OutVal n (cup2Idx4 n hn9)
                (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1 c5.1) +
              p012exact_sigRank (p012exact_sigSuccIdx4 (p012exact_sigOfConfig n hn4 hn9 c) c5)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ = localFcBefore (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 c5.1 +
            (localFcDelta (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 c5.1
              (TMidVal (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1 c5.1) +
              p012exact_sigRank (p012exact_sigSuccIdx4 (p012exact_sigOfConfig n hn4 hn9 c) c5)) := by
          rw [hout']
        _ ≤ localFcBefore (c (cup2Idx3 n hn9)).1
              (c (cup2Idx4 n hn9)).1 c5.1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (cup2Idx3 n hn9)).1
                (c (cup2Idx4 n hn9)).1 c5.1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2Idx4 n hn9),
      cup2Fc_split n hn4 c (cup2Idx4 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2Idx4 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2Idx4 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012exact_sig_step_noninc_idxN4
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2IdxN4 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2IdxN4 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2IdxN4 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2IdxN4 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2IdxN4 n hn9)) =
        p012exact_sigSuccIdxN4 (p012exact_sigOfConfig n hn4 hn9 c) cN5 := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        move_val_apply_ne n hn4 c (cup2IdxN4 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2IdxN4 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2IdxN4 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2IdxN4 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2IdxN4]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2IdxN4 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2IdxN4]
            omega))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5]
      rw [move_apply_self_val n hn4 c (cup2IdxN4 n hn9), cup2OutVal,
        if_neg h0, if_neg h1, if_neg htop, if_neg hhigh,
        left_cup2IdxN4_eq_idxN5 n hn9, right_cup2IdxN4_eq_boundaryIdxN3 n hn9]
      simp [cN5, stateAsFin3]
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2IdxN4 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2IdxN4, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2IdxN4 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2IdxN4, cup2BoundaryIdxN2]
            omega))
      simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, cN5] using
        move_val_apply_ne n hn4 c (cup2IdxN4 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2IdxN4, cup2BoundaryIdxN1]
            omega))
  have htpLocal :
      midTpLocal cN5.1 (c (cup2IdxN4 n hn9)).1 (c (cup2BoundaryIdxN3 n hn9)).1 := by
    have hlocal := midTpLocal_of_tpPreserving n hn4 c (i := cup2IdxN4 n hn9)
      (by
        simp [cup2IdxN4]
        omega)
      (by
        simp [cup2IdxN4]
        omega)
      htp
    rw [left_cup2IdxN4_eq_idxN5 n hn9, right_cup2IdxN4_eq_boundaryIdxN3 n hn9] at hlocal
    simpa [cN5, stateAsFin3] using hlocal
  have hlocal := p012exact_sig_step_IdxN4 (p012exact_sigOfConfig n hn4 hn9 c) cN5 hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2IdxN4 n hn9))).1 = cN5.1 := by
      rw [left_cup2IdxN4_eq_idxN5 n hn9]
      simp [cN5, stateAsFin3]
    have hright : (c (right (cup2IdxN4 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
      rw [right_cup2IdxN4_eq_boundaryIdxN3 n hn9]
    have hout' :
        cup2OutVal n (cup2IdxN4 n hn9)
          cN5.1
          (c (cup2IdxN4 n hn9)).1
          (c (cup2BoundaryIdxN3 n hn9)).1 =
            TMidVal cN5.1
              (c (cup2IdxN4 n hn9)).1
              (c (cup2BoundaryIdxN3 n hn9)).1 := by
      rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have h' :
        localFcDelta (c (left (cup2IdxN4 n hn9))).1
            (c (cup2IdxN4 n hn9)).1
            (c (right (cup2IdxN4 n hn9))).1
            (TMidVal (c (left (cup2IdxN4 n hn9))).1
              (c (cup2IdxN4 n hn9)).1
              (c (right (cup2IdxN4 n hn9))).1) +
          p012exact_sigRank (p012exact_sigSuccIdxN4 (p012exact_sigOfConfig n hn4 hn9 c) cN5) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccIdxN4, stateAsFin3, cN5, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2IdxN4 n hn9))).1
            (c (cup2IdxN4 n hn9)).1
            (c (right (cup2IdxN4 n hn9))).1
            (cup2OutVal n (cup2IdxN4 n hn9)
              (c (left (cup2IdxN4 n hn9))).1
              (c (cup2IdxN4 n hn9)).1
              (c (right (cup2IdxN4 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccIdxN4 (p012exact_sigOfConfig n hn4 hn9 c) cN5) ≤
        localFcBefore (c (left (cup2IdxN4 n hn9))).1
          (c (cup2IdxN4 n hn9)).1
          (c (right (cup2IdxN4 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      rw [hleft, hright]
      calc
        (localFcAfter cN5.1
            (c (cup2IdxN4 n hn9)).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (cup2OutVal n (cup2IdxN4 n hn9)
              cN5.1
              (c (cup2IdxN4 n hn9)).1
              (c (cup2BoundaryIdxN3 n hn9)).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccIdxN4 (p012exact_sigOfConfig n hn4 hn9 c) cN5) =
          localFcBefore cN5.1
              (c (cup2IdxN4 n hn9)).1
              (c (cup2BoundaryIdxN3 n hn9)).1 +
            (localFcDelta cN5.1
              (c (cup2IdxN4 n hn9)).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (cup2OutVal n (cup2IdxN4 n hn9)
                cN5.1
                (c (cup2IdxN4 n hn9)).1
                (c (cup2BoundaryIdxN3 n hn9)).1) +
              p012exact_sigRank (p012exact_sigSuccIdxN4 (p012exact_sigOfConfig n hn4 hn9 c) cN5)) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ = localFcBefore cN5.1
              (c (cup2IdxN4 n hn9)).1
              (c (cup2BoundaryIdxN3 n hn9)).1 +
            (localFcDelta cN5.1
              (c (cup2IdxN4 n hn9)).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (TMidVal cN5.1
                (c (cup2IdxN4 n hn9)).1
                (c (cup2BoundaryIdxN3 n hn9)).1) +
              p012exact_sigRank (p012exact_sigSuccIdxN4 (p012exact_sigOfConfig n hn4 hn9 c) cN5)) := by
          rw [hout']
        _ ≤ localFcBefore cN5.1
              (c (cup2IdxN4 n hn9)).1
              (c (cup2BoundaryIdxN3 n hn9)).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore cN5.1
                (c (cup2IdxN4 n hn9)).1
                (c (cup2BoundaryIdxN3 n hn9)).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2IdxN4 n hn9),
      cup2Fc_split n hn4 c (cup2IdxN4 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2IdxN4 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2IdxN4 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012exact_sig_step_noninc_idxN3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
        p012exact_sigSuccPN3 (p012exact_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2BoundaryIdxN3]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2IdxN4, cup2BoundaryIdxN3]
            omega))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccPN3]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN3 n hn9),
        cup2OutVal_boundaryIdxN3 n hn9, left_cup2BoundaryIdxN3_eq_idxN4 n hn9,
        right_cup2BoundaryIdxN3 n hn9]
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdxN2, cup2BoundaryIdxN3]
            omega))
      simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdxN1, cup2BoundaryIdxN3]
            omega))
  have htpLocal :
      pn3TpLocal (c (cup2IdxN4 n hn9)).1 (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1 := by
    have hlocal := pn3TpLocal_of_tpPreserving n hn4 hn9 c htp
    rw [left_cup2BoundaryIdxN3_eq_idxN4 n hn9] at hlocal
    exact hlocal
  have hlocal := p012exact_sig_step_PN3 (p012exact_sigOfConfig n hn4 hn9 c) hrank htpLocal
  constructor
  · simpa [hsig] using hlocal.1
  · have hleft : (c (left (cup2BoundaryIdxN3 n hn9))).1 = (c (cup2IdxN4 n hn9)).1 := by
      rw [left_cup2BoundaryIdxN3_eq_idxN4 n hn9]
    have hright : (c (right (cup2BoundaryIdxN3 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      rw [right_cup2BoundaryIdxN3 n hn9]
    have h' :
        localFcDelta (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1
            (TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1) +
          p012exact_sigRank (p012exact_sigSuccPN3 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccPN3, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
              (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccPN3 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
              (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccPN3 (p012exact_sigOfConfig n hn4 hn9 c)) =
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
              p012exact_sigRank (p012exact_sigSuccPN3 (p012exact_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (right (cup2BoundaryIdxN3 n hn9))).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left h'
              (localFcBefore (c (left (cup2BoundaryIdxN3 n hn9))).1
                (c (cup2BoundaryIdxN3 n hn9)).1
                (c (right (cup2BoundaryIdxN3 n hn9))).1)
    rw [hsig, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN3 n hn9),
      cup2Fc_split n hn4 c (cup2BoundaryIdxN3 n hn9),
      cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN3 n hn9)]
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hdelta
        (Finset.sum (adjacentComplement (cup2BoundaryIdxN3 n hn9))
          (cup2FrontierBit n hn4 c) : Nat)

private theorem p012exact_sig_step_noninc_idxN2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN2 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
        p012exact_sigSuccPN2 (p012exact_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN2]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN2]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN2]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2BoundaryIdxN2]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2BoundaryIdxN2]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2IdxN4, cup2BoundaryIdxN2]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdxN3, cup2BoundaryIdxN2]
            omega))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccPN2]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN2 n hn9),
        cup2OutVal_boundaryIdxN2 n hn9, left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9]
      simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdxN1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdxN1, cup2BoundaryIdxN2]
            omega))
  have htpLocal :
      pn2TpLocal (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (cup2BoundaryIdxN1 n hn9)).1 := by
    exact pn2TpLocal_of_tpPreserving n hn4 hn9 c htp
  have hlocal := p012exact_sig_step_PN2 (p012exact_sigOfConfig n hn4 hn9 c) hrank htpLocal
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
          p012exact_sigRank (p012exact_sigSuccPN2 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccPN2, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccPN2 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN2 n hn9)
              (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccPN2 (p012exact_sigOfConfig n hn4 hn9 c)) =
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
              p012exact_sigRank (p012exact_sigSuccPN2 (p012exact_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN2 n hn9))).1
              (c (cup2BoundaryIdxN2 n hn9)).1
              (c (right (cup2BoundaryIdxN2 n hn9))).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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

private theorem p012exact_sig_step_noninc_idxN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c))
    (_htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN1 n hn9)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ∧
      (cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) : Int) +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
            (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))) ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  have hsig :
      p012exact_sigOfConfig n hn4 hn9
          (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        p012exact_sigSuccPN1 (p012exact_sigOfConfig n hn4 hn9 c) := by
    ext
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        move_val_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN1]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN1]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN1]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx3, cup2BoundaryIdxN1]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2Idx4, cup2BoundaryIdxN1]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2IdxN4 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2IdxN4, cup2BoundaryIdxN1]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN3 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdxN3, cup2BoundaryIdxN1]
            omega))
    · simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1] using
        stateAsFin3_val_move_eq_of_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9)
          (fin_ne_of_val_ne (by
            simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1]
            omega))
    · simp [p012exact_sigOfConfig, p012exact_sigSuccPN1]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
        cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
  have hlocal := p012exact_sig_step_PN1 (p012exact_sigOfConfig n hn4 hn9 c) hrank
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
          p012exact_sigRank (p012exact_sigSuccPN1 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      simpa [p012exact_sigOfConfig, p012exact_sigSuccPN1, stateAsFin3, hleft, hright] using hlocal.2
    have hdelta :
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
          p012exact_sigRank (p012exact_sigSuccPN1 (p012exact_sigOfConfig n hn4 hn9 c)) ≤
        localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 +
          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
      calc
        (localFcAfter (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1
            (cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1) : Int) +
            p012exact_sigRank (p012exact_sigSuccPN1 (p012exact_sigOfConfig n hn4 hn9 c)) =
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
              p012exact_sigRank (p012exact_sigSuccPN1 (p012exact_sigOfConfig n hn4 hn9 c))) := by
          rw [localFcAfter_eq_localFcBefore_add_localFcDelta]
          omega
        _ ≤ localFcBefore (c (left (cup2BoundaryIdxN1 n hn9))).1
              (c (cup2BoundaryIdxN1 n hn9)).1
              (c (right (cup2BoundaryIdxN1 n hn9))).1 +
            p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
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

private theorem p012exact_sig_step_noninc
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hrank : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c)) :
    0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c') ∧
      (cup2Fc n hn4 c' : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c') ≤
        (cup2Fc n hn4 c : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
  rcases hstep.1.2.2 with ⟨i, hpriv, hmove⟩
  subst c'
  have htpMove : cup2TpPreservingMove n hn4 c i := by
    simpa [cup2TpPreservingMove] using hstep.2
  by_cases hi0v : i.1 = 0
  · have hi : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0v
    subst i
    exact p012exact_sig_step_noninc_idx0 n hn4 hn9 c hrank htpMove
  · by_cases hi1v : i.1 = 1
    · have hi : i = cup2BoundaryIdx1 n hn9 := by
        apply Fin.ext
        simpa [cup2BoundaryIdx1] using hi1v
      subst i
      exact p012exact_sig_step_noninc_idx1 n hn4 hn9 c hrank htpMove
    · by_cases hi2v : i.1 = 2
      · have hi : i = cup2BoundaryIdx2 n hn9 := by
          apply Fin.ext
          simpa [cup2BoundaryIdx2] using hi2v
        subst i
        exact p012exact_sig_step_noninc_idx2 n hn4 hn9 c hrank htpMove
      · by_cases hi3v : i.1 = 3
        · have hi : i = cup2Idx3 n hn9 := by
            apply Fin.ext
            simpa [cup2Idx3] using hi3v
          subst i
          exact p012exact_sig_step_noninc_idx3 n hn4 hn9 c hrank htpMove
        · by_cases hi4v : i.1 = 4
          · have hi : i = cup2Idx4 n hn9 := by
              apply Fin.ext
              simpa [cup2Idx4] using hi4v
            subst i
            exact p012exact_sig_step_noninc_idx4 n hn4 hn9 c hrank htpMove
          · by_cases hiN1v : i.1 + 1 = n
            · have hi : i = cup2BoundaryIdxN1 n hn9 := by
                have hi_val : i.1 = n - 1 := by omega
                apply Fin.ext
                simp [cup2BoundaryIdxN1, hi_val]
              subst i
              exact p012exact_sig_step_noninc_idxN1 n hn4 hn9 c hrank htpMove
            · by_cases hiN2v : i.1 + 2 = n
              · have hi : i = cup2BoundaryIdxN2 n hn9 := by
                  have hi_val : i.1 = n - 2 := by omega
                  apply Fin.ext
                  simp [cup2BoundaryIdxN2, hi_val]
                subst i
                exact p012exact_sig_step_noninc_idxN2 n hn4 hn9 c hrank htpMove
              · by_cases hiN3v : i.1 + 3 = n
                · have hi : i = cup2BoundaryIdxN3 n hn9 := by
                    have hi_val : i.1 = n - 3 := by omega
                    apply Fin.ext
                    simp [cup2BoundaryIdxN3, hi_val]
                  subst i
                  exact p012exact_sig_step_noninc_idxN3 n hn4 hn9 c hrank htpMove
                · by_cases hiN4v : i.1 + 4 = n
                  · have hi : i = cup2IdxN4 n hn9 := by
                      have hi_val : i.1 = n - 4 := by omega
                      apply Fin.ext
                      simp [cup2IdxN4, hi_val]
                    subst i
                    exact p012exact_sig_step_noninc_idxN4 n hn4 hn9 c hrank htpMove
                  · have hi0 : i ≠ cup2BoundaryIdx0 n hn9 := by
                      exact fin_ne_of_val_ne (by simpa [cup2BoundaryIdx0] using hi0v)
                    have hi1 : i ≠ cup2BoundaryIdx1 n hn9 := by
                      exact fin_ne_of_val_ne (by simpa [cup2BoundaryIdx1] using hi1v)
                    have hi2 : i ≠ cup2BoundaryIdx2 n hn9 := by
                      exact fin_ne_of_val_ne (by simpa [cup2BoundaryIdx2] using hi2v)
                    have hi3 : i ≠ cup2Idx3 n hn9 := by
                      exact fin_ne_of_val_ne (by simpa [cup2Idx3] using hi3v)
                    have hi4 : i ≠ cup2Idx4 n hn9 := by
                      exact fin_ne_of_val_ne (by simpa [cup2Idx4] using hi4v)
                    have hiN4 : i ≠ cup2IdxN4 n hn9 := by
                      refine fin_ne_of_val_ne ?_
                      simp [cup2IdxN4]
                      omega
                    have hiN3 : i ≠ cup2BoundaryIdxN3 n hn9 := by
                      refine fin_ne_of_val_ne ?_
                      simp [cup2BoundaryIdxN3]
                      omega
                    have hiN2 : i ≠ cup2BoundaryIdxN2 n hn9 := by
                      refine fin_ne_of_val_ne ?_
                      simp [cup2BoundaryIdxN2]
                      omega
                    have hiN1 : i ≠ cup2BoundaryIdxN1 n hn9 := by
                      refine fin_ne_of_val_ne ?_
                      simp [cup2BoundaryIdxN1]
                      omega
                    have hsig := p012exact_sig_eq_of_move_off_window n hn4 hn9 c i hi0 hi1 hi2 hi3 hi4 hiN4 hiN3 hiN2 hiN1
                    have hleft : 2 < i.1 := by omega
                    have hright : i.1 + 3 < n := by omega
                    have hfixed :
                        cup2BoundaryState n hn4 hn9 (move (cup2System n hn4) c i) =
                          cup2BoundaryState n hn4 hn9 c := by
                      exact cup2BoundaryState_move_eq_of_deep n hn4 hn9 c i hleft hright
                    have hfc_le := p012exact_fc_noninc_of_boundary_fixed_tpStep n hn4 hn9 hstep hfixed
                    have hrank' : 0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
                        (move (cup2System n hn4) c i)) := by
                      simpa [hsig] using hrank
                    have hfc_le' : (cup2Fc n hn4 (move (cup2System n hn4) c i) : Int) ≤ cup2Fc n hn4 c := by
                      exact_mod_cast hfc_le
                    have hle :
                        (cup2Fc n hn4 (move (cup2System n hn4) c i) : Int) +
                          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9
                            (move (cup2System n hn4) c i)) ≤
                        (cup2Fc n hn4 c : Int) +
                          p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) := by
                      rw [hsig]
                      omega
                    exact ⟨hrank', hle⟩

theorem p1_012_exact_src_tpReachable_fc_le_core
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤ cup2Fc n hn4 c := by
  let c3 := stateAsFin3 n hn4 c (cup2Idx3 n hn9)
  let c4 := stateAsFin3 n hn4 c (cup2Idx4 n hn9)
  have hsig0 : p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) = 0 := by
    simpa [p012exact_sigOfConfig, stateAsFin3, c3, c4, hc0, hc1, hc2, hcN4, hcN3, hcN2, hcN1] using
      p012exact_src_start_rank_zero c3 c4
  have hstrong :
      ∀ {x : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c x →
          0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 x) ∧
            (cup2Fc n hn4 x : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 x) ≤
              (cup2Fc n hn4 c : Int) := by
    intro x hreach'
    induction hreach' with
    | refl =>
        exact ⟨by simpa [hsig0], by simpa [hsig0]⟩
    | tail _ hstep ih =>
        rcases p012exact_sig_step_noninc n hn4 hn9 hstep ih.1 with ⟨hrank', hstep'⟩
        exact ⟨hrank', le_trans hstep' ih.2⟩
  have hbound := hstrong hreach
  have hfc_le' : (cup2Fc n hn4 d : Int) ≤ cup2Fc n hn4 c := by
    omega
  exact Int.ofNat_le.mp hfc_le'

theorem p1_012_exact_dst_tpReachable_fc_le_core
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    (hcN4 : (c (cup2IdxN4 n hn9)).1 = 2)
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤
      cup2Fc n hn4 c +
        (if (c (cup2Idx3 n hn9)).1 = 2 ∧ (c (cup2Idx4 n hn9)).1 = 2 then 1 else 0) := by
  let c3 := stateAsFin3 n hn4 c (cup2Idx3 n hn9)
  let c4 := stateAsFin3 n hn4 c (cup2Idx4 n hn9)
  have hsig0 :
      p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 c) =
        if c3.1 = 2 ∧ c4.1 = 2 then 1 else 0 := by
    simpa [p012exact_sigOfConfig, stateAsFin3, c3, c4, hc0, hc1, hc2, hcN4, hcN3, hcN2, hcN1] using
      p012exact_dst_start_rank c3 c4
  have hstrong :
      ∀ {x : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c x →
          0 ≤ p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 x) ∧
            (cup2Fc n hn4 x : Int) + p012exact_sigRank (p012exact_sigOfConfig n hn4 hn9 x) ≤
              (cup2Fc n hn4 c : Int) + (if c3.1 = 2 ∧ c4.1 = 2 then 1 else 0) := by
    intro x hreach'
    induction hreach' with
    | refl =>
        exact ⟨by
          rw [hsig0]
          split_ifs <;> omega,
          by
            rw [hsig0]
            split_ifs <;> omega⟩
    | tail _ hstep ih =>
        rcases p012exact_sig_step_noninc n hn4 hn9 hstep ih.1 with ⟨hrank', hstep'⟩
        exact ⟨hrank', le_trans hstep' ih.2⟩
  have hbound := hstrong hreach
  have hfc_le' :
      (cup2Fc n hn4 d : Int) ≤
        cup2Fc n hn4 c + (if c3.1 = 2 ∧ c4.1 = 2 then 1 else 0) := by
    omega
  simpa [c3, c4, stateAsFin3] using Int.ofNat_le.mp hfc_le'

-/

end LeanMn
