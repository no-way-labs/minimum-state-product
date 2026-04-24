import LeanMn.LowerBound.SmallN.BinaryQ4Word
import LeanMn.LowerBound.SmallN.BinaryQ4Core

namespace LeanMn

/-!
Bridge scratch file connecting the symbolic `Word4` language to the concrete
`LB2222` encoding on `rs2222`.

This file is intentionally not imported by the live path yet.
-/

def cfgFromBits4 (bits : Proc4 → Bool) : Config rs2222 := fun i =>
  ⟨if bits i then 1 else 0, by
    have hm : rs2222.m i = 2 := rs2222_m i
    split <;> omega⟩

def bitsOfCfg4 (c : Config rs2222) : Proc4 → Bool := fun j => (c j).val = 1

@[simp] theorem cfgFromBits4_val (bits : Proc4 → Bool) (j : Proc4) :
    (cfgFromBits4 bits j).val = if bits j then 1 else 0 := by
  simp [cfgFromBits4]

@[simp] theorem bitsOfCfg4_true_iff (c : Config rs2222) (j : Proc4) :
    bitsOfCfg4 c j = true ↔ (c j).val = 1 := by
  simp [bitsOfCfg4]

@[simp] theorem bitsOfCfg4_false_iff (c : Config rs2222) (j : Proc4) :
    bitsOfCfg4 c j = false ↔ (c j).val = 0 := by
  have hlt : (c j).val < 2 := Nat.lt_of_lt_of_eq (c j).isLt (rs2222_m j)
  by_cases h : (c j).val = 1
  · simp [bitsOfCfg4, h]
  · have h0 : (c j).val = 0 := by omega
    simp [bitsOfCfg4, h0]

theorem cfgFromBits4_bitsOfCfg4 (c : Config rs2222) :
    cfgFromBits4 (bitsOfCfg4 c) = c := by
  funext j
  apply Fin.ext
  have hlt : (c j).val < 2 := Nat.lt_of_lt_of_eq (c j).isLt (rs2222_m j)
  by_cases h1 : (c j).val = 1
  · simp [cfgFromBits4, bitsOfCfg4, h1]
  · have h0 : (c j).val = 0 := by omega
    simp [cfgFromBits4, bitsOfCfg4, h0]

theorem bitsOfCfg4_cfgFromBits4 (bits : Proc4 → Bool) :
    bitsOfCfg4 (cfgFromBits4 bits) = bits := by
  funext j
  by_cases h : bits j
  · simp [bitsOfCfg4, cfgFromBits4, h]
  · simp [bitsOfCfg4, cfgFromBits4, h]

theorem cfgFromBits4_flipBit4_bitsOfCfg4 (c : Config rs2222) (j : Proc4) :
    cfgFromBits4 (flipBit4 (bitsOfCfg4 c) j) = flipCfg c j := by
  funext i
  apply Fin.ext
  by_cases hij : i = j
  · subst hij
    have hlt : (c i).val < 2 := Nat.lt_of_lt_of_eq (c i).isLt (rs2222_m i)
    by_cases h1 : (c i).val = 1
    · simp [cfgFromBits4, flipBit4, bitsOfCfg4, flipCfg, h1]
    · have h0 : (c i).val = 0 := by omega
      simp [cfgFromBits4, flipBit4, bitsOfCfg4, flipCfg, h0]
  · have hlt : (c i).val < 2 := Nat.lt_of_lt_of_eq (c i).isLt (rs2222_m i)
    by_cases h1 : (c i).val = 1
    · simp [cfgFromBits4, flipBit4, bitsOfCfg4, flipCfg, hij, h1]
    · have h0 : (c i).val = 0 := by omega
      simp [cfgFromBits4, flipBit4, bitsOfCfg4, flipCfg, hij, h0]

theorem bitsOfCfg4_flipCfg (c : Config rs2222) (j : Proc4) :
    bitsOfCfg4 (flipCfg c j) = flipBit4 (bitsOfCfg4 c) j := by
  symm
  simpa [bitsOfCfg4_cfgFromBits4] using
    congrArg bitsOfCfg4 (cfgFromBits4_flipBit4_bitsOfCfg4 c j)

@[simp] theorem getBit_cfgFromBits4 (bits : Proc4 → Bool) (j : Proc4) :
    getBit (encCfg (cfgFromBits4 bits)).val j.val = if bits j then 1 else 0 := by
  have h := congrArg (fun c => (c j).val) (dec_enc (cfgFromBits4 bits))
  simpa [decCfg, getBit, cfgFromBits4] using h

theorem leftP_eq_left4 (j : Proc4) : leftP j.val = (left4 j).val := by
  simp [leftP, left4]

theorem rightP_eq_right4 (j : Proc4) : rightP j.val = (right4 j).val := by
  simp [rightP, right4]

@[simp] theorem tfKeyNat_cfgFromBits4 (bits : Proc4 → Bool) (j : Proc4) :
    tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val =
      j.val * 8
        + (if bits (left4 j) then 1 else 0) * 4
        + (if bits j then 1 else 0) * 2
        + (if bits (right4 j) then 1 else 0) := by
  unfold tfKeyNat
  rw [leftP_eq_left4, rightP_eq_right4]
  rw [getBit_cfgFromBits4 bits j]
  rw [getBit_cfgFromBits4 bits (left4 j)]
  rw [getBit_cfgFromBits4 bits (right4 j)]

def pathFromWord4 : (Proc4 → Bool) → Word4 → List (Nat × Nat)
  | _bits, [] => []
  | bits, mover :: rest =>
      ((encCfg (cfgFromBits4 bits)).val, mover.val) :: pathFromWord4 (flipBit4 bits mover) rest

@[simp] theorem pathFromWord4_nil (bits : Proc4 → Bool) :
    pathFromWord4 bits [] = [] := rfl

@[simp] theorem pathFromWord4_cons (bits : Proc4 → Bool) (mover : Proc4) (rest : Word4) :
    pathFromWord4 bits (mover :: rest) =
      ((encCfg (cfgFromBits4 bits)).val, mover.val) :: pathFromWord4 (flipBit4 bits mover) rest := rfl

@[simp] theorem pathFromWord4_cons_bitsOfCfg4 (c : Config rs2222) (mover : Proc4) (rest : Word4) :
    pathFromWord4 (bitsOfCfg4 c) (mover :: rest) =
      ((encCfg c).val, mover.val) :: pathFromWord4 (flipBit4 (bitsOfCfg4 c) mover) rest := by
  rw [pathFromWord4_cons]
  simp [cfgFromBits4_bitsOfCfg4]

@[simp] theorem pathFromWord4_cons_cfg (c : Config rs2222) (mover : Proc4) (rest : Word4) :
    pathFromWord4 (bitsOfCfg4 c) (mover :: rest) =
      ((encCfg c).val, mover.val) :: pathFromWord4 (bitsOfCfg4 (flipCfg c mover)) rest := by
  rw [pathFromWord4_cons_bitsOfCfg4]
  simp [bitsOfCfg4_flipCfg]

@[simp] theorem pathFromWord4_length (bits : Proc4 → Bool) (w : Word4) :
    (pathFromWord4 bits w).length = w.length := by
  induction w generalizing bits with
  | nil =>
      simp [pathFromWord4]
  | cons x xs ih =>
      simp [pathFromWord4, ih]

theorem pathFromWord4_congr (bits : Proc4 → Bool) {w₁ w₂ : Word4} (h : w₁ = w₂) :
    pathFromWord4 bits w₁ = pathFromWord4 bits w₂ := by
  subst h
  rfl

theorem prefixState4From_zero (bits : Proc4 → Bool) (w : Word4) :
    prefixState4From bits w 0 = bits := by
  funext j
  simp [prefixState4From]

theorem prefixState4From_succ (bits : Proc4 → Bool) (x : Proc4) (xs : Word4) (t : Nat) :
    prefixState4From bits (x :: xs) (t + 1) = prefixState4From (flipBit4 bits x) xs t := by
  unfold prefixState4From
  simp

theorem moverEntry_head_mem_collectTF_pathFromWord4
    (bits : Proc4 → Bool) (mover : Proc4) (rest : Word4) :
    (tfKeyNat (encCfg (cfgFromBits4 bits)).val mover.val,
      1 - (if bits mover then 1 else 0)) ∈
      collectTF (pathFromWord4 bits (mover :: rest)) := by
  simp [pathFromWord4, collectTF]

theorem nonmoverEntry_head_mem_collectTF_singleton
    (bits : Proc4 → Bool) (mover j : Proc4) (hj : j ≠ mover) :
    (tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val,
      (if bits j then 1 else 0)) ∈
      collectTF [((encCfg (cfgFromBits4 bits)).val, mover.val)] := by
  have hjv : j.val ≠ mover.val := by
    intro h
    apply hj
    exact Fin.ext h
  unfold collectTF
  simp only [List.append_nil, List.mem_cons]
  right
  have hmem :
      (tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val, if bits j then 1 else 0) ∈
        (List.range 4).filterMap
          (fun p =>
            if p == mover.val then none
            else some (tfKeyNat (encCfg (cfgFromBits4 bits)).val p,
              getBit (encCfg (cfgFromBits4 bits)).val p)) := by
    refine List.mem_filterMap.2 ?_
    refine ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
    change (if j.val == mover.val then none else
      some (tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val,
        getBit (encCfg (cfgFromBits4 bits)).val j.val)) =
      some (tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val, if bits j then 1 else 0)
    rw [beq_eq_false_iff_ne.mpr hjv]
    simp
  exact List.mem_append.2 (Or.inl hmem)

theorem nonmoverEntry_head_mem_collectTF_pathFromWord4
    (bits : Proc4 → Bool) (mover j : Proc4) (rest : Word4) (hj : j ≠ mover) :
    (tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val,
      (if bits j then 1 else 0)) ∈
      collectTF (pathFromWord4 bits (mover :: rest)) := by
  have hsingle :
      (tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val,
        (if bits j then 1 else 0)) ∈
      collectTF [((encCfg (cfgFromBits4 bits)).val, mover.val)] :=
    nonmoverEntry_head_mem_collectTF_singleton bits mover j hj
  simpa [pathFromWord4, collectTF] using
    (List.mem_append.2 (Or.inl hsingle) :
      (tfKeyNat (encCfg (cfgFromBits4 bits)).val j.val,
        (if bits j then 1 else 0)) ∈
      collectTF [((encCfg (cfgFromBits4 bits)).val, mover.val)] ++
        collectTF (pathFromWord4 (flipBit4 bits mover) rest))

theorem moverEntry_mem_collectTF_pathFromWord4
    (bits0 : Proc4 → Bool) :
    ∀ w t j,
      moverAt? w t = some j →
      (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w t))).val j.val,
        1 - (if prefixState4From bits0 w t j then 1 else 0)) ∈
        collectTF (pathFromWord4 bits0 w)
  | [], _, _, h => by cases h
  | mover :: rest, 0, j, h => by
      simp only [moverAt?] at h
      injection h with hEq
      subst hEq
      simpa [prefixState4From_zero] using moverEntry_head_mem_collectTF_pathFromWord4 bits0 mover rest
  | mover :: rest, t + 1, j, h => by
      simp only [moverAt?] at h
      have ih :=
        moverEntry_mem_collectTF_pathFromWord4 (bits0 := flipBit4 bits0 mover) rest t j h
      have ih' :
          (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From (flipBit4 bits0 mover) rest t))).val j.val,
            1 - (if prefixState4From (flipBit4 bits0 mover) rest t j then 1 else 0)) ∈
            collectTF (pathFromWord4 (flipBit4 bits0 mover) rest) := ih
      have hstep :
          (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From (flipBit4 bits0 mover) rest t))).val j.val,
            1 - (if prefixState4From (flipBit4 bits0 mover) rest t j then 1 else 0)) ∈
            ((tfKeyNat (encCfg (cfgFromBits4 bits0)).val mover.val,
              1 - getBit (encCfg (cfgFromBits4 bits0)).val mover.val) ::
              (List.range 4).filterMap
                (fun p =>
                  if p == mover.val then none
                  else some (tfKeyNat (encCfg (cfgFromBits4 bits0)).val p,
                    getBit (encCfg (cfgFromBits4 bits0)).val p))) ++
              collectTF (pathFromWord4 (flipBit4 bits0 mover) rest) := by
        exact List.mem_append.2 (Or.inr ih')
      rw [pathFromWord4, collectTF, prefixState4From_succ]
      exact hstep

theorem nonmoverEntry_mem_collectTF_pathFromWord4
    (bits0 : Proc4 → Bool) :
    ∀ w t j,
      t < w.length →
      moverAt? w t ≠ some j →
      (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w t))).val j.val,
        (if prefixState4From bits0 w t j then 1 else 0)) ∈
        collectTF (pathFromWord4 bits0 w)
  | [], t, j, ht, _ => by cases ht
  | mover :: rest, 0, j, _ht, hneq => by
      have hj : j ≠ mover := by
        intro hEq
        apply hneq
        simpa [moverAt?, hEq]
      simpa [prefixState4From_zero] using
        nonmoverEntry_head_mem_collectTF_pathFromWord4 bits0 mover j rest hj
  | mover :: rest, t + 1, j, ht, hneq => by
      have ht' : t < rest.length := by simpa using ht
      have hneq' : moverAt? rest t ≠ some j := by
        simpa [moverAt?] using hneq
      have ih :=
        nonmoverEntry_mem_collectTF_pathFromWord4 (bits0 := flipBit4 bits0 mover) rest t j ht' hneq'
      have ih' :
          (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From (flipBit4 bits0 mover) rest t))).val j.val,
            (if prefixState4From (flipBit4 bits0 mover) rest t j then 1 else 0)) ∈
            collectTF (pathFromWord4 (flipBit4 bits0 mover) rest) := ih
      have hstep :
          (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From (flipBit4 bits0 mover) rest t))).val j.val,
            (if prefixState4From (flipBit4 bits0 mover) rest t j then 1 else 0)) ∈
            ((tfKeyNat (encCfg (cfgFromBits4 bits0)).val mover.val,
              1 - getBit (encCfg (cfgFromBits4 bits0)).val mover.val) ::
              (List.range 4).filterMap
                (fun p =>
                  if p == mover.val then none
                  else some (tfKeyNat (encCfg (cfgFromBits4 bits0)).val p,
                    getBit (encCfg (cfgFromBits4 bits0)).val p))) ++
              collectTF (pathFromWord4 (flipBit4 bits0 mover) rest) := by
        exact List.mem_append.2 (Or.inr ih')
      rw [pathFromWord4, collectTF, prefixState4From_succ]
      exact hstep

theorem tfKeyNat_prefixState4From_eq_of_sigEq
    (bits0 : Proc4 → Bool) (w : Word4) (j : Proc4) (t u : Nat)
    (hsig : sig4From bits0 w t j = sig4From bits0 w u j) :
    tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w t))).val j.val =
      tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w u))).val j.val := by
  let pack : Bool × Bool × Bool → Nat :=
    fun s => j.val * 8 + (if s.1 then 1 else 0) * 4 + (if s.2.1 then 1 else 0) * 2 + (if s.2.2 then 1 else 0)
  simpa [pack, tfKeyNat_cfgFromBits4, sig4From] using congrArg pack hsig

theorem hasTFConflict_of_mem_mem
    (constraints : List (Nat × Nat)) (k v₁ v₂ : Nat)
    (hm₁ : (k, v₁) ∈ constraints) (hm₂ : (k, v₂) ∈ constraints) (hneq : v₁ ≠ v₂) :
    hasTFConflict constraints = true := by
  unfold hasTFConflict
  apply List.any_eq_true.2
  refine ⟨(k, v₁), hm₁, ?_⟩
  apply List.any_eq_true.2
  refine ⟨(k, v₂), hm₂, ?_⟩
  have hbeq : (v₁ == v₂) = false := beq_eq_false_iff_ne.mpr hneq
  simp [hbeq]

theorem sigConflict4From_imp_isTFBlocked
    (bits0 : Proc4 → Bool) {w : Word4} (h : sigConflict4From bits0 w) :
    isTFBlocked (pathFromWord4 bits0 w) = true := by
  rcases h with ⟨j, t, u, htu, hu, hsig, hx⟩
  have ht : t < w.length := by omega
  have hkey := tfKeyNat_prefixState4From_eq_of_sigEq bits0 w j t u hsig
  have hmid :
      prefixState4From bits0 w t j = prefixState4From bits0 w u j := by
    exact congrArg (Prod.fst ∘ Prod.snd) hsig
  by_cases htj : moverAt? w t = some j
  · have huj : moverAt? w u ≠ some j := by
      simpa [Xor', htj] using hx
    have hmover :
        (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w t))).val j.val,
          1 - (if prefixState4From bits0 w t j then 1 else 0)) ∈
          collectTF (pathFromWord4 bits0 w) :=
      moverEntry_mem_collectTF_pathFromWord4 bits0 w t j htj
    have hnonmover :
        (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w t))).val j.val,
          (if prefixState4From bits0 w u j then 1 else 0)) ∈
          collectTF (pathFromWord4 bits0 w) := by
      simpa [hkey] using
        nonmoverEntry_mem_collectTF_pathFromWord4 bits0 w u j hu huj
    have hneqv :
        1 - (if prefixState4From bits0 w t j then 1 else 0) ≠
          (if prefixState4From bits0 w u j then 1 else 0) := by
      rw [hmid]
      by_cases hb : prefixState4From bits0 w u j
      · simp [hb]
      · simp [hb]
    unfold isTFBlocked
    exact hasTFConflict_of_mem_mem _ _ _ _ hmover hnonmover hneqv
  · have huj : moverAt? w u = some j := by
      simpa [Xor', htj] using hx
    have hnonmover :
        (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w t))).val j.val,
          (if prefixState4From bits0 w t j then 1 else 0)) ∈
          collectTF (pathFromWord4 bits0 w) :=
      nonmoverEntry_mem_collectTF_pathFromWord4 bits0 w t j ht htj
    have hmover :
        (tfKeyNat (encCfg (cfgFromBits4 (prefixState4From bits0 w t))).val j.val,
          1 - (if prefixState4From bits0 w u j then 1 else 0)) ∈
          collectTF (pathFromWord4 bits0 w) := by
      simpa [hkey] using
        moverEntry_mem_collectTF_pathFromWord4 bits0 w u j huj
    have hneqv :
        (if prefixState4From bits0 w t j then 1 else 0) ≠
          1 - (if prefixState4From bits0 w u j then 1 else 0) := by
      rw [hmid]
      by_cases hb : prefixState4From bits0 w u j
      · simp [hb]
      · simp [hb]
    unfold isTFBlocked
    exact hasTFConflict_of_mem_mem _ _ _ _ hnonmover hmover hneqv

theorem sigConflict4_imp_isTFBlocked
    (bits0 : Proc4 → Bool) {w : Word4} (h : sigConflict4 w) :
    isTFBlocked (pathFromWord4 bits0 w) = true :=
  sigConflict4From_imp_isTFBlocked bits0 (sigConflict4.lift bits0 h)

theorem isTFBlocked_forwardSweepWord4_of_ne
    (bits0 : Proc4 → Bool) (σ τ : Proc4) (h : τ ≠ σ) :
    isTFBlocked (pathFromWord4 bits0 (forwardSweepWord4 σ τ)) = true :=
  sigConflict4_imp_isTFBlocked bits0 (sigConflict4_forwardSweepWord4_of_ne σ τ h)

theorem isTFBlocked_reverseSweepWord4
    (bits0 : Proc4 → Bool) (σ τ : Proc4) :
    isTFBlocked (pathFromWord4 bits0 (reverseSweepWord4 σ τ)) = true :=
  sigConflict4_imp_isTFBlocked bits0 (sigConflict4_reverseSweepWord4 σ τ)

theorem isTFBlocked_of_not_nodup_first_four
    (bits0 : Proc4 → Bool)
    {a b c d : Proc4} {rest : Word4}
    (hrest : rest ≠ [])
    (hsimple : SimpleWord4 (a :: b :: c :: d :: rest))
    (hbal : BalancedWord4 (a :: b :: c :: d :: rest))
    (hnodup : ¬ List.Nodup [a, b, c, d]) :
    isTFBlocked (pathFromWord4 bits0 (a :: b :: c :: d :: rest)) = true :=
  sigConflict4_imp_isTFBlocked bits0
    (sigConflict4_of_not_nodup_first_four hrest hsimple hbal hnodup)

theorem first_four_sweep_or_reverse_of_isTFBlocked_false
    (bits0 : Proc4 → Bool)
    {a b c d : Proc4} {rest : Word4}
    (hrest : rest ≠ [])
    (hsimple : SimpleWord4 (a :: b :: c :: d :: rest))
    (hbal : BalancedWord4 (a :: b :: c :: d :: rest))
    (hfalse : isTFBlocked (pathFromWord4 bits0 (a :: b :: c :: d :: rest)) = false) :
    (b = right4 a ∧ c = anti4 a ∧ d = left4 a) ∨
      (b = left4 a ∧ c = anti4 a ∧ d = right4 a) := by
  have hno : ¬ sigConflict4 (a :: b :: c :: d :: rest) := by
    intro hs
    have htrue := sigConflict4_imp_isTFBlocked bits0 hs
    rw [hfalse] at htrue
    contradiction
  exact first_four_sweep_or_reverse_of_no_sigConflict hrest hsimple hbal hno

theorem eight_word_sweep_of_isTFBlocked_false
    (bits0 : Proc4 → Bool)
    {a b c d e f g h : Proc4}
    (hsimple : SimpleWord4 [a, b, c, d, e, f, g, h])
    (hbal : BalancedWord4 [a, b, c, d, e, f, g, h])
    (hfalse : isTFBlocked (pathFromWord4 bits0 [a, b, c, d, e, f, g, h]) = false) :
    ([a, b, c, d, e, f, g, h] = forwardSweepWord4 a a) ∨
      ([a, b, c, d, e, f, g, h] = [a, left4 a, anti4 a, right4 a, a, left4 a, anti4 a, right4 a]) := by
  have hno : ¬ sigConflict4 [a, b, c, d, e, f, g, h] := by
    intro hs
    have htrue := sigConflict4_imp_isTFBlocked bits0 hs
    rw [hfalse] at htrue
    contradiction
  have hrest : [e, f, g, h] ≠ [] := by simp
  exact eight_word_sweep_of_no_sigConflict hrest hsimple hbal hno

theorem pathFromWord4_eight_word_sweep_of_isTFBlocked_false
    (bits0 : Proc4 → Bool)
    {a b c d e f g h : Proc4}
    (hsimple : SimpleWord4 [a, b, c, d, e, f, g, h])
    (hbal : BalancedWord4 [a, b, c, d, e, f, g, h])
    (hfalse : isTFBlocked (pathFromWord4 bits0 [a, b, c, d, e, f, g, h]) = false) :
    (pathFromWord4 bits0 [a, b, c, d, e, f, g, h] = pathFromWord4 bits0 (forwardSweepWord4 a a)) ∨
      (pathFromWord4 bits0 [a, b, c, d, e, f, g, h] =
        pathFromWord4 bits0 [a, left4 a, anti4 a, right4 a, a, left4 a, anti4 a, right4 a]) := by
  rcases eight_word_sweep_of_isTFBlocked_false (bits0 := bits0) (a := a) (b := b) (c := c) (d := d)
    (e := e) (f := f) (g := g) (h := h) hsimple hbal hfalse with hw | hw
  · left
    exact pathFromWord4_congr bits0 hw
  · right
    exact pathFromWord4_congr bits0 hw

end LeanMn
