import LeanMn.Dijkstra

namespace LeanMn

def rs2222 : RingSpec where
  n := 4
  n_ge_4 := le_refl 4
  m := fun _ => 2
  m_pos := fun _ => le_refl 2

@[simp] theorem rs2222_n : rs2222.n = 4 := rfl
@[simp] theorem rs2222_m (i : Fin 4) : rs2222.m i = 2 := rfl

theorem stateProduct_rs2222 : stateProduct rs2222 = 16 := by native_decide

@[inline] def getBit (cfg j : Nat) : Nat := (cfg >>> j) &&& 1
@[inline] def flipBit (cfg j : Nat) : Nat := cfg ^^^ (1 <<< j)
@[inline] def leftP (j : Nat) : Nat := (j + 3) % 4
@[inline] def rightP (j : Nat) : Nat := (j + 1) % 4

@[inline] def tfKeyNat (cfg proc : Nat) : Nat :=
  proc * 8 + getBit cfg (leftP proc) * 4 + getBit cfg proc * 2 + getBit cfg (rightP proc)

def collectTF : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (cfg, proc) :: rest =>
    let mc := (tfKeyNat cfg proc, 1 - getBit cfg proc)
    let nmc := (List.range 4).filterMap (fun p =>
      if p == proc then none else some (tfKeyNat cfg p, getBit cfg p))
    mc :: nmc ++ collectTF rest

def hasTFConflict (constraints : List (Nat × Nat)) : Bool :=
  constraints.any (fun (k1, v1) =>
    constraints.any (fun (k2, v2) => k1 == k2 && !(v1 == v2)))

def isTFBlocked (cycle : List (Nat × Nat)) : Bool :=
  hasTFConflict (collectTF cycle)

def assocLookup (key : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (k, v) :: rest => if k == key then some v else assocLookup key rest

def buildTF : List (Nat × Nat) → List (Nat × Nat) → Option (List (Nat × Nat))
  | [], acc => some acc
  | (k, v) :: rest, acc =>
    match assocLookup k acc with
    | some v' => if v == v' then buildTF rest acc else none
    | none => buildTF rest ((k, v) :: acc)

theorem binary_priv_val {sys : System} {c : Config sys.rs} {i : Fin sys.rs.n}
    (hpriv : privileged sys c i) (hm : sys.rs.m i = 2) :
    (sys.f i (c (left i)) (c i) (c (right i))).val = 1 - (c i).val := by
  unfold privileged at hpriv
  have hfi : (sys.f i (c (left i)) (c i) (c (right i))).val < 2 :=
    Nat.lt_of_lt_of_eq (sys.f i (c (left i)) (c i) (c (right i))).isLt hm
  have hci : (c i).val < 2 := Nat.lt_of_lt_of_eq (c i).isLt hm
  have hne : (sys.f i (c (left i)) (c i) (c (right i))).val ≠ (c i).val :=
    fun heq => hpriv (Fin.ext heq)
  omega

def encCfg (c : Config rs2222) : Fin 16 := by
  refine ⟨(c ⟨0, by decide⟩).val + (c ⟨1, by decide⟩).val * 2 +
         (c ⟨2, by decide⟩).val * 4 + (c ⟨3, by decide⟩).val * 8, ?_⟩
  have h0 : (c (⟨0, by decide⟩ : Fin 4)).val < 2 :=
    Nat.lt_of_lt_of_eq (c _).isLt (rs2222_m _)
  have h1 : (c (⟨1, by decide⟩ : Fin 4)).val < 2 :=
    Nat.lt_of_lt_of_eq (c _).isLt (rs2222_m _)
  have h2 : (c (⟨2, by decide⟩ : Fin 4)).val < 2 :=
    Nat.lt_of_lt_of_eq (c _).isLt (rs2222_m _)
  have h3 : (c (⟨3, by decide⟩ : Fin 4)).val < 2 :=
    Nat.lt_of_lt_of_eq (c _).isLt (rs2222_m _)
  omega

def decCfg (n : Fin 16) : Config rs2222 := fun i =>
  ⟨(n.val >>> i.val) &&& 1, by
    simp only [rs2222]
    have : (n.val >>> i.val) &&& 1 ≤ 1 := Nat.and_le_right
    omega⟩

theorem dec_enc : ∀ c : Config rs2222, decCfg (encCfg c) = c := by native_decide
theorem enc_dec : ∀ n : Fin 16, encCfg (decCfg n) = n := by native_decide

theorem config_card_rs2222 : Fintype.card (Config rs2222) = 16 := by
  let e : Config rs2222 ≃ Fin 16 :=
    { toFun := encCfg
      invFun := decCfg
      left_inv := dec_enc
      right_inv := enc_dec }
  simpa using Fintype.card_congr e

def flipCfg (c : Config rs2222) (i : Fin 4) : Config rs2222 := fun j =>
  if j = i then ⟨1 - (c i).val, by have := (c i).isLt; simp [rs2222]; omega⟩
  else c j

theorem encCfg_flipCfg :
    ∀ (c : Config rs2222) (i : Fin 4),
      (encCfg (flipCfg c i)).val = (encCfg c).val ^^^ (1 <<< i.val) := by
  native_decide

theorem move_eq_flipCfg {f : TransFn rs2222} {c : Config rs2222} {i : Fin 4}
    (hp : privileged ⟨rs2222, f⟩ c i) :
    move ⟨rs2222, f⟩ c i = flipCfg c i := by
  have hbpv := binary_priv_val hp (rs2222_m i)
  funext j
  unfold move flipCfg
  by_cases hji : j = i
  · subst hji
    simp only [dif_pos rfl, ite_true]
    exact Fin.ext hbpv
  · rw [dif_neg hji, if_neg hji]

theorem encCfg_move {f : TransFn rs2222} {c : Config rs2222} {i : Fin 4}
    (hp : privileged ⟨rs2222, f⟩ c i) :
    (encCfg (move ⟨rs2222, f⟩ c i)).val = (encCfg c).val ^^^ (1 <<< i.val) := by
  rw [move_eq_flipCfg hp, encCfg_flipCfg]

theorem encCfg_injective : Function.Injective (encCfg) := by
  intro a b h
  have := congrArg decCfg h
  rwa [dec_enc, dec_enc] at this

theorem leftP_eq_left (j : Fin 4) : leftP j.val = (left j : Fin 4).val := by
  simp [leftP, left, rs2222]

theorem rightP_eq_right (j : Fin 4) : rightP j.val = (right j : Fin 4).val := by
  simp [rightP, right, rs2222]

theorem getBit_encCfg (c : Config rs2222) (j : Fin 4) :
    getBit (encCfg c).val j.val = (c j).val := by
  have h := congrArg (fun cfg => cfg j) (dec_enc c)
  simp only [decCfg] at h
  exact congrArg Fin.val h

end LeanMn
