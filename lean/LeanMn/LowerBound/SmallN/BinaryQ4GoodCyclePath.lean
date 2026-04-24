import LeanMn.LowerBound.SmallN.BinaryQ4LBBridge
import LeanMn.LowerBound.GoodCycleBasics

namespace LeanMn

variable {f : TransFn rs2222}

noncomputable def gcCfgAt (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k ≤ gc.configs.length) : Config rs2222 :=
  if hlt : k < gc.configs.length then gc.configs.get ⟨k, hlt⟩
  else gc.configs.get ⟨0, gc.configs_length_pos⟩

@[simp] theorem gcCfgAt_of_lt (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length) :
    gcCfgAt gc k (Nat.le_of_lt hk) = gc.configs.get ⟨k, hk⟩ := by
  simp [gcCfgAt, hk]

@[simp] theorem gcCfgAt_of_ge (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : gc.configs.length ≤ k) (hk' : k ≤ gc.configs.length) :
    gcCfgAt gc k hk' = gc.configs.get ⟨0, gc.configs_length_pos⟩ := by
  simp [gcCfgAt, Nat.not_lt.mpr hk]

theorem gcCfgAt_succ (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length) :
    flipCfg (gcCfgAt gc k (Nat.le_of_lt hk)) (gc.moverAt ⟨k, hk⟩) =
      gcCfgAt gc (k + 1) (by omega) := by
  rw [gcCfgAt_of_lt gc k hk]
  rw [← move_eq_flipCfg (gc.moverAt_privileged ⟨k, hk⟩)]
  by_cases hk1 : k + 1 < gc.configs.length
  · rw [gcCfgAt_of_lt gc (k + 1) hk1]
    have hnext : nextIndex gc.configs ⟨k, hk⟩ = ⟨k + 1, hk1⟩ := by
      apply Fin.ext
      simp [nextIndex, Nat.mod_eq_of_lt hk1]
    rw [← gc.step_eq_move ⟨k, hk⟩, hnext]
  · have hk1eq : k + 1 = gc.configs.length := by omega
    rw [gcCfgAt_of_ge gc (k + 1) (by omega) (by omega)]
    have hnext : nextIndex gc.configs ⟨k, hk⟩ = ⟨0, gc.configs_length_pos⟩ := by
      apply Fin.ext
      simp [nextIndex, hk1eq]
    rw [← gc.step_eq_move ⟨k, hk⟩, hnext]

noncomputable def gcWordFrom (gc : GoodCycle ⟨rs2222, f⟩) :
    (k rem : Nat) → k + rem ≤ gc.configs.length → Word4
  | _, 0, _ => []
  | k, rem + 1, hkr =>
      gc.moverAt ⟨k, by omega⟩ :: gcWordFrom gc (k + 1) rem (by omega)

@[simp] theorem gcWordFrom_length (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + rem ≤ gc.configs.length),
      (gcWordFrom gc k rem hkr).length = rem
  | _, 0, _ => by simp [gcWordFrom]
  | k, rem + 1, hkr => by
      simp [gcWordFrom, gcWordFrom_length]

theorem gcWordFrom_snoc (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 1) ≤ gc.configs.length),
      gcWordFrom gc k (rem + 1) hkr =
        gcWordFrom gc k rem (by omega) ++ ([gc.moverAt ⟨k + rem, by omega⟩] : Word4)
  | k, 0, hkr => by
      simp [gcWordFrom]
  | k, rem + 1, hkr => by
      have htail := gcWordFrom_snoc gc (k + 1) rem (by omega)
      simpa [gcWordFrom, List.cons_append, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using htail

theorem gcWordFrom_append (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem₁ rem₂ : Nat) (hkr : k + (rem₁ + rem₂) ≤ gc.configs.length),
      gcWordFrom gc k (rem₁ + rem₂) hkr =
        gcWordFrom gc k rem₁ (by omega) ++
          gcWordFrom gc (k + rem₁) rem₂ (by omega)
  | k, 0, rem₂, hkr => by
      simp [gcWordFrom]
  | k, rem₁ + 1, rem₂, hkr => by
      have htail := gcWordFrom_append gc (k + 1) rem₁ rem₂ (by omega)
      simpa [gcWordFrom, List.cons_append, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using htail

theorem gcWordFrom_prefix_four (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 4) ≤ gc.configs.length),
      gcWordFrom gc k (rem + 4) hkr =
        ([gc.moverAt ⟨k, by omega⟩,
          gc.moverAt ⟨k + 1, by omega⟩,
          gc.moverAt ⟨k + 2, by omega⟩,
          gc.moverAt ⟨k + 3, by omega⟩] : Word4) ++
          gcWordFrom gc (k + 4) rem (by omega)
  | k, rem, hkr => by
      simp [gcWordFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem gcWordFrom_prefix_five (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 5) ≤ gc.configs.length),
      gcWordFrom gc k (rem + 5) hkr =
        ([gc.moverAt ⟨k, by omega⟩,
          gc.moverAt ⟨k + 1, by omega⟩,
          gc.moverAt ⟨k + 2, by omega⟩,
          gc.moverAt ⟨k + 3, by omega⟩,
          gc.moverAt ⟨k + 4, by omega⟩] : Word4) ++
          gcWordFrom gc (k + 5) rem (by omega)
  | k, rem, hkr => by
      simp [gcWordFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem gcWordFrom_prefix_seven (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 7) ≤ gc.configs.length),
      gcWordFrom gc k (rem + 7) hkr =
        ([gc.moverAt ⟨k, by omega⟩,
          gc.moverAt ⟨k + 1, by omega⟩,
          gc.moverAt ⟨k + 2, by omega⟩,
          gc.moverAt ⟨k + 3, by omega⟩,
          gc.moverAt ⟨k + 4, by omega⟩,
          gc.moverAt ⟨k + 5, by omega⟩,
          gc.moverAt ⟨k + 6, by omega⟩] : Word4) ++
          gcWordFrom gc (k + 7) rem (by omega)
  | k, rem, hkr => by
      simp [gcWordFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem gcWordFrom_prefix_nine (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 9) ≤ gc.configs.length),
      gcWordFrom gc k (rem + 9) hkr =
        ([gc.moverAt ⟨k, by omega⟩,
          gc.moverAt ⟨k + 1, by omega⟩,
          gc.moverAt ⟨k + 2, by omega⟩,
          gc.moverAt ⟨k + 3, by omega⟩,
          gc.moverAt ⟨k + 4, by omega⟩,
          gc.moverAt ⟨k + 5, by omega⟩,
          gc.moverAt ⟨k + 6, by omega⟩,
          gc.moverAt ⟨k + 7, by omega⟩,
          gc.moverAt ⟨k + 8, by omega⟩] : Word4) ++
          gcWordFrom gc (k + 9) rem (by omega)
  | k, rem, hkr => by
      simp [gcWordFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem gcWordFrom_prefix_eleven (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 11) ≤ gc.configs.length),
      gcWordFrom gc k (rem + 11) hkr =
        ([gc.moverAt ⟨k, by omega⟩,
          gc.moverAt ⟨k + 1, by omega⟩,
          gc.moverAt ⟨k + 2, by omega⟩,
          gc.moverAt ⟨k + 3, by omega⟩,
          gc.moverAt ⟨k + 4, by omega⟩,
          gc.moverAt ⟨k + 5, by omega⟩,
          gc.moverAt ⟨k + 6, by omega⟩,
          gc.moverAt ⟨k + 7, by omega⟩,
          gc.moverAt ⟨k + 8, by omega⟩,
          gc.moverAt ⟨k + 9, by omega⟩,
          gc.moverAt ⟨k + 10, by omega⟩] : Word4) ++
          gcWordFrom gc (k + 11) rem (by omega)
  | k, rem, hkr => by
      simp [gcWordFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem gcWordFrom_prefix_thirteen (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 13) ≤ gc.configs.length),
      gcWordFrom gc k (rem + 13) hkr =
        ([gc.moverAt ⟨k, by omega⟩,
          gc.moverAt ⟨k + 1, by omega⟩,
          gc.moverAt ⟨k + 2, by omega⟩,
          gc.moverAt ⟨k + 3, by omega⟩,
          gc.moverAt ⟨k + 4, by omega⟩,
          gc.moverAt ⟨k + 5, by omega⟩,
          gc.moverAt ⟨k + 6, by omega⟩,
          gc.moverAt ⟨k + 7, by omega⟩,
          gc.moverAt ⟨k + 8, by omega⟩,
          gc.moverAt ⟨k + 9, by omega⟩,
          gc.moverAt ⟨k + 10, by omega⟩,
          gc.moverAt ⟨k + 11, by omega⟩,
          gc.moverAt ⟨k + 12, by omega⟩] : Word4) ++
          gcWordFrom gc (k + 13) rem (by omega)
  | k, rem, hkr => by
      simp [gcWordFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

noncomputable def gcPathFrom (gc : GoodCycle ⟨rs2222, f⟩) :
    (k rem : Nat) → k + rem ≤ gc.configs.length → List (Nat × Nat)
  | _, 0, _ => []
  | k, rem + 1, hkr =>
      ((encCfg (gc.configs.get ⟨k, by omega⟩)).val, (gc.moverAt ⟨k, by omega⟩).val) ::
        gcPathFrom gc (k + 1) rem (by omega)

noncomputable def gcEntryAt (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length) : Nat × Nat :=
  ((encCfg (gc.configs.get ⟨k, hk⟩)).val, (gc.moverAt ⟨k, hk⟩).val)

theorem gcPathFrom_eq_pathFromWord4 (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + rem ≤ gc.configs.length),
      gcPathFrom gc k rem hkr =
        pathFromWord4 (bitsOfCfg4 (gcCfgAt gc k (by omega)))
          (gcWordFrom gc k rem hkr)
  | k, 0, hkr => by
      simp [gcPathFrom, gcWordFrom, pathFromWord4]
  | k, rem + 1, hkr => by
      have hk : k < gc.configs.length := by omega
      simp [gcPathFrom, gcWordFrom, gcCfgAt_of_lt gc k hk]
      constructor
      · simp [cfgFromBits4_bitsOfCfg4]
      · have hbits :
            flipBit4 (bitsOfCfg4 (gc.configs.get ⟨k, hk⟩)) (gc.moverAt ⟨k, hk⟩) =
              bitsOfCfg4 (flipCfg (gc.configs.get ⟨k, hk⟩) (gc.moverAt ⟨k, hk⟩)) := by
          simpa using (bitsOfCfg4_flipCfg (gc.configs.get ⟨k, hk⟩) (gc.moverAt ⟨k, hk⟩)).symm
        change gcPathFrom gc (k + 1) rem (by omega) =
          pathFromWord4
            (flipBit4 (bitsOfCfg4 (gc.configs.get ⟨k, hk⟩)) (gc.moverAt ⟨k, hk⟩))
            (gcWordFrom gc (k + 1) rem (by omega))
        rw [hbits, ← gcCfgAt_of_lt gc k hk, gcCfgAt_succ gc k hk]
        simpa using gcPathFrom_eq_pathFromWord4 gc (k + 1) rem (by omega)

theorem gcCfgAt_eq_cfgFromBits4_prefixState4From (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + rem ≤ gc.configs.length) (t : Nat) (ht : t ≤ rem),
      gcCfgAt gc (k + t) (by omega) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc k (by omega)))
            (gcWordFrom gc k rem hkr) t)
  | k, rem, hkr, 0, ht => by
      simp [prefixState4From_zero, cfgFromBits4_bitsOfCfg4]
  | k, 0, hkr, t + 1, ht => by
      omega
  | k, rem + 1, hkr, t + 1, ht => by
      have hk : k < gc.configs.length := by omega
      have hbits :
          bitsOfCfg4 (gcCfgAt gc (k + 1) (by omega)) =
            flipBit4 (bitsOfCfg4 (gcCfgAt gc k (by omega))) (gc.moverAt ⟨k, hk⟩) := by
        rw [← gcCfgAt_succ gc k hk]
        exact bitsOfCfg4_flipCfg _ _
      calc
        gcCfgAt gc (k + (t + 1)) (by omega) =
            gcCfgAt gc ((k + 1) + t) (by omega) := by
              have hkt : k + (t + 1) = (k + 1) + t := by omega
              by_cases hlt : k + (t + 1) < gc.configs.length
              · simp [gcCfgAt, hlt, hkt]
              · have hge : gc.configs.length ≤ k + (t + 1) := Nat.le_of_not_lt hlt
                simp [gcCfgAt, Nat.not_lt.mpr hge, hkt]
        _ =
            cfgFromBits4
              (prefixState4From (bitsOfCfg4 (gcCfgAt gc (k + 1) (by omega)))
                (gcWordFrom gc (k + 1) rem (by omega)) t) :=
            gcCfgAt_eq_cfgFromBits4_prefixState4From gc (k + 1) rem (by omega) t (by omega)
        _ =
            cfgFromBits4
              (prefixState4From
                (flipBit4 (bitsOfCfg4 (gcCfgAt gc k (by omega))) (gc.moverAt ⟨k, hk⟩))
                (gcWordFrom gc (k + 1) rem (by omega)) t) := by
            rw [hbits]
        _ =
            cfgFromBits4
              (prefixState4From (bitsOfCfg4 (gcCfgAt gc k (by omega)))
                (gcWordFrom gc k (rem + 1) hkr) (t + 1)) := by
            simp [gcWordFrom, prefixState4From_succ]

@[simp] theorem gcPathFrom_snoc (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + (rem + 1) ≤ gc.configs.length),
      gcPathFrom gc k (rem + 1) hkr =
        gcPathFrom gc k rem (by omega) ++ [gcEntryAt gc (k + rem) (by omega)]
  | k, 0, hkr => by
      simp [gcPathFrom, gcEntryAt]
  | k, rem + 1, hkr => by
      have htail := gcPathFrom_snoc gc (k + 1) rem (by omega)
      simpa [gcPathFrom, gcEntryAt, List.cons_append, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using htail

noncomputable def gcPathPrefix (gc : GoodCycle ⟨rs2222, f⟩) :
    (k : Nat) → k ≤ gc.configs.length → List (Nat × Nat)
  | 0, _ => []
  | k + 1, hk =>
      gcPathPrefix gc k (by omega) ++ [gcEntryAt gc k (by omega)]

@[simp] theorem gcPathPrefix_eq_gcPathFrom_zero (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k : Nat) (hk : k ≤ gc.configs.length),
      gcPathPrefix gc k hk = gcPathFrom gc 0 k (by simpa using hk)
  | 0, hk => by
      simp [gcPathPrefix, gcPathFrom]
  | k + 1, hk => by
      rw [gcPathPrefix]
      rw [gcPathPrefix_eq_gcPathFrom_zero gc k (by omega)]
      simpa using gcPathFrom_snoc gc 0 k (by simpa using hk)

end LeanMn
