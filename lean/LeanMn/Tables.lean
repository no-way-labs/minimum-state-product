import LeanMn.Basic

namespace LeanMn

inductive PositionClass
  | bot
  | low
  | mid
  | high
  | top
  deriving DecidableEq, Repr

def PositionClass.leftStates : PositionClass → Nat
  | .bot => 2
  | .low => 2
  | .mid => 3
  | .high => 3
  | .top => 3

def PositionClass.selfStates : PositionClass → Nat
  | .bot => 2
  | .low => 3
  | .mid => 3
  | .high => 3
  | .top => 2

def PositionClass.rightStates : PositionClass → Nat
  | .bot => 3
  | .low => 3
  | .mid => 3
  | .high => 2
  | .top => 2

def TBotVal : Nat → Nat → Nat → Nat
  | 0, 0, 0 => 1
  | 0, 0, 1 => 1
  | 0, 0, 2 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 0, 1, 2 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 1
  | 1, 0, 2 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 1
  | 1, 1, 2 => 0
  | _, _, _ => 0

def TLowVal : Nat → Nat → Nat → Nat
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 1
  | 0, 1, 2 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 2
  | 0, 2, 2 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 1
  | 1, 0, 2 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 2
  | 1, 2, 0 => 0
  | 1, 2, 1 => 1
  | 1, 2, 2 => 2
  | _, _, _ => 0

def TMidVal : Nat → Nat → Nat → Nat
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 1
  | 0, 1, 2 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 2
  | 0, 2, 2 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 1
  | 1, 0, 2 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 2
  | 1, 2, 0 => 0
  | 1, 2, 1 => 1
  | 1, 2, 2 => 2
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 0, 2 => 2
  | 2, 1, 0 => 1
  | 2, 1, 1 => 0  -- liveness fix (was 2): ensures convergence from all configs
  | 2, 1, 2 => 2
  | 2, 2, 0 => 0
  | 2, 2, 1 => 2
  | 2, 2, 2 => 2
  | _, _, _ => 0

def THighVal : Nat → Nat → Nat → Nat
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 2
  | 1, 2, 0 => 0
  | 1, 2, 1 => 2
  | 2, 0, 0 => 0
  | 2, 0, 1 => 2
  | 2, 1, 0 => 0
  | 2, 1, 1 => 2
  | 2, 2, 0 => 2
  | 2, 2, 1 => 2
  | _, _, _ => 0

def TTopVal : Nat → Nat → Nat → Nat
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 2, 0, 0 => 1
  | 2, 0, 1 => 1
  | 2, 1, 0 => 1
  | 2, 1, 1 => 1
  | _, _, _ => 0

lemma TBotVal_lt {L S R : Nat} (hL : L < 2) (hS : S < 2) (hR : R < 3) : TBotVal L S R < 2 := by
  interval_cases L <;> interval_cases S <;> interval_cases R <;> decide

lemma TLowVal_lt {L S R : Nat} (hL : L < 2) (hS : S < 3) (hR : R < 3) : TLowVal L S R < 3 := by
  interval_cases L <;> interval_cases S <;> interval_cases R <;> decide

lemma TMidVal_lt {L S R : Nat} (hL : L < 3) (hS : S < 3) (hR : R < 3) : TMidVal L S R < 3 := by
  interval_cases L <;> interval_cases S <;> interval_cases R <;> decide

lemma THighVal_lt {L S R : Nat} (hL : L < 3) (hS : S < 3) (hR : R < 2) : THighVal L S R < 3 := by
  interval_cases L <;> interval_cases S <;> interval_cases R <;> decide

lemma TTopVal_lt {L S R : Nat} (hL : L < 3) (hS : S < 2) (hR : R < 2) : TTopVal L S R < 2 := by
  interval_cases L <;> interval_cases S <;> interval_cases R <;> decide

def T_bot (L : Fin 2) (S : Fin 2) (R : Fin 3) : Fin 2 :=
  ⟨TBotVal L.1 S.1 R.1, TBotVal_lt L.2 S.2 R.2⟩

def T_low (L : Fin 2) (S : Fin 3) (R : Fin 3) : Fin 3 :=
  ⟨TLowVal L.1 S.1 R.1, TLowVal_lt L.2 S.2 R.2⟩

def T_mid (L : Fin 3) (S : Fin 3) (R : Fin 3) : Fin 3 :=
  ⟨TMidVal L.1 S.1 R.1, TMidVal_lt L.2 S.2 R.2⟩

def T_high (L : Fin 3) (S : Fin 3) (R : Fin 2) : Fin 3 :=
  ⟨THighVal L.1 S.1 R.1, THighVal_lt L.2 S.2 R.2⟩

def T_top (L : Fin 3) (S : Fin 2) (R : Fin 2) : Fin 2 :=
  ⟨TTopVal L.1 S.1 R.1, TTopVal_lt L.2 S.2 R.2⟩

structure TableEntry where
  cls : PositionClass
  left : Nat
  self : Nat
  right : Nat
  out : Nat
  deriving DecidableEq, Repr

def TableEntry.WellFormed (e : TableEntry) : Prop :=
  e.left < e.cls.leftStates ∧
    e.self < e.cls.selfStates ∧
      e.right < e.cls.rightStates ∧
        e.out < e.cls.selfStates

def TableEntry.wellFormedB (e : TableEntry) : Bool :=
  decide (e.left < e.cls.leftStates ∧
    e.self < e.cls.selfStates ∧
      e.right < e.cls.rightStates ∧
        e.out < e.cls.selfStates)

def TableEntry.privileged (e : TableEntry) : Bool :=
  e.out != e.self

def TableEntry.copyNeighbor (e : TableEntry) : Bool :=
  e.out == e.left || e.out == e.right

def TableEntry.anomalous (e : TableEntry) : Bool :=
  e.privileged && !e.copyNeighbor

def TableEntry.signature (e : TableEntry) : PositionClass × Nat × Nat × Nat × Nat :=
  (e.cls, e.left, e.self, e.right, e.out)

def botEntries : List TableEntry :=
  do
    let L ← allFin 2
    let S ← allFin 2
    let R ← allFin 3
    pure { cls := .bot, left := L.1, self := S.1, right := R.1, out := (T_bot L S R).1 }

def lowEntries : List TableEntry :=
  do
    let L ← allFin 2
    let S ← allFin 3
    let R ← allFin 3
    pure { cls := .low, left := L.1, self := S.1, right := R.1, out := (T_low L S R).1 }

def midEntries : List TableEntry :=
  do
    let L ← allFin 3
    let S ← allFin 3
    let R ← allFin 3
    pure { cls := .mid, left := L.1, self := S.1, right := R.1, out := (T_mid L S R).1 }

def highEntries : List TableEntry :=
  do
    let L ← allFin 3
    let S ← allFin 3
    let R ← allFin 2
    pure { cls := .high, left := L.1, self := S.1, right := R.1, out := (T_high L S R).1 }

def topEntries : List TableEntry :=
  do
    let L ← allFin 3
    let S ← allFin 2
    let R ← allFin 2
    pure { cls := .top, left := L.1, self := S.1, right := R.1, out := (T_top L S R).1 }

def allEntries : List TableEntry :=
  botEntries ++ lowEntries ++ midEntries ++ highEntries ++ topEntries

def privilegedEntries : List TableEntry :=
  allEntries.filter TableEntry.privileged

def copyNeighborEntries : List TableEntry :=
  allEntries.filter fun e => e.privileged && e.copyNeighbor

def anomalousEntries : List TableEntry :=
  allEntries.filter TableEntry.anomalous

def allEntriesWellFormed : Bool :=
  allEntries.all TableEntry.wellFormedB

theorem allEntries_length : allEntries.length = 87 := by
  native_decide

theorem claim_3_1_1 : allEntriesWellFormed = true := by
  native_decide

theorem claim_3_3_1_privileged_count : privilegedEntries.length = 45 := by
  native_decide

theorem claim_3_3_1_copyNeighbor_count : copyNeighborEntries.length = 40 := by
  native_decide

theorem claim_3_3_1_anomalous_count : anomalousEntries.length = 5 := by
  native_decide

theorem anomalous_signatures :
    anomalousEntries.map TableEntry.signature =
      [(.bot, 0, 0, 0, 1), (.bot, 1, 1, 2, 0), (.mid, 2, 1, 1, 0),
       (.high, 1, 1, 1, 2), (.top, 2, 0, 0, 1)] := by
  native_decide

end LeanMn
