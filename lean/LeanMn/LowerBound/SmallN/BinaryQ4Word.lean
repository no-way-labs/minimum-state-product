import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop

namespace LeanMn

/-!
Scratch formalization anchor for the binary `Q4` word theorem.

This file is intentionally not imported anywhere yet. It packages the core
objects from the controller-route notes into actual Lean definitions.
-/

abbrev Proc4 := Fin 4
abbrev Word4 := List Proc4

def left4 (j : Proc4) : Proc4 := ⟨(j.1 + 3) % 4, by omega⟩
def right4 (j : Proc4) : Proc4 := ⟨(j.1 + 1) % 4, by omega⟩
def anti4 (j : Proc4) : Proc4 := ⟨(j.1 + 2) % 4, by omega⟩

def rotProc4 (k : Nat) (j : Proc4) : Proc4 := ⟨(j.1 + k) % 4, by omega⟩
def revProc4 (j : Proc4) : Proc4 := ⟨(4 - j.1) % 4, by omega⟩

def rotWord4 (k : Nat) (w : Word4) : Word4 := w.map (rotProc4 k)
def revWord4 (w : Word4) : Word4 := w.map revProc4

def invRotProc4 (k : Nat) (j : Proc4) : Proc4 := rotProc4 ((4 - k % 4) % 4) j
def rotBits4 (k : Nat) (bits : Proc4 → Bool) : Proc4 → Bool := fun j => bits (invRotProc4 k j)
def revBits4 (bits : Proc4 → Bool) : Proc4 → Bool := fun j => bits (revProc4 j)

def flipBit4 (bits : Proc4 → Bool) (j : Proc4) : Proc4 → Bool :=
  fun i => if i = j then !(bits i) else bits i

def prefixState4 (w : Word4) (t : Nat) : Proc4 → Bool :=
  (w.take t).foldl (fun bits j => flipBit4 bits j) (fun _ => false)

def prefixState4From (bits0 : Proc4 → Bool) (w : Word4) (t : Nat) : Proc4 → Bool :=
  (w.take t).foldl (fun bits j => flipBit4 bits j) bits0

def prefixParity4 (w : Word4) (t : Nat) (j : Proc4) : Bool :=
  prefixState4 w t j

def prefixParity4From (bits0 : Proc4 → Bool) (w : Word4) (t : Nat) (j : Proc4) : Bool :=
  prefixState4From bits0 w t j

def sig4 (w : Word4) (t : Nat) (j : Proc4) : Bool × Bool × Bool :=
  (prefixParity4 w t (left4 j), prefixParity4 w t j, prefixParity4 w t (right4 j))

def sig4From (bits0 : Proc4 → Bool) (w : Word4) (t : Nat) (j : Proc4) : Bool × Bool × Bool :=
  (prefixParity4From bits0 w t (left4 j), prefixParity4From bits0 w t j, prefixParity4From bits0 w t (right4 j))

def moverAt? : Word4 → Nat → Option Proc4
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, t + 1 => moverAt? xs t

def sigConflict4 (w : Word4) : Prop :=
  ∃ (j : Proc4) (t u : Nat),
    t < u ∧
    u < w.length ∧
    sig4 w t j = sig4 w u j ∧
    Xor' (moverAt? w t = some j) (moverAt? w u = some j)

def sigConflict4From (bits0 : Proc4 → Bool) (w : Word4) : Prop :=
  ∃ (j : Proc4) (t u : Nat),
    t < u ∧
    u < w.length ∧
    sig4From bits0 w t j = sig4From bits0 w u j ∧
    Xor' (moverAt? w t = some j) (moverAt? w u = some j)

def HasAdjacentRepeat4 (w : Word4) : Prop :=
  ∃ (pre suf : Word4) (j : Proc4), w = pre ++ j :: j :: suf

def SimpleWord4 (w : Word4) : Prop :=
  ∀ {t u : Nat}, t < u → u < w.length → prefixState4 w t ≠ prefixState4 w u

def BalancedWord4 (w : Word4) : Prop :=
  ∀ j : Proc4, w.count j = 2

def PositiveWord4 (w : Word4) : Prop :=
  ∀ j : Proc4, 0 < w.count j

def HasAdjacentAnti4 (w : Word4) : Prop :=
  ∃ (pre suf : Word4) (j : Proc4), w = pre ++ anti4 j :: j :: suf

def LocalNoStayWord4 : Word4 → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (b = left4 a ∨ b = right4 a) ∧ LocalNoStayWord4 (b :: rest)

def cyclicWord4 (σ : Proc4) : Word4 :=
  [σ, right4 σ, anti4 σ, left4 σ, σ, right4 σ, anti4 σ, left4 σ]

def reverseWord4 (σ : Proc4) : Word4 :=
  [σ, left4 σ, anti4 σ, right4 σ, σ, left4 σ, anti4 σ, right4 σ]

def bounceRightWord4 (a : Proc4) : Nat → Word4
  | 0 => [a]
  | n + 1 => [a, right4 a] ++ bounceRightWord4 a n

def bounceLeftWord4 (a : Proc4) : Nat → Word4
  | 0 => [a]
  | n + 1 => [a, left4 a] ++ bounceLeftWord4 a n

def stepByChoice4 (a : Proc4) (goRight : Bool) : Proc4 :=
  if goRight then right4 a else left4 a

def wordFromChoices4 : Proc4 → List Bool → Word4
  | a, [] => [a]
  | a, d :: ds => a :: wordFromChoices4 (stepByChoice4 a d) ds

def p0 : Proc4 := ⟨0, by decide⟩
def p1 : Proc4 := ⟨1, by decide⟩
def p2 : Proc4 := ⟨2, by decide⟩
def p3 : Proc4 := ⟨3, by decide⟩

def baseWord4 : Word4 := [p0, p1, p2, p3, p0, p1, p2, p3]
def baseWord4_forwardRot1 : Word4 := [p0, p1, p2, p3, p1, p2, p3, p0]
def baseWord4_forwardRot2 : Word4 := [p0, p1, p2, p3, p2, p3, p0, p1]
def baseWord4_forwardRot3 : Word4 := [p0, p1, p2, p3, p3, p0, p1, p2]
def baseWord4_reverse0 : Word4 := [p0, p1, p2, p3, p0, p3, p2, p1]
def baseWord4_reverse1 : Word4 := [p0, p1, p2, p3, p1, p0, p3, p2]
def baseWord4_reverse2 : Word4 := [p0, p1, p2, p3, p2, p1, p0, p3]
def baseWord4_reverse3 : Word4 := [p0, p1, p2, p3, p3, p2, p1, p0]

def forwardSweepFrom0 (start : Proc4) : Word4 := [p0, p1, p2, p3, start, right4 start, anti4 start, left4 start]
def reverseSweepFrom0 (start : Proc4) : Word4 := [p0, p1, p2, p3, start, left4 start, anti4 start, right4 start]
def forwardSweepWord4 (σ τ : Proc4) : Word4 := [σ, right4 σ, anti4 σ, left4 σ, τ, right4 τ, anti4 τ, left4 τ]
def reverseSweepWord4 (σ τ : Proc4) : Word4 := [σ, right4 σ, anti4 σ, left4 σ, τ, left4 τ, anti4 τ, right4 τ]

theorem anti4_ne_left4 (j : Proc4) : anti4 j ≠ left4 j := by
  exact (show ∀ j : Proc4, anti4 j ≠ left4 j from by decide) j

theorem anti4_ne_self (j : Proc4) : anti4 j ≠ j := by
  exact (show ∀ j : Proc4, anti4 j ≠ j from by decide) j

theorem anti4_ne_right4 (j : Proc4) : anti4 j ≠ right4 j := by
  exact (show ∀ j : Proc4, anti4 j ≠ right4 j from by decide) j

theorem Proc4_cases (j : Proc4) : j = p0 ∨ j = p1 ∨ j = p2 ∨ j = p3 := by
  exact (show ∀ j : Proc4, j = p0 ∨ j = p1 ∨ j = p2 ∨ j = p3 from by decide) j

theorem eq_left_or_right_of_ne_self_ne_anti {a b : Proc4}
    (hself : b ≠ a) (hanti : b ≠ anti4 a) :
    b = left4 a ∨ b = right4 a := by
  have hbself : b.1 ≠ a.1 := by
    intro h
    apply hself
    exact Fin.ext h
  have hbanti : b.1 ≠ (a.1 + 2) % 4 := by
    intro h
    apply hanti
    apply Fin.ext
    simpa [anti4] using h
  have hmod : (b.1 + 4 - a.1) % 4 = 1 ∨ (b.1 + 4 - a.1) % 4 = 3 := by
    omega
  cases hmod with
  | inl h =>
      right
      apply Fin.ext
      simp [right4]
      omega
  | inr h =>
      left
      apply Fin.ext
      simp [left4]
      omega

theorem localTriple_distinct (j : Proc4) :
    left4 j ≠ j ∧ right4 j ≠ j ∧ left4 j ≠ right4 j := by
  exact (show ∀ j : Proc4, left4 j ≠ j ∧ right4 j ≠ j ∧ left4 j ≠ right4 j from by decide) j

theorem localNoStay_cons_left {a b : Proc4} {rest : Word4}
    (h : LocalNoStayWord4 (a :: b :: rest)) :
    b = left4 a ∨ b = right4 a := h.1

theorem localNoStay_tail {a b : Proc4} {rest : Word4}
    (h : LocalNoStayWord4 (a :: b :: rest)) :
    LocalNoStayWord4 (b :: rest) := h.2

theorem wordFromChoices4_length (a : Proc4) :
    ∀ ds : List Bool, (wordFromChoices4 a ds).length = ds.length + 1
  | [] => by simp [wordFromChoices4]
  | _ :: ds => by
      simp [wordFromChoices4, wordFromChoices4_length]

theorem wordFromChoices4_localNoStay (a : Proc4) :
    ∀ ds : List Bool, LocalNoStayWord4 (wordFromChoices4 a ds)
  | [] => by simp [wordFromChoices4, LocalNoStayWord4]
  | false :: ds => by
      cases ds with
      | nil =>
          simp [wordFromChoices4, LocalNoStayWord4, stepByChoice4]
      | cons d ds' =>
          change (left4 a = left4 a ∨ left4 a = right4 a) ∧
            LocalNoStayWord4 (wordFromChoices4 (left4 a) (d :: ds'))
          constructor
          · exact Or.inl rfl
          · exact wordFromChoices4_localNoStay (left4 a) (d :: ds')
  | true :: ds => by
      cases ds with
      | nil =>
          simp [wordFromChoices4, LocalNoStayWord4, stepByChoice4]
      | cons d ds' =>
          change (right4 a = left4 a ∨ right4 a = right4 a) ∧
            LocalNoStayWord4 (wordFromChoices4 (right4 a) (d :: ds'))
          constructor
          · exact Or.inr rfl
          · exact wordFromChoices4_localNoStay (right4 a) (d :: ds')

theorem exists_wordFromChoices4_of_localNoStay :
    ∀ {w : Word4}, LocalNoStayWord4 w → w ≠ [] → ∃ a ds, w = wordFromChoices4 a ds
  | [], hlocal, hne => False.elim (hne rfl)
  | [a], hlocal, hne => ⟨a, [], by simp [wordFromChoices4]⟩
  | a :: b :: rest, hlocal, hne => by
      have htail_ne : (b :: rest) ≠ [] := by simp
      rcases exists_wordFromChoices4_of_localNoStay hlocal.2 htail_ne with ⟨a', ds, htail⟩
      have ha' : a' = b := by
        cases ds with
        | nil =>
            simp [wordFromChoices4] at htail
            exact htail.1.symm
        | cons d ds' =>
            simp [wordFromChoices4] at htail
            exact htail.1.symm
      subst ha'
      rcases hlocal.1 with hleft | hright
      · refine ⟨a, false :: ds, ?_⟩
        simpa [wordFromChoices4, stepByChoice4, hleft] using congrArg (List.cons a) htail
      · refine ⟨a, true :: ds, ?_⟩
        simpa [wordFromChoices4, stepByChoice4, hright] using congrArg (List.cons a) htail

theorem left4_right4 (j : Proc4) : left4 (right4 j) = j := by
  apply Fin.ext
  simp [left4, right4]
  omega

theorem right4_left4 (j : Proc4) : right4 (left4 j) = j := by
  apply Fin.ext
  simp [left4, right4]
  omega

theorem left4_left4 (j : Proc4) : left4 (left4 j) = anti4 j := by
  apply Fin.ext
  simp [left4, anti4]
  omega

theorem right4_right4 (j : Proc4) : right4 (right4 j) = anti4 j := by
  apply Fin.ext
  simp [right4, anti4]

theorem anti4_anti4 (j : Proc4) : anti4 (anti4 j) = j := by
  apply Fin.ext
  simp [anti4]
  omega

theorem left4_anti4 (j : Proc4) : left4 (anti4 j) = right4 j := by
  apply Fin.ext
  simp [left4, anti4, right4]
  omega

theorem right4_anti4 (j : Proc4) : right4 (anti4 j) = left4 j := by
  apply Fin.ext
  simp [left4, anti4, right4]

theorem anti4_left4 (j : Proc4) : anti4 (left4 j) = right4 j := by
  apply Fin.ext
  simp [anti4, left4, right4]
  omega

theorem anti4_right4 (j : Proc4) : anti4 (right4 j) = left4 j := by
  apply Fin.ext
  simp [anti4, left4, right4]

theorem left4_rotProc4 (k : Nat) (j : Proc4) :
    left4 (rotProc4 k j) = rotProc4 k (left4 j) := by
  apply Fin.ext
  simp [left4, rotProc4]
  omega

theorem right4_rotProc4 (k : Nat) (j : Proc4) :
    right4 (rotProc4 k j) = rotProc4 k (right4 j) := by
  apply Fin.ext
  simp [right4, rotProc4]
  omega

theorem anti4_rotProc4 (k : Nat) (j : Proc4) :
    anti4 (rotProc4 k j) = rotProc4 k (anti4 j) := by
  apply Fin.ext
  simp [anti4, rotProc4]
  omega

theorem rotProc4_p0 (j : Proc4) : rotProc4 j.1 p0 = j := by
  apply Fin.ext
  simp [rotProc4, p0]

theorem rotProc4_p1 (j : Proc4) : rotProc4 j.1 p1 = right4 j := by
  apply Fin.ext
  simp [rotProc4, right4, p1]
  omega

theorem rotProc4_p2 (j : Proc4) : rotProc4 j.1 p2 = anti4 j := by
  apply Fin.ext
  simp [rotProc4, anti4, p2]
  omega

theorem rotProc4_p3 (j : Proc4) : rotProc4 j.1 p3 = left4 j := by
  apply Fin.ext
  simp [rotProc4, left4, p3]
  omega

theorem rotProc4_inv_left (k : Nat) (j : Proc4) :
    rotProc4 k (invRotProc4 k j) = j := by
  apply Fin.ext
  simp [rotProc4, invRotProc4]
  omega

theorem rotProc4_inv_right (k : Nat) (j : Proc4) :
    invRotProc4 k (rotProc4 k j) = j := by
  apply Fin.ext
  simp [rotProc4, invRotProc4]
  omega

theorem rotProc4_injective (k : Nat) : Function.Injective (rotProc4 k) := by
  intro a b h
  have h' := congrArg (invRotProc4 k) h
  simpa [rotProc4_inv_right] using h'

theorem revProc4_involutive (j : Proc4) : revProc4 (revProc4 j) = j := by
  apply Fin.ext
  simp [revProc4]
  omega

theorem revProc4_injective : Function.Injective revProc4 := by
  intro a b h
  have h' := congrArg revProc4 h
  simpa [revProc4_involutive] using h'

theorem rotProc4_left4 (k : Nat) (j : Proc4) :
    rotProc4 k (left4 j) = left4 (rotProc4 k j) :=
  (left4_rotProc4 k j).symm

theorem rotProc4_right4 (k : Nat) (j : Proc4) :
    rotProc4 k (right4 j) = right4 (rotProc4 k j) :=
  (right4_rotProc4 k j).symm

theorem rotProc4_anti4 (k : Nat) (j : Proc4) :
    rotProc4 k (anti4 j) = anti4 (rotProc4 k j) :=
  (anti4_rotProc4 k j).symm

theorem Proc4_rel_cases (a b : Proc4) :
    b = a ∨ b = right4 a ∨ b = anti4 a ∨ b = left4 a := by
  rcases Proc4_cases (invRotProc4 a.1 b) with h0 | h1 | h2 | h3
  · left
    calc
      b = rotProc4 a.1 (invRotProc4 a.1 b) := by rw [rotProc4_inv_left]
      _ = rotProc4 a.1 p0 := by rw [h0]
      _ = a := rotProc4_p0 a
  · right
    left
    calc
      b = rotProc4 a.1 (invRotProc4 a.1 b) := by rw [rotProc4_inv_left]
      _ = rotProc4 a.1 p1 := by rw [h1]
      _ = right4 a := rotProc4_p1 a
  · right
    right
    left
    calc
      b = rotProc4 a.1 (invRotProc4 a.1 b) := by rw [rotProc4_inv_left]
      _ = rotProc4 a.1 p2 := by rw [h2]
      _ = anti4 a := rotProc4_p2 a
  · right
    right
    right
    calc
      b = rotProc4 a.1 (invRotProc4 a.1 b) := by rw [rotProc4_inv_left]
      _ = rotProc4 a.1 p3 := by rw [h3]
      _ = left4 a := rotProc4_p3 a

theorem eq_right_or_left_of_ne_self_ne_anti (a b : Proc4)
    (hself : b ≠ a) (hanti : b ≠ anti4 a) :
    b = right4 a ∨ b = left4 a := by
  rcases Proc4_rel_cases a b with h | h | h | h
  · contradiction
  · exact Or.inl h
  · contradiction
  · exact Or.inr h

theorem sweep_or_reverse_of_distinct_no_adjacent_anti
    {a b c d : Proc4}
    (hab : b ≠ a) (hac : c ≠ a) (had : d ≠ a)
    (hbc : c ≠ b) (hbd : d ≠ b) (hcd : d ≠ c)
    (habAnti : b ≠ anti4 a) (hbcAnti : c ≠ anti4 b) (_hcdAnti : d ≠ anti4 c) :
    (b = right4 a ∧ c = anti4 a ∧ d = left4 a) ∨
      (b = left4 a ∧ c = anti4 a ∧ d = right4 a) := by
  rcases eq_right_or_left_of_ne_self_ne_anti a b hab habAnti with hb | hb
  · left
    have hc : c = anti4 a := by
      rcases Proc4_rel_cases b c with h | h | h | h
      · exfalso
        exact hbc h
      · calc
          c = right4 b := h
          _ = anti4 a := by rw [hb, right4_right4]
      · exfalso
        exact hbcAnti h
      · exfalso
        have : c = a := by rwa [hb, left4_right4] at h
        exact hac this
    have hd : d = left4 a := by
      rcases Proc4_rel_cases c d with h | h | h | h
      · exfalso
        exact hcd h
      · calc
          d = right4 c := h
          _ = left4 a := by rw [hc, right4_anti4]
      · exfalso
        have : d = a := by rwa [hc, anti4_anti4] at h
        exact had this
      · exfalso
        have hd' : d = right4 a := by
          calc
            d = left4 c := h
            _ = right4 a := by rw [hc, left4_anti4]
        have : d = b := by
          calc
            d = right4 a := hd'
            _ = b := by simpa using hb.symm
        exact hbd this
    exact ⟨hb, ⟨hc, hd⟩⟩
  · right
    have hc : c = anti4 a := by
      rcases Proc4_rel_cases b c with h | h | h | h
      · exfalso
        exact hbc h
      · exfalso
        have : c = a := by rwa [hb, right4_left4] at h
        exact hac this
      · exfalso
        exact hbcAnti h
      · calc
          c = left4 b := h
          _ = anti4 a := by rw [hb, left4_left4]
    have hd : d = right4 a := by
      rcases Proc4_rel_cases c d with h | h | h | h
      · exfalso
        exact hcd h
      · exfalso
        have hd' : d = left4 a := by
          calc
            d = right4 c := h
            _ = left4 a := by rw [hc, right4_anti4]
        have : d = b := by
          calc
            d = left4 a := hd'
            _ = b := by simpa using hb.symm
        exact hbd this
      · exfalso
        have : d = a := by rwa [hc, anti4_anti4] at h
        exact had this
      · calc
          d = left4 c := h
          _ = right4 a := by rw [hc, left4_anti4]
    exact ⟨hb, ⟨hc, hd⟩⟩

theorem repeat_shape_of_not_nodup_adjacent_ne
    {a b c d : Proc4}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d)
    (hnodup : ¬ List.Nodup [a, b, c, d])
    (hnalt : ¬ (a = c ∧ b = d)) :
    (a = c ∧ b ≠ d) ∨ a = d ∨ (b = d ∧ a ≠ c) := by
  by_cases hac : a = c
  · left
    refine ⟨hac, ?_⟩
    intro hbd
    exact hnalt ⟨hac, hbd⟩
  · right
    by_cases had : a = d
    · exact Or.inl had
    · right
      have hbd : b = d := by
        by_contra hbd
        apply hnodup
        simp [hab, hbc, hcd, hac, had, hbd]
      exact ⟨hbd, hac⟩

theorem flipBit4_commute (bits : Proc4 → Bool) (i j : Proc4) (hij : i ≠ j) :
    flipBit4 (flipBit4 bits i) j = flipBit4 (flipBit4 bits j) i := by
  funext k
  unfold flipBit4
  by_cases hk_i : k = i
  · subst hk_i
    simp [hij]
  · by_cases hk_j : k = j
    · subst hk_j
      simp [hij, hk_i]
    · simp [hk_i, hk_j]

theorem flipBit4_self_self (bits : Proc4 → Bool) (j : Proc4) :
    flipBit4 (flipBit4 bits j) j = bits := by
  funext i
  unfold flipBit4
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem flipBit4_abab (bits : Proc4 → Bool) (a b : Proc4) (hab : a ≠ b) :
    flipBit4 (flipBit4 (flipBit4 (flipBit4 bits a) b) a) b = bits := by
  calc
    flipBit4 (flipBit4 (flipBit4 (flipBit4 bits a) b) a) b
        = flipBit4 (flipBit4 (flipBit4 (flipBit4 bits a) a) b) b := by
            rw [flipBit4_commute (bits := flipBit4 bits a) (i := b) (j := a) hab.symm]
    _ = flipBit4 (flipBit4 bits b) b := by simp [flipBit4_self_self]
    _ = bits := by simp [flipBit4_self_self]

theorem left4_revProc4 (j : Proc4) :
    left4 (revProc4 j) = revProc4 (right4 j) := by
  apply Fin.ext
  simp [left4, right4, revProc4]
  omega

theorem right4_revProc4 (j : Proc4) :
    right4 (revProc4 j) = revProc4 (left4 j) := by
  apply Fin.ext
  simp [left4, right4, revProc4]
  omega

theorem anti4_revProc4 (j : Proc4) :
    anti4 (revProc4 j) = revProc4 (anti4 j) := by
  apply Fin.ext
  simp [anti4, revProc4]
  omega

theorem flipBit4_rotBits4 (bits : Proc4 → Bool) (k : Nat) (i : Proc4) :
    flipBit4 (rotBits4 k bits) (rotProc4 k i) = rotBits4 k (flipBit4 bits i) := by
  funext j
  unfold flipBit4 rotBits4
  by_cases h : j = rotProc4 k i
  · subst h
    simp [rotProc4_inv_right]
  · have h' : invRotProc4 k j ≠ i := by
      intro hEq
      apply h
      rw [← hEq, rotProc4_inv_left]
    simp [h, h']

theorem flipBit4_revBits4 (bits : Proc4 → Bool) (i : Proc4) :
    flipBit4 (revBits4 bits) (revProc4 i) = revBits4 (flipBit4 bits i) := by
  funext j
  unfold flipBit4 revBits4
  by_cases h : j = revProc4 i
  · subst h
    simp [revProc4_involutive]
  · have h' : revProc4 j ≠ i := by
      intro hEq
      apply h
      rw [← hEq, revProc4_involutive]
    simp [h, h']

theorem foldl_flipBit4_rotBits4 (bits : Proc4 → Bool) (k : Nat) :
    ∀ ws : Word4,
      List.foldl (fun bits j => flipBit4 bits j) (rotBits4 k bits) (rotWord4 k ws) =
        rotBits4 k (List.foldl (fun bits j => flipBit4 bits j) bits ws)
  | [] => by
      funext j
      simp [rotWord4, rotBits4]
  | x :: xs => by
      simpa [rotWord4, flipBit4_rotBits4] using
        (foldl_flipBit4_rotBits4 (bits := flipBit4 bits x) (k := k) xs)

theorem foldl_flipBit4_revBits4 (bits : Proc4 → Bool) :
    ∀ ws : Word4,
      List.foldl (fun bits j => flipBit4 bits j) (revBits4 bits) (revWord4 ws) =
        revBits4 (List.foldl (fun bits j => flipBit4 bits j) bits ws)
  | [] => by
      funext j
      simp [revWord4, revBits4]
  | x :: xs => by
      simpa [revWord4, flipBit4_revBits4] using
        (foldl_flipBit4_revBits4 (bits := flipBit4 bits x) xs)

theorem flipBit4_eq_xor_flipBit4_false (bits0 : Proc4 → Bool) (x : Proc4) :
    flipBit4 bits0 x = fun j => xor (bits0 j) (flipBit4 (fun _ => false) x j) := by
  funext j
  unfold flipBit4
  by_cases h : j = x
  · subst h
    simp
  · simp [h]

theorem foldl_flipBit4_eq_xor (bits0 : Proc4 → Bool) :
    ∀ ws : Word4,
      List.foldl (fun bits j => flipBit4 bits j) bits0 ws =
        fun j => xor (bits0 j) (List.foldl (fun bits j => flipBit4 bits j) (fun _ => false) ws j)
  | [] => by
      funext j
      simp
  | x :: xs => by
      rw [List.foldl_cons, foldl_flipBit4_eq_xor (flipBit4 bits0 x) xs]
      funext j
      have hxs :=
        congrFun (foldl_flipBit4_eq_xor (flipBit4 (fun _ => false) x) xs) j
      rw [flipBit4_eq_xor_flipBit4_false]
      rw [List.foldl_cons]
      rw [hxs]
      simp

theorem prefixState4From_eq_xor_prefixState4 (bits0 : Proc4 → Bool) (w : Word4) (t : Nat) :
    prefixState4From bits0 w t = fun j => xor (bits0 j) (prefixState4 w t j) := by
  unfold prefixState4From prefixState4
  simpa using foldl_flipBit4_eq_xor bits0 (w.take t)

theorem prefixState4_append_shift (pre suf : Word4) (t : Nat) :
    prefixState4 (pre ++ suf) (pre.length + t) =
      prefixState4From (prefixState4 pre pre.length) suf t := by
  unfold prefixState4From prefixState4
  have htake : (pre ++ suf).take (pre.length + t) = pre ++ suf.take t := by
    simp [List.take_append, Nat.sub_eq_zero_iff_le, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  rw [htake]
  simp [List.foldl_append]

theorem prefixParity4From_eq_xor (bits0 : Proc4 → Bool) (w : Word4) (t : Nat) (j : Proc4) :
    prefixParity4From bits0 w t j = xor (bits0 j) (prefixParity4 w t j) := by
  unfold prefixParity4From prefixParity4
  rw [prefixState4From_eq_xor_prefixState4]

theorem sig4From_eq_xor_sig4 (bits0 : Proc4 → Bool) (w : Word4) (t : Nat) (j : Proc4) :
    sig4From bits0 w t j =
      (xor (bits0 (left4 j)) (prefixParity4 w t (left4 j)),
        xor (bits0 j) (prefixParity4 w t j),
        xor (bits0 (right4 j)) (prefixParity4 w t (right4 j))) := by
  simp [sig4From, prefixParity4From_eq_xor]

theorem sigConflict4.lift (bits0 : Proc4 → Bool) {w : Word4} (h : sigConflict4 w) :
    sigConflict4From bits0 w := by
  rcases h with ⟨j, t, u, htu, hu, hsig, hx⟩
  refine ⟨j, t, u, htu, hu, ?_, hx⟩
  let liftSig :
      Bool × Bool × Bool → Bool × Bool × Bool :=
    fun p => (xor (bits0 (left4 j)) p.1, xor (bits0 j) p.2.1, xor (bits0 (right4 j)) p.2.2)
  simpa [liftSig, sig4From_eq_xor_sig4] using congrArg liftSig hsig

theorem moverAt?_append_right (pre suf : Word4) (t : Nat) :
    moverAt? (pre ++ suf) (pre.length + t) = moverAt? suf t := by
  induction pre generalizing t with
  | nil =>
      simp [moverAt?]
  | cons x xs ih =>
      cases t with
      | zero =>
          simpa [moverAt?, Nat.add_assoc] using ih 0
      | succ t =>
          simp [moverAt?]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (t + 1)

theorem sigConflict4_append_suffix (pre suf : Word4) (h : sigConflict4 suf) :
    sigConflict4 (pre ++ suf) := by
  rcases sigConflict4.lift (prefixState4 pre pre.length) h with ⟨j, t, u, htu, hu, hsig, hx⟩
  refine ⟨j, pre.length + t, pre.length + u, by omega, ?_, ?_, ?_⟩
  · simp
    omega
  · simpa [sig4, sig4From, prefixParity4, prefixParity4From, prefixState4_append_shift] using hsig
  · simpa [moverAt?_append_right] using hx

theorem prefixState4_rotWord4 (bits : Proc4 → Bool) (k t : Nat) (w : Word4) :
    List.foldl (fun bits j => flipBit4 bits j) (rotBits4 k bits) ((rotWord4 k w).take t) =
      rotBits4 k (List.foldl (fun bits j => flipBit4 bits j) bits (w.take t)) := by
  simpa [rotWord4, List.map_take] using foldl_flipBit4_rotBits4 (bits := bits) (k := k) (ws := w.take t)

theorem prefixState4_revWord4 (bits : Proc4 → Bool) (t : Nat) (w : Word4) :
    List.foldl (fun bits j => flipBit4 bits j) (revBits4 bits) ((revWord4 w).take t) =
      revBits4 (List.foldl (fun bits j => flipBit4 bits j) bits (w.take t)) := by
  simpa [revWord4, List.map_take] using foldl_flipBit4_revBits4 (bits := bits) (ws := w.take t)

theorem prefixParity4_rotWord4 (k t : Nat) (w : Word4) (j : Proc4) :
    prefixParity4 (rotWord4 k w) t (rotProc4 k j) = prefixParity4 w t j := by
  unfold prefixParity4 prefixState4
  have h :=
    prefixState4_rotWord4 (bits := fun _ => false) (k := k) (t := t) (w := w)
  change
    List.foldl (fun bits j => flipBit4 bits j) (rotBits4 k (fun _ => false)) ((rotWord4 k w).take t) (rotProc4 k j) =
      List.foldl (fun bits j => flipBit4 bits j) (fun _ => false) (w.take t) j
  rw [h]
  unfold rotBits4
  simp [rotProc4_inv_right]

theorem prefixParity4_revWord4 (t : Nat) (w : Word4) (j : Proc4) :
    prefixParity4 (revWord4 w) t (revProc4 j) = prefixParity4 w t j := by
  unfold prefixParity4 prefixState4
  have h := prefixState4_revWord4 (bits := fun _ => false) (t := t) (w := w)
  change
    List.foldl (fun bits j => flipBit4 bits j) (revBits4 (fun _ => false)) ((revWord4 w).take t) (revProc4 j) =
      List.foldl (fun bits j => flipBit4 bits j) (fun _ => false) (w.take t) j
  rw [h]
  unfold revBits4
  simp [revProc4_involutive]

theorem sig4_rotWord4 (k t : Nat) (w : Word4) (j : Proc4) :
    sig4 (rotWord4 k w) t (rotProc4 k j) = sig4 w t j := by
  simp [sig4, prefixParity4_rotWord4, left4_rotProc4, right4_rotProc4]

def revSig4 : Bool × Bool × Bool → Bool × Bool × Bool
  | (l,s,r) => (r,s,l)

theorem sig4_revWord4 (t : Nat) (w : Word4) (j : Proc4) :
    sig4 (revWord4 w) t (revProc4 j) = revSig4 (sig4 w t j) := by
  simp [sig4, revSig4, prefixParity4_revWord4, left4_revProc4, right4_revProc4]

theorem moverAt?_rotWord4 (k t : Nat) (w : Word4) :
    moverAt? (rotWord4 k w) t = Option.map (rotProc4 k) (moverAt? w t) := by
  induction w generalizing t with
  | nil =>
      cases t <;> rfl
  | cons x xs ih =>
      cases t with
      | zero => rfl
      | succ t =>
          simpa [rotWord4, moverAt?] using ih t

theorem moverAt?_revWord4 (t : Nat) (w : Word4) :
    moverAt? (revWord4 w) t = Option.map revProc4 (moverAt? w t) := by
  induction w generalizing t with
  | nil =>
      cases t <;> rfl
  | cons x xs ih =>
      cases t with
      | zero => rfl
      | succ t =>
          simpa [revWord4, moverAt?] using ih t

theorem moverAt?_rot_eq (k : Nat) (w : Word4) (t : Nat) (j : Proc4) :
    Option.map (rotProc4 k) (moverAt? w t) = some (rotProc4 k j) ↔ moverAt? w t = some j := by
  cases hm : moverAt? w t with
  | none =>
      simp
  | some a =>
      simp
      exact (rotProc4_injective k).eq_iff

theorem moverAt?_rev_eq (w : Word4) (t : Nat) (j : Proc4) :
    Option.map revProc4 (moverAt? w t) = some (revProc4 j) ↔ moverAt? w t = some j := by
  cases hm : moverAt? w t with
  | none =>
      simp
  | some a =>
      simp
      exact revProc4_injective.eq_iff

theorem sigConflict4_rotWord4 (k : Nat) (w : Word4) (h : sigConflict4 w) :
    sigConflict4 (rotWord4 k w) := by
  rcases h with ⟨j, t, u, htu, hu, hsig, hx⟩
  refine ⟨rotProc4 k j, t, u, htu, ?_, ?_, ?_⟩
  · simpa [rotWord4] using hu
  · calc
      sig4 (rotWord4 k w) t (rotProc4 k j) = sig4 w t j := sig4_rotWord4 k t w j
      _ = sig4 w u j := hsig
      _ = sig4 (rotWord4 k w) u (rotProc4 k j) := (sig4_rotWord4 k u w j).symm
  · rw [moverAt?_rotWord4, moverAt?_rotWord4]
    rw [moverAt?_rot_eq, moverAt?_rot_eq]
    exact hx

theorem sigConflict4_revWord4 (w : Word4) (h : sigConflict4 w) :
    sigConflict4 (revWord4 w) := by
  rcases h with ⟨j, t, u, htu, hu, hsig, hx⟩
  refine ⟨revProc4 j, t, u, htu, ?_, ?_, ?_⟩
  · simpa [revWord4] using hu
  · calc
      sig4 (revWord4 w) t (revProc4 j) = revSig4 (sig4 w t j) := sig4_revWord4 t w j
      _ = revSig4 (sig4 w u j) := by rw [hsig]
      _ = sig4 (revWord4 w) u (revProc4 j) := (sig4_revWord4 u w j).symm
  · rw [moverAt?_revWord4, moverAt?_revWord4]
    rw [moverAt?_rev_eq, moverAt?_rev_eq]
    exact hx

theorem sigConflict4_rev_transport {w w' : Word4} (hshape : revWord4 w = w') (h : sigConflict4 w) :
    sigConflict4 w' := by
  simpa [hshape] using sigConflict4_revWord4 w h

theorem rotWord4_invRot (k : Nat) (w : Word4) :
    rotWord4 k (rotWord4 ((4 - k % 4) % 4) w) = w := by
  induction w with
  | nil =>
      simp [rotWord4]
  | cons x xs ih =>
      change rotProc4 k (rotProc4 ((4 - k % 4) % 4) x) ::
          rotWord4 k (rotWord4 ((4 - k % 4) % 4) xs) = x :: xs
      have hx : rotProc4 k (rotProc4 ((4 - k % 4) % 4) x) = x := by
        apply Fin.ext
        simp [rotProc4]
        omega
      rw [hx]
      simpa [ih]

theorem revWord4_involutive (w : Word4) :
    revWord4 (revWord4 w) = w := by
  induction w with
  | nil =>
      simp [revWord4]
  | cons x xs ih =>
      change revProc4 (revProc4 x) :: revWord4 (revWord4 xs) = x :: xs
      simp [revProc4_involutive, ih]

theorem LocalNoStayWord4_revWord4 : ∀ {w : Word4},
    LocalNoStayWord4 w → LocalNoStayWord4 (revWord4 w)
  | [] => by
      intro _
      simp [revWord4, LocalNoStayWord4]
  | [_] => by
      intro _
      simp [revWord4, LocalNoStayWord4]
  | a :: b :: rest => by
      intro h
      rcases localNoStay_cons_left h with hleft | hright
      · have htail := LocalNoStayWord4_revWord4 (w := b :: rest) (localNoStay_tail h)
        refine And.intro ?_ htail
        right
        simpa [hleft, left4_revProc4, right4_revProc4]
      · have htail := LocalNoStayWord4_revWord4 (w := b :: rest) (localNoStay_tail h)
        refine And.intro ?_ htail
        left
        simpa [hright, left4_revProc4, right4_revProc4]

theorem sigConflict4_rev_iff (w : Word4) :
    sigConflict4 (revWord4 w) ↔ sigConflict4 w := by
  constructor
  · intro hrev
    have h := sigConflict4_revWord4 (revWord4 w) hrev
    simpa [revWord4_involutive] using h
  · intro h
    exact sigConflict4_revWord4 w h

theorem flipBit4_anti_preserves_localTriple (bits : Proc4 → Bool) (j : Proc4) :
    (flipBit4 bits (anti4 j)) (left4 j) = bits (left4 j) ∧
    (flipBit4 bits (anti4 j)) j = bits j ∧
    (flipBit4 bits (anti4 j)) (right4 j) = bits (right4 j) := by
  constructor
  · unfold flipBit4
    simp [show left4 j ≠ anti4 j from by intro h; exact anti4_ne_left4 j h.symm]
  constructor
  · unfold flipBit4
    simp [show j ≠ anti4 j from by intro h; exact anti4_ne_self j h.symm]
  · unfold flipBit4
    simp [show right4 j ≠ anti4 j from by intro h; exact anti4_ne_right4 j h.symm]

theorem prefixState4_append_self_self_eq (pre suf : Word4) (j : Proc4) :
    prefixState4 (pre ++ j :: j :: suf) pre.length =
      prefixState4 (pre ++ j :: j :: suf) (pre.length + 2) := by
  unfold prefixState4
  have htake0 : (pre ++ j :: j :: suf).take pre.length = pre := by
    simp
  have htake2 : (pre ++ j :: j :: suf).take (pre.length + 2) = pre ++ [j, j] := by
    induction pre with
    | nil =>
        simp
    | cons x xs ih =>
        simp [ih]
  rw [htake0, htake2]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [flipBit4_self_self]

theorem not_simple_of_adjacentRepeat4_before_end {w : Word4}
    (h : HasAdjacentRepeat4 w)
    (hend : ∃ pre suf j, w = pre ++ j :: j :: suf ∧ pre.length + 2 < w.length) :
    ¬ SimpleWord4 w := by
  intro hsimple
  rcases hend with ⟨pre, suf, j, rfl, hu⟩
  have hstates := prefixState4_append_self_self_eq pre suf j
  exact hsimple (by omega) hu hstates

theorem not_simple_of_adjacent_repeat_with_tail (pre suf : Word4) (j : Proc4) (hsuf : suf ≠ []) :
    ¬ SimpleWord4 (pre ++ j :: j :: suf) := by
  apply not_simple_of_adjacentRepeat4_before_end
  · refine ⟨pre, suf, j, rfl⟩
  · refine ⟨pre, suf, j, rfl, ?_⟩
    cases suf with
    | nil => contradiction
    | cons x xs =>
        simp

theorem prefixState4_append_abab_eq (pre suf : Word4) (a b : Proc4) (hab : a ≠ b) :
    prefixState4 (pre ++ a :: b :: a :: b :: suf) pre.length =
      prefixState4 (pre ++ a :: b :: a :: b :: suf) (pre.length + 4) := by
  unfold prefixState4
  have htake0 : (pre ++ a :: b :: a :: b :: suf).take pre.length = pre := by
    simp
  have htake4 : (pre ++ a :: b :: a :: b :: suf).take (pre.length + 4) = pre ++ [a, b, a, b] := by
    induction pre with
    | nil =>
        simp
    | cons x xs ih =>
        simp [ih]
  rw [htake0, htake4]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [flipBit4_abab _ _ _ hab]

theorem not_simple_of_abab_before_end (pre suf : Word4) (a b : Proc4)
    (hab : a ≠ b) (hu : pre.length + 4 < (pre ++ a :: b :: a :: b :: suf).length) :
    ¬ SimpleWord4 (pre ++ a :: b :: a :: b :: suf) := by
  intro hsimple
  have hstates := prefixState4_append_abab_eq pre suf a b hab
  exact hsimple (by omega) hu hstates

theorem first_four_repeat_shape_of_simple
    {a b c d : Proc4} {rest : Word4}
    (hrest : rest ≠ [])
    (hsimple : SimpleWord4 (a :: b :: c :: d :: rest))
    (hnodup : ¬ List.Nodup [a, b, c, d]) :
    (a = c ∧ b ≠ d) ∨ a = d ∨ (b = d ∧ a ≠ c) := by
  have hab : a ≠ b := by
    by_contra hab
    have hns := not_simple_of_adjacent_repeat_with_tail [] (c :: d :: rest) a (by simp [hab])
    have hsimple' : SimpleWord4 (a :: a :: c :: d :: rest) := by
      intro t u htu huu
      simpa [hab] using hsimple (t := t) (u := u) htu huu
    have hns' : ¬ SimpleWord4 (a :: a :: c :: d :: rest) := by
      simpa [hab] using hns
    exact hns' hsimple'
  have hbc : b ≠ c := by
    by_contra hbc
    have hns := not_simple_of_adjacent_repeat_with_tail [a] (d :: rest) b (by simp [hbc])
    have hsimple' : SimpleWord4 (a :: c :: c :: d :: rest) := by
      intro t u htu huu
      simpa [hbc] using hsimple (t := t) (u := u) htu huu
    have hns' : ¬ SimpleWord4 (a :: c :: c :: d :: rest) := by
      simpa [hbc] using hns
    exact hns' hsimple'
  have hcd : c ≠ d := by
    by_contra hcd
    have hns := not_simple_of_adjacent_repeat_with_tail [a, b] rest c hrest
    have hsimple' : SimpleWord4 (a :: b :: d :: d :: rest) := by
      intro t u htu huu
      simpa [hcd] using hsimple (t := t) (u := u) htu huu
    have hns' : ¬ SimpleWord4 (a :: b :: d :: d :: rest) := by
      simpa [hcd] using hns
    exact hns' hsimple'
  have hnalt : ¬ (a = c ∧ b = d) := by
    intro h
    rcases h with ⟨hac, hbd⟩
    have hu : ([] : Word4).length + 4 < ([] ++ a :: b :: a :: b :: rest).length := by
      cases rest with
      | nil => contradiction
      | cons x xs =>
          simp
    have hns := not_simple_of_abab_before_end [] rest a b hab hu
    have hns' : ¬ SimpleWord4 (a :: b :: a :: b :: rest) := by
      simpa using hns
    have hsimple' : SimpleWord4 (a :: b :: a :: b :: rest) := by
      intro t u htu huu
      simpa [hac, hbd] using hsimple (t := t) (u := u) htu huu
    exact hns' hsimple'
  exact repeat_shape_of_not_nodup_adjacent_ne hab hbc hcd hnodup hnalt

theorem sig4_append_anti_self_eq (pre suf : Word4) (j : Proc4) :
    sig4 (pre ++ anti4 j :: j :: suf) pre.length j =
      sig4 (pre ++ anti4 j :: j :: suf) (pre.length + 1) j := by
  unfold sig4 prefixParity4 prefixState4
  have htake0 : (pre ++ anti4 j :: j :: suf).take pre.length = pre := by
    simp
  have htake1 : (pre ++ anti4 j :: j :: suf).take (pre.length + 1) = pre ++ [anti4 j] := by
    simpa [htake0] using
      (List.take_concat_get' (l := pre ++ anti4 j :: j :: suf) (i := pre.length) (by simp)).symm
  rw [htake0, htake1]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rcases flipBit4_anti_preserves_localTriple
      (List.foldl (fun bits j => flipBit4 bits j) (fun _ => false) pre) j with
    ⟨hL, hS, hR⟩
  simp [hL, hS, hR]

theorem moverAt?_append_anti (pre suf : Word4) (j : Proc4) :
    moverAt? (pre ++ anti4 j :: j :: suf) pre.length = some (anti4 j) := by
  induction pre with
  | nil => simp [moverAt?]
  | cons x xs ih =>
      simp [moverAt?, ih]

theorem moverAt?_append_self (pre suf : Word4) (j : Proc4) :
    moverAt? (pre ++ anti4 j :: j :: suf) (pre.length + 1) = some j := by
  induction pre with
  | nil => simp [moverAt?]
  | cons x xs ih =>
      simp [moverAt?, ih]

theorem sigConflict4_of_adjacent_anti_self (pre suf : Word4) (j : Proc4) :
    sigConflict4 (pre ++ anti4 j :: j :: suf) := by
  refine ⟨j, pre.length, pre.length + 1, by omega, by simp, ?_, ?_⟩
  · exact sig4_append_anti_self_eq pre suf j
  · rw [moverAt?_append_anti, moverAt?_append_self]
    simp [Xor', anti4_ne_self]

theorem sigConflict4_of_hasAdjacentAnti4 {w : Word4} (h : HasAdjacentAnti4 w) :
    sigConflict4 w := by
  rcases h with ⟨pre, suf, j, rfl⟩
  exact sigConflict4_of_adjacent_anti_self pre suf j

theorem sigConflict4_prefix_0102 (rest : Word4) :
    sigConflict4 ([p0, p1, p0, p2] ++ rest) := by
  refine ⟨p2, 2, 3, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake2 : ([p0, p1, p0, p2] ++ rest).take 2 = [p0, p1] := by simp
    have htake3 : ([p0, p1, p0, p2] ++ rest).take 3 = [p0, p1, p0] := by simp
    rw [htake2, htake3]
    simp [flipBit4, left4, right4, p0, p1, p2]
  · simp [moverAt?, Xor', p0, p1, p2]

theorem sigConflict4_prefix_0103 (rest : Word4) :
    sigConflict4 ([p0, p1, p0, p3] ++ rest) := by
  refine ⟨p3, 0, 3, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake0 : ([p0, p1, p0, p3] ++ rest).take 0 = ([] : Word4) := by simp
    have htake3 : ([p0, p1, p0, p3] ++ rest).take 3 = [p0, p1, p0] := by simp
    rw [htake0, htake3]
    simp [flipBit4, left4, right4, p0, p1, p3]
  · simp [moverAt?, Xor', p0, p1, p3]

theorem sigConflict4_prefix_0201 (rest : Word4) :
    sigConflict4 ([p0, p2, p0, p1] ++ rest) := by
  refine ⟨p2, 0, 1, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake0 : ([p0, p2, p0, p1] ++ rest).take 0 = ([] : Word4) := by simp
    have htake1 : ([p0, p2, p0, p1] ++ rest).take 1 = [p0] := by simp
    rw [htake0, htake1]
    simp [flipBit4, left4, right4, p0, p1, p2]
  · simp [moverAt?, Xor', p0, p1, p2]

theorem sigConflict4_prefix_0120 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p0] ++ rest) := by
  refine ⟨p0, 2, 3, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake2 : ([p0, p1, p2, p0] ++ rest).take 2 = [p0, p1] := by simp
    have htake3 : ([p0, p1, p2, p0] ++ rest).take 3 = [p0, p1, p2] := by simp
    rw [htake2, htake3]
    simp [flipBit4, left4, right4, p0, p1, p2]
  · simp [moverAt?, Xor', p0, p1, p2]

theorem sigConflict4_prefix_0130 (rest : Word4) :
    sigConflict4 ([p0, p1, p3, p0] ++ rest) := by
  refine ⟨p3, 1, 2, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake1 : ([p0, p1, p3, p0] ++ rest).take 1 = [p0] := by simp
    have htake2 : ([p0, p1, p3, p0] ++ rest).take 2 = [p0, p1] := by simp
    rw [htake1, htake2]
    simp [flipBit4, left4, right4, p0, p1, p3]
  · simp [moverAt?, Xor', p0, p1, p3]

theorem sigConflict4_prefix_0210 (rest : Word4) :
    sigConflict4 ([p0, p2, p1, p0] ++ rest) := by
  refine ⟨p2, 0, 1, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake0 : ([p0, p2, p1, p0] ++ rest).take 0 = ([] : Word4) := by simp
    have htake1 : ([p0, p2, p1, p0] ++ rest).take 1 = [p0] := by simp
    rw [htake0, htake1]
    simp [flipBit4, left4, right4, p0, p1, p2]
  · simp [moverAt?, Xor', p0, p1, p2]

theorem sigConflict4_prefix_0131 (rest : Word4) :
    sigConflict4 ([p0, p1, p3, p1] ++ rest) := by
  refine ⟨p3, 1, 2, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake1 : ([p0, p1, p3, p1] ++ rest).take 1 = [p0] := by simp
    have htake2 : ([p0, p1, p3, p1] ++ rest).take 2 = [p0, p1] := by simp
    rw [htake1, htake2]
    simp [flipBit4, left4, right4, p0, p1, p3]
  · simp [moverAt?, Xor', p0, p1, p3]

theorem sigConflict4_prefix_0212 (rest : Word4) :
    sigConflict4 ([p0, p2, p1, p2] ++ rest) := by
  refine ⟨p2, 0, 1, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake0 : ([p0, p2, p1, p2] ++ rest).take 0 = ([] : Word4) := by simp
    have htake1 : ([p0, p2, p1, p2] ++ rest).take 1 = [p0] := by simp
    rw [htake0, htake1]
    simp [flipBit4, left4, right4, p0, p1, p2]
  · simp [moverAt?, Xor', p0, p1, p2]

theorem sigConflict4_prefix_01210 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p1, p0] ++ rest) := by
  refine ⟨p0, 1, 4, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake1 : ([p0, p1, p2, p1, p0] ++ rest).take 1 = [p0] := by simp
    have htake4 : ([p0, p1, p2, p1, p0] ++ rest).take 4 = [p0, p1, p2, p1] := by simp
    rw [htake1, htake4]
    simp [flipBit4, left4, right4, p0, p1, p2]
  · simp [moverAt?, Xor', p0, p1, p2]

theorem sigConflict4_prefix_01212 (x : Proc4) (rest : Word4) (hx : x ≠ p1) :
    sigConflict4 ([p0, p1, p2, p1, p2, x] ++ rest) := by
  refine ⟨p1, 1, 5, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake1 : ([p0, p1, p2, p1, p2, x] ++ rest).take 1 = [p0] := by simp
    have htake5 : ([p0, p1, p2, p1, p2, x] ++ rest).take 5 = [p0, p1, p2, p1, p2] := by simp
    rw [htake1, htake5]
    simp [flipBit4, left4, right4, p0, p1, p2]
  · have hx1 : ¬ x = 1 := by simpa [p1] using hx
    simp [moverAt?, Xor', p0, p1, p2, hx1]

theorem sigConflict4_prefix_01213 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p1, p3] ++ rest) := by
  refine ⟨p3, 3, 4, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake3 : ([p0, p1, p2, p1, p3] ++ rest).take 3 = [p0, p1, p2] := by simp
    have htake4 : ([p0, p1, p2, p1, p3] ++ rest).take 4 = [p0, p1, p2, p1] := by simp
    rw [htake3, htake4]
    simp [flipBit4, left4, right4, p0, p1, p2, p3]
  · simp [moverAt?, Xor', p0, p1, p2, p3]

theorem sigConflict4_prefix_0123032 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p3, p0, p3, p2] ++ rest) := by
  refine ⟨p2, 3, 6, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake3 : ([p0, p1, p2, p3, p0, p3, p2] ++ rest).take 3 = [p0, p1, p2] := by simp
    have htake6 : ([p0, p1, p2, p3, p0, p3, p2] ++ rest).take 6 = [p0, p1, p2, p3, p0, p3] := by simp
    rw [htake3, htake6]
    decide
  · simp [moverAt?, Xor', p0, p1, p2, p3]

theorem sigConflict4_sweep_turnback_two_steps_right (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, left4 a, a, left4 a, anti4 a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p3, p0, p3, p2] ++ rest') :=
    sigConflict4_prefix_0123032 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p2, p3, p0, p3, p2] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p3, p0, p3, p2] ++ rest') =
        [a, right4 a, anti4 a, left4 a, a, left4 a, anti4 a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2, rotProc4_p3]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_sweep_turnback_two_steps_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, anti4 a, right4 a, a, right4 a, anti4 a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_sweep_turnback_two_steps_right a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', left4 a', a', left4 a', anti4 a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, right4 a, a, right4 a, anti4 a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_prefix_0121210 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p1, p2, p1, p0] ++ rest) := by
  refine ⟨p0, 2, 6, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake2 : ([p0, p1, p2, p1, p2, p1, p0] ++ rest).take 2 = [p0, p1] := by simp
    have htake6 : ([p0, p1, p2, p1, p2, p1, p0] ++ rest).take 6 = [p0, p1, p2, p1, p2, p1] := by simp
    rw [htake2, htake6]
    decide
  · simp [moverAt?, Xor', p0, p1, p2, p3]

theorem sigConflict4_oneSided_right_long (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p1, p2, p1, p0] ++ rest') :=
    sigConflict4_prefix_0121210 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p2, p1, p2, p1, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p1, p2, p1, p0] ++ rest') =
        [a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_oneSided_left_long (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_oneSided_right_long a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', right4 a', anti4 a', right4 a', a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_prefix_012121210 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest) := by
  refine ⟨p0, 1, 8, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake1 : ([p0, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest).take 1 = [p0] := by simp
    have htake8 : ([p0, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest).take 8 =
        [p0, p1, p2, p1, p2, p1, p2, p1] := by simp
    rw [htake1, htake8]
    decide
  · simp [moverAt?, Xor', p0, p1, p2, p3]

theorem sigConflict4_oneSided_right_longer (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') :=
    sigConflict4_prefix_012121210 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') =
        [a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_oneSided_left_longer (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_oneSided_right_longer a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', right4 a', anti4 a', right4 a', anti4 a', right4 a', a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_prefix_01212121210 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest) := by
  refine ⟨p0, 2, 10, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake2 : ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest).take 2 = [p0, p1] := by simp
    have htake10 :
        ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest).take 10 =
          [p0, p1, p2, p1, p2, p1, p2, p1, p2, p1] := by simp
    rw [htake2, htake10]
    decide
  · simp [moverAt?, Xor', p0, p1, p2, p3]

theorem sigConflict4_oneSided_right_longest (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') :=
    sigConflict4_prefix_01212121210 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') =
        [a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_oneSided_left_longest (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_oneSided_right_longest a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', right4 a', anti4 a', right4 a', anti4 a', right4 a', anti4 a', right4 a', a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_prefix_0121212121210 (rest : Word4) :
    sigConflict4 ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest) := by
  refine ⟨p0, 1, 12, by decide, by simp, ?_, ?_⟩
  · unfold sig4 prefixParity4 prefixState4
    have htake1 : ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest).take 1 = [p0] := by
      simp
    have htake12 :
        ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest).take 12 =
          [p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p2, p1] := by
      simp
    rw [htake1, htake12]
    decide
  · simp [moverAt?, Xor', p0, p1, p2, p3]

theorem sigConflict4_oneSided_right_len12 (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') :=
    sigConflict4_prefix_0121212121210 rest'
  have hrot := sigConflict4_rotWord4 a.val
    ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p1, p2, p1, p2, p1, p2, p1, p2, p1, p0] ++ rest') =
        [a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, anti4 a, right4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_oneSided_left_len12 (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_oneSided_right_len12 a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', right4 a', anti4 a', right4 a', anti4 a', right4 a', anti4 a', right4 a', anti4 a', right4 a', a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, anti4 a, left4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abac_right_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, a, anti4 a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p0, p2] ++ rest') :=
    sigConflict4_prefix_0102 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p0, p2] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hword :
      rotWord4 a.val ([p0, p1, p0, p2] ++ rest') = [a, right4 a, a, anti4 a] ++ rest := by
    have hrest' : List.map (rotProc4 a.val) rest' = rest := by
      simpa [rotWord4] using hrest
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abac_right_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, a, left4 a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p0, p3] ++ rest') :=
    sigConflict4_prefix_0103 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p0, p3] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p0, p3] ++ rest') = [a, right4 a, a, left4 a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p3]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abac_anti_right (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, anti4 a, a, right4 a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p2, p0, p1] ++ rest') :=
    sigConflict4_prefix_0201 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p2, p0, p1] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p2, p0, p1] ++ rest') = [a, anti4 a, a, right4 a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abac_left_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, a, anti4 a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abac_right_anti a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', a', anti4 a'] ++ revWord4 rest) =
        [a, left4 a, a, anti4 a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abac_left_right (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, a, right4 a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abac_right_left a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', a', left4 a'] ++ revWord4 rest) =
        [a, left4 a, a, right4 a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abac_anti_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, anti4 a, a, left4 a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abac_anti_right a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', anti4 a', a', right4 a'] ++ revWord4 rest) =
        [a, anti4 a, a, left4 a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abac
    {a b d : Proc4} (hab : b ≠ a) (had : d ≠ a) (hbd : b ≠ d) (rest : Word4) :
    sigConflict4 ([a, b, a, d] ++ rest) := by
  rcases Proc4_rel_cases a b with h | h | h | h
  · contradiction
  · subst h
    rcases Proc4_rel_cases a d with hd | hd | hd | hd
    · contradiction
    · exact False.elim (hbd hd.symm)
    · subst hd
      simpa using sigConflict4_abac_right_anti a rest
    · subst hd
      simpa using sigConflict4_abac_right_left a rest
  · subst h
    rcases Proc4_rel_cases a d with hd | hd | hd | hd
    · contradiction
    · subst hd
      simpa using sigConflict4_abac_anti_right a rest
    · exact False.elim (hbd hd.symm)
    · subst hd
      simpa using sigConflict4_abac_anti_left a rest
  · subst h
    rcases Proc4_rel_cases a d with hd | hd | hd | hd
    · contradiction
    · subst hd
      simpa using sigConflict4_abac_left_right a rest
    · subst hd
      simpa using sigConflict4_abac_left_anti a rest
    · exact False.elim (hbd hd.symm)

theorem sigConflict4_bounce_right_exit_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, a, right4 a, a, left4 a] ++ rest) := by
  apply sigConflict4_append_suffix [a, right4 a]
  simpa [List.cons_append] using sigConflict4_abac_right_left a rest

theorem sigConflict4_bounce_right_exit_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, a, right4 a, a, anti4 a] ++ rest) := by
  apply sigConflict4_append_suffix [a, right4 a]
  simpa [List.cons_append] using sigConflict4_abac_right_anti a rest

theorem sigConflict4_bounce_left_exit_right (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, a, left4 a, a, right4 a] ++ rest) := by
  apply sigConflict4_append_suffix [a, left4 a]
  simpa [List.cons_append] using sigConflict4_abac_left_right a rest

theorem sigConflict4_bounce_left_exit_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, a, left4 a, a, anti4 a] ++ rest) := by
  apply sigConflict4_append_suffix [a, left4 a]
  simpa [List.cons_append] using sigConflict4_abac_left_anti a rest

theorem sigConflict4_bounceRight_exit_left (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 (bounceRightWord4 a (n + 1) ++ [left4 a] ++ rest)
  | 0, rest => by
      simpa [bounceRightWord4, List.append_assoc] using
        sigConflict4_abac_right_left a rest
  | n + 1, rest => by
      apply sigConflict4_append_suffix [a, right4 a]
      simpa [bounceRightWord4, List.append_assoc] using
        sigConflict4_bounceRight_exit_left a n rest

theorem sigConflict4_bounceRight_exit_anti (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 (bounceRightWord4 a (n + 1) ++ [anti4 a] ++ rest)
  | 0, rest => by
      simpa [bounceRightWord4, List.append_assoc] using
        sigConflict4_abac_right_anti a rest
  | n + 1, rest => by
      apply sigConflict4_append_suffix [a, right4 a]
      simpa [bounceRightWord4, List.append_assoc] using
        sigConflict4_bounceRight_exit_anti a n rest

theorem sigConflict4_bounceLeft_exit_right (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 (bounceLeftWord4 a (n + 1) ++ [right4 a] ++ rest)
  | 0, rest => by
      simpa [bounceLeftWord4, List.append_assoc] using
        sigConflict4_abac_left_right a rest
  | n + 1, rest => by
      apply sigConflict4_append_suffix [a, left4 a]
      simpa [bounceLeftWord4, List.append_assoc] using
        sigConflict4_bounceLeft_exit_right a n rest

theorem sigConflict4_bounceLeft_exit_anti (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 (bounceLeftWord4 a (n + 1) ++ [anti4 a] ++ rest)
  | 0, rest => by
      simpa [bounceLeftWord4, List.append_assoc] using
        sigConflict4_abac_left_anti a rest
  | n + 1, rest => by
      apply sigConflict4_append_suffix [a, left4 a]
      simpa [bounceLeftWord4, List.append_assoc] using
        sigConflict4_bounceLeft_exit_anti a n rest

theorem sigConflict4_shortRightBounce_exit_left (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 ([a] ++ bounceLeftWord4 (right4 a) (n + 1) ++ [left4 a] ++ rest)
  | n, rest => by
      apply sigConflict4_append_suffix [a]
      simpa [bounceLeftWord4, List.append_assoc, anti4_right4] using
        sigConflict4_bounceLeft_exit_anti (right4 a) n rest

theorem sigConflict4_shortRightBounce_exit_anti (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 ([a] ++ bounceLeftWord4 (right4 a) (n + 1) ++ [anti4 a] ++ rest)
  | n, rest => by
      apply sigConflict4_append_suffix [a]
      simpa [bounceLeftWord4, List.append_assoc, right4_right4] using
        sigConflict4_bounceLeft_exit_right (right4 a) n rest

theorem sigConflict4_shortLeftBounce_exit_right (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 ([a] ++ bounceRightWord4 (left4 a) (n + 1) ++ [right4 a] ++ rest)
  | n, rest => by
      apply sigConflict4_append_suffix [a]
      simpa [bounceRightWord4, List.append_assoc, anti4_left4] using
        sigConflict4_bounceRight_exit_anti (left4 a) n rest

theorem sigConflict4_shortLeftBounce_exit_anti (a : Proc4) :
    ∀ (n : Nat) (rest : Word4),
      sigConflict4 ([a] ++ bounceRightWord4 (left4 a) (n + 1) ++ [anti4 a] ++ rest)
  | n, rest => by
      apply sigConflict4_append_suffix [a]
      simpa [bounceRightWord4, List.append_assoc, left4_left4] using
        sigConflict4_bounceRight_exit_left (left4 a) n rest

theorem sigConflict4_abca_right_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p0] ++ rest') :=
    sigConflict4_prefix_0120 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p2, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p0] ++ rest') = [a, right4 a, anti4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abca_right_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, left4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p3, p0] ++ rest') :=
    sigConflict4_prefix_0130 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p3, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p3, p0] ++ rest') = [a, right4 a, left4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p3]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abca_anti_right (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, anti4 a, right4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p2, p1, p0] ++ rest') :=
    sigConflict4_prefix_0210 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p2, p1, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p2, p1, p0] ++ rest') = [a, anti4 a, right4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abca_left_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, anti4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abca_right_anti a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abca_left_right (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, right4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abca_right_left a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', left4 a', a'] ++ revWord4 rest) =
        [a, left4 a, right4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abca_anti_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, anti4 a, left4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abca_anti_right a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', anti4 a', right4 a', a'] ++ revWord4 rest) =
        [a, anti4 a, left4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abca
    {a b c : Proc4} (hab : b ≠ a) (hac : c ≠ a) (hbc : b ≠ c) (rest : Word4) :
    sigConflict4 ([a, b, c, a] ++ rest) := by
  rcases Proc4_rel_cases a b with h | h | h | h
  · contradiction
  · subst h
    rcases Proc4_rel_cases a c with hc | hc | hc | hc
    · contradiction
    · exact False.elim (hbc hc.symm)
    · subst hc
      simpa using sigConflict4_abca_right_anti a rest
    · subst hc
      simpa using sigConflict4_abca_right_left a rest
  · subst h
    rcases Proc4_rel_cases a c with hc | hc | hc | hc
    · contradiction
    · subst hc
      simpa using sigConflict4_abca_anti_right a rest
    · exact False.elim (hbc hc.symm)
    · subst hc
      simpa using sigConflict4_abca_anti_left a rest
  · subst h
    rcases Proc4_rel_cases a c with hc | hc | hc | hc
    · contradiction
    · subst hc
      simpa using sigConflict4_abca_left_right a rest
    · subst hc
      simpa using sigConflict4_abca_left_anti a rest
    · exact False.elim (hbc hc.symm)

theorem sigConflict4_abcb_right_left_right (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, left4 a, right4 a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p3, p1] ++ rest') :=
    sigConflict4_prefix_0131 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p3, p1] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p3, p1] ++ rest') = [a, right4 a, left4 a, right4 a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p3]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abcb_anti_right_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, anti4 a, right4 a, anti4 a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p2, p1, p2] ++ rest') :=
    sigConflict4_prefix_0212 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p2, p1, p2] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p2, p1, p2] ++ rest') = [a, anti4 a, right4 a, anti4 a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abcb_right_anti_right_self (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p1, p0] ++ rest') :=
    sigConflict4_prefix_01210 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p2, p1, p0] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p1, p0] ++ rest') = [a, right4 a, anti4 a, right4 a, a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abcb_right_anti_right_anti (a : Proc4) (x : Proc4) (rest : Word4)
    (hx : x ≠ right4 a) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, anti4 a, x] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hxrot : rotProc4 a.val (rotProc4 ((4 - a.val % 4) % 4) x) = x := by
    apply Fin.ext
    simp [rotProc4]
    omega
  have hx' : rotProc4 ((4 - a.val % 4) % 4) x ≠ p1 := by
    intro h
    apply hx
    calc
      x = rotProc4 a.val (rotProc4 ((4 - a.val % 4) % 4) x) := hxrot.symm
      _ = rotProc4 a.val p1 := by rw [h]
      _ = right4 a := rotProc4_p1 a
  have hcanon : sigConflict4 ([p0, p1, p2, p1, p2, rotProc4 ((4 - a.val % 4) % 4) x] ++ rest') :=
    sigConflict4_prefix_01212 _ rest' hx'
  have hrot := sigConflict4_rotWord4 a.val
    ([p0, p1, p2, p1, p2, rotProc4 ((4 - a.val % 4) % 4) x] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p1, p2, rotProc4 ((4 - a.val % 4) % 4) x] ++ rest') =
        [a, right4 a, anti4 a, right4 a, anti4 a, x] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2, hxrot]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abcb_right_anti_right_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, left4 a] ++ rest) := by
  let rest' := rotWord4 ((4 - a.val % 4) % 4) rest
  have hcanon : sigConflict4 ([p0, p1, p2, p1, p3] ++ rest') :=
    sigConflict4_prefix_01213 rest'
  have hrot := sigConflict4_rotWord4 a.val ([p0, p1, p2, p1, p3] ++ rest') hcanon
  have hrest : rotWord4 a.val rest' = rest := by
    unfold rest'
    exact rotWord4_invRot a.val rest
  have hrest' : List.map (rotProc4 a.val) rest' = rest := by
    simpa [rotWord4] using hrest
  have hword :
      rotWord4 a.val ([p0, p1, p2, p1, p3] ++ rest') = [a, right4 a, anti4 a, right4 a, left4 a] ++ rest := by
    rw [rotWord4, List.map_append, hrest']
    simp [rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2, rotProc4_p3]
  rw [hword] at hrot
  exact hrot

theorem sigConflict4_abcb_right_anti_right_anti_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a, anti4 a, left4 a] ++ rest) :=
  sigConflict4_abcb_right_anti_right_anti a (left4 a) rest ((localTriple_distinct a).2.2)

theorem head_ne_right_of_balanced_abcb_right_anti_right
    (a x : Proc4) (rest : Word4)
    (hbal : BalancedWord4 ([a, right4 a, anti4 a, right4 a, x] ++ rest)) :
    x ≠ right4 a := by
  intro hx
  have hcnt := hbal (right4 a)
  have ha : a ≠ right4 a := by
    intro h
    exact (localTriple_distinct a).2.1 h.symm
  have hanti : anti4 a ≠ right4 a := anti4_ne_right4 a
  simp [BalancedWord4, List.count_append, List.count_cons, hx, ha, hanti] at hcnt

theorem tail_nonempty_of_balanced_abcb_right_anti_right_anti
    (a : Proc4) (rest : Word4)
    (hbal : BalancedWord4 ([a, right4 a, anti4 a, right4 a, anti4 a] ++ rest)) :
    rest ≠ [] := by
  intro hnil
  have hcnt := hbal (left4 a)
  have ha : a ≠ left4 a := by
    intro h
    exact (localTriple_distinct a).1 h.symm
  have hright : right4 a ≠ left4 a := by
    intro h
    exact (localTriple_distinct a).2.2 h.symm
  have hanti : anti4 a ≠ left4 a := anti4_ne_left4 a
  simp [BalancedWord4, List.count_append, List.count_cons, hnil, ha, hright, hanti] at hcnt

theorem head_ne_right_of_balanced_abcb_right_anti_right_anti
    (a y : Proc4) (rest : Word4)
    (hbal : BalancedWord4 ([a, right4 a, anti4 a, right4 a, anti4 a, y] ++ rest)) :
    y ≠ right4 a := by
  intro hy
  have hcnt := hbal (right4 a)
  have ha : a ≠ right4 a := by
    intro h
    exact (localTriple_distinct a).2.1 h.symm
  have hanti : anti4 a ≠ right4 a := anti4_ne_right4 a
  simp [BalancedWord4, List.count_append, List.count_cons, hy, ha, hanti] at hcnt

theorem sigConflict4_abcb_right_anti_right_balanced
    (a : Proc4) (rest : Word4)
    (hbal : BalancedWord4 ([a, right4 a, anti4 a, right4 a] ++ rest)) :
    sigConflict4 ([a, right4 a, anti4 a, right4 a] ++ rest) := by
  cases rest with
  | nil =>
      have hcnt := hbal (left4 a)
      have ha : a ≠ left4 a := by
        intro h
        exact (localTriple_distinct a).1 h.symm
      have hright : right4 a ≠ left4 a := by
        intro h
        exact (localTriple_distinct a).2.2 h.symm
      have hanti : anti4 a ≠ left4 a := anti4_ne_left4 a
      simp [BalancedWord4, List.count_append, List.count_cons, ha, hright, hanti] at hcnt
  | cons x xs =>
      have hxR : x ≠ right4 a :=
        head_ne_right_of_balanced_abcb_right_anti_right a x xs (by simpa [List.cons_append] using hbal)
      rcases Proc4_rel_cases a x with hx0 | hx0 | hx0 | hx0
      · subst hx0
        simpa [List.cons_append] using sigConflict4_abcb_right_anti_right_self _ xs
      · contradiction
      · subst hx0
        cases xs with
        | nil =>
            have hne := tail_nonempty_of_balanced_abcb_right_anti_right_anti a []
              (by simpa [List.cons_append] using hbal)
            contradiction
        | cons y ys =>
            have hyR : y ≠ right4 a :=
              head_ne_right_of_balanced_abcb_right_anti_right_anti a y ys
                (by simpa [List.cons_append] using hbal)
            simpa [List.cons_append] using sigConflict4_abcb_right_anti_right_anti _ y ys hyR
      · subst hx0
        simpa [List.cons_append] using sigConflict4_abcb_right_anti_right_left _ xs

theorem BalancedWord4_revWord4 {w : Word4} (h : BalancedWord4 w) :
    BalancedWord4 (revWord4 w) := by
  intro j
  calc
    (revWord4 w).count j = w.count (revProc4 j) := by
      simpa [revWord4, revProc4_involutive] using
        (List.count_map_of_injective (l := w) (f := revProc4) revProc4_injective (x := revProc4 j))
    _ = 2 := h (revProc4 j)

theorem sigConflict4_abcb_left_right_left (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, right4 a, left4 a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abcb_right_left_right a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', left4 a', right4 a'] ++ revWord4 rest) =
        [a, left4 a, right4 a, left4 a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abcb_anti_left_anti (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, anti4 a, left4 a, anti4 a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abcb_anti_right_anti a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', anti4 a', right4 a', anti4 a'] ++ revWord4 rest) =
        [a, anti4 a, left4 a, anti4 a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abcb_left_anti_left_balanced (a : Proc4) (rest : Word4)
    (hbal : BalancedWord4 ([a, left4 a, anti4 a, left4 a] ++ rest)) :
    sigConflict4 ([a, left4 a, anti4 a, left4 a] ++ rest) := by
  let a' := revProc4 a
  have hbal' : BalancedWord4 ([a', right4 a', anti4 a', right4 a'] ++ revWord4 rest) := by
    simpa [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive] using
      BalancedWord4_revWord4 hbal
  have h := sigConflict4_abcb_right_anti_right_balanced a' (revWord4 rest) hbal'
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', right4 a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, left4 a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abcb_left_anti_left_self (a : Proc4) (rest : Word4) :
    sigConflict4 ([a, left4 a, anti4 a, left4 a, a] ++ rest) := by
  let a' := revProc4 a
  have h := sigConflict4_abcb_right_anti_right_self a' (revWord4 rest)
  have hrest : revWord4 (revWord4 rest) = rest := revWord4_involutive rest
  have hrest' : List.map revProc4 (revWord4 rest) = rest := by
    simpa [revWord4] using hrest
  have hshape :
      revWord4 ([a', right4 a', anti4 a', right4 a', a'] ++ revWord4 rest) =
        [a, left4 a, anti4 a, left4 a, a] ++ rest := by
    rw [revWord4, List.map_append, hrest']
    simp [a', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4, revProc4_involutive]
  exact sigConflict4_rev_transport hshape h

theorem sigConflict4_abcb
    {a b c : Proc4} (hab : b ≠ a) (hac : c ≠ a) (hbc : b ≠ c)
    (rest : Word4) (hbal : BalancedWord4 ([a, b, c, b] ++ rest)) :
    sigConflict4 ([a, b, c, b] ++ rest) := by
  rcases Proc4_rel_cases a b with hb | hb | hb | hb
  · contradiction
  · subst hb
    rcases Proc4_rel_cases a c with hc | hc | hc | hc
    · contradiction
    · exact False.elim (hbc hc.symm)
    · subst hc
      simpa using sigConflict4_abcb_right_anti_right_balanced a rest hbal
    · subst hc
      simpa using sigConflict4_abcb_right_left_right a rest
  · subst hb
    rcases Proc4_rel_cases a c with hc | hc | hc | hc
    · contradiction
    · subst hc
      simpa using sigConflict4_abcb_anti_right_anti a rest
    · exact False.elim (hbc hc.symm)
    · subst hc
      simpa using sigConflict4_abcb_anti_left_anti a rest
  · subst hb
    rcases Proc4_rel_cases a c with hc | hc | hc | hc
    · contradiction
    · subst hc
      simpa using sigConflict4_abcb_left_right_left a rest
    · subst hc
      simpa using sigConflict4_abcb_left_anti_left_balanced a rest hbal
    · exact False.elim (hbc hc.symm)

theorem first_four_adjacent_ne_of_simple
    {a b c d : Proc4} {rest : Word4}
    (hrest : rest ≠ [])
    (hsimple : SimpleWord4 (a :: b :: c :: d :: rest)) :
    a ≠ b ∧ b ≠ c ∧ c ≠ d := by
  constructor
  · intro hab
    have hns := not_simple_of_adjacent_repeat_with_tail [] (c :: d :: rest) a (by simp [hab])
    have hsimple' : SimpleWord4 (a :: a :: c :: d :: rest) := by
      intro t u htu huu
      simpa [hab] using hsimple (t := t) (u := u) htu huu
    have hns' : ¬ SimpleWord4 (a :: a :: c :: d :: rest) := by
      simpa [hab] using hns
    exact hns' hsimple'
  constructor
  · intro hbc
    have hns := not_simple_of_adjacent_repeat_with_tail [a] (d :: rest) b (by simp [hbc])
    have hsimple' : SimpleWord4 (a :: c :: c :: d :: rest) := by
      intro t u htu huu
      simpa [hbc] using hsimple (t := t) (u := u) htu huu
    have hns' : ¬ SimpleWord4 (a :: c :: c :: d :: rest) := by
      simpa [hbc] using hns
    exact hns' hsimple'
  · intro hcd
    have hns := not_simple_of_adjacent_repeat_with_tail [a, b] rest c hrest
    have hsimple' : SimpleWord4 (a :: b :: d :: d :: rest) := by
      intro t u htu huu
      simpa [hcd] using hsimple (t := t) (u := u) htu huu
    have hns' : ¬ SimpleWord4 (a :: b :: d :: d :: rest) := by
      simpa [hcd] using hns
    exact hns' hsimple'

theorem sigConflict4_of_not_nodup_first_four
    {a b c d : Proc4} {rest : Word4}
    (hrest : rest ≠ [])
    (hsimple : SimpleWord4 (a :: b :: c :: d :: rest))
    (hbal : BalancedWord4 (a :: b :: c :: d :: rest))
    (hnodup : ¬ List.Nodup [a, b, c, d]) :
    sigConflict4 (a :: b :: c :: d :: rest) := by
  rcases first_four_adjacent_ne_of_simple hrest hsimple with ⟨hab, hbc, hcd⟩
  rcases first_four_repeat_shape_of_simple hrest hsimple hnodup with hshape | hshape
  · rcases hshape with ⟨hac, hbd⟩
    have had : d ≠ a := by
      intro h
      exact hcd (hac.symm.trans h.symm)
    simpa [hac] using sigConflict4_abac (a := a) (b := b) (d := d) hab.symm had hbd rest
  · rcases hshape with had | hshape
    · have hac : c ≠ a := by
        intro h
        exact hcd (h.trans had)
      simpa [had] using sigConflict4_abca (a := a) (b := b) (c := c) hab.symm hac hbc rest
    · rcases hshape with ⟨hbd, hac⟩
      have hbal' : BalancedWord4 ([a, b, c, b] ++ rest) := by
        simpa [hbd] using hbal
      simpa [hbd] using sigConflict4_abcb (a := a) (b := b) (c := c) hab.symm hac.symm hbc rest hbal'

theorem first_four_nodup_of_no_sigConflict
    {a b c d : Proc4} {rest : Word4}
    (hrest : rest ≠ [])
    (hsimple : SimpleWord4 (a :: b :: c :: d :: rest))
    (hbal : BalancedWord4 (a :: b :: c :: d :: rest))
    (hno : ¬ sigConflict4 (a :: b :: c :: d :: rest)) :
    List.Nodup [a, b, c, d] := by
  by_contra hnodup
  exact hno (sigConflict4_of_not_nodup_first_four hrest hsimple hbal hnodup)

theorem first_four_sweep_or_reverse_of_no_sigConflict
    {a b c d : Proc4} {rest : Word4}
    (hrest : rest ≠ [])
    (hsimple : SimpleWord4 (a :: b :: c :: d :: rest))
    (hbal : BalancedWord4 (a :: b :: c :: d :: rest))
    (hno : ¬ sigConflict4 (a :: b :: c :: d :: rest)) :
    (b = right4 a ∧ c = anti4 a ∧ d = left4 a) ∨
      (b = left4 a ∧ c = anti4 a ∧ d = right4 a) := by
  have hnodup := first_four_nodup_of_no_sigConflict hrest hsimple hbal hno
  have hneqs : (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d) ∧ c ≠ d := by
    simpa using hnodup
  have hab : b ≠ a := hneqs.1.1.symm
  have hac : c ≠ a := hneqs.1.2.1.symm
  have had : d ≠ a := hneqs.1.2.2.symm
  have hbc : c ≠ b := hneqs.2.1.1.symm
  have hbd : d ≠ b := hneqs.2.1.2.symm
  have hcd : d ≠ c := hneqs.2.2.symm
  have habAnti : b ≠ anti4 a := by
    intro h
    apply hno
    apply sigConflict4_of_hasAdjacentAnti4
    refine ⟨[], c :: d :: rest, anti4 a, ?_⟩
    simp [h, anti4_anti4]
  have hbcAnti : c ≠ anti4 b := by
    intro h
    apply hno
    apply sigConflict4_of_hasAdjacentAnti4
    refine ⟨[a], d :: rest, anti4 b, ?_⟩
    simp [h, anti4_anti4]
  have hcdAnti : d ≠ anti4 c := by
    intro h
    apply hno
    apply sigConflict4_of_hasAdjacentAnti4
    refine ⟨[a, b], rest, anti4 c, ?_⟩
    simp [h, anti4_anti4]
  exact sweep_or_reverse_of_distinct_no_adjacent_anti hab hac had hbc hbd hcd habAnti hbcAnti hcdAnti

theorem first_four_sweep_or_reverse_of_localNoStay
    {a b c d : Proc4} {rest : Word4}
    (hlocal : LocalNoStayWord4 (a :: b :: c :: d :: rest))
    (hnodup : List.Nodup [a, b, c, d]) :
    (b = right4 a ∧ c = anti4 a ∧ d = left4 a) ∨
      (b = left4 a ∧ c = anti4 a ∧ d = right4 a) := by
  have hneqs : (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d) ∧ c ≠ d := by
    simpa using hnodup
  have hab : b ≠ a := hneqs.1.1.symm
  have hac : c ≠ a := hneqs.1.2.1.symm
  have had : d ≠ a := hneqs.1.2.2.symm
  have hbc : c ≠ b := hneqs.2.1.1.symm
  have hbd : d ≠ b := hneqs.2.1.2.symm
  have hcd : d ≠ c := hneqs.2.2.symm
  have habAnti : b ≠ anti4 a := by
    rcases localNoStay_cons_left hlocal with hb | hb
    · rw [hb]
      exact (anti4_ne_left4 a).symm
    · rw [hb]
      exact (anti4_ne_right4 a).symm
  have hbcAnti : c ≠ anti4 b := by
    rcases localNoStay_cons_left (localNoStay_tail hlocal) with hc | hc
    · rw [hc]
      exact (anti4_ne_left4 b).symm
    · rw [hc]
      exact (anti4_ne_right4 b).symm
  have hcdAnti : d ≠ anti4 c := by
    rcases localNoStay_cons_left (localNoStay_tail (localNoStay_tail hlocal)) with hd | hd
    · rw [hd]
      exact (anti4_ne_left4 c).symm
    · rw [hd]
      exact (anti4_ne_right4 c).symm
  exact sweep_or_reverse_of_distinct_no_adjacent_anti hab hac had hbc hbd hcd
    habAnti hbcAnti hcdAnti

theorem count_sweep_prefix_eq_one (a j : Proc4) :
    [a, right4 a, anti4 a, left4 a].count j = 1 := by
  rcases Proc4_rel_cases a j with h | h | h | h
  · rw [h]
    have h1 : a ≠ right4 a := by
      intro h'
      exact (localTriple_distinct a).2.1 h'.symm
    have h2 : a ≠ anti4 a := by
      intro h'
      exact anti4_ne_self a h'.symm
    have h3 : a ≠ left4 a := by
      intro h'
      exact (localTriple_distinct a).1 h'.symm
    have hb1 : (right4 a == a) = false := beq_eq_false_iff_ne.mpr (by exact h1.symm)
    have hb2 : (anti4 a == a) = false := beq_eq_false_iff_ne.mpr (by exact h2.symm)
    have hb3 : (left4 a == a) = false := beq_eq_false_iff_ne.mpr (by exact h3.symm)
    simp [List.count_cons, hb1, hb2, hb3]
  · rw [h]
    have h1 : right4 a ≠ a := (localTriple_distinct a).2.1
    have h2 : right4 a ≠ anti4 a := by
      intro h'
      exact anti4_ne_right4 a h'.symm
    have h3 : right4 a ≠ left4 a := by
      intro h'
      exact (localTriple_distinct a).2.2 h'.symm
    have hb1 : (a == right4 a) = false := beq_eq_false_iff_ne.mpr (by exact h1.symm)
    have hb2 : (anti4 a == right4 a) = false := beq_eq_false_iff_ne.mpr (by exact h2.symm)
    have hb3 : (left4 a == right4 a) = false := beq_eq_false_iff_ne.mpr (by exact h3.symm)
    simp [List.count_cons, hb1, hb2, hb3]
  · rw [h]
    have h1 : anti4 a ≠ a := anti4_ne_self a
    have h2 : anti4 a ≠ right4 a := anti4_ne_right4 a
    have h3 : anti4 a ≠ left4 a := anti4_ne_left4 a
    have hb1 : (a == anti4 a) = false := beq_eq_false_iff_ne.mpr (by exact h1.symm)
    have hb2 : (right4 a == anti4 a) = false := beq_eq_false_iff_ne.mpr (by exact h2.symm)
    have hb3 : (left4 a == anti4 a) = false := beq_eq_false_iff_ne.mpr (by exact h3.symm)
    simp [List.count_cons, hb1, hb2, hb3]
  · rw [h]
    have h1 : left4 a ≠ a := (localTriple_distinct a).1
    have h2 : left4 a ≠ right4 a := (localTriple_distinct a).2.2
    have h3 : left4 a ≠ anti4 a := by
      intro h'
      exact anti4_ne_left4 a h'.symm
    have hb1 : (a == left4 a) = false := beq_eq_false_iff_ne.mpr (by exact h1.symm)
    have hb2 : (right4 a == left4 a) = false := beq_eq_false_iff_ne.mpr (by exact h2.symm)
    have hb3 : (anti4 a == left4 a) = false := beq_eq_false_iff_ne.mpr (by exact h3.symm)
    simp [List.count_cons, hb1, hb2, hb3]

theorem tail_count_eq_one_of_balanced_first_sweep
    (a e f g h j : Proc4)
    (hbal : BalancedWord4 ([a, right4 a, anti4 a, left4 a] ++ [e, f, g, h])) :
    [e, f, g, h].count j = 1 := by
  have h := hbal j
  rw [List.count_append, count_sweep_prefix_eq_one] at h
  omega

theorem tail_nodup_of_balanced_first_sweep
    (a e f g h : Proc4)
    (hbal : BalancedWord4 ([a, right4 a, anti4 a, left4 a] ++ [e, f, g, h])) :
    List.Nodup [e, f, g, h] := by
  apply (List.nodup_iff_count_le_one).2
  intro j
  have h := tail_count_eq_one_of_balanced_first_sweep a e f g h j hbal
  omega

theorem baseWord4_sig_p0_t1 : sig4 baseWord4 1 p0 = (false, true, false) := by
  decide

theorem baseWord4_sig_p0_t2 : sig4 baseWord4 2 p0 = (false, true, true) := by
  decide

theorem baseWord4_sig_p1_t2 : sig4 baseWord4 2 p1 = (true, true, false) := by
  decide

theorem baseWord4_sig_p1_t3 : sig4 baseWord4 3 p1 = (true, true, true) := by
  decide

theorem baseWord4_sig_p2_t2 : sig4 baseWord4 2 p2 = (true, false, false) := by
  decide

theorem baseWord4_sig_p2_t3 : sig4 baseWord4 3 p2 = (true, true, false) := by
  decide

theorem baseWord4_forwardRot1_sig_p1_t3 :
    sig4 baseWord4_forwardRot1 3 p1 = (true, true, true) := by
  decide

theorem baseWord4_forwardRot1_sig_p1_t4 :
    sig4 baseWord4_forwardRot1 4 p1 = (true, true, true) := by
  decide

theorem sigConflict4_base_forwardRot1 : sigConflict4 baseWord4_forwardRot1 := by
  refine ⟨p1, 3, 4, by decide, by decide, ?_, ?_⟩
  · rw [baseWord4_forwardRot1_sig_p1_t3, baseWord4_forwardRot1_sig_p1_t4]
  · decide

theorem baseWord4_forwardRot2_sig_p0_t2 :
    sig4 baseWord4_forwardRot2 2 p0 = (false, true, true) := by
  decide

theorem baseWord4_forwardRot2_sig_p0_t6 :
    sig4 baseWord4_forwardRot2 6 p0 = (false, true, true) := by
  decide

theorem sigConflict4_base_forwardRot2 : sigConflict4 baseWord4_forwardRot2 := by
  refine ⟨p0, 2, 6, by decide, by decide, ?_, ?_⟩
  · rw [baseWord4_forwardRot2_sig_p0_t2, baseWord4_forwardRot2_sig_p0_t6]
  · decide

theorem baseWord4_forwardRot3_sig_p0_t2 :
    sig4 baseWord4_forwardRot3 2 p0 = (false, true, true) := by
  decide

theorem baseWord4_forwardRot3_sig_p0_t5 :
    sig4 baseWord4_forwardRot3 5 p0 = (false, true, true) := by
  decide

theorem sigConflict4_base_forwardRot3 : sigConflict4 baseWord4_forwardRot3 := by
  refine ⟨p0, 2, 5, by decide, by decide, ?_, ?_⟩
  · rw [baseWord4_forwardRot3_sig_p0_t2, baseWord4_forwardRot3_sig_p0_t5]
  · decide

theorem baseWord4_reverse0_sig_p2_t3 :
    sig4 baseWord4_reverse0 3 p2 = (true, true, false) := by
  decide

theorem baseWord4_reverse0_sig_p2_t6 :
    sig4 baseWord4_reverse0 6 p2 = (true, true, false) := by
  decide

theorem sigConflict4_base_reverse0 : sigConflict4 baseWord4_reverse0 := by
  refine ⟨p2, 3, 6, by decide, by decide, ?_, ?_⟩
  · rw [baseWord4_reverse0_sig_p2_t3, baseWord4_reverse0_sig_p2_t6]
  · decide

theorem baseWord4_reverse1_sig_p0_t0 :
    sig4 baseWord4_reverse1 0 p0 = (false, false, false) := by
  decide

theorem baseWord4_reverse1_sig_p0_t7 :
    sig4 baseWord4_reverse1 7 p0 = (false, false, false) := by
  decide

theorem sigConflict4_base_reverse1 : sigConflict4 baseWord4_reverse1 := by
  refine ⟨p0, 0, 7, by decide, by decide, ?_, ?_⟩
  · rw [baseWord4_reverse1_sig_p0_t0, baseWord4_reverse1_sig_p0_t7]
  · decide

theorem baseWord4_reverse2_sig_p1_t2 :
    sig4 baseWord4_reverse2 2 p1 = (true, true, false) := by
  decide

theorem baseWord4_reverse2_sig_p1_t5 :
    sig4 baseWord4_reverse2 5 p1 = (true, true, false) := by
  decide

theorem sigConflict4_base_reverse2 : sigConflict4 baseWord4_reverse2 := by
  refine ⟨p1, 2, 5, by decide, by decide, ?_, ?_⟩
  · rw [baseWord4_reverse2_sig_p1_t2, baseWord4_reverse2_sig_p1_t5]
  · decide

theorem baseWord4_reverse3_sig_p1_t2 :
    sig4 baseWord4_reverse3 2 p1 = (true, true, false) := by
  decide

theorem baseWord4_reverse3_sig_p1_t6 :
    sig4 baseWord4_reverse3 6 p1 = (true, true, false) := by
  decide

theorem sigConflict4_base_reverse3 : sigConflict4 baseWord4_reverse3 := by
  refine ⟨p1, 2, 6, by decide, by decide, ?_, ?_⟩
  · rw [baseWord4_reverse3_sig_p1_t2, baseWord4_reverse3_sig_p1_t6]
  · decide

theorem sigConflict4_rot_base_forwardRot1 (k : Nat) :
    sigConflict4 (rotWord4 k baseWord4_forwardRot1) :=
  sigConflict4_rotWord4 k baseWord4_forwardRot1 sigConflict4_base_forwardRot1

theorem sigConflict4_rot_base_reverse0 (k : Nat) :
    sigConflict4 (rotWord4 k baseWord4_reverse0) :=
  sigConflict4_rotWord4 k baseWord4_reverse0 sigConflict4_base_reverse0

theorem forwardSweepFrom0_eq_baseWord4_forwardRot1 :
    forwardSweepFrom0 p1 = baseWord4_forwardRot1 := by
  rfl

theorem forwardSweepFrom0_eq_baseWord4_forwardRot2 :
    forwardSweepFrom0 p2 = baseWord4_forwardRot2 := by
  rfl

theorem forwardSweepFrom0_eq_baseWord4_forwardRot3 :
    forwardSweepFrom0 p3 = baseWord4_forwardRot3 := by
  rfl

theorem reverseSweepFrom0_eq_baseWord4_reverse0 :
    reverseSweepFrom0 p0 = baseWord4_reverse0 := by
  rfl

theorem reverseSweepFrom0_eq_baseWord4_reverse1 :
    reverseSweepFrom0 p1 = baseWord4_reverse1 := by
  rfl

theorem reverseSweepFrom0_eq_baseWord4_reverse2 :
    reverseSweepFrom0 p2 = baseWord4_reverse2 := by
  rfl

theorem reverseSweepFrom0_eq_baseWord4_reverse3 :
    reverseSweepFrom0 p3 = baseWord4_reverse3 := by
  rfl

theorem sigConflict4_forwardSweepFrom0_of_ne_p0 (start : Proc4) (hstart : start ≠ p0) :
    sigConflict4 (forwardSweepFrom0 start) := by
  rcases Proc4_cases start with rfl | rfl | rfl | rfl
  · contradiction
  · simpa [forwardSweepFrom0_eq_baseWord4_forwardRot1] using sigConflict4_base_forwardRot1
  · simpa [forwardSweepFrom0_eq_baseWord4_forwardRot2] using sigConflict4_base_forwardRot2
  · simpa [forwardSweepFrom0_eq_baseWord4_forwardRot3] using sigConflict4_base_forwardRot3

theorem sigConflict4_reverseSweepFrom0 (start : Proc4) :
    sigConflict4 (reverseSweepFrom0 start) := by
  rcases Proc4_cases start with rfl | rfl | rfl | rfl
  · simpa [reverseSweepFrom0_eq_baseWord4_reverse0] using sigConflict4_base_reverse0
  · simpa [reverseSweepFrom0_eq_baseWord4_reverse1] using sigConflict4_base_reverse1
  · simpa [reverseSweepFrom0_eq_baseWord4_reverse2] using sigConflict4_base_reverse2
  · simpa [reverseSweepFrom0_eq_baseWord4_reverse3] using sigConflict4_base_reverse3

theorem forwardSweepWord4_eq_rot (σ τ : Proc4) :
    forwardSweepWord4 σ τ = rotWord4 σ.1 (forwardSweepFrom0 (invRotProc4 σ.1 τ)) := by
  simp [forwardSweepWord4, forwardSweepFrom0, rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2,
    rotProc4_p3, rotProc4_inv_left, rotProc4_right4, rotProc4_anti4, rotProc4_left4]

theorem reverseSweepWord4_eq_rot (σ τ : Proc4) :
    reverseSweepWord4 σ τ = rotWord4 σ.1 (reverseSweepFrom0 (invRotProc4 σ.1 τ)) := by
  simp [reverseSweepWord4, reverseSweepFrom0, rotWord4, rotProc4_p0, rotProc4_p1, rotProc4_p2,
    rotProc4_p3, rotProc4_inv_left, rotProc4_right4, rotProc4_anti4, rotProc4_left4]

theorem invRotProc4_ne_p0_of_ne (σ τ : Proc4) (h : τ ≠ σ) :
    invRotProc4 σ.1 τ ≠ p0 := by
  intro h0
  apply h
  calc
    τ = rotProc4 σ.1 (invRotProc4 σ.1 τ) := by rw [rotProc4_inv_left]
    _ = rotProc4 σ.1 p0 := by rw [h0]
    _ = σ := rotProc4_p0 σ

theorem sigConflict4_forwardSweepWord4_of_ne (σ τ : Proc4) (h : τ ≠ σ) :
    sigConflict4 (forwardSweepWord4 σ τ) := by
  rw [forwardSweepWord4_eq_rot]
  exact sigConflict4_rotWord4 σ.1 _ <|
    sigConflict4_forwardSweepFrom0_of_ne_p0 _ (invRotProc4_ne_p0_of_ne σ τ h)

theorem sigConflict4_reverseSweepWord4 (σ τ : Proc4) :
    sigConflict4 (reverseSweepWord4 σ τ) := by
  rw [reverseSweepWord4_eq_rot]
  exact sigConflict4_rotWord4 σ.1 _ (sigConflict4_reverseSweepFrom0 _)

theorem second_four_sweep_or_reverse_of_forward_no_sigConflict
    (a e f g h : Proc4)
    (hbal : BalancedWord4 [a, right4 a, anti4 a, left4 a, e, f, g, h])
    (hno : ¬ sigConflict4 [a, right4 a, anti4 a, left4 a, e, f, g, h]) :
    (f = right4 e ∧ g = anti4 e ∧ h = left4 e) ∨
      (f = left4 e ∧ g = anti4 e ∧ h = right4 e) := by
  have htail := tail_nodup_of_balanced_first_sweep a e f g h hbal
  have hneqs : (e ≠ f ∧ e ≠ g ∧ e ≠ h) ∧ (f ≠ g ∧ f ≠ h) ∧ g ≠ h := by
    simpa using htail
  have hef : e ≠ f := hneqs.1.1
  have heg : e ≠ g := hneqs.1.2.1
  have heh : e ≠ h := hneqs.1.2.2
  have hfg : f ≠ g := hneqs.2.1.1
  have hfh : f ≠ h := hneqs.2.1.2
  have hgh : g ≠ h := hneqs.2.2
  have hfg' : g ≠ f := hfg.symm
  have hfh' : h ≠ f := hfh.symm
  have hgh' : h ≠ g := hgh.symm
  have hefAnti : f ≠ anti4 e := by
    intro heq
    apply hno
    apply sigConflict4_of_hasAdjacentAnti4
    refine ⟨[a, right4 a, anti4 a, left4 a], [g, h], anti4 e, ?_⟩
    simp [heq, anti4_anti4]
  have hfgAnti : g ≠ anti4 f := by
    intro heq
    apply hno
    apply sigConflict4_of_hasAdjacentAnti4
    refine ⟨[a, right4 a, anti4 a, left4 a, e], [h], anti4 f, ?_⟩
    simp [heq, anti4_anti4]
  have hghAnti : h ≠ anti4 g := by
    intro heq
    apply hno
    apply sigConflict4_of_hasAdjacentAnti4
    refine ⟨[a, right4 a, anti4 a, left4 a, e, f], [], anti4 g, ?_⟩
    simp [heq, anti4_anti4]
  exact sweep_or_reverse_of_distinct_no_adjacent_anti hef.symm heg.symm heh.symm hfg' hfh' hgh'
    hefAnti hfgAnti hghAnti

theorem second_four_agree_of_forward_no_sigConflict
    (a e f g h : Proc4)
    (hbal : BalancedWord4 [a, right4 a, anti4 a, left4 a, e, f, g, h])
    (hno : ¬ sigConflict4 [a, right4 a, anti4 a, left4 a, e, f, g, h]) :
    e = a ∧ f = right4 a ∧ g = anti4 a ∧ h = left4 a := by
  rcases second_four_sweep_or_reverse_of_forward_no_sigConflict a e f g h hbal hno with hsweep | hsweep
  · have hea : e = a := by
      by_contra hne
      apply hno
      simpa [forwardSweepWord4, hsweep.1, hsweep.2.1, hsweep.2.2] using
        sigConflict4_forwardSweepWord4_of_ne a e hne
    subst hea
    exact ⟨rfl, hsweep⟩
  · exfalso
    apply hno
    simpa [reverseSweepWord4, hsweep.1, hsweep.2.1, hsweep.2.2] using
      sigConflict4_reverseSweepWord4 a e

theorem second_four_agree_of_reverse_no_sigConflict
    (a e f g h : Proc4)
    (hbal : BalancedWord4 [a, left4 a, anti4 a, right4 a, e, f, g, h])
    (hno : ¬ sigConflict4 [a, left4 a, anti4 a, right4 a, e, f, g, h]) :
    e = a ∧ f = left4 a ∧ g = anti4 a ∧ h = right4 a := by
  let a' := revProc4 a
  let e' := revProc4 e
  let f' := revProc4 f
  let g' := revProc4 g
  let h' := revProc4 h
  have hbal' : BalancedWord4 [a', right4 a', anti4 a', left4 a', e', f', g', h'] := by
    simpa [a', e', f', g', h', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4,
      revProc4_involutive] using
      BalancedWord4_revWord4 hbal
  have hshape :
      revWord4 [a', right4 a', anti4 a', left4 a', e', f', g', h'] =
        [a, left4 a, anti4 a, right4 a, e, f, g, h] := by
    simp [a', e', f', g', h', revWord4, left4_revProc4, right4_revProc4, anti4_revProc4,
      revProc4_involutive]
  have hno' : ¬ sigConflict4 [a', right4 a', anti4 a', left4 a', e', f', g', h'] := by
    intro hs
    exact hno (sigConflict4_rev_transport hshape hs)
  have hforward := second_four_agree_of_forward_no_sigConflict a' e' f' g' h' hbal' hno'
  rcases hforward with ⟨he, hf, hg, hh⟩
  have he' : e = a := by
    apply revProc4_injective
    simpa [a', e'] using he
  have hf' : f = left4 a := by
    apply revProc4_injective
    simpa [a', f', right4_revProc4] using hf
  have hg' : g = anti4 a := by
    apply revProc4_injective
    simpa [a', g', anti4_revProc4] using hg
  have hh' : h = right4 a := by
    apply revProc4_injective
    simpa [a', h', left4_revProc4] using hh
  exact ⟨he', hf', hg', hh'⟩

theorem eight_word_sweep_of_no_sigConflict
    {a b c d e f g h : Proc4}
    (hrest : [e, f, g, h] ≠ [])
    (hsimple : SimpleWord4 [a, b, c, d, e, f, g, h])
    (hbal : BalancedWord4 [a, b, c, d, e, f, g, h])
    (hno : ¬ sigConflict4 [a, b, c, d, e, f, g, h]) :
    ([a, b, c, d, e, f, g, h] = forwardSweepWord4 a a) ∨
      ([a, b, c, d, e, f, g, h] = [a, left4 a, anti4 a, right4 a, a, left4 a, anti4 a, right4 a]) := by
  rcases first_four_sweep_or_reverse_of_no_sigConflict hrest hsimple hbal hno with hsweep | hsweep
  · rcases hsweep with ⟨hb, hc, hd⟩
    subst hb hc hd
    have htail := second_four_agree_of_forward_no_sigConflict a e f g h hbal hno
    rcases htail with ⟨hea, hfr, hga, hhl⟩
    subst hea hfr hga hhl
    left
    rfl
  · rcases hsweep with ⟨hb, hc, hd⟩
    subst hb hc hd
    have htail := second_four_agree_of_reverse_no_sigConflict a e f g h hbal hno
    rcases htail with ⟨hea, hfl, hga, hhr⟩
    subst hea hfl hga hhr
    right
    rfl

end LeanMn
