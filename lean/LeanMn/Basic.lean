import Mathlib

namespace LeanMn

def castFin {n m : Nat} (h : n = m) : Fin n → Fin m := Fin.cast h

def allFin (n : Nat) : List (Fin n) := List.finRange n

@[simp] theorem length_allFin (n : Nat) : (allFin n).length = n := by
  simp [allFin]

end LeanMn
