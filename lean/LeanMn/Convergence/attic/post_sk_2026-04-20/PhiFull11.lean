/- 
  Convergence/PhiFull11.lean — Encoded active no-drop base check at n=11

  Purpose:
  - feasibility check for the finite-base computational route at n=11
  - keep the file minimal: encoded configs, array PhiFull, active checker only
-/
import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SixTuple

namespace LeanMn

private abbrev hn4_11 : 4 ≤ 11 := by omega
private abbrev hn9_11 : 9 ≤ 11 := by omega
private def N11 : Nat := 78732
private abbrev fin11 (k : Nat) (h : k < 11) : Fin (cup2Spec 11 hn4_11).n :=
  ⟨k, by show k < 11; exact h⟩

private def encodeCfg11 (c : Config (cup2Spec 11 hn4_11)) : Nat :=
  (c (fin11 0 (by omega))).1 * 39366 + (c (fin11 1 (by omega))).1 * 13122 +
  (c (fin11 2 (by omega))).1 * 4374 + (c (fin11 3 (by omega))).1 * 1458 +
  (c (fin11 4 (by omega))).1 * 486 + (c (fin11 5 (by omega))).1 * 162 +
  (c (fin11 6 (by omega))).1 * 54 + (c (fin11 7 (by omega))).1 * 18 +
  (c (fin11 8 (by omega))).1 * 6 + (c (fin11 9 (by omega))).1 * 2 +
  (c (fin11 10 (by omega))).1

private def decodeCfg11 (idx : Nat) : Config (cup2Spec 11 hn4_11) :=
  let d (w m : Nat) (hm : 0 < m) : Fin m := ⟨(idx / w) % m, Nat.mod_lt _ hm⟩
  fun i => match i with
    | ⟨0, _⟩ => ⟨(d 39366 2 (by omega)).1, by have := (d 39366 2 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨1, _⟩ => ⟨(d 13122 3 (by omega)).1, by have := (d 13122 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨2, _⟩ => ⟨(d 4374 3 (by omega)).1, by have := (d 4374 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨3, _⟩ => ⟨(d 1458 3 (by omega)).1, by have := (d 1458 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨4, _⟩ => ⟨(d 486 3 (by omega)).1, by have := (d 486 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨5, _⟩ => ⟨(d 162 3 (by omega)).1, by have := (d 162 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨6, _⟩ => ⟨(d 54 3 (by omega)).1, by have := (d 54 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨7, _⟩ => ⟨(d 18 3 (by omega)).1, by have := (d 18 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨8, _⟩ => ⟨(d 6 3 (by omega)).1, by have := (d 6 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨9, _⟩ => ⟨(d 2 3 (by omega)).1, by have := (d 2 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨10, _⟩ => ⟨(d 1 2 (by omega)).1, by have := (d 1 2 (by omega)).2; simp [cup2Spec, cup2M]⟩

private def fc11 (idx : Nat) : Nat := cup2Fc 11 hn4_11 (decodeCfg11 idx)
private def fire11 (idx : Nat) (p : Fin 11) : Nat :=
  encodeCfg11 (move (cup2System 11 hn4_11) (decodeCfg11 idx) p)
private def priv11 (idx : Nat) (p : Fin 11) : Bool :=
  decide (privileged (cup2System 11 hn4_11) (decodeCfg11 idx) p)
private def good11 (idx : Nat) : Bool :=
  decide (decodeCfg11 idx ∈ (cup2GoodCycle 11 hn4_11).configs)
private def tpPres11 (idx : Nat) (p : Fin 11) : Bool :=
  cup2TpInvariant 11 hn4_11 (move (cup2System 11 hn4_11) (decodeCfg11 idx) p) ==
    cup2TpInvariant 11 hn4_11 (decodeCfg11 idx)
private def hasDeepCopyPair11 (idx : Nat) : Bool :=
  let c := decodeCfg11 idx
  (c (fin11 4 (by omega))).1 == (c (fin11 3 (by omega))).1 ||
  (c (fin11 4 (by omega))).1 == (c (fin11 5 (by omega))).1 ||
  (c (fin11 5 (by omega))).1 == (c (fin11 4 (by omega))).1 ||
  (c (fin11 5 (by omega))).1 == (c (fin11 6 (by omega))).1 ||
  (c (fin11 6 (by omega))).1 == (c (fin11 5 (by omega))).1 ||
  (c (fin11 6 (by omega))).1 == (c (fin11 7 (by omega))).1 ||
  (c (fin11 7 (by omega))).1 == (c (fin11 6 (by omega))).1 ||
  (c (fin11 7 (by omega))).1 == (c (fin11 8 (by omega))).1

private def phiStep11 (phi : Array Nat) : Array Nat :=
  Array.ofFn fun (v : Fin N11) =>
    let base := fc11 v.1
    let maxSucc := Id.run do
      let mut best := 0
      for p in List.finRange 11 do
        if priv11 v.1 p && !good11 (fire11 v.1 p) && tpPres11 v.1 p then
          let sv := fire11 v.1 p
          if sv < N11 then
            let sphi := phi.getD sv 0
            if sphi > best then best := sphi
      return best
    if good11 v.1 then 0 else Nat.max base maxSucc

private def phiIter11 : Nat → Array Nat
  | 0 => Array.ofFn fun (v : Fin N11) => if good11 v.1 then 0 else fc11 v.1
  | k + 1 => phiStep11 (phiIter11 k)

def phiFull11Array : Array Nat := phiIter11 22
private def phiFull11 (idx : Nat) : Nat := phiFull11Array.getD idx 0

private def activeCheck11 (src_idx : Nat) (p : Fin 11) : Bool :=
  let dst_idx := fire11 src_idx p
  if !(priv11 src_idx p) then true else
  if good11 src_idx || good11 dst_idx then true else
  if (cup2BoundaryState 11 hn4_11 hn9_11 (decodeCfg11 dst_idx)).1 ==
     (cup2BoundaryState 11 hn4_11 hn9_11 (decodeCfg11 src_idx)).1 then true else
  if !(hasDeepCopyPair11 dst_idx) then true else
  if !(phiFull11 dst_idx == phiFull11 src_idx) then true else
  if !(tpPres11 src_idx p) then true else
  sixTupleEdge
    (cup2BoundaryState 11 hn4_11 hn9_11 (decodeCfg11 dst_idx))
    (cup2BoundaryState 11 hn4_11 hn9_11 (decodeCfg11 src_idx))

private theorem ac11b0 : ∀ s : Fin N11, activeCheck11 s.1 ⟨0, by omega⟩ = true := by native_decide
private theorem ac11b1 : ∀ s : Fin N11, activeCheck11 s.1 ⟨1, by omega⟩ = true := by native_decide
private theorem ac11b2 : ∀ s : Fin N11, activeCheck11 s.1 ⟨2, by omega⟩ = true := by native_decide
private theorem ac11b3 : ∀ s : Fin N11, activeCheck11 s.1 ⟨3, by omega⟩ = true := by native_decide
private theorem ac11b4 : ∀ s : Fin N11, activeCheck11 s.1 ⟨4, by omega⟩ = true := by native_decide
private theorem ac11b5 : ∀ s : Fin N11, activeCheck11 s.1 ⟨5, by omega⟩ = true := by native_decide
private theorem ac11b6 : ∀ s : Fin N11, activeCheck11 s.1 ⟨6, by omega⟩ = true := by native_decide
private theorem ac11b7 : ∀ s : Fin N11, activeCheck11 s.1 ⟨7, by omega⟩ = true := by native_decide
private theorem ac11b8 : ∀ s : Fin N11, activeCheck11 s.1 ⟨8, by omega⟩ = true := by native_decide
private theorem ac11b9 : ∀ s : Fin N11, activeCheck11 s.1 ⟨9, by omega⟩ = true := by native_decide
private theorem ac11b10 : ∀ s : Fin N11, activeCheck11 s.1 ⟨10, by omega⟩ = true := by native_decide

theorem active_base11 :
    ∀ src_idx : Fin N11, ∀ p : Fin 11,
      activeCheck11 src_idx.1 p = true := by
  intro s p
  fin_cases p <;> first
    | exact ac11b0 s | exact ac11b1 s | exact ac11b2 s | exact ac11b3 s
    | exact ac11b4 s | exact ac11b5 s | exact ac11b6 s | exact ac11b7 s
    | exact ac11b8 s | exact ac11b9 s | exact ac11b10 s

end LeanMn
