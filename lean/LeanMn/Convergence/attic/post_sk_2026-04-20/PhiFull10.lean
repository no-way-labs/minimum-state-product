/-
  Convergence/PhiFull10.lean — PhiFull at n=10 + passive base case

  Uses Array-based fixpoint (same approach as PhiFull9.lean) to compute
  PhiFull at n=10. The passive base case checks all 26244 × 10 entries.
-/
import LeanMn.Convergence.PhiFullTP
import LeanMn.Convergence.SixTuple

namespace LeanMn

private abbrev hn4_10 : 4 ≤ 10 := by omega
private abbrev hn9_10 : 9 ≤ 10 := by omega
private def N10 : Nat := 26244
private abbrev fin10 (k : Nat) (h : k < 10) : Fin (cup2Spec 10 hn4_10).n :=
  ⟨k, by show k < 10; exact h⟩

private def encodeCfg10 (c : Config (cup2Spec 10 hn4_10)) : Nat :=
  (c (fin10 0 (by omega))).1 * 13122 + (c (fin10 1 (by omega))).1 * 4374 +
  (c (fin10 2 (by omega))).1 * 1458 + (c (fin10 3 (by omega))).1 * 486 +
  (c (fin10 4 (by omega))).1 * 162 + (c (fin10 5 (by omega))).1 * 54 +
  (c (fin10 6 (by omega))).1 * 18 + (c (fin10 7 (by omega))).1 * 6 +
  (c (fin10 8 (by omega))).1 * 2 + (c (fin10 9 (by omega))).1

private def decodeCfg10 (idx : Nat) : Config (cup2Spec 10 hn4_10) :=
  let d (w m : Nat) (hm : 0 < m) : Fin m := ⟨(idx / w) % m, Nat.mod_lt _ hm⟩
  fun i => match i with
    | ⟨0, _⟩ => ⟨(d 13122 2 (by omega)).1, by have := (d 13122 2 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨1, _⟩ => ⟨(d 4374 3 (by omega)).1, by have := (d 4374 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨2, _⟩ => ⟨(d 1458 3 (by omega)).1, by have := (d 1458 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨3, _⟩ => ⟨(d 486 3 (by omega)).1, by have := (d 486 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨4, _⟩ => ⟨(d 162 3 (by omega)).1, by have := (d 162 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨5, _⟩ => ⟨(d 54 3 (by omega)).1, by have := (d 54 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨6, _⟩ => ⟨(d 18 3 (by omega)).1, by have := (d 18 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨7, _⟩ => ⟨(d 6 3 (by omega)).1, by have := (d 6 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨8, _⟩ => ⟨(d 2 3 (by omega)).1, by have := (d 2 3 (by omega)).2; simp [cup2Spec, cup2M]⟩
    | ⟨9, _⟩ => ⟨(d 1 2 (by omega)).1, by have := (d 1 2 (by omega)).2; simp [cup2Spec, cup2M]⟩

private def fc10 (idx : Nat) : Nat := cup2Fc 10 hn4_10 (decodeCfg10 idx)
private def fire10 (idx : Nat) (p : Fin 10) : Nat :=
  encodeCfg10 (move (cup2System 10 hn4_10) (decodeCfg10 idx) p)
private def priv10 (idx : Nat) (p : Fin 10) : Bool :=
  decide (privileged (cup2System 10 hn4_10) (decodeCfg10 idx) p)
private def good10 (idx : Nat) : Bool :=
  decide (decodeCfg10 idx ∈ (cup2GoodCycle 10 hn4_10).configs)
private def tpPres10 (idx : Nat) (p : Fin 10) : Bool :=
  cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) (decodeCfg10 idx) p) ==
    cup2TpInvariant 10 hn4_10 (decodeCfg10 idx)
private def bdry10 (idx : Nat) : Nat :=
  (cup2BoundaryState 10 hn4_10 hn9_10 (decodeCfg10 idx)).1
private def hasDeepCopyPair10 (idx : Nat) : Bool :=
  let c := decodeCfg10 idx
  (c (fin10 4 (by omega))).1 == (c (fin10 3 (by omega))).1 ||
  (c (fin10 4 (by omega))).1 == (c (fin10 5 (by omega))).1 ||
  (c (fin10 5 (by omega))).1 == (c (fin10 4 (by omega))).1 ||
  (c (fin10 5 (by omega))).1 == (c (fin10 6 (by omega))).1 ||
  (c (fin10 6 (by omega))).1 == (c (fin10 5 (by omega))).1 ||
  (c (fin10 6 (by omega))).1 == (c (fin10 7 (by omega))).1

/-! ### Array-based PhiFull10 -/

private def phiStep10 (phi : Array Nat) : Array Nat :=
  Array.ofFn fun (v : Fin N10) =>
    let base := fc10 v.1
    let maxSucc := Id.run do
      let mut best := 0
      for p in List.finRange 10 do
        if priv10 v.1 p && !good10 (fire10 v.1 p) && tpPres10 v.1 p then
          let sv := fire10 v.1 p
          if sv < N10 then
            let sphi := phi.getD sv 0
            if sphi > best then best := sphi
      return best
    if good10 v.1 then 0 else Nat.max base maxSucc

private def phiIter10 : Nat → Array Nat
  | 0 => Array.ofFn fun (v : Fin N10) => if good10 v.1 then 0 else fc10 v.1
  | k + 1 => phiStep10 (phiIter10 k)

def phiFull10Array : Array Nat := phiIter10 20
private def phiFull10 (idx : Nat) : Nat := phiFull10Array.getD idx 0

/-! ### H_nocopy check -/

private def noCopyEdgeCodes10 : Array Nat := #[
  973, 1952, 2277, 2927, 3256, 3581, 6823, 7802, 8127, 8777, 9106, 9431, 11664, 11989, 12314,
  12639, 12673, 12964, 13289, 13614, 13652, 13939, 13977, 14264, 14589, 14627, 14914, 14956, 15239, 15281,
  15564, 15889, 16214, 16539, 16864, 17189, 17568, 17893, 18218, 18523, 18543, 18851, 18868, 19193, 19502,
  19518, 19827, 19843, 20168, 20477, 20493, 20801, 20806, 20818, 21131, 21143, 21468, 21793, 22118, 22443,
  22751, 22768, 23093, 23418, 23743, 24068, 24373, 24393, 24701, 24718, 25043, 25352, 25368, 25677, 25693,
  26018, 26327, 26343, 26651, 26656, 26668, 26981, 26993, 27318, 27643, 27968, 28293, 28601, 28618, 28943,
  30223, 30551, 31202, 31527, 32177, 32501, 32506, 32831, 34451, 36073, 36401, 37052, 37377, 38027, 38351,
  38356, 38681, 40301, 40932, 41257, 41582, 41907, 41923, 42232, 42251, 42557, 42882, 42902, 43207, 43227,
  43532, 43857, 43877, 44182, 44201, 44206, 44507, 44531, 44832, 45157, 45482, 45807, 46132, 46151, 46457,
  46692, 47017, 47342, 47667, 47773, 47992, 48317, 48642, 48752, 48967, 49077, 49292, 49617, 49727, 49942,
  50056, 50267, 50381, 50592, 50917, 51242, 51567, 51892, 52217, 52974, 53623, 54602, 54924, 54927, 55251,
  55577, 55906, 56231, 56874, 58824, 59473, 60452, 60774, 60777, 61101, 61427, 61756, 62081, 62724, 64314,
  64639, 64674, 64964, 65289, 65323, 65614, 65939, 66264, 66302, 66589, 66624, 66627, 66914, 66951, 67239,
  67277, 67564, 67606, 67889, 67931, 68214, 68539, 68574, 68864, 69189, 69514, 69839, 70218, 70524, 70543,
  70868, 71173, 71193, 71518, 71843, 72152, 72168, 72474, 72477, 72493, 72801, 72818, 73127, 73143, 73456,
  73468, 73781, 73793, 74118, 74424, 74443, 74768, 75093, 75418, 75743, 76068, 76374, 76393, 76718, 77023,
  77043, 77368, 77693, 78002, 78018, 78324, 78327, 78343, 78651, 78668, 78977, 78993, 79306, 79318, 79631,
  79643, 79968, 80274, 80293, 80618, 80943, 81268, 81593, 81954, 82224, 82279, 82604, 82873, 82929, 83254,
  83579, 83852, 83904, 84174, 84177, 84229, 84501, 84554, 84827, 84879, 85156, 85204, 85481, 85529, 85854,
  86179, 86504, 86829, 87154, 87479, 88074, 88723, 89702, 90024, 90027, 90351, 90677, 91006, 91331, 93582,
  93907, 93924, 94232, 94557, 94573, 94882, 95207, 95532, 95552, 95857, 95874, 95877, 96182, 96201, 96507,
  96527, 96832, 96856, 97157, 97181, 97482, 97807, 98132, 98457, 98782, 99107, 99774, 100423, 101402, 101724,
  101727, 102051, 102377, 102706, 103031]

private def passiveCheck10 (src_idx : Nat) (p : Fin 10) : Bool :=
  let dst_idx := fire10 src_idx p
  if !(priv10 src_idx p) then true else
  if good10 src_idx || good10 dst_idx then true else
  if bdry10 dst_idx == bdry10 src_idx then true else
  if hasDeepCopyPair10 dst_idx then true else
  if !(phiFull10 dst_idx == phiFull10 src_idx) then true else
  if !(tpPres10 src_idx p) then true else
  noCopyEdgeCodes10.contains (bdry10 src_idx * 324 + bdry10 dst_idx)

/-! ### Full n=10 no-witness check -/


/-! ### Passive base case -/

private theorem pcb0 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨0, by omega⟩ = true := by native_decide
private theorem pcb1 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨1, by omega⟩ = true := by native_decide
private theorem pcb2 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨2, by omega⟩ = true := by native_decide
private theorem pcb3 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨3, by omega⟩ = true := by native_decide
private theorem pcb4 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨4, by omega⟩ = true := by native_decide
private theorem pcb5 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨5, by omega⟩ = true := by native_decide
private theorem pcb6 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨6, by omega⟩ = true := by native_decide
private theorem pcb7 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨7, by omega⟩ = true := by native_decide
private theorem pcb8 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨8, by omega⟩ = true := by native_decide
private theorem pcb9 : ∀ s : Fin N10, passiveCheck10 s.1 ⟨9, by omega⟩ = true := by native_decide

theorem passive_noCopy_base10 :
    ∀ src_idx : Fin N10, ∀ p : Fin 10,
      passiveCheck10 src_idx.1 p = true := by
  intro s p; fin_cases p <;> first | exact pcb0 s | exact pcb1 s | exact pcb2 s |
    exact pcb3 s | exact pcb4 s | exact pcb5 s | exact pcb6 s | exact pcb7 s |
    exact pcb8 s | exact pcb9 s

private theorem asb0 :
    ∀ (c : Config (cup2Spec 10 hn4_10)),
    privileged (cup2System 10 hn4_10) c ⟨0, by omega⟩ →
    c ∉ (cup2GoodCycle 10 hn4_10).configs →
    move (cup2System 10 hn4_10) c ⟨0, by omega⟩ ∉ (cup2GoodCycle 10 hn4_10).configs →
    cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨0, by omega⟩) =
      cup2TpInvariant 10 hn4_10 c →
    cup2PhiFull 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨0, by omega⟩) =
      cup2PhiFull 10 hn4_10 c →
    cup2BoundaryState 10 hn4_10 hn9_10
      (move (cup2System 10 hn4_10) c ⟨0, by omega⟩) ≠
      cup2BoundaryState 10 hn4_10 hn9_10 c →
    let dst := move (cup2System 10 hn4_10) c ⟨0, by omega⟩
    ((dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨3, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨4, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨6, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨7, by omega⟩ : Fin 10)).1) →
    sixTupleEdge
      (cup2BoundaryState 10 hn4_10 hn9_10
        (move (cup2System 10 hn4_10) c ⟨0, by omega⟩))
      (cup2BoundaryState 10 hn4_10 hn9_10 c) := by
  native_decide

private theorem asb1 :
    ∀ (c : Config (cup2Spec 10 hn4_10)),
    privileged (cup2System 10 hn4_10) c ⟨1, by omega⟩ →
    c ∉ (cup2GoodCycle 10 hn4_10).configs →
    move (cup2System 10 hn4_10) c ⟨1, by omega⟩ ∉ (cup2GoodCycle 10 hn4_10).configs →
    cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨1, by omega⟩) =
      cup2TpInvariant 10 hn4_10 c →
    cup2PhiFull 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨1, by omega⟩) =
      cup2PhiFull 10 hn4_10 c →
    cup2BoundaryState 10 hn4_10 hn9_10
      (move (cup2System 10 hn4_10) c ⟨1, by omega⟩) ≠
      cup2BoundaryState 10 hn4_10 hn9_10 c →
    let dst := move (cup2System 10 hn4_10) c ⟨1, by omega⟩
    ((dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨3, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨4, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨6, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨7, by omega⟩ : Fin 10)).1) →
    sixTupleEdge
      (cup2BoundaryState 10 hn4_10 hn9_10
        (move (cup2System 10 hn4_10) c ⟨1, by omega⟩))
      (cup2BoundaryState 10 hn4_10 hn9_10 c) := by
  native_decide

private theorem asb2 :
    ∀ (c : Config (cup2Spec 10 hn4_10)),
    privileged (cup2System 10 hn4_10) c ⟨2, by omega⟩ →
    c ∉ (cup2GoodCycle 10 hn4_10).configs →
    move (cup2System 10 hn4_10) c ⟨2, by omega⟩ ∉ (cup2GoodCycle 10 hn4_10).configs →
    cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨2, by omega⟩) =
      cup2TpInvariant 10 hn4_10 c →
    cup2PhiFull 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨2, by omega⟩) =
      cup2PhiFull 10 hn4_10 c →
    cup2BoundaryState 10 hn4_10 hn9_10
      (move (cup2System 10 hn4_10) c ⟨2, by omega⟩) ≠
      cup2BoundaryState 10 hn4_10 hn9_10 c →
    let dst := move (cup2System 10 hn4_10) c ⟨2, by omega⟩
    ((dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨3, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨4, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨6, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨7, by omega⟩ : Fin 10)).1) →
    sixTupleEdge
      (cup2BoundaryState 10 hn4_10 hn9_10
        (move (cup2System 10 hn4_10) c ⟨2, by omega⟩))
      (cup2BoundaryState 10 hn4_10 hn9_10 c) := by
  native_decide

private theorem asb7 :
    ∀ (c : Config (cup2Spec 10 hn4_10)),
    privileged (cup2System 10 hn4_10) c ⟨7, by omega⟩ →
    c ∉ (cup2GoodCycle 10 hn4_10).configs →
    move (cup2System 10 hn4_10) c ⟨7, by omega⟩ ∉ (cup2GoodCycle 10 hn4_10).configs →
    cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨7, by omega⟩) =
      cup2TpInvariant 10 hn4_10 c →
    cup2PhiFull 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨7, by omega⟩) =
      cup2PhiFull 10 hn4_10 c →
    cup2BoundaryState 10 hn4_10 hn9_10
      (move (cup2System 10 hn4_10) c ⟨7, by omega⟩) ≠
      cup2BoundaryState 10 hn4_10 hn9_10 c →
    let dst := move (cup2System 10 hn4_10) c ⟨7, by omega⟩
    ((dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨3, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨4, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨6, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨7, by omega⟩ : Fin 10)).1) →
    sixTupleEdge
      (cup2BoundaryState 10 hn4_10 hn9_10
        (move (cup2System 10 hn4_10) c ⟨7, by omega⟩))
      (cup2BoundaryState 10 hn4_10 hn9_10 c) := by
  native_decide

private theorem asb8 :
    ∀ (c : Config (cup2Spec 10 hn4_10)),
    privileged (cup2System 10 hn4_10) c ⟨8, by omega⟩ →
    c ∉ (cup2GoodCycle 10 hn4_10).configs →
    move (cup2System 10 hn4_10) c ⟨8, by omega⟩ ∉ (cup2GoodCycle 10 hn4_10).configs →
    cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨8, by omega⟩) =
      cup2TpInvariant 10 hn4_10 c →
    cup2PhiFull 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨8, by omega⟩) =
      cup2PhiFull 10 hn4_10 c →
    cup2BoundaryState 10 hn4_10 hn9_10
      (move (cup2System 10 hn4_10) c ⟨8, by omega⟩) ≠
      cup2BoundaryState 10 hn4_10 hn9_10 c →
    let dst := move (cup2System 10 hn4_10) c ⟨8, by omega⟩
    ((dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨3, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨4, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨6, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨7, by omega⟩ : Fin 10)).1) →
    sixTupleEdge
      (cup2BoundaryState 10 hn4_10 hn9_10
        (move (cup2System 10 hn4_10) c ⟨8, by omega⟩))
      (cup2BoundaryState 10 hn4_10 hn9_10 c) := by
  native_decide

private theorem asb9 :
    ∀ (c : Config (cup2Spec 10 hn4_10)),
    privileged (cup2System 10 hn4_10) c ⟨9, by omega⟩ →
    c ∉ (cup2GoodCycle 10 hn4_10).configs →
    move (cup2System 10 hn4_10) c ⟨9, by omega⟩ ∉ (cup2GoodCycle 10 hn4_10).configs →
    cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨9, by omega⟩) =
      cup2TpInvariant 10 hn4_10 c →
    cup2PhiFull 10 hn4_10 (move (cup2System 10 hn4_10) c ⟨9, by omega⟩) =
      cup2PhiFull 10 hn4_10 c →
    cup2BoundaryState 10 hn4_10 hn9_10
      (move (cup2System 10 hn4_10) c ⟨9, by omega⟩) ≠
      cup2BoundaryState 10 hn4_10 hn9_10 c →
    let dst := move (cup2System 10 hn4_10) c ⟨9, by omega⟩
    ((dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨3, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨4, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨6, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨7, by omega⟩ : Fin 10)).1) →
    sixTupleEdge
      (cup2BoundaryState 10 hn4_10 hn9_10
        (move (cup2System 10 hn4_10) c ⟨9, by omega⟩))
      (cup2BoundaryState 10 hn4_10 hn9_10 c) := by
  native_decide

theorem active_sixTuple_base10 :
    ∀ (c : Config (cup2Spec 10 hn4_10)) (p : Fin 10),
    (p.1 ≤ 2 ∨ 7 ≤ p.1) →
    privileged (cup2System 10 hn4_10) c p →
    c ∉ (cup2GoodCycle 10 hn4_10).configs →
    move (cup2System 10 hn4_10) c p ∉ (cup2GoodCycle 10 hn4_10).configs →
    cup2TpInvariant 10 hn4_10 (move (cup2System 10 hn4_10) c p) =
      cup2TpInvariant 10 hn4_10 c →
    cup2PhiFull 10 hn4_10 (move (cup2System 10 hn4_10) c p) =
      cup2PhiFull 10 hn4_10 c →
    cup2BoundaryState 10 hn4_10 hn9_10
      (move (cup2System 10 hn4_10) c p) ≠
      cup2BoundaryState 10 hn4_10 hn9_10 c →
    let dst := move (cup2System 10 hn4_10) c p
    ((dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨3, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨4, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨4, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨5, by omega⟩ : Fin 10)).1 = (dst (⟨6, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨5, by omega⟩ : Fin 10)).1 ∨
     (dst (⟨6, by omega⟩ : Fin 10)).1 = (dst (⟨7, by omega⟩ : Fin 10)).1) →
    sixTupleEdge
      (cup2BoundaryState 10 hn4_10 hn9_10
        (move (cup2System 10 hn4_10) c p))
      (cup2BoundaryState 10 hn4_10 hn9_10 c) := by
  intro c p hp_bdry
  fin_cases p
  · exact asb0 c
  · exact asb1 c
  · exact asb2 c
  · omega
  · omega
  · omega
  · omega
  · exact asb7 c
  · exact asb8 c
  · exact asb9 c

end LeanMn
