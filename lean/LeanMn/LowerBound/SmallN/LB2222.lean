/-
  SmallN/LB2222.lean — No valid self-stabilizing system on ms=(2,2,2,2), n=4.

  Discharges M_4_lower: for n=4, stateProduct < 24 → ¬valid sys.

  Proof:
  1. Arithmetic: sub-24 product with n=4, all m_i ≥ 2 ⟹ all m_i = 2.
  2. Computational: exhaustive DFS over fair directed cycles on Q₄ verifies
     all are blocked by TF entry conflict or forced bad kernel.  (~46s native_decide)
  3. Analytical bridge: GoodCycle on rs2222 → fair Q₄ cycle → DFS finds it blocked.
     (a) DFS one-step extraction (dfs_branch): proved analytically.
     (b) DFS completeness (dfs_complete): induction on remaining cycle steps.
     (c) isBlocked soundness: TF conflict contradicts f; forced kernel
         contradicts WellFounded(badStep).
-/
import LeanMn.LowerBound.SmallN.BinaryQ4Core
import LeanMn.LowerBound.SmallN.BinaryQ4GoodCyclePath
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.OfFn
import LeanMn.LowerBound.CycleTypes
import LeanMn.LowerBound.EntryConflict.BinaryParity
import LeanMn.LowerBound.EntryConflict.IsolatedFirings
import LeanMn.LowerBound.EntryConflict.TernaryPhaseEC

open scoped BigOperators

namespace LeanMn

/-! ## 1. The rs2222 ring spec -/

/-- Any RingSpec with n=4 and product < 24 must have all m_i = 2. -/
theorem sub24_all_eq_2 {n : Nat} (hn4 : 4 ≤ n) (m : Fin n → Nat)
    (hm : ∀ i, 2 ≤ m i) (hn : n = 4)
    (hsub : (∏ i : Fin n, m i) < 24) :
    ∀ i : Fin n, m i = 2 := by
  subst hn; intro i; by_contra h
  have hmi : 3 ≤ m i := by have := hm i; omega
  have h0 := hm ⟨0, by omega⟩; have h1 := hm ⟨1, by omega⟩
  have h2 := hm ⟨2, by omega⟩; have h3 := hm ⟨3, by omega⟩
  simp only [Fin.prod_univ_four] at hsub; exfalso; apply Nat.not_lt.mpr _ hsub
  show 24 ≤ m ⟨0, by omega⟩ * m ⟨1, by omega⟩ * m ⟨2, by omega⟩ * m ⟨3, by omega⟩
  fin_cases i
  · calc 24 ≤ 3 * 2 * 2 * 2 := by norm_num
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hmi h1) h2) h3
  · calc 24 ≤ 2 * 3 * 2 * 2 := by norm_num
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 hmi) h2) h3
  · calc 24 ≤ 2 * 2 * 3 * 2 := by norm_num
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) hmi) h3
  · calc 24 ≤ 2 * 2 * 2 * 3 := by norm_num
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) hmi

/-! ## 2. DFS blocking check on Q₄ -/

def hasForcedKernel (cycle : List (Nat × Nat)) : Bool :=
  match buildTF (collectTF cycle) [] with
  | none => true
  | some tfMap =>
    let cycleMask := cycle.foldl (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0
    let forcedTargets := (List.range 16).map (fun cfg =>
      if (cycleMask >>> cfg) &&& 1 == 1 then 0
      else (List.range 4).foldl (fun mask proc =>
        match assocLookup (tfKeyNat cfg proc) tfMap with
        | some val =>
          if val != getBit cfg proc then
            let target := flipBit cfg proc
            if (cycleMask >>> target) &&& 1 == 0 then mask ||| (1 <<< target)
            else mask
          else mask
        | none => mask) 0)
    let allMask : Nat := 65535
    let initRemaining := allMask &&& (allMask ^^^ cycleMask)
    let rec sinkRemove : Nat → Nat → Bool
      | 0, remaining => remaining != 0
      | fuel + 1, remaining =>
        let sinks := (List.range 16).foldl (fun mask cfg =>
          if (remaining >>> cfg) &&& 1 == 0 then mask
          else if forcedTargets[cfg]! &&& remaining == 0 then mask ||| (1 <<< cfg)
          else mask) 0
        if sinks == 0 then remaining != 0
        else sinkRemove fuel (remaining &&& (allMask ^^^ sinks))
    sinkRemove 16 initRemaining

def isBlocked (cycle : List (Nat × Nat)) : Bool :=
  isTFBlocked cycle || hasForcedKernel cycle

def dfsBlocked : Nat → Nat → Nat → Nat → List (Nat × Nat) → Nat → Bool
  | 0, _, _, _, _, _ => true
  | fuel + 1, start, cur, visited, path, fairMask =>
    (List.range 4).all (fun proc =>
      let next := flipBit cur proc
      let newFair := fairMask ||| (1 <<< proc)
      let newPath := path ++ [(cur, proc)]
      if next == start then
        if newFair == 15 then isBlocked newPath
        else true
      else if (visited >>> next) &&& 1 == 1 then true
      else dfsBlocked fuel start next (visited ||| (1 <<< next)) newPath newFair)

def allQ4CyclesBlocked : Bool :=
  (List.range 16).all (fun s => dfsBlocked 15 s s (1 <<< s) [] 0)

/-- Computational core: all fair Q₄ cycles are blocked. ~46s native_decide. -/
theorem allQ4CyclesBlocked_eq_true : allQ4CyclesBlocked = true := by native_decide

def allQ4CyclesBlocked16 : Bool :=
  (List.range 16).all (fun s => dfsBlocked 16 s s (1 <<< s) [] 0)

theorem allQ4CyclesBlocked16_eq_true : allQ4CyclesBlocked16 = true := by native_decide

/-! ## 4. Bridge

**Structure**. We work with sys = ⟨rs2222, f⟩. Given a GoodCycle gc with
convergence hconv, we derive False.

Step A. Extract the mover at each cycle step (Classical.choose from gc.closed).
Step B. Encode: each step k ↦ ((encCfg cₖ).val, moverₖ.val), a fair Q₄ cycle.
Step C. DFS completeness: the encoded cycle is among those explored by the DFS.
        By allQ4CyclesBlocked_eq_true, isBlocked returns true for it.
Step D. Soundness: isBlocked = true → False.
        - TF conflict: f_j(L,S,R) = 1−S (mover) and f_j(L,S,R) = S (non-mover)
          for the same (j,L,S,R). Since f is a function, S = 1−S. Impossible.
        - Forced kernel: the complement configs form a trap with forced privileged
          edges cycling forever. Construct infinite badStep chain → ¬WellFounded.

**DFS completeness** (Step C) is the core bridge lemma. It says: the DFS at
start = encCfg(gc.configs[0]) explores all possible mover sequences from start,
including the GoodCycle's mover sequence. This follows from the DFS structure:
at each step, (List.range 4).all checks all 4 movers; the GoodCycle's mover is
one of them; distinct configs ensure the path is not pruned.

This is a standard exhaustive-DFS property. The proof is by induction on the
remaining cycle steps, using dfs_branch to extract one step at a time.
-/

variable {f : TransFn rs2222}

/-- Extract the unique mover at step k of a GoodCycle. -/
noncomputable def gcMover (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) : Fin 4 :=
  Classical.choose (gc.closed k)

theorem gcMover_priv (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) :
    privileged ⟨rs2222, f⟩ (gc.configs.get k) (gcMover gc k) :=
  (Classical.choose_spec (gc.closed k)).1

theorem gcMover_step (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) :
    gc.configs.get (nextIndex gc.configs k) =
      move ⟨rs2222, f⟩ (gc.configs.get k) (gcMover gc k) :=
  (Classical.choose_spec (gc.closed k)).2

/-- Encoded next config = flipBit of current at mover. -/
theorem gcEnc_step (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) :
    (encCfg (gc.configs.get (nextIndex gc.configs k))).val =
      flipBit (encCfg (gc.configs.get k)).val (gcMover gc k).val := by
  rw [gcMover_step gc k]; exact encCfg_move (gcMover_priv gc k)

/-- Distinct configs have distinct encodings. -/
theorem gcEnc_ne (gc : GoodCycle ⟨rs2222, f⟩) (j₁ j₂ : Fin gc.configs.length)
    (hne : j₁ ≠ j₂) :
    (encCfg (gc.configs.get j₁)).val ≠ (encCfg (gc.configs.get j₂)).val := by
  intro h; exact hne (gc.distinct j₁ j₂ (encCfg_injective (Fin.ext h)))

/-- One-step DFS extraction. -/
theorem dfs_branch (fuel start cur visited : Nat) (path : List (Nat × Nat))
    (fairMask proc : Nat) (hproc : proc < 4)
    (hdfs : dfsBlocked (fuel + 1) start cur visited path fairMask = true) :
    let next := flipBit cur proc
    let newPath := path ++ [(cur, proc)]
    let newFair := fairMask ||| (1 <<< proc)
    (next = start → newFair = 15 → isBlocked newPath = true) ∧
    (next ≠ start → (visited >>> next) &&& 1 = 0 →
      dfsBlocked fuel start next (visited ||| (1 <<< next)) newPath newFair = true) := by
  simp only [dfsBlocked] at hdfs
  have hb := (List.all_eq_true).mp hdfs proc (List.mem_range.mpr hproc)
  constructor
  · intro heq hfair
    have h1 : (flipBit cur proc == start) = true := beq_iff_eq.mpr heq
    have h2 : (fairMask ||| 1 <<< proc == 15) = true := beq_iff_eq.mpr hfair
    simp only [h1, h2, ite_true] at hb; exact hb
  · intro hne hvis
    have h1 : (flipBit cur proc == start) = false := beq_eq_false_iff_ne.mpr hne
    have h2 : ((visited >>> flipBit cur proc) &&& 1 == 1) = false :=
      beq_eq_false_iff_ne.mpr (by omega)
    simp only [h1, h2, ite_false, Bool.false_eq_true, ↓reduceIte] at hb
    exact hb

/-! ### Bridge: analytical proof — GoodCycle on rs2222 → False.

For n=4 with all m_i = 2, every GoodCycle leads to a contradiction with
convergence via the partner/shadow construction. No DFS bridge needed. -/

/-- Infinite bad-step chain from a finite cycle contradicts WellFounded. -/
private theorem not_acc_of_finite_cycle' {α : Type*} {r : α → α → Prop}
    {n : Nat} (hn : 0 < n) (cyc : Fin n → α)
    (hcycle : ∀ k : Fin n, r (cyc ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩) (cyc k)) :
    ∀ k : Fin n, ¬Acc r (cyc k) := by
  suffices h : ∀ x, Acc r x → (∀ k : Fin n, cyc k ≠ x) from
    fun k hacc => h (cyc k) hacc k rfl
  intro x hacc
  induction hacc with
  | intro x _ ih =>
    intro k hfk; subst hfk
    exact ih _ (hcycle k) ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩ rfl

/-- For n=4, (m+2)%4 is distinct from m, left m, and right m. -/
private theorem opp_ne_all :
    ∀ (m : Fin 4), (⟨(m.val + 2) % 4, by omega⟩ : Fin 4) ≠ m ∧
      (⟨(m.val + 2) % 4, by omega⟩ : Fin 4) ≠ (⟨(m.val + 3) % 4, by omega⟩ : Fin 4) ∧
      (⟨(m.val + 2) % 4, by omega⟩ : Fin 4) ≠ (⟨(m.val + 1) % 4, by omega⟩ : Fin 4) := by
  decide

/-- flipCfg preserves TF context for proc m when flipping bit (m+2)%4. -/
private theorem flipCfg_preserves_tf (c : Config rs2222) (m : Fin 4) :
    let q : Fin 4 := ⟨(m.val + 2) % 4, by omega⟩
    (flipCfg c q) (left m) = c (left m) ∧ (flipCfg c q) m = c m ∧
    (flipCfg c q) (right m) = c (right m) := by
  refine ⟨?_, ?_, ?_⟩ <;> {
    show flipCfg c ⟨(m.val + 2) % 4, _⟩ _ = c _
    unfold flipCfg
    split
    · next h => exfalso; fin_cases m <;> simp_all [left, right, Fin.ext_iff]
    · rfl
  }

private theorem flipCfg_twice (c : Config rs2222) (i : Fin 4) :
    flipCfg (flipCfg c i) i = c := by
  apply encCfg_injective
  apply Fin.ext
  rw [encCfg_flipCfg, encCfg_flipCfg]
  simpa [Nat.xor_assoc]

private theorem flipCfg_comm (c : Config rs2222) (i j : Fin 4) :
    flipCfg (flipCfg c i) j = flipCfg (flipCfg c j) i := by
  apply encCfg_injective
  apply Fin.ext
  rw [encCfg_flipCfg, encCfg_flipCfg, encCfg_flipCfg, encCfg_flipCfg]
  simpa [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm]

private theorem opp_eq_anti4 (m : Fin 4) :
    (⟨(m.val + 2) % 4, by omega⟩ : Fin 4) = anti4 m := by
  apply Fin.ext
  simp [anti4]

private theorem opp_left4_eq_right4 (m : Fin 4) :
    (⟨((left4 m).val + 2) % 4, by omega⟩ : Fin 4) = right4 m := by
  apply Fin.ext
  simp [left4, right4]
  omega

private theorem opp_right4_eq_left4 (m : Fin 4) :
    (⟨((right4 m).val + 2) % 4, by omega⟩ : Fin 4) = left4 m := by
  apply Fin.ext
  simp [left4, right4]

/-- Partner configuration: flip the antipodal bit of the mover. -/
private noncomputable def partnerCfg (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) :
    Config rs2222 :=
  flipCfg (gc.configs.get k) ⟨((gcMover gc k).val + 2) % 4, by omega⟩

/-- The partner of a cycle config has the mover privileged. -/
private theorem partner_priv (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) :
    privileged ⟨rs2222, f⟩
      (partnerCfg gc k)
      (gcMover gc k) := by
  have ⟨hL, hS, hR⟩ := flipCfg_preserves_tf (gc.configs.get k) (gcMover gc k)
  unfold privileged partnerCfg
  rw [hL, hS, hR]
  exact gcMover_priv gc k

private theorem partner_step3_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) (k : Fin gc.configs.length) :
    let k1 := nextIndex gc.configs k
    let k2 := nextIndex gc.configs k1
    let k3 := nextIndex gc.configs k2
    flipCfg (partnerCfg gc k) (gcMover gc k) = partnerCfg gc k3 := by
  let m := gcMover gc k
  let k1 := nextIndex gc.configs k
  let k2 := nextIndex gc.configs k1
  let k3 := nextIndex gc.configs k2
  have hm : gcMover gc k = gc.moverAt k := by
    exact gc.moverAt_unique k (gcMover gc k) (gcMover_priv gc k)
  have hm1 : gcMover gc k1 = right4 m := by
    have hm1' : gcMover gc k1 = right (gcMover gc k) := by
      calc
        gcMover gc k1 = gc.moverAt k1 := by
          exact gc.moverAt_unique k1 (gcMover gc k1) (gcMover_priv gc k1)
        _ = right (gc.moverAt k) := hCW k
        _ = right (gcMover gc k) := by rw [hm]
    simpa [m, right, right4] using hm1'
  have hm2 : gcMover gc k2 = anti4 m := by
    have hm2' : gcMover gc k2 = right (gcMover gc k1) := by
      have hk1eq : gc.moverAt k1 = gcMover gc k1 := by
        exact (gc.moverAt_unique k1 (gcMover gc k1) (gcMover_priv gc k1)).symm
      calc
        gcMover gc k2 = gc.moverAt k2 := by
          exact gc.moverAt_unique k2 (gcMover gc k2) (gcMover_priv gc k2)
        _ = right (gc.moverAt k1) := hCW k1
        _ = right (gcMover gc k1) := by rw [hk1eq]
    rw [hm1] at hm2'
    simpa [m, right, right4, anti4] using hm2'
  have hm3 : gcMover gc k3 = left4 m := by
    have hm3' : gcMover gc k3 = right (gcMover gc k2) := by
      have hk2eq : gc.moverAt k2 = gcMover gc k2 := by
        exact (gc.moverAt_unique k2 (gcMover gc k2) (gcMover_priv gc k2)).symm
      calc
        gcMover gc k3 = gc.moverAt k3 := by
          exact gc.moverAt_unique k3 (gcMover gc k3) (gcMover_priv gc k3)
        _ = right (gc.moverAt k2) := hCW k2
        _ = right (gcMover gc k2) := by rw [hk2eq]
    rw [hm2] at hm3'
    simpa [m, right, left4, anti4, right4] using hm3'
  have hk1 :
      gc.configs.get k1 = flipCfg (gc.configs.get k) m := by
    rw [gcMover_step gc k, move_eq_flipCfg (gcMover_priv gc k)]
  have hk2 :
      gc.configs.get k2 = flipCfg (gc.configs.get k1) (gcMover gc k1) := by
    rw [gcMover_step gc k1, move_eq_flipCfg (gcMover_priv gc k1)]
  have hk3 :
      gc.configs.get k3 = flipCfg (gc.configs.get k2) (gcMover gc k2) := by
    rw [gcMover_step gc k2, move_eq_flipCfg (gcMover_priv gc k2)]
  have hop3 :
      (⟨((gcMover gc k3).val + 2) % 4, by omega⟩ : Fin 4) = right4 (gcMover gc k) := by
    apply Fin.ext
    simp [hm3, left4, right4]
    omega
  change flipCfg (flipCfg (gc.configs.get k) ⟨((gcMover gc k).val + 2) % 4, by omega⟩)
      (gcMover gc k) =
    flipCfg (gc.configs.get k3) ⟨((gcMover gc k3).val + 2) % 4, by omega⟩
  rw [hk3, hk2, hm2, hk1, hm1, opp_eq_anti4, hop3]
  rw [flipCfg_comm (gc.configs.get k) (anti4 (gcMover gc k)) (gcMover gc k)]
  rw [flipCfg_comm (flipCfg (gc.configs.get k) (gcMover gc k)) (right4 (gcMover gc k))
    (anti4 (gcMover gc k))]
  rw [flipCfg_twice (flipCfg (flipCfg (gc.configs.get k) (gcMover gc k))
    (anti4 (gcMover gc k))) (right4 (gcMover gc k))]

private theorem partner_step3_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) (k : Fin gc.configs.length) :
    let k1 := nextIndex gc.configs k
    let k2 := nextIndex gc.configs k1
    let k3 := nextIndex gc.configs k2
    flipCfg (partnerCfg gc k) (gcMover gc k) = partnerCfg gc k3 := by
  let m := gcMover gc k
  let k1 := nextIndex gc.configs k
  let k2 := nextIndex gc.configs k1
  let k3 := nextIndex gc.configs k2
  have hm : gcMover gc k = gc.moverAt k := by
    exact gc.moverAt_unique k (gcMover gc k) (gcMover_priv gc k)
  have hm1 : gcMover gc k1 = left4 m := by
    have hm1' : gcMover gc k1 = left (gcMover gc k) := by
      calc
        gcMover gc k1 = gc.moverAt k1 := by
          exact gc.moverAt_unique k1 (gcMover gc k1) (gcMover_priv gc k1)
        _ = left (gc.moverAt k) := hCCW k
        _ = left (gcMover gc k) := by rw [hm]
    simpa [m, left, left4] using hm1'
  have hm2 : gcMover gc k2 = anti4 m := by
    have hm2' : gcMover gc k2 = left (gcMover gc k1) := by
      have hk1eq : gc.moverAt k1 = gcMover gc k1 := by
        exact (gc.moverAt_unique k1 (gcMover gc k1) (gcMover_priv gc k1)).symm
      calc
        gcMover gc k2 = gc.moverAt k2 := by
          exact gc.moverAt_unique k2 (gcMover gc k2) (gcMover_priv gc k2)
        _ = left (gc.moverAt k1) := hCCW k1
        _ = left (gcMover gc k1) := by rw [hk1eq]
    rw [hm1] at hm2'
    apply Fin.ext
    have hval := congrArg Fin.val hm2'
    simp [m, left, left4, anti4] at hval ⊢
    omega
  have hm3 : gcMover gc k3 = right4 m := by
    have hm3' : gcMover gc k3 = left (gcMover gc k2) := by
      have hk2eq : gc.moverAt k2 = gcMover gc k2 := by
        exact (gc.moverAt_unique k2 (gcMover gc k2) (gcMover_priv gc k2)).symm
      calc
        gcMover gc k3 = gc.moverAt k3 := by
          exact gc.moverAt_unique k3 (gcMover gc k3) (gcMover_priv gc k3)
        _ = left (gc.moverAt k2) := hCCW k2
        _ = left (gcMover gc k2) := by rw [hk2eq]
    rw [hm2] at hm3'
    apply Fin.ext
    have hval := congrArg Fin.val hm3'
    simp [m, left, left4, anti4, right4] at hval ⊢
    omega
  have hk1 :
      gc.configs.get k1 = flipCfg (gc.configs.get k) m := by
    rw [gcMover_step gc k, move_eq_flipCfg (gcMover_priv gc k)]
  have hk2 :
      gc.configs.get k2 = flipCfg (gc.configs.get k1) (gcMover gc k1) := by
    rw [gcMover_step gc k1, move_eq_flipCfg (gcMover_priv gc k1)]
  have hk3 :
      gc.configs.get k3 = flipCfg (gc.configs.get k2) (gcMover gc k2) := by
    rw [gcMover_step gc k2, move_eq_flipCfg (gcMover_priv gc k2)]
  have hop3 :
      (⟨((gcMover gc k3).val + 2) % 4, by omega⟩ : Fin 4) = left4 (gcMover gc k) := by
    apply Fin.ext
    simp [hm3, left4, right4]
    omega
  change flipCfg (flipCfg (gc.configs.get k) ⟨((gcMover gc k).val + 2) % 4, by omega⟩)
      (gcMover gc k) =
    flipCfg (gc.configs.get k3) ⟨((gcMover gc k3).val + 2) % 4, by omega⟩
  rw [hk3, hk2, hm2, hk1, hm1, opp_eq_anti4, hop3]
  rw [flipCfg_comm (gc.configs.get k) (anti4 (gcMover gc k)) (gcMover gc k)]
  rw [flipCfg_comm (flipCfg (gc.configs.get k) (gcMover gc k)) (left4 (gcMover gc k))
    (anti4 (gcMover gc k))]
  rw [flipCfg_twice (flipCfg (flipCfg (gc.configs.get k) (gcMover gc k))
    (anti4 (gcMover gc k))) (left4 (gcMover gc k))]

private theorem gcMover_next_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) (k : Fin gc.configs.length) :
    gcMover gc (nextIndex gc.configs k) = right4 (gcMover gc k) := by
  have hm : gcMover gc k = gc.moverAt k := by
    exact gc.moverAt_unique k (gcMover gc k) (gcMover_priv gc k)
  have hm' : gcMover gc (nextIndex gc.configs k) = gc.moverAt (nextIndex gc.configs k) := by
    exact gc.moverAt_unique (nextIndex gc.configs k) (gcMover gc (nextIndex gc.configs k))
      (gcMover_priv gc (nextIndex gc.configs k))
  calc
    gcMover gc (nextIndex gc.configs k) = gc.moverAt (nextIndex gc.configs k) := hm'
    _ = right (gc.moverAt k) := hCW k
    _ = right (gcMover gc k) := by rw [hm]
    _ = right4 (gcMover gc k) := by simpa [right, right4]

private theorem gcMover_next_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) (k : Fin gc.configs.length) :
    gcMover gc (nextIndex gc.configs k) = left4 (gcMover gc k) := by
  have hm : gcMover gc k = gc.moverAt k := by
    exact gc.moverAt_unique k (gcMover gc k) (gcMover_priv gc k)
  have hm' : gcMover gc (nextIndex gc.configs k) = gc.moverAt (nextIndex gc.configs k) := by
    exact gc.moverAt_unique (nextIndex gc.configs k) (gcMover gc (nextIndex gc.configs k))
      (gcMover_priv gc (nextIndex gc.configs k))
  calc
    gcMover gc (nextIndex gc.configs k) = gc.moverAt (nextIndex gc.configs k) := hm'
    _ = left (gc.moverAt k) := hCCW k
    _ = left (gcMover gc k) := by rw [hm]
    _ = left4 (gcMover gc k) := by simpa [left, left4]

private theorem gcMover_next3_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) (k : Fin gc.configs.length) :
    let k1 := nextIndex gc.configs k
    let k2 := nextIndex gc.configs k1
    let k3 := nextIndex gc.configs k2
    gcMover gc k3 = left4 (gcMover gc k) := by
  let k1 := nextIndex gc.configs k
  let k2 := nextIndex gc.configs k1
  let k3 := nextIndex gc.configs k2
  have h1 : gcMover gc k1 = right4 (gcMover gc k) := gcMover_next_of_uniformCW gc hCW k
  have h2 : gcMover gc k2 = right4 (gcMover gc k1) := gcMover_next_of_uniformCW gc hCW k1
  have h3 : gcMover gc k3 = right4 (gcMover gc k2) := gcMover_next_of_uniformCW gc hCW k2
  rw [h1] at h2
  rw [h2] at h3
  simpa [k1, k2, k3, right4_right4, right4_anti4] using h3

private theorem gcMover_next3_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) (k : Fin gc.configs.length) :
    let k1 := nextIndex gc.configs k
    let k2 := nextIndex gc.configs k1
    let k3 := nextIndex gc.configs k2
    gcMover gc k3 = right4 (gcMover gc k) := by
  let k1 := nextIndex gc.configs k
  let k2 := nextIndex gc.configs k1
  let k3 := nextIndex gc.configs k2
  have h1 : gcMover gc k1 = left4 (gcMover gc k) := gcMover_next_of_uniformCCW gc hCCW k
  have h2 : gcMover gc k2 = left4 (gcMover gc k1) := gcMover_next_of_uniformCCW gc hCCW k1
  have h3 : gcMover gc k3 = left4 (gcMover gc k2) := gcMover_next_of_uniformCCW gc hCCW k2
  rw [h1] at h2
  rw [h2] at h3
  simpa [k1, k2, k3, left4_left4, left4_anti4] using h3

private theorem partner_not_get_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) (k s : Fin gc.configs.length) :
    partnerCfg gc k ≠ gc.configs.get s := by
  intro hEq
  have hprivAtS : privileged ⟨rs2222, f⟩ (gc.configs.get s) (gcMover gc k) := by
    rw [← hEq]
    exact partner_priv gc k
  have hm_eq : gcMover gc s = gcMover gc k := by
    calc
      gcMover gc s = gc.moverAt s := by
        exact gc.moverAt_unique s (gcMover gc s) (gcMover_priv gc s)
      _ = gcMover gc k := by
        symm
        exact gc.moverAt_unique s (gcMover gc k) hprivAtS
  let s1 := nextIndex gc.configs s
  let k1 := nextIndex gc.configs k
  let k2 := nextIndex gc.configs k1
  let k3 := nextIndex gc.configs k2
  have hsucc : partnerCfg gc k3 = gc.configs.get s1 := by
    calc
      partnerCfg gc k3 = flipCfg (partnerCfg gc k) (gcMover gc k) := by
        symm
        simpa [k1, k2, k3] using partner_step3_of_uniformCW gc hCW k
      _ = flipCfg (gc.configs.get s) (gcMover gc k) := by rw [hEq]
      _ = flipCfg (gc.configs.get s) (gcMover gc s) := by rw [hm_eq]
      _ = gc.configs.get s1 := by
        rw [← move_eq_flipCfg (gcMover_priv gc s), ← gcMover_step gc s]
  have hprivAtS1 : privileged ⟨rs2222, f⟩ (gc.configs.get s1) (gcMover gc k3) := by
    rw [← hsucc]
    exact partner_priv gc k3
  have hm_eq_succ : gcMover gc s1 = gcMover gc k3 := by
    calc
      gcMover gc s1 = gc.moverAt s1 := by
        exact gc.moverAt_unique s1 (gcMover gc s1) (gcMover_priv gc s1)
      _ = gcMover gc k3 := by
        symm
        exact gc.moverAt_unique s1 (gcMover gc k3) hprivAtS1
  have hnextS : gcMover gc s1 = right4 (gcMover gc s) := gcMover_next_of_uniformCW gc hCW s
  have hnextK : gcMover gc k3 = left4 (gcMover gc k) := by
    simpa [k1, k2, k3] using gcMover_next3_of_uniformCW gc hCW k
  rw [hm_eq, hm_eq_succ, hnextK] at hnextS
  exact (localTriple_distinct (gcMover gc k)).2.2 hnextS

private theorem partner_not_get_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) (k s : Fin gc.configs.length) :
    partnerCfg gc k ≠ gc.configs.get s := by
  intro hEq
  have hprivAtS : privileged ⟨rs2222, f⟩ (gc.configs.get s) (gcMover gc k) := by
    rw [← hEq]
    exact partner_priv gc k
  have hm_eq : gcMover gc s = gcMover gc k := by
    calc
      gcMover gc s = gc.moverAt s := by
        exact gc.moverAt_unique s (gcMover gc s) (gcMover_priv gc s)
      _ = gcMover gc k := by
        symm
        exact gc.moverAt_unique s (gcMover gc k) hprivAtS
  let s1 := nextIndex gc.configs s
  let k1 := nextIndex gc.configs k
  let k2 := nextIndex gc.configs k1
  let k3 := nextIndex gc.configs k2
  have hsucc : partnerCfg gc k3 = gc.configs.get s1 := by
    calc
      partnerCfg gc k3 = flipCfg (partnerCfg gc k) (gcMover gc k) := by
        symm
        simpa [k1, k2, k3] using partner_step3_of_uniformCCW gc hCCW k
      _ = flipCfg (gc.configs.get s) (gcMover gc k) := by rw [hEq]
      _ = flipCfg (gc.configs.get s) (gcMover gc s) := by rw [hm_eq]
      _ = gc.configs.get s1 := by
        rw [← move_eq_flipCfg (gcMover_priv gc s), ← gcMover_step gc s]
  have hprivAtS1 : privileged ⟨rs2222, f⟩ (gc.configs.get s1) (gcMover gc k3) := by
    rw [← hsucc]
    exact partner_priv gc k3
  have hm_eq_succ : gcMover gc s1 = gcMover gc k3 := by
    calc
      gcMover gc s1 = gc.moverAt s1 := by
        exact gc.moverAt_unique s1 (gcMover gc s1) (gcMover_priv gc s1)
      _ = gcMover gc k3 := by
        symm
        exact gc.moverAt_unique s1 (gcMover gc k3) hprivAtS1
  have hnextS : gcMover gc s1 = left4 (gcMover gc s) := gcMover_next_of_uniformCCW gc hCCW s
  have hnextK : gcMover gc k3 = right4 (gcMover gc k) := by
    simpa [k1, k2, k3] using gcMover_next3_of_uniformCCW gc hCCW k
  rw [hm_eq, hm_eq_succ, hnextK] at hnextS
  exact (localTriple_distinct (gcMover gc k)).2.2 hnextS.symm

private theorem partner_not_mem_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) (k : Fin gc.configs.length) :
    partnerCfg gc k ∉ gc.configs := by
  intro hmem
  obtain ⟨s, hs⟩ := List.mem_iff_get.mp hmem
  exact partner_not_get_of_uniformCW gc hCW k s hs.symm

private theorem partner_not_mem_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) (k : Fin gc.configs.length) :
    partnerCfg gc k ∉ gc.configs := by
  intro hmem
  obtain ⟨s, hs⟩ := List.mem_iff_get.mp hmem
  exact partner_not_get_of_uniformCCW gc hCCW k s hs.symm

/-- Non-mover value is preserved. -/
private theorem nonmover_preserved' (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length)
    (j : Fin 4) (hj : j ≠ gcMover gc k) :
    (gc.configs.get (nextIndex gc.configs k)) j = (gc.configs.get k) j := by
  rw [gcMover_step gc k]; simp [move, hj]

private theorem gc_len_pos' (gc : GoodCycle ⟨rs2222, f⟩) : 0 < gc.configs.length := by
  match hc : gc.configs with
  | [] => exact absurd hc gc.nonempty
  | _ :: _ => simp [List.length_cons]

/-- The TF context for proc j at config c (on rs2222). -/
private noncomputable def tfCtx (c : Config rs2222) (j : Fin 4) :
    Fin 2 × Fin 2 × Fin 2 :=
  (c (left j), c j, c (right j))

/-- TF conflict: if the same TF context for proc j appears at two cycle steps
    where j is mover at one and non-mover at the other → False. -/
private theorem tf_conflict_false (gc : GoodCycle ⟨rs2222, f⟩)
    (k₁ k₂ : Fin gc.configs.length) (j : Fin 4)
    (htf : tfCtx (gc.configs.get k₁) j = tfCtx (gc.configs.get k₂) j)
    (hmov₁ : gcMover gc k₁ = j) (hnotmov₂ : gcMover gc k₂ ≠ j) : False := by
  -- At k₁, j is mover: f_j(L,S,R) = 1-S (by binary_priv_val)
  -- At k₂, j is non-mover: f_j(L,S,R) = S (value preserved)
  -- Same (L,S,R) → 1-S = S → impossible for S ∈ {0,1}
  unfold tfCtx at htf
  -- Extract component equalities from the product equality
  have hL : (gc.configs.get k₁) (left j) = (gc.configs.get k₂) (left j) :=
    congr_arg Prod.fst htf
  have hS : (gc.configs.get k₁) j = (gc.configs.get k₂) j :=
    congr_arg (Prod.fst ∘ Prod.snd) htf
  have hR : (gc.configs.get k₁) (right j) = (gc.configs.get k₂) (right j) :=
    congr_arg (Prod.snd ∘ Prod.snd) htf
  -- At k₁ (mover): f_j(L,S,R) = 1-S
  have hpriv₁ := gcMover_priv gc k₁; rw [hmov₁] at hpriv₁
  have hbpv := binary_priv_val hpriv₁ (rs2222_m j)
  -- Rewrite to use k₂'s values (which equal k₁'s by hL, hS, hR)
  rw [hL, hS, hR] at hbpv
  -- hbpv : f_j(c₂(L), c₂(S), c₂(R)).val = 1 - c₂(j).val
  -- At k₂ (non-mover): f_j(c₂(L), c₂(S), c₂(R)) = c₂(j) (not privileged → f = current)
  have hnp₂ : ¬privileged ⟨rs2222, f⟩ (gc.configs.get k₂) j := by
    intro hp
    -- j is privileged at k₂, but gcMover gc k₂ ≠ j.
    -- By unique_privileged, the unique privileged proc = gcMover gc k₂.
    -- So j = gcMover gc k₂. Contradiction with hnotmov₂.
    have hmem : gc.configs.get k₂ ∈ gc.configs := List.get_mem _ _
    have huniq := gc.unique_privileged (gc.configs.get k₂) hmem
    have := huniq.unique hp (gcMover_priv gc k₂)
    exact hnotmov₂ this.symm
  unfold privileged at hnp₂; push_neg at hnp₂
  -- hnp₂ : f_j(c2_L, c2_S, c2_R) = c2_j
  have heq₂ : (⟨rs2222, f⟩ : System).f j ((gc.configs.get k₂) (left j))
      ((gc.configs.get k₂) j) ((gc.configs.get k₂) (right j)) = (gc.configs.get k₂) j := hnp₂
  -- Now: f output = 1 - c₂(j).val (from hbpv) and f output = c₂(j).val (from heq₂)
  have hlt : (gc.configs.get k₂ j).val < 2 :=
    Nat.lt_of_lt_of_eq (gc.configs.get k₂ j).isLt (rs2222_m j)
  have : (⟨rs2222, f⟩ : System).f j ((gc.configs.get k₂) (left j))
      ((gc.configs.get k₂) j) ((gc.configs.get k₂) (right j)) =
      (gc.configs.get k₂) j := hnp₂
  rw [Fin.ext_iff] at this
  omega

/-! ### DFS Bridge: GoodCycle on rs2222 → False via computational DFS result.

The bridge encodes the GoodCycle as a Nat-level cycle, follows it through the
DFS using `dfs_branch`, and derives `False` from `isBlocked = true`. -/

/-- Connection between `>>>` `&&&` and `testBit` (= 0 case). -/
private theorem shr_and1_eq (n j : Nat) :
    ((n >>> j) &&& 1 = 0) ↔ (n.testBit j = false) := by
  rw [Nat.and_one_is_mod]; simp [Nat.testBit]

/-- Connection between `>>>` `&&&` and `testBit` (= 1 case). -/
private theorem shr_and1_eq_one (n j : Nat) :
    ((n >>> j) &&& 1 = 1) ↔ (n.testBit j = true) := by
  rw [Nat.and_one_is_mod]; simp [Nat.testBit]

/-- If bit y is unset in mask and x ≠ y, bit y is unset in mask ||| (1 <<< x). -/
private theorem bit_unset_or (mask x y : Nat) (hne : x ≠ y)
    (hunset : (mask >>> y) &&& 1 = 0) :
    ((mask ||| (1 <<< x)) >>> y) &&& 1 = 0 := by
  rw [shr_and1_eq] at hunset ⊢
  simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne hne,
    Bool.or_false, hunset]

/-- Bit x IS set in (1 <<< x). -/
private theorem bit_set_self (x : Nat) : ((1 <<< x) >>> x) &&& 1 = 1 := by
  rw [shr_and1_eq_one, Nat.one_shiftLeft, Nat.testBit_two_pow_self]

/-- Encoded config values are < 16. -/
private theorem gcEnc_lt_16 (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) :
    (encCfg (gc.configs.get k)).val < 16 :=
  (encCfg (gc.configs.get k)).isLt

/-- GoodCycle length ≤ 16 (at most 16 distinct configs from Config rs2222). -/
private theorem gc_len_le_16 (gc : GoodCycle ⟨rs2222, f⟩) :
    gc.configs.length ≤ 16 := by
  by_contra h; push_neg at h
  have hnd : gc.configs.Nodup :=
    List.nodup_iff_injective_get.mpr (fun a b h => gc.distinct a b h)
  have hle : gc.configs.length ≤ Fintype.card (Config rs2222) :=
    List.Nodup.length_le_card hnd
  have : Fintype.card (Config rs2222) = 16 := config_card_rs2222
  omega

/-- GoodCycle has ≥ 1 config. -/
private theorem gc_len_ge_1 (gc : GoodCycle ⟨rs2222, f⟩) :
    1 ≤ gc.configs.length :=
  by match hc : gc.configs with
     | [] => exact absurd hc gc.nonempty
     | _ :: _ => simp [List.length_cons]

/-- Mover values are < 4. -/
private theorem gcMover_lt_4 (gc : GoodCycle ⟨rs2222, f⟩) (k : Fin gc.configs.length) :
    (gcMover gc k).val < 4 := (gcMover gc k).isLt

/-- Build visited mask by ORing bits for configs 0..k. -/
private noncomputable def gcMask (gc : GoodCycle ⟨rs2222, f⟩) :
    (k : Nat) → k ≤ gc.configs.length → Nat
  | 0, _ => 0
  | k + 1, hk =>
    gcMask gc k (by omega) ||| (1 <<< (encCfg (gc.configs.get ⟨k, by omega⟩)).val)

/-- Future cycle configs are unvisited in the mask. -/
private theorem gcMask_unset (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k ≤ gc.configs.length)
    (j : Nat) (hj : j < gc.configs.length) (hjk : k ≤ j) :
    (gcMask gc k hk >>> (encCfg (gc.configs.get ⟨j, hj⟩)).val) &&& 1 = 0 := by
  induction k with
  | zero => simp [gcMask]
  | succ n ih =>
    simp only [gcMask]
    apply bit_unset_or
    · apply Ne.symm
      apply gcEnc_ne gc ⟨j, hj⟩ ⟨n, by omega⟩
      intro h; simp [Fin.ext_iff] at h; omega
    · exact ih (by omega) (by omega)

/-- Past cycle configs are visited in the mask (specifically, bit for config k is set
    at mask step k+1). We state: the mask at step k+1 has bit enc(c_k) set. -/
private theorem gcMask_set (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length) :
    (gcMask gc (k + 1) (by omega) >>> (encCfg (gc.configs.get ⟨k, hk⟩)).val) &&& 1 = 1 := by
  simp only [gcMask]
  -- The mask at k+1 is (mask at k) ||| (1 <<< enc(c_k)).
  -- Bit enc(c_k) is set in (1 <<< enc(c_k)).
  rw [shr_and1_eq_one]
  simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self]

/-- Build the fair mask from movers 0..k-1. -/
private noncomputable def gcFair (gc : GoodCycle ⟨rs2222, f⟩) :
    (k : Nat) → k ≤ gc.configs.length → Nat
  | 0, _ => 0
  | k + 1, hk =>
    gcFair gc k (by omega) ||| (1 <<< (gcMover gc ⟨k, by omega⟩).val)

/-- Build the path from cycle steps 0..k-1. -/
private noncomputable def gcPathN (gc : GoodCycle ⟨rs2222, f⟩) :
    (k : Nat) → k ≤ gc.configs.length → List (Nat × Nat)
  | 0, _ => []
  | k + 1, hk =>
    gcPathN gc k (by omega) ++
      [((encCfg (gc.configs.get ⟨k, by omega⟩)).val, (gcMover gc ⟨k, by omega⟩).val)]

/-- Proof irrelevance for gcFair. -/
private theorem gcFair_eq (gc : GoodCycle ⟨rs2222, f⟩)
    (a b : Nat) (ha : a ≤ gc.configs.length) (hb : b ≤ gc.configs.length) (hab : a = b) :
    gcFair gc a ha = gcFair gc b hb := by subst hab; rfl

/-- Proof irrelevance for gcPathN. -/
private theorem gcPathN_eq (gc : GoodCycle ⟨rs2222, f⟩)
    (a b : Nat) (ha : a ≤ gc.configs.length) (hb : b ≤ gc.configs.length) (hab : a = b) :
    gcPathN gc a ha = gcPathN gc b hb := by subst hab; rfl

-- Main DFS induction: following the GoodCycle's mover sequence through the DFS,
-- the DFS returns true at each step and ultimately isBlocked returns true.
--
-- We prove: if dfsBlocked returns true at position k with the appropriate
-- state, then isBlocked of the full encoded cycle is true.
--
-- Specifically, by induction on remaining = L - k (where L = gc.configs.length):
-- - Base case (k = L-1): next step returns to start, fairMask = 15,
--   so isBlocked is called and returns true.
-- - Inductive step: dfs_branch extracts the GoodCycle's mover, giving a
--   sub-DFS at position k+1. The induction hypothesis applies.

/-- The DFS starting at enc(c₀) returns true (from allQ4CyclesBlocked16). -/
private theorem dfs_start (gc : GoodCycle ⟨rs2222, f⟩) :
    dfsBlocked 16
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (1 <<< (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val)
      []
      0 = true := by
  have h := allQ4CyclesBlocked16_eq_true
  unfold allQ4CyclesBlocked16 at h
  have hlt := gcEnc_lt_16 gc ⟨0, gc_len_ge_1 gc⟩
  exact (List.all_eq_true).mp h
    (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
    (List.mem_range.mpr hlt)

/-- gcPathN at step k+1 extends gcPathN at step k by one entry. -/
private theorem gcPathN_succ (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length) :
    gcPathN gc (k + 1) (by omega) =
      gcPathN gc k (by omega) ++
        [((encCfg (gc.configs.get ⟨k, hk⟩)).val, (gcMover gc ⟨k, hk⟩).val)] := by
  simp only [gcPathN, show k < gc.configs.length from hk, dite_true]

private theorem gcMover_eq_moverAt (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Fin gc.configs.length) :
    gcMover gc k = gc.moverAt k := by
  exact gc.moverAt_unique k (gcMover gc k) (gcMover_priv gc k)

private theorem gcPathN_eq_gcPathPrefix (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k : Nat) (hk : k ≤ gc.configs.length),
      gcPathN gc k hk = gcPathPrefix gc k hk
  | 0, hk => by
      simp [gcPathN, gcPathPrefix]
  | k + 1, hk => by
      rw [gcPathN, gcPathPrefix]
      rw [gcPathN_eq_gcPathPrefix gc k (by omega)]
      congr 1
      simp [gcEntryAt, gcMover_eq_moverAt]

private theorem gcPathN_eq_pathFromWord4 (gc : GoodCycle ⟨rs2222, f⟩) :
    gcPathN gc gc.configs.length (le_refl _) =
      pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (gcWordFrom gc 0 gc.configs.length (by simpa using (le_refl gc.configs.length))) := by
  calc
    gcPathN gc gc.configs.length (le_refl _) =
        gcPathPrefix gc gc.configs.length (le_refl _) :=
      gcPathN_eq_gcPathPrefix gc gc.configs.length (le_refl _)
    _ = gcPathFrom gc 0 gc.configs.length (by simp) :=
      gcPathPrefix_eq_gcPathFrom_zero gc gc.configs.length (le_refl _)
    _ = pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by simpa using (le_refl gc.configs.length))) :=
      gcPathFrom_eq_pathFromWord4 gc 0 gc.configs.length
        (by simpa using (le_refl gc.configs.length))

private theorem gc_fireCount_pos (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) :
    0 < gc.fireCount p := by
  obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair p
  have hmov : gc.moverAt k = p := by
    rw [← hj]
    exact (gc.moverAt_unique k j hpriv).symm
  rw [gc.fireCount_eq_sum_moverAt p]
  have hsingle : 1 ≤ ∑ i : Fin gc.configs.length, if gc.moverAt i = p then (1 : Nat) else 0 := by
    calc
      1 = (if gc.moverAt k = p then (1 : Nat) else 0) := by simp [hmov]
      _ ≤ ∑ i : Fin gc.configs.length, if gc.moverAt i = p then (1 : Nat) else 0 := by
        exact Finset.single_le_sum
          (f := fun i : Fin gc.configs.length => if gc.moverAt i = p then (1 : Nat) else 0)
          (fun i _ => by simp) (Finset.mem_univ k)
  exact Nat.succ_le_iff.mp hsingle

private theorem gc_fireCount_ge_two (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) :
    2 ≤ gc.fireCount p :=
  binary_fireCount_ge_two gc p (rs2222_m p) (gc_fireCount_pos gc p)

private noncomputable def gcFireSteps (gc : GoodCycle ⟨rs2222, f⟩)
    (p : Fin 4) : Finset (Fin gc.configs.length) :=
  Finset.univ.filter fun k => gc.moverAt k = p

private theorem mem_gcFireSteps_iff (gc : GoodCycle ⟨rs2222, f⟩)
    (p : Fin 4) (k : Fin gc.configs.length) :
    k ∈ gcFireSteps gc p ↔ gc.moverAt k = p := by
  simp [gcFireSteps]

private theorem gcFireSteps_card (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) :
    (gcFireSteps gc p).card = gc.fireCount p := by
  classical
  unfold gcFireSteps
  rw [gc.fireCount_eq_sum_moverAt p]
  symm
  have hsum :
      (∑ k : Fin gc.configs.length, if gc.moverAt k = p then (1 : Nat) else 0) =
        Finset.sum (Finset.univ.filter (fun k => gc.moverAt k = p)) (fun _ => (1 : Nat)) := by
    simpa [Finset.sum_filter]
  rw [hsum]
  simp

private theorem exists_fireCount_eq_two_of_not_all_four
    (gc : GoodCycle ⟨rs2222, f⟩)
    (hnot4 : ¬ ∀ p : Fin 4, gc.fireCount p = 4) :
    ∃ q : Fin 4, gc.fireCount q = 2 := by
  by_contra hno2
  push_neg at hno2
  have hge4 : ∀ p : Fin 4, 4 ≤ gc.fireCount p := by
    intro p
    have hge2 : 2 ≤ gc.fireCount p := gc_fireCount_ge_two gc p
    have hne2 : gc.fireCount p ≠ 2 := hno2 p
    have heven : Even (gc.fireCount p) := gc.binary_fireCount_even p (rs2222_m p)
    rcases heven with ⟨m, hm⟩
    omega
  have hsum := gc.sum_fireCount
  have hlen16 : gc.configs.length = 16 := by
    have hle16 : gc.configs.length ≤ 16 := gc_len_le_16 gc
    have hge16 : 16 ≤ gc.configs.length := by
      calc
        16 = ∑ _p : Fin 4, 4 := by norm_num
        _ ≤ ∑ p : Fin 4, gc.fireCount p := by
              apply Finset.sum_le_sum
              intro p _
              exact hge4 p
        _ = gc.configs.length := hsum
    omega
  have hall4 : ∀ p : Fin 4, gc.fireCount p = 4 := by
    intro p
    have hp4 := hge4 p
    have hsum' : ∑ r : Fin 4, gc.fireCount r = 16 := by
      simpa [hlen16] using hsum
    have hrest : 12 ≤ Finset.sum (Finset.univ.erase p) (fun r => gc.fireCount r) := by
      calc
        12 = Finset.sum (Finset.univ.erase p) (fun _ => (4 : Nat)) := by
              simp [Finset.card_erase_of_mem (Finset.mem_univ p)]
        _ ≤ Finset.sum (Finset.univ.erase p) (fun r => gc.fireCount r) := by
              apply Finset.sum_le_sum
              intro r hr
              exact hge4 r
    have hdecomp :
        gc.fireCount p + Finset.sum (Finset.univ.erase p) (fun r => gc.fireCount r) = 16 := by
      have hsplit :
          Finset.sum Finset.univ (fun r : Fin 4 => gc.fireCount r) =
            Finset.sum (Finset.univ.erase p) (fun r => gc.fireCount r) + gc.fireCount p := by
        simpa using (Finset.sum_erase_add (s := Finset.univ) (a := p)
          (f := fun r : Fin 4 => gc.fireCount r) (by simp)).symm
      -- Rewrite the standard full-sum decomposition into the order needed for omega.
      have hsplit' :
          gc.fireCount p + Finset.sum (Finset.univ.erase p) (fun r => gc.fireCount r) =
            Finset.sum Finset.univ (fun r : Fin 4 => gc.fireCount r) := by
        omega
      omega
    omega
  exact hnot4 hall4

private theorem gcFireSteps_nonempty_of_pos (gc : GoodCycle ⟨rs2222, f⟩)
    (p : Fin 4) (hpos : 0 < gc.fireCount p) :
    (gcFireSteps gc p).Nonempty := by
  have hcard : 0 < (gcFireSteps gc p).card := by
    rwa [gcFireSteps_card]
  exact Finset.card_pos.mp hcard

private theorem exists_four_consecutive_fire_steps_of_ge_four
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4)
    (hfc4 : 4 ≤ gc.fireCount p) :
    ∃ a b c d : Fin gc.configs.length,
      a.val < b.val ∧ b.val < c.val ∧ c.val < d.val ∧
      gc.moverAt a = p ∧ gc.moverAt b = p ∧ gc.moverAt c = p ∧ gc.moverAt d = p ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p) ∧
      (∀ k : Fin gc.configs.length, b.val < k.val → k.val < c.val → gc.moverAt k ≠ p) ∧
      (∀ k : Fin gc.configs.length, c.val < k.val → k.val < d.val → gc.moverAt k ≠ p) := by
  classical
  let S0 := gcFireSteps gc p
  have hS0card : 4 ≤ S0.card := by
    change 4 ≤ (gcFireSteps gc p).card
    rwa [gcFireSteps_card]
  have hS0ne : S0.Nonempty := Finset.card_pos.mp (by omega)
  let a := S0.min' hS0ne
  have ha0 : a ∈ S0 := Finset.min'_mem S0 hS0ne
  have ha_fire : gc.moverAt a = p := (mem_gcFireSteps_iff gc p a).mp ha0
  let S1 := S0.erase a
  have hS1card : 3 ≤ S1.card := by
    have hcard : S1.card + 1 = S0.card := by
      simpa [S1, S0] using (Finset.card_erase_add_one ha0)
    omega
  have hS1ne : S1.Nonempty := Finset.card_pos.mp (by omega)
  let b := S1.min' hS1ne
  have hb1 : b ∈ S1 := Finset.min'_mem S1 hS1ne
  have hb0 : b ∈ S0 := Finset.mem_of_mem_erase hb1
  have hb_fire : gc.moverAt b = p := (mem_gcFireSteps_iff gc p b).mp hb0
  have hab : a.val < b.val := by
    have hle : a ≤ b := Finset.min'_le S0 b hb0
    have hne : b ≠ a := Finset.ne_of_mem_erase hb1
    simpa using lt_of_le_of_ne hle hne.symm
  let S2 := S1.erase b
  have hS2card : 2 ≤ S2.card := by
    have hcard : S2.card + 1 = S1.card := by
      simpa [S2, S1] using (Finset.card_erase_add_one hb1)
    omega
  have hS2ne : S2.Nonempty := Finset.card_pos.mp (by omega)
  let c := S2.min' hS2ne
  have hc2 : c ∈ S2 := Finset.min'_mem S2 hS2ne
  have hc1 : c ∈ S1 := Finset.mem_of_mem_erase hc2
  have hc0 : c ∈ S0 := Finset.mem_of_mem_erase hc1
  have hc_fire : gc.moverAt c = p := (mem_gcFireSteps_iff gc p c).mp hc0
  have hbc : b.val < c.val := by
    have hle : b ≤ c := Finset.min'_le S1 c hc1
    have hne : c ≠ b := Finset.ne_of_mem_erase hc2
    simpa using lt_of_le_of_ne hle hne.symm
  let S3 := S2.erase c
  have hS3card : 1 ≤ S3.card := by
    have hcard : S3.card + 1 = S2.card := by
      simpa [S3, S2] using (Finset.card_erase_add_one hc2)
    omega
  have hS3ne : S3.Nonempty := Finset.card_pos.mp (by omega)
  let d := S3.min' hS3ne
  have hd3 : d ∈ S3 := Finset.min'_mem S3 hS3ne
  have hd2 : d ∈ S2 := Finset.mem_of_mem_erase hd3
  have hd1 : d ∈ S1 := Finset.mem_of_mem_erase hd2
  have hd0 : d ∈ S0 := Finset.mem_of_mem_erase hd1
  have hd_fire : gc.moverAt d = p := (mem_gcFireSteps_iff gc p d).mp hd0
  have hcd : c.val < d.val := by
    have hle : c ≤ d := Finset.min'_le S2 d hd2
    have hne : d ≠ c := Finset.ne_of_mem_erase hd3
    simpa using lt_of_le_of_ne hle hne.symm
  have hno_ab :
      ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p := by
    intro k hak hkb hk
    have hk0 : k ∈ S0 := (mem_gcFireSteps_iff gc p k).2 hk
    have hk1 : k ∈ S1 := Finset.mem_erase.mpr ⟨by
      intro hEq; subst hEq; omega, hk0⟩
    have hble : b ≤ k := Finset.min'_le S1 k hk1
    omega
  have hno_bc :
      ∀ k : Fin gc.configs.length, b.val < k.val → k.val < c.val → gc.moverAt k ≠ p := by
    intro k hbk hkc hk
    have hk1 : k ∈ S1 := Finset.mem_erase.mpr ⟨by
      intro hEq; subst hEq; omega, (mem_gcFireSteps_iff gc p k).2 hk⟩
    have hk2 : k ∈ S2 := Finset.mem_erase.mpr ⟨by
      intro hEq; subst hEq; omega, hk1⟩
    have hcle : c ≤ k := Finset.min'_le S2 k hk2
    omega
  have hno_cd :
      ∀ k : Fin gc.configs.length, c.val < k.val → k.val < d.val → gc.moverAt k ≠ p := by
    intro k hck hkd hk
    have hk1 : k ∈ S1 := Finset.mem_erase.mpr ⟨by
      intro hEq; subst hEq; omega, (mem_gcFireSteps_iff gc p k).2 hk⟩
    have hk2 : k ∈ S2 := Finset.mem_erase.mpr ⟨by
      intro hEq; subst hEq; omega, hk1⟩
    have hk3 : k ∈ S3 := Finset.mem_erase.mpr ⟨by
      intro hEq; subst hEq; omega, hk2⟩
    have hdle : d ≤ k := Finset.min'_le S3 k hk3
    omega
  exact ⟨a, b, c, d, hab, hbc, hcd, ha_fire, hb_fire, hc_fire, hd_fire,
    hno_ab, hno_bc, hno_cd⟩

private theorem gc_prefixFireCount_mono
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4)
    {a b : Nat} (hab : a ≤ b) :
    gc.prefixFireCount p a ≤ gc.prefixFireCount p b := by
  unfold GoodCycle.prefixFireCount
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)

private theorem gc_intervalFireCount_eq_sub
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) {a b : Nat} :
    gc.intervalFireCount p a b = gc.prefixFireCount p b - gc.prefixFireCount p a := by
  rfl

private theorem gc_intervalFireCount_split
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4)
    {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    gc.intervalFireCount p a c =
      gc.intervalFireCount p a b + gc.intervalFireCount p b c := by
  rw [gc_intervalFireCount_eq_sub, gc_intervalFireCount_eq_sub,
    gc_intervalFireCount_eq_sub]
  have hab' := gc_prefixFireCount_mono gc p hab
  have hbc' := gc_prefixFireCount_mono gc p hbc
  omega

private theorem gc_fireCount_eq_intervalFireCount_full
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) :
    gc.fireCount p = gc.intervalFireCount p 0 gc.configs.length := by
  unfold GoodCycle.fireCount
  rw [gc_intervalFireCount_eq_sub]
  simp [GoodCycle.prefixFireCount_zero]

private theorem gc_intervalFireCount_le_fireCount
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ gc.configs.length) :
    gc.intervalFireCount p a b ≤ gc.fireCount p := by
  rw [gc_fireCount_eq_intervalFireCount_full, gc_intervalFireCount_eq_sub,
    gc_intervalFireCount_eq_sub]
  have hmono_a := gc_prefixFireCount_mono gc p (Nat.zero_le a)
  have hmono_b := gc_prefixFireCount_mono gc p hb
  omega

private theorem gc_intervalFireCount_single
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4)
    {k : Nat} (hk : k < gc.configs.length) :
    gc.intervalFireCount p k (k + 1) =
      (if gc.moverAt ⟨k, hk⟩ = p then 1 else 0) := by
  rw [gc_intervalFireCount_eq_sub, gc.prefixFireCount_succ]
  rw [gc.fireIndicator_of_lt p hk]
  by_cases hm : gc.moverAt ⟨k, hk⟩ = p <;> simp [hm]

private theorem gc_intervalFireCount_eq_zero_not_mover
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4)
    {a b k : Nat} (hgap0 : gc.intervalFireCount p a b = 0)
    (hak : a ≤ k) (hkb : k + 1 ≤ b) (hk : k < gc.configs.length) :
    gc.moverAt ⟨k, hk⟩ ≠ p := by
  intro hm
  have hsingle : gc.intervalFireCount p k (k + 1) = 1 := by
    simp [gc_intervalFireCount_single gc p hk, hm]
  rw [gc_intervalFireCount_eq_sub] at hgap0
  rw [gc_intervalFireCount_eq_sub] at hsingle
  have hmono_a := gc_prefixFireCount_mono gc p hak
  have hmono_b := gc_prefixFireCount_mono gc p hkb
  omega

private theorem gc_firings_isolated_early (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) :
    ∀ (a : Fin gc.configs.length),
      gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p := by
  have hfc : 2 ≤ gc.fireCount p := gc_fireCount_ge_two gc p
  rcases binary_isolated_firings_or_ec gc p (rs2222_m p) hfc with hec | hall | hiso
  · exact False.elim (entryConflict_impossible gc hec)
  · exfalso
    have hneq : right p ≠ p := by
      exact (show ∀ p : Fin 4, right p ≠ p from by decide) p
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair (right p)
    have hmov : gc.moverAt k = right p := by
      rw [← hj]
      exact (gc.moverAt_unique k j hpriv).symm
    exact hneq (by
      calc
        right p = gc.moverAt k := hmov.symm
        _ = p := hall k)
  · exact hiso

private theorem gc_next_mover_left_or_right_early (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Fin gc.configs.length) :
    gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) ∨
      gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k) := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · exact Or.inl hleft
  · exfalso
    exact gc_firings_isolated_early gc (gc.moverAt k) k rfl hself
  · exact Or.inr hright

private theorem gc_nextIndex_eq_succ_pre (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k + 1 < gc.configs.length) :
    nextIndex gc.configs ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
  apply Fin.ext
  simp [nextIndex, Nat.mod_eq_of_lt hk]

private theorem gcWordFrom_simple_pre (gc : GoodCycle ⟨rs2222, f⟩) :
    SimpleWord4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
  intro t u htu hu hEq
  have hword_len :
      (gcWordFrom gc 0 gc.configs.length (by omega)).length = gc.configs.length := by
    simpa using gcWordFrom_length gc 0 gc.configs.length (by omega)
  have hu_lt : u < gc.configs.length := by
    simpa [hword_len] using hu
  have ht_lt : t < gc.configs.length := lt_trans htu hu_lt
  have hEqFrom :
      prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (gcWordFrom gc 0 gc.configs.length (by omega)) t =
      prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (gcWordFrom gc 0 gc.configs.length (by omega)) u := by
    rw [prefixState4From_eq_xor_prefixState4, prefixState4From_eq_xor_prefixState4]
    simp [hEq]
  have hcfg_t0 :
      gcCfgAt gc (0 + t) (by omega) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) t) :=
    gcCfgAt_eq_cfgFromBits4_prefixState4From gc 0 gc.configs.length
      (by omega) t (Nat.le_of_lt ht_lt)
  have hcfg_t1 :
      gc.configs.get ⟨0 + t, by omega⟩ =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) t) := by
    simpa [gcCfgAt_of_lt gc (0 + t) (by omega)] using hcfg_t0
  have hcfg_t :
      gcCfgAt gc t (Nat.le_of_lt ht_lt) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) t) := by
    rw [gcCfgAt_of_lt gc t ht_lt]
    simpa [Nat.zero_add] using hcfg_t1
  have hcfg_u0 :
      gcCfgAt gc (0 + u) (by omega) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) u) :=
    gcCfgAt_eq_cfgFromBits4_prefixState4From gc 0 gc.configs.length
      (by omega) u (Nat.le_of_lt hu_lt)
  have hcfg_u1 :
      gc.configs.get ⟨0 + u, by omega⟩ =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) u) := by
    simpa [gcCfgAt_of_lt gc (0 + u) (by omega)] using hcfg_u0
  have hcfg_u :
      gcCfgAt gc u (Nat.le_of_lt hu_lt) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) u) := by
    rw [gcCfgAt_of_lt gc u hu_lt]
    simpa [Nat.zero_add] using hcfg_u1
  have hcfgEq : gcCfgAt gc t (Nat.le_of_lt ht_lt) = gcCfgAt gc u (Nat.le_of_lt hu_lt) := by
    rw [hcfg_t, hcfg_u, hEqFrom]
  rw [gcCfgAt_of_lt gc t ht_lt, gcCfgAt_of_lt gc u hu_lt] at hcfgEq
  have hidx : (⟨t, ht_lt⟩ : Fin gc.configs.length) = ⟨u, hu_lt⟩ :=
    gc.distinct ⟨t, ht_lt⟩ ⟨u, hu_lt⟩ hcfgEq
  exact (Nat.ne_of_lt htu) (congrArg Fin.val hidx)

private theorem exists_zero_gap_of_fireCount_two_vs_four
    (gc : GoodCycle ⟨rs2222, f⟩) (p q : Fin 4)
    (hpfire4 : 4 ≤ gc.fireCount p) (hq2 : gc.fireCount q = 2) :
    ∃ a b : Fin gc.configs.length,
      a.val < b.val ∧
      gc.moverAt a = p ∧ gc.moverAt b = p ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p) ∧
      gc.intervalFireCount q a.val b.val = 0 := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hno_ab, hno_bc, hno_cd⟩ :=
    exists_four_consecutive_fire_steps_of_ge_four gc p hpfire4
  by_cases hab0 : gc.intervalFireCount q a.val b.val = 0
  · exact ⟨a, b, hab, ha, hb, hno_ab, hab0⟩
  by_cases hbc0 : gc.intervalFireCount q b.val c.val = 0
  · exact ⟨b, c, hbc, hb, hc, hno_bc, hbc0⟩
  by_cases hcd0 : gc.intervalFireCount q c.val d.val = 0
  · exact ⟨c, d, hcd, hc, hd, hno_cd, hcd0⟩
  have hab1 : 1 ≤ gc.intervalFireCount q a.val b.val := Nat.one_le_iff_ne_zero.mpr hab0
  have hbc1 : 1 ≤ gc.intervalFireCount q b.val c.val := Nat.one_le_iff_ne_zero.mpr hbc0
  have hcd1 : 1 ≤ gc.intervalFireCount q c.val d.val := Nat.one_le_iff_ne_zero.mpr hcd0
  have hsplit1 :
      gc.intervalFireCount q a.val c.val =
        gc.intervalFireCount q a.val b.val + gc.intervalFireCount q b.val c.val :=
    gc_intervalFireCount_split gc q (Nat.le_of_lt hab) (Nat.le_of_lt hbc)
  have hsplit2 :
      gc.intervalFireCount q a.val d.val =
        gc.intervalFireCount q a.val c.val + gc.intervalFireCount q c.val d.val :=
    gc_intervalFireCount_split gc q (by omega) (Nat.le_of_lt hcd)
  have hsum3 : 3 ≤ gc.intervalFireCount q a.val d.val := by
    rw [hsplit2, hsplit1]
    omega
  have hqd_le : gc.intervalFireCount q a.val d.val ≤ gc.fireCount q :=
    gc_intervalFireCount_le_fireCount gc q (by omega) (Nat.le_of_lt d.isLt)
  omega

private theorem exists_zero_gap_context_of_fireCount_two_vs_four
    (gc : GoodCycle ⟨rs2222, f⟩) (p q : Fin 4)
    (hpfire4 : 4 ≤ gc.fireCount p) (hq2 : gc.fireCount q = 2) :
    ∃ a b c d : Fin gc.configs.length,
      a.val < b.val ∧ b.val < c.val ∧ c.val < d.val ∧
      gc.moverAt a = p ∧ gc.moverAt b = p ∧ gc.moverAt c = p ∧ gc.moverAt d = p ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p) ∧
      (∀ k : Fin gc.configs.length, b.val < k.val → k.val < c.val → gc.moverAt k ≠ p) ∧
      (∀ k : Fin gc.configs.length, c.val < k.val → k.val < d.val → gc.moverAt k ≠ p) ∧
      (gc.intervalFireCount q a.val b.val = 0 ∨
        gc.intervalFireCount q b.val c.val = 0 ∨
        gc.intervalFireCount q c.val d.val = 0) := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hno_ab, hno_bc, hno_cd⟩ :=
    exists_four_consecutive_fire_steps_of_ge_four gc p hpfire4
  by_cases hab0 : gc.intervalFireCount q a.val b.val = 0
  · exact ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hno_ab, hno_bc, hno_cd, Or.inl hab0⟩
  by_cases hbc0 : gc.intervalFireCount q b.val c.val = 0
  · exact ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hno_ab, hno_bc, hno_cd, Or.inr (Or.inl hbc0)⟩
  by_cases hcd0 : gc.intervalFireCount q c.val d.val = 0
  · exact ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hno_ab, hno_bc, hno_cd, Or.inr (Or.inr hcd0)⟩
  have hab1 : 1 ≤ gc.intervalFireCount q a.val b.val := Nat.one_le_iff_ne_zero.mpr hab0
  have hbc1 : 1 ≤ gc.intervalFireCount q b.val c.val := Nat.one_le_iff_ne_zero.mpr hbc0
  have hcd1 : 1 ≤ gc.intervalFireCount q c.val d.val := Nat.one_le_iff_ne_zero.mpr hcd0
  have hsplit1 :
      gc.intervalFireCount q a.val c.val =
        gc.intervalFireCount q a.val b.val + gc.intervalFireCount q b.val c.val :=
    gc_intervalFireCount_split gc q (Nat.le_of_lt hab) (Nat.le_of_lt hbc)
  have hsplit2 :
      gc.intervalFireCount q a.val d.val =
        gc.intervalFireCount q a.val c.val + gc.intervalFireCount q c.val d.val :=
    gc_intervalFireCount_split gc q (by omega) (Nat.le_of_lt hcd)
  have hsum3 : 3 ≤ gc.intervalFireCount q a.val d.val := by
    rw [hsplit2, hsplit1]
    omega
  have hqd_le : gc.intervalFireCount q a.val d.val ≤ gc.fireCount q :=
    gc_intervalFireCount_le_fireCount gc q (by omega) (Nat.le_of_lt d.isLt)
  omega

private theorem internal_zero_gap_len2_false_left
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b c : Fin gc.configs.length)
    (hq : q = left p)
    (hab : a.val < b.val) (hbc : b.val < c.val)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p) (hc : gc.moverAt c = p)
    (hno_ab : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hno_bc : ∀ k : Fin gc.configs.length, b.val < k.val → k.val < c.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen2 : b.val = a.val + 2) : False := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right_early gc a
    rw [gc_nextIndex_eq_succ_pre gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h1neqq (by simpa [hq] using hleft)
    · exact hright
  have hb2 : (⟨a.val + 2, by omega⟩ : Fin gc.configs.length) = b := by
    apply Fin.ext
    exact hlen2.symm
  have hpair := gc_next_mover_left_or_right_early gc b
  rw [hb] at hpair
  have hnextb : nextIndex gc.configs b = ⟨a.val + 3, ha3lt⟩ := by
    apply Fin.ext
    have hbnext : b.val + 1 = a.val + 3 := by omega
    simpa [nextIndex, hbnext, Nat.mod_eq_of_lt ha3lt]
  rw [hnextb] at hpair
  rcases hpair with hleft | hright
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = q := by
      simpa [hq] using hleft
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
    have hsuf :
        gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
          ([p, right p, p, left p] : Word4) ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        ha, h1, hb2, hb, h3, hq] using
        (gcWordFrom_prefix_four gc a.val rem (by omega))
    have hsigma :
        sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
      rw [hsplit, hsuf]
      apply sigConflict4_append_suffix
      simpa [List.cons_append] using
        sigConflict4_abac_right_left p
          (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
    have htfTrue :
        isTFBlocked
          (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
      sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
    have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
      simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
    rw [htf] at htfTrue'
    contradiction
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = right p := by
      simpa using hright
    have hword :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            [p, right p, p, right p] ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hsplit :
          gcWordFrom gc 0 gc.configs.length (by omega) =
            gcWordFrom gc 0 a.val (by omega) ++
              gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      have hsuf :
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
            ([p, right p, p, right p] : Word4) ++
              gcWordFrom gc (a.val + 4) rem (by omega) := by
        simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          ha, h1, hb2, hb, h3] using
          (gcWordFrom_prefix_four gc a.val rem (by omega))
      rw [hsplit, hsuf]
      simp [rem, List.append_assoc]
    have hsimple' : SimpleWord4
        (gcWordFrom gc 0 a.val (by omega) ++
          p :: right p :: p :: right p :: gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) := by
      have hword' :
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: right p :: p :: right p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) =
            gcWordFrom gc 0 gc.configs.length (by omega) := by
        simpa [List.append_assoc] using hword.symm
      rw [hword']
      intro t u htu huu
      exact gcWordFrom_simple_pre gc htu huu
    have hnepr : p ≠ right p := by
      intro hp
      have hneq : right p ≠ p := by
        intro h
        have hval : ((p.val + 1) % 4) = p.val := congrArg Fin.val h
        omega
      exact hneq hp.symm
    have hc_gt3 : a.val + 3 < c.val := by
      have hneq : c ≠ ⟨a.val + 3, ha3lt⟩ := by
        intro hc_eq
        have hcp : gc.moverAt ⟨a.val + 3, ha3lt⟩ = p := by
          simpa [hc_eq] using hc
        rw [h3] at hcp
        exact hnepr hcp.symm
      have hle : a.val + 3 ≤ c.val := by omega
      exact lt_of_le_of_ne hle (by
        intro hEq
        apply hneq
        exact Fin.ext hEq.symm)
    have hlen_abab :
        (gcWordFrom gc 0 a.val (by omega)).length + 4 <
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: right p :: p :: right p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)).length := by
      simp [gcWordFrom_length]
      have hlen4 : a.val + 4 < gc.configs.length := by
        omega
      omega
    have hns :=
      not_simple_of_abab_before_end
        (gcWordFrom gc 0 a.val (by omega))
        (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
        p (right p)
        hnepr
        hlen_abab
    exact hns hsimple'

private theorem internal_zero_gap_len2_false_right
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b c : Fin gc.configs.length)
    (hq : q = right p)
    (hab : a.val < b.val) (hbc : b.val < c.val)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p) (hc : gc.moverAt c = p)
    (hno_ab : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hno_bc : ∀ k : Fin gc.configs.length, b.val < k.val → k.val < c.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen2 : b.val = a.val + 2) : False := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right_early gc a
    rw [gc_nextIndex_eq_succ_pre gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exact hleft
    · exfalso
      exact h1neqq (by simpa [hq] using hright)
  have hb2 : (⟨a.val + 2, by omega⟩ : Fin gc.configs.length) = b := by
    apply Fin.ext
    exact hlen2.symm
  have hpair := gc_next_mover_left_or_right_early gc b
  rw [hb] at hpair
  have hnextb : nextIndex gc.configs b = ⟨a.val + 3, ha3lt⟩ := by
    apply Fin.ext
    have hbnext : b.val + 1 = a.val + 3 := by omega
    simpa [nextIndex, hbnext, Nat.mod_eq_of_lt ha3lt]
  rw [hnextb] at hpair
  rcases hpair with hleft | hright
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = left p := by
      simpa using hleft
    have hword :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            [p, left p, p, left p] ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hsplit :
          gcWordFrom gc 0 gc.configs.length (by omega) =
            gcWordFrom gc 0 a.val (by omega) ++
              gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      have hsuf :
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
            ([p, left p, p, left p] : Word4) ++
              gcWordFrom gc (a.val + 4) rem (by omega) := by
        simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          ha, h1, hb2, hb, h3] using
          (gcWordFrom_prefix_four gc a.val rem (by omega))
      rw [hsplit, hsuf]
      simp [rem, List.append_assoc]
    have hsimple' : SimpleWord4
        (gcWordFrom gc 0 a.val (by omega) ++
          p :: left p :: p :: left p :: gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) := by
      have hword' :
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: left p :: p :: left p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) =
            gcWordFrom gc 0 gc.configs.length (by omega) := by
        simpa [List.append_assoc] using hword.symm
      rw [hword']
      intro t u htu huu
      exact gcWordFrom_simple_pre gc htu huu
    have hnepl : p ≠ left p := by
      intro hp
      have hneq : left p ≠ p := by
        intro h
        have hval : ((p.val + 3) % 4) = p.val := congrArg Fin.val h
        omega
      exact hneq hp.symm
    have hc_gt3 : a.val + 3 < c.val := by
      have hneq : c ≠ ⟨a.val + 3, ha3lt⟩ := by
        intro hc_eq
        have hcp : gc.moverAt ⟨a.val + 3, ha3lt⟩ = p := by
          simpa [hc_eq] using hc
        rw [h3] at hcp
        exact hnepl hcp.symm
      have hle : a.val + 3 ≤ c.val := by omega
      exact lt_of_le_of_ne hle (by
        intro hEq
        apply hneq
        exact Fin.ext hEq.symm)
    have hlen_abab :
        (gcWordFrom gc 0 a.val (by omega)).length + 4 <
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: left p :: p :: left p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)).length := by
      simp [gcWordFrom_length]
      have hlen4 : a.val + 4 < gc.configs.length := by
        omega
      omega
    have hns :=
      not_simple_of_abab_before_end
        (gcWordFrom gc 0 a.val (by omega))
        (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
        p (left p)
        hnepl
        hlen_abab
    exact hns hsimple'
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = q := by
      simpa [hq] using hright
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
    have hsuf :
        gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
          ([p, left p, p, right p] : Word4) ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        ha, h1, hb2, hb, h3, hq] using
        (gcWordFrom_prefix_four gc a.val rem (by omega))
    have hsigma :
        sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
      rw [hsplit, hsuf]
      apply sigConflict4_append_suffix
      simpa [List.cons_append] using
        sigConflict4_abac_left_right p
          (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
    have htfTrue :
        isTFBlocked
          (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
      sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
    have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
      simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
    rw [htf] at htfTrue'
    contradiction

private theorem zero_gap_len2_false_left_core
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen2 : b.val = a.val + 2)
    (ha4lt : a.val + 4 < gc.configs.length) : False := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right_early gc a
    rw [gc_nextIndex_eq_succ_pre gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h1neqq (by simpa [hq] using hleft)
    · exact hright
  have hb2 : (⟨a.val + 2, by omega⟩ : Fin gc.configs.length) = b := by
    apply Fin.ext
    exact hlen2.symm
  have hpair := gc_next_mover_left_or_right_early gc b
  rw [hb] at hpair
  have hnextb : nextIndex gc.configs b = ⟨a.val + 3, ha3lt⟩ := by
    apply Fin.ext
    have hbnext : b.val + 1 = a.val + 3 := by omega
    simpa [nextIndex, hbnext, Nat.mod_eq_of_lt ha3lt]
  rw [hnextb] at hpair
  rcases hpair with hleft | hright
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = q := by
      simpa [hq] using hleft
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
    have hsuf :
        gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
          ([p, right p, p, left p] : Word4) ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        ha, h1, hb2, hb, h3, hq] using
        (gcWordFrom_prefix_four gc a.val rem (by omega))
    have hsigma :
        sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
      rw [hsplit, hsuf]
      apply sigConflict4_append_suffix
      simpa [List.cons_append] using
        sigConflict4_abac_right_left p
          (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
    have htfTrue :
        isTFBlocked
          (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
      sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
    have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
      simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
    rw [htf] at htfTrue'
    contradiction
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = right p := by
      simpa using hright
    have hword :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            [p, right p, p, right p] ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hsplit :
          gcWordFrom gc 0 gc.configs.length (by omega) =
            gcWordFrom gc 0 a.val (by omega) ++
              gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      have hsuf :
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
            ([p, right p, p, right p] : Word4) ++
              gcWordFrom gc (a.val + 4) rem (by omega) := by
        simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          ha, h1, hb2, hb, h3] using
          (gcWordFrom_prefix_four gc a.val rem (by omega))
      rw [hsplit, hsuf]
      simp [rem, List.append_assoc]
    have hsimple' : SimpleWord4
        (gcWordFrom gc 0 a.val (by omega) ++
          p :: right p :: p :: right p :: gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) := by
      have hword' :
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: right p :: p :: right p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) =
            gcWordFrom gc 0 gc.configs.length (by omega) := by
        simpa [List.append_assoc] using hword.symm
      rw [hword']
      intro t u htu huu
      exact gcWordFrom_simple_pre gc htu huu
    have hnepr : p ≠ right p := by
      intro hp
      have hneq : right p ≠ p := by
        intro h
        have hval : ((p.val + 1) % 4) = p.val := congrArg Fin.val h
        omega
      exact hneq hp.symm
    have hlen_abab :
        (gcWordFrom gc 0 a.val (by omega)).length + 4 <
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: right p :: p :: right p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)).length := by
      simp [gcWordFrom_length]
      omega
    have hns :=
      not_simple_of_abab_before_end
        (gcWordFrom gc 0 a.val (by omega))
        (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
        p (right p)
        hnepr
        hlen_abab
    exact hns hsimple'

private theorem zero_gap_len2_false_right_core
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen2 : b.val = a.val + 2)
    (ha4lt : a.val + 4 < gc.configs.length) : False := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right_early gc a
    rw [gc_nextIndex_eq_succ_pre gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exact hleft
    · exfalso
      exact h1neqq (by simpa [hq] using hright)
  have hb2 : (⟨a.val + 2, by omega⟩ : Fin gc.configs.length) = b := by
    apply Fin.ext
    exact hlen2.symm
  have hpair := gc_next_mover_left_or_right_early gc b
  rw [hb] at hpair
  have hnextb : nextIndex gc.configs b = ⟨a.val + 3, ha3lt⟩ := by
    apply Fin.ext
    have hbnext : b.val + 1 = a.val + 3 := by omega
    simpa [nextIndex, hbnext, Nat.mod_eq_of_lt ha3lt]
  rw [hnextb] at hpair
  rcases hpair with hleft | hright
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = left p := by
      simpa using hleft
    have hword :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            [p, left p, p, left p] ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hsplit :
          gcWordFrom gc 0 gc.configs.length (by omega) =
            gcWordFrom gc 0 a.val (by omega) ++
              gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      have hsuf :
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
            ([p, left p, p, left p] : Word4) ++
              gcWordFrom gc (a.val + 4) rem (by omega) := by
        simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          ha, h1, hb2, hb, h3] using
          (gcWordFrom_prefix_four gc a.val rem (by omega))
      rw [hsplit, hsuf]
      simp [rem, List.append_assoc]
    have hsimple' : SimpleWord4
        (gcWordFrom gc 0 a.val (by omega) ++
          p :: left p :: p :: left p :: gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) := by
      have hword' :
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: left p :: p :: left p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)) =
            gcWordFrom gc 0 gc.configs.length (by omega) := by
        simpa [List.append_assoc] using hword.symm
      rw [hword']
      intro t u htu huu
      exact gcWordFrom_simple_pre gc htu huu
    have hnepl : p ≠ left p := by
      intro hp
      have hneq : left p ≠ p := by
        intro h
        have hval : ((p.val + 3) % 4) = p.val := congrArg Fin.val h
        omega
      exact hneq hp.symm
    have hlen_abab :
        (gcWordFrom gc 0 a.val (by omega)).length + 4 <
          (gcWordFrom gc 0 a.val (by omega) ++
            p :: left p :: p :: left p ::
              gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega)).length := by
      simp [gcWordFrom_length]
      omega
    have hns :=
      not_simple_of_abab_before_end
        (gcWordFrom gc 0 a.val (by omega))
        (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
        p (left p)
        hnepl
        hlen_abab
    exact hns hsimple'
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = q := by
      simpa [hq] using hright
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
    have hsuf :
        gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
          ([p, left p, p, right p] : Word4) ++
            gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega) := by
      let rem := gc.configs.length - (a.val + 4)
      have hlenRem : gc.configs.length - a.val = rem + 4 := by
        unfold rem
        omega
      simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        ha, h1, hb2, hb, h3, hq] using
        (gcWordFrom_prefix_four gc a.val rem (by omega))
    have hsigma :
        sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
      rw [hsplit, hsuf]
      apply sigConflict4_append_suffix
      simpa [List.cons_append] using
        sigConflict4_abac_left_right p
          (gcWordFrom gc (a.val + 4) (gc.configs.length - (a.val + 4)) (by omega))
    have htfTrue :
        isTFBlocked
          (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
      sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
    have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
      simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
    rw [htf] at htfTrue'
    contradiction

private theorem gcWordFrom_full_prefixState_zero (gc : GoodCycle ⟨rs2222, f⟩) :
    prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length = (fun _ => false) := by
  funext j
  let bits0 := bitsOfCfg4 (gcCfgAt gc 0 (by omega))
  have hcfg :
      gcCfgAt gc gc.configs.length (le_refl _) =
        cfgFromBits4 (prefixState4From bits0
          (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length) :=
    by
      simpa [Nat.zero_add] using
        (gcCfgAt_eq_cfgFromBits4_prefixState4From gc 0 gc.configs.length (by omega)
          gc.configs.length (le_refl _))
  have hcfg' :
      gcCfgAt gc gc.configs.length (le_refl _) = gcCfgAt gc 0 (by omega) := by
    rw [gcCfgAt_of_ge gc gc.configs.length (le_refl _) (le_refl _)]
    rw [gcCfgAt_of_lt gc 0 (gc.configs_length_pos)]
  have hbits :
      prefixState4From bits0 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length = bits0 := by
    have hbitsfun :
        bitsOfCfg4
          (cfgFromBits4
            (prefixState4From bits0
              (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length)) = bits0 := by
      calc
        bitsOfCfg4
          (cfgFromBits4
            (prefixState4From bits0
              (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length))
            = bitsOfCfg4 (gcCfgAt gc gc.configs.length (le_refl _)) := by rw [hcfg.symm]
        _ = bitsOfCfg4 (gcCfgAt gc 0 (by omega)) := by rw [hcfg']
        _ = bits0 := rfl
    simpa [bitsOfCfg4_cfgFromBits4] using hbitsfun
  have hbit := congrArg (fun f => f j) hbits
  rw [prefixState4From_eq_xor_prefixState4] at hbit
  cases hbj : bits0 j <;> simp [hbj] at hbit ⊢
  · exact hbit
  · exact hbit

private theorem zero_gap_len2_false_left_end
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen2 : b.val = a.val + 2)
    (hend : a.val + 4 = gc.configs.length) : False := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right_early gc a
    rw [gc_nextIndex_eq_succ_pre gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h1neqq (by simpa [hq] using hleft)
    · exact hright
  have hb2 : (⟨a.val + 2, by omega⟩ : Fin gc.configs.length) = b := by
    apply Fin.ext
    exact hlen2.symm
  have hpair := gc_next_mover_left_or_right_early gc b
  rw [hb] at hpair
  have hnextb : nextIndex gc.configs b = ⟨a.val + 3, ha3lt⟩ := by
    apply Fin.ext
    have hbnext : b.val + 1 = a.val + 3 := by omega
    simpa [nextIndex, hbnext, Nat.mod_eq_of_lt ha3lt]
  rw [hnextb] at hpair
  rcases hpair with hleft | hright
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = q := by
      simpa [hq] using hleft
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
    have hsuf :
        gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
          ([p, right p, p, left p] : Word4) := by
      have hlenRem : gc.configs.length - a.val = 4 := by omega
      simpa [hlenRem, ha, h1, hb2, hb, h3, hq] using
        (gcWordFrom_prefix_four gc a.val 0 (by omega))
    have hsigma :
        sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
      rw [hsplit, hsuf]
      apply sigConflict4_append_suffix
      simpa [List.cons_append] using sigConflict4_abac_right_left p ([] : Word4)
    have htfTrue :
        isTFBlocked
          (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
      sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
    have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
      simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
    rw [htf] at htfTrue'
    contradiction
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = right p := by
      simpa using hright
    have hword :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++ [p, right p, p, right p] := by
      have hsplit :
          gcWordFrom gc 0 gc.configs.length (by omega) =
            gcWordFrom gc 0 a.val (by omega) ++
              gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
      have hlenRem : gc.configs.length - a.val = 4 := by omega
      have hsuf :
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
            ([p, right p, p, right p] : Word4) := by
        simpa [hlenRem, ha, h1, hb2, hb, h3] using
          (gcWordFrom_prefix_four gc a.val 0 (by omega))
      rw [hsplit, hsuf]
    have hword' :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            p :: right p :: p :: right p :: [] := by
      simpa [List.append_assoc] using hword
    have hclose : prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length = (fun _ => false) :=
      gcWordFrom_full_prefixState_zero gc
    have hsame0 :
        prefixState4
          (gcWordFrom gc 0 a.val (by omega) ++ [p, right p, p, right p])
          a.val =
        prefixState4
          (gcWordFrom gc 0 a.val (by omega) ++ [p, right p, p, right p])
          gc.configs.length := by
      have habab := prefixState4_append_abab_eq (gcWordFrom gc 0 a.val (by omega)) [] p (right p) (by
          intro hp
          have hval : ((p.val + 1) % 4) = p.val := by simpa using congrArg Fin.val hp.symm
          omega)
      have hprelen : (gcWordFrom gc 0 a.val (by omega)).length = a.val := by
        simpa using gcWordFrom_length gc 0 a.val (by omega)
      simpa [hprelen, hend] using habab
    have hsame :
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) a.val =
          prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length := by
      simpa [hword'] using hsame0
    have hzero : prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length =
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 0 := by
      simpa [prefixState4, gcWordFrom_length] using hclose
    have hEq : prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) a.val =
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 0 := by
      rw [hsame, hzero]
    have hsimple : SimpleWord4 (gcWordFrom gc 0 gc.configs.length (by omega)) := gcWordFrom_simple_pre gc
    have hlenWord : (gcWordFrom gc 0 gc.configs.length (by omega)).length = gc.configs.length := by
      simpa using gcWordFrom_length gc 0 gc.configs.length (by omega)
    have hlen8 : 8 ≤ gc.configs.length := by
      have hsum := gc.sum_fireCount
      calc
        8 = ∑ _p : Fin 4, 2 := by norm_num
        _ ≤ ∑ p : Fin 4, gc.fireCount p := by
              apply Finset.sum_le_sum
              intro p _
              exact gc_fireCount_ge_two gc p
        _ = gc.configs.length := hsum
    have ha_pos : 0 < a.val := by
      omega
    have ha_lt_word : a.val < (gcWordFrom gc 0 gc.configs.length (by omega)).length := by
      simpa [hlenWord] using a.isLt
    exact hsimple ha_pos ha_lt_word hEq.symm

private theorem zero_gap_len2_false_right_end
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen2 : b.val = a.val + 2)
    (hend : a.val + 4 = gc.configs.length) : False := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right_early gc a
    rw [gc_nextIndex_eq_succ_pre gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exact hleft
    · exfalso
      exact h1neqq (by simpa [hq] using hright)
  have hb2 : (⟨a.val + 2, by omega⟩ : Fin gc.configs.length) = b := by
    apply Fin.ext
    exact hlen2.symm
  have hpair := gc_next_mover_left_or_right_early gc b
  rw [hb] at hpair
  have hnextb : nextIndex gc.configs b = ⟨a.val + 3, ha3lt⟩ := by
    apply Fin.ext
    have hbnext : b.val + 1 = a.val + 3 := by omega
    simpa [nextIndex, hbnext, Nat.mod_eq_of_lt ha3lt]
  rw [hnextb] at hpair
  rcases hpair with hleft | hright
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = left p := by
      simpa using hleft
    have hword :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++ [p, left p, p, left p] := by
      have hsplit :
          gcWordFrom gc 0 gc.configs.length (by omega) =
            gcWordFrom gc 0 a.val (by omega) ++
              gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
      have hlenRem : gc.configs.length - a.val = 4 := by omega
      have hsuf :
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
            ([p, left p, p, left p] : Word4) := by
        simpa [hlenRem, ha, h1, hb2, hb, h3] using
          (gcWordFrom_prefix_four gc a.val 0 (by omega))
      rw [hsplit, hsuf]
    have hword' :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            p :: left p :: p :: left p :: [] := by
      simpa [List.append_assoc] using hword
    have hclose : prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length = (fun _ => false) :=
      gcWordFrom_full_prefixState_zero gc
    have hsame0 :
        prefixState4
          (gcWordFrom gc 0 a.val (by omega) ++ [p, left p, p, left p])
          a.val =
        prefixState4
          (gcWordFrom gc 0 a.val (by omega) ++ [p, left p, p, left p])
          gc.configs.length := by
      have habab := prefixState4_append_abab_eq (gcWordFrom gc 0 a.val (by omega)) [] p (left p) (by
          intro hp
          have hval : ((p.val + 3) % 4) = p.val := by simpa using congrArg Fin.val hp.symm
          omega)
      have hprelen : (gcWordFrom gc 0 a.val (by omega)).length = a.val := by
        simpa using gcWordFrom_length gc 0 a.val (by omega)
      simpa [hprelen, hend] using habab
    have hsame :
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) a.val =
          prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length := by
      simpa [hword'] using hsame0
    have hzero : prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) gc.configs.length =
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 0 := by
      simpa [prefixState4, gcWordFrom_length] using hclose
    have hEq : prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) a.val =
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 0 := by
      rw [hsame, hzero]
    have hsimple : SimpleWord4 (gcWordFrom gc 0 gc.configs.length (by omega)) := gcWordFrom_simple_pre gc
    have hlenWord : (gcWordFrom gc 0 gc.configs.length (by omega)).length = gc.configs.length := by
      simpa using gcWordFrom_length gc 0 gc.configs.length (by omega)
    have hlen8 : 8 ≤ gc.configs.length := by
      have hsum := gc.sum_fireCount
      calc
        8 = ∑ _p : Fin 4, 2 := by norm_num
        _ ≤ ∑ p : Fin 4, gc.fireCount p := by
              apply Finset.sum_le_sum
              intro p _
              exact gc_fireCount_ge_two gc p
        _ = gc.configs.length := hsum
    have ha_pos : 0 < a.val := by
      omega
    have ha_lt_word : a.val < (gcWordFrom gc 0 gc.configs.length (by omega)).length := by
      simpa [hlenWord] using a.isLt
    exact hsimple ha_pos ha_lt_word hEq.symm
  · have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = q := by
      simpa [hq] using hright
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) =
          gcWordFrom gc 0 a.val (by omega) ++
            gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
    have hsuf :
        gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
          ([p, left p, p, right p] : Word4) := by
      have hlenRem : gc.configs.length - a.val = 4 := by omega
      simpa [hlenRem, ha, h1, hb2, hb, h3, hq] using
        (gcWordFrom_prefix_four gc a.val 0 (by omega))
    have hsigma :
        sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
      rw [hsplit, hsuf]
      apply sigConflict4_append_suffix
      simpa [List.cons_append] using sigConflict4_abac_left_right p ([] : Word4)
    have htfTrue :
        isTFBlocked
          (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
      sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
    have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
      simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
    rw [htf] at htfTrue'
    contradiction

private theorem zero_gap_len2_false_left_wrap
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b c d : Fin gc.configs.length)
    (hq : q = left p)
    (hab : a.val < b.val) (hbc : b.val < c.val)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hc : gc.moverAt c = p) (hd : gc.moverAt d = p)
    (hq2 : gc.fireCount q = 2)
    (hab_nz : gc.intervalFireCount q a.val b.val ≠ 0)
    (hbc_nz : gc.intervalFireCount q b.val c.val ≠ 0)
    (hgap0 : gc.intervalFireCount q c.val d.val = 0)
    (hlen2 : d.val = c.val + 2)
    (hwrap : gc.configs.length < c.val + 4) : False := by
  have hnepr : right p ≠ p := by
    intro h
    have hval : ((p.val + 1) % 4) = p.val := by
      simpa [right] using congrArg Fin.val h
    omega
  have h0neqq : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ ≠ q := by
    intro h0q
    have ha_ne0 : a.val ≠ 0 := by
      intro ha0
      have h0p : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ = p := by
        have ha_eq : a = ⟨0, gc_len_ge_1 gc⟩ := by
          apply Fin.ext
          exact ha0
        simpa [ha_eq] using ha
      have hqnep : q ≠ p := by
        rw [hq]
        intro hqp
        have hval : ((p.val + 3) % 4) = p.val := by
          simpa [left] using congrArg Fin.val hqp
        omega
      exact hqnep (by rw [← h0q, h0p])
    have ha_pos : 1 ≤ a.val := by omega
    have h01 : gc.intervalFireCount q 0 1 = 1 := by
      rw [gc_intervalFireCount_single gc q (gc_len_ge_1 gc)]
      simp [h0q]
    have h0a_split :
        gc.intervalFireCount q 0 a.val =
          gc.intervalFireCount q 0 1 + gc.intervalFireCount q 1 a.val :=
      gc_intervalFireCount_split gc q (Nat.zero_le 1) ha_pos
    have h0a_pos : 1 ≤ gc.intervalFireCount q 0 a.val := by
      rw [h0a_split]
      omega
    have hab_pos : 1 ≤ gc.intervalFireCount q a.val b.val := Nat.one_le_iff_ne_zero.mpr hab_nz
    have hbc_pos : 1 ≤ gc.intervalFireCount q b.val c.val := Nat.one_le_iff_ne_zero.mpr hbc_nz
    have h0b_split :
        gc.intervalFireCount q 0 b.val =
          gc.intervalFireCount q 0 a.val + gc.intervalFireCount q a.val b.val :=
      gc_intervalFireCount_split gc q (Nat.zero_le a.val) (Nat.le_of_lt hab)
    have h0c_split :
        gc.intervalFireCount q 0 c.val =
          gc.intervalFireCount q 0 b.val + gc.intervalFireCount q b.val c.val :=
      gc_intervalFireCount_split gc q (Nat.zero_le b.val) (Nat.le_of_lt hbc)
    have h0c_pos : 3 ≤ gc.intervalFireCount q 0 c.val := by
      rw [h0c_split, h0b_split]
      omega
    have h0c_le : gc.intervalFireCount q 0 c.val ≤ gc.fireCount q :=
      gc_intervalFireCount_le_fireCount gc q (Nat.zero_le c.val) (Nat.le_of_lt c.isLt)
    rw [hq2] at h0c_le
    omega
  have hc1lt : c.val + 1 < gc.configs.length := by omega
  have hdlast : d.val + 1 = gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨c.val + 1, hc1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) hc1lt
  have h1 : gc.moverAt ⟨c.val + 1, hc1lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right_early gc c
    rw [gc_nextIndex_eq_succ_pre gc c.val hc1lt, hc] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h1neqq (by simpa [hq] using hleft)
    · exact hright
  have hnextd0 : nextIndex gc.configs d = ⟨0, gc.configs_length_pos⟩ := by
    apply Fin.ext
    simp [nextIndex, hdlast]
  have h0 : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ = right p := by
    have hpair := gc_next_mover_left_or_right_early gc d
    rw [hd, hnextd0] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h0neqq (by simpa [hq] using hleft)
    · exact hright
  let pre := gcWordFrom gc 0 c.val (by omega)
  have hprelen : pre.length = c.val := by
    simpa [pre] using gcWordFrom_length gc 0 c.val (by omega)
  have hd2 : (⟨c.val + 2, by omega⟩ : Fin gc.configs.length) = d := by
    apply Fin.ext
    exact hlen2.symm
  have hsuf : gcWordFrom gc c.val 3 (by omega) = ([p, right p, p] : Word4) := by
    simp [gcWordFrom, hc, h1, hd2, hd]
  have hclen : gc.configs.length = c.val + 3 := by omega
  have hword :
      gcWordFrom gc 0 gc.configs.length (by omega) = pre ++ [p, right p, p] := by
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) = pre ++ gcWordFrom gc c.val 3 (by omega) := by
      simpa [pre, hclen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 c.val 3 (by omega))
    rw [hsplit, hsuf]
  have hword' : gcWordFrom gc 0 (c.val + 3) (by omega) = pre ++ [p, right p, p] := by
    have hsplit' :
        gcWordFrom gc 0 (c.val + 3) (by omega) = pre ++ gcWordFrom gc c.val 3 (by omega) := by
      simpa [pre, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 c.val 3 (by omega))
    rw [hsplit', hsuf]
  have hclose :
      prefixState4 (pre ++ [p, right p, p]) (pre.length + 3) = (fun _ => false) := by
    rw [← hword']
    simpa [hprelen] using (show
      prefixState4 (gcWordFrom gc 0 (c.val + 3) (by omega)) (c.val + 3) = (fun _ => false) from by
        simpa [hclen] using gcWordFrom_full_prefixState_zero gc)
  have hshift := prefixState4_append_shift pre ([p, right p, p] : Word4) 3
  have hclose' :
      prefixState4From (prefixState4 pre pre.length) [p, right p, p] 3 = (fun _ => false) := by
    rw [← hshift]
    exact hclose
  have hclose_eval :
      flipBit4 (flipBit4 (flipBit4 (prefixState4 pre pre.length) p) (right p)) p = (fun _ => false) := by
    simpa [prefixState4From, prefixState4] using hclose'
  have hpap :
      flipBit4 (flipBit4 (flipBit4 (prefixState4 pre pre.length) p) (right p)) p =
        flipBit4 (prefixState4 pre pre.length) (right p) := by
    rw [flipBit4_commute (bits := flipBit4 (prefixState4 pre pre.length) p)
      (i := right p) (j := p) hnepr]
    simp [flipBit4_self_self]
  have hflip : flipBit4 (prefixState4 pre pre.length) (right p) = (fun _ => false) := by
    rw [← hpap]
    exact hclose_eval
  have hstatec : prefixState4 pre pre.length = flipBit4 (fun _ => false) (right p) := by
    simpa [flipBit4_self_self] using congrArg (fun bits => flipBit4 bits (right p)) hflip
  have hword0 :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        [right p] ++ gcWordFrom gc 1 (gc.configs.length - 1) (by omega) := by
    have hlen1 : 1 + (gc.configs.length - 1) = gc.configs.length := by omega
    simpa [hlen1, gcWordFrom, h0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 1 (gc.configs.length - 1) (by omega))
  have hprefix1 :
      prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 1 =
        flipBit4 (fun _ => false) (right p) := by
    rw [hword0]
    simp [prefixState4]
  have hshift0 := prefixState4_append_shift pre ([p, right p, p] : Word4) 0
  have hprefixc_pre :
      prefixState4 (pre ++ [p, right p, p]) pre.length = prefixState4 pre pre.length := by
    simpa [prefixState4From, prefixState4] using hshift0
  have hprefixc :
      prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) c.val = prefixState4 pre pre.length := by
    simpa [hword, hprelen] using hprefixc_pre
  have hEq :
      prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 1 =
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) c.val := by
    rw [hprefixc]
    exact hprefix1.trans hstatec.symm
  have hsimple : SimpleWord4 (gcWordFrom gc 0 gc.configs.length (by omega)) := gcWordFrom_simple_pre gc
  have h1c : 1 < c.val := by
    have ha_ne0 : a.val ≠ 0 := by
      intro ha0
      have h0p : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ = p := by
        have ha_eq : a = ⟨0, gc_len_ge_1 gc⟩ := by
          apply Fin.ext
          exact ha0
        simpa [ha_eq] using ha
      exact hnepr (by rw [← h0, h0p])
    omega
  exact hsimple h1c (by simpa using c.isLt) hEq

private theorem zero_gap_len2_false_right_wrap
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b c d : Fin gc.configs.length)
    (hq : q = right p)
    (hab : a.val < b.val) (hbc : b.val < c.val)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hc : gc.moverAt c = p) (hd : gc.moverAt d = p)
    (hq2 : gc.fireCount q = 2)
    (hab_nz : gc.intervalFireCount q a.val b.val ≠ 0)
    (hbc_nz : gc.intervalFireCount q b.val c.val ≠ 0)
    (hgap0 : gc.intervalFireCount q c.val d.val = 0)
    (hlen2 : d.val = c.val + 2)
    (hwrap : gc.configs.length < c.val + 4) : False := by
  have hnepl : left p ≠ p := by
    intro h
    have hval : ((p.val + 3) % 4) = p.val := by
      simpa [left] using congrArg Fin.val h
    omega
  have h0neqq : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ ≠ q := by
    intro h0q
    have ha_ne0 : a.val ≠ 0 := by
      intro ha0
      have h0p : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ = p := by
        have ha_eq : a = ⟨0, gc_len_ge_1 gc⟩ := by
          apply Fin.ext
          exact ha0
        simpa [ha_eq] using ha
      have hqnep : q ≠ p := by
        rw [hq]
        intro hqp
        have hval : ((p.val + 1) % 4) = p.val := by
          simpa [right] using congrArg Fin.val hqp
        omega
      exact hqnep (by rw [← h0q, h0p])
    have ha_pos : 1 ≤ a.val := by omega
    have h01 : gc.intervalFireCount q 0 1 = 1 := by
      rw [gc_intervalFireCount_single gc q (gc_len_ge_1 gc)]
      simp [h0q]
    have h0a_split :
        gc.intervalFireCount q 0 a.val =
          gc.intervalFireCount q 0 1 + gc.intervalFireCount q 1 a.val :=
      gc_intervalFireCount_split gc q (Nat.zero_le 1) ha_pos
    have h0a_pos : 1 ≤ gc.intervalFireCount q 0 a.val := by
      rw [h0a_split]
      omega
    have hab_pos : 1 ≤ gc.intervalFireCount q a.val b.val := Nat.one_le_iff_ne_zero.mpr hab_nz
    have hbc_pos : 1 ≤ gc.intervalFireCount q b.val c.val := Nat.one_le_iff_ne_zero.mpr hbc_nz
    have h0b_split :
        gc.intervalFireCount q 0 b.val =
          gc.intervalFireCount q 0 a.val + gc.intervalFireCount q a.val b.val :=
      gc_intervalFireCount_split gc q (Nat.zero_le a.val) (Nat.le_of_lt hab)
    have h0c_split :
        gc.intervalFireCount q 0 c.val =
          gc.intervalFireCount q 0 b.val + gc.intervalFireCount q b.val c.val :=
      gc_intervalFireCount_split gc q (Nat.zero_le b.val) (Nat.le_of_lt hbc)
    have h0c_pos : 3 ≤ gc.intervalFireCount q 0 c.val := by
      rw [h0c_split, h0b_split]
      omega
    have h0c_le : gc.intervalFireCount q 0 c.val ≤ gc.fireCount q :=
      gc_intervalFireCount_le_fireCount gc q (Nat.zero_le c.val) (Nat.le_of_lt c.isLt)
    rw [hq2] at h0c_le
    omega
  have hc1lt : c.val + 1 < gc.configs.length := by omega
  have hdlast : d.val + 1 = gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨c.val + 1, hc1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) hc1lt
  have h1 : gc.moverAt ⟨c.val + 1, hc1lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right_early gc c
    rw [gc_nextIndex_eq_succ_pre gc c.val hc1lt, hc] at hpair
    rcases hpair with hleft | hright
    · exact hleft
    · exfalso
      exact h1neqq (by simpa [hq] using hright)
  have hnextd0 : nextIndex gc.configs d = ⟨0, gc.configs_length_pos⟩ := by
    apply Fin.ext
    simp [nextIndex, hdlast]
  have h0 : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ = left p := by
    have hpair := gc_next_mover_left_or_right_early gc d
    rw [hd, hnextd0] at hpair
    rcases hpair with hleft | hright
    · exact hleft
    · exfalso
      exact h0neqq (by simpa [hq] using hright)
  let pre := gcWordFrom gc 0 c.val (by omega)
  have hprelen : pre.length = c.val := by
    simpa [pre] using gcWordFrom_length gc 0 c.val (by omega)
  have hd2 : (⟨c.val + 2, by omega⟩ : Fin gc.configs.length) = d := by
    apply Fin.ext
    exact hlen2.symm
  have hsuf : gcWordFrom gc c.val 3 (by omega) = ([p, left p, p] : Word4) := by
    simp [gcWordFrom, hc, h1, hd2, hd]
  have hclen : gc.configs.length = c.val + 3 := by omega
  have hword :
      gcWordFrom gc 0 gc.configs.length (by omega) = pre ++ [p, left p, p] := by
    have hsplit :
        gcWordFrom gc 0 gc.configs.length (by omega) = pre ++ gcWordFrom gc c.val 3 (by omega) := by
      simpa [pre, hclen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 c.val 3 (by omega))
    rw [hsplit, hsuf]
  have hword' : gcWordFrom gc 0 (c.val + 3) (by omega) = pre ++ [p, left p, p] := by
    have hsplit' :
        gcWordFrom gc 0 (c.val + 3) (by omega) = pre ++ gcWordFrom gc c.val 3 (by omega) := by
      simpa [pre, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (gcWordFrom_append gc 0 c.val 3 (by omega))
    rw [hsplit', hsuf]
  have hclose :
      prefixState4 (pre ++ [p, left p, p]) (pre.length + 3) = (fun _ => false) := by
    rw [← hword']
    simpa [hprelen] using (show
      prefixState4 (gcWordFrom gc 0 (c.val + 3) (by omega)) (c.val + 3) = (fun _ => false) from by
        simpa [hclen] using gcWordFrom_full_prefixState_zero gc)
  have hshift := prefixState4_append_shift pre ([p, left p, p] : Word4) 3
  have hclose' :
      prefixState4From (prefixState4 pre pre.length) [p, left p, p] 3 = (fun _ => false) := by
    rw [← hshift]
    exact hclose
  have hclose_eval :
      flipBit4 (flipBit4 (flipBit4 (prefixState4 pre pre.length) p) (left p)) p = (fun _ => false) := by
    simpa [prefixState4From, prefixState4] using hclose'
  have hpap :
      flipBit4 (flipBit4 (flipBit4 (prefixState4 pre pre.length) p) (left p)) p =
        flipBit4 (prefixState4 pre pre.length) (left p) := by
    rw [flipBit4_commute (bits := flipBit4 (prefixState4 pre pre.length) p)
      (i := left p) (j := p) hnepl]
    simp [flipBit4_self_self]
  have hflip : flipBit4 (prefixState4 pre pre.length) (left p) = (fun _ => false) := by
    rw [← hpap]
    exact hclose_eval
  have hstatec : prefixState4 pre pre.length = flipBit4 (fun _ => false) (left p) := by
    simpa [flipBit4_self_self] using congrArg (fun bits => flipBit4 bits (left p)) hflip
  have hword0 :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        [left p] ++ gcWordFrom gc 1 (gc.configs.length - 1) (by omega) := by
    have hlen1 : 1 + (gc.configs.length - 1) = gc.configs.length := by omega
    simpa [hlen1, gcWordFrom, h0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 1 (gc.configs.length - 1) (by omega))
  have hprefix1 :
      prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 1 =
        flipBit4 (fun _ => false) (left p) := by
    rw [hword0]
    simp [prefixState4]
  have hshift0 := prefixState4_append_shift pre ([p, left p, p] : Word4) 0
  have hprefixc_pre :
      prefixState4 (pre ++ [p, left p, p]) pre.length = prefixState4 pre pre.length := by
    simpa [prefixState4From, prefixState4] using hshift0
  have hprefixc :
      prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) c.val = prefixState4 pre pre.length := by
    simpa [hword, hprelen] using hprefixc_pre
  have hEq :
      prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) 1 =
        prefixState4 (gcWordFrom gc 0 gc.configs.length (by omega)) c.val := by
    rw [hprefixc]
    exact hprefix1.trans hstatec.symm
  have hsimple : SimpleWord4 (gcWordFrom gc 0 gc.configs.length (by omega)) := gcWordFrom_simple_pre gc
  have h1c : 1 < c.val := by
    have ha_ne0 : a.val ≠ 0 := by
      intro ha0
      have h0p : gc.moverAt ⟨0, gc_len_ge_1 gc⟩ = p := by
        have ha_eq : a = ⟨0, gc_len_ge_1 gc⟩ := by
          apply Fin.ext
          exact ha0
        simpa [ha_eq] using ha
      exact hnepl (by rw [← h0, h0p])
    omega
  exact hsimple h1c (by simpa using c.isLt) hEq

private theorem gc_fireCount_eq_two_of_not_ge_four
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4)
    (hnot : ¬ 4 ≤ gc.fireCount p) :
    gc.fireCount p = 2 := by
  have hge2 : 2 ≤ gc.fireCount p := gc_fireCount_ge_two gc p
  have heven : Even (gc.fireCount p) := gc.binary_fireCount_even p (rs2222_m p)
  rcases heven with ⟨m, hm⟩
  omega

private theorem exists_adjacent_high_low_fireCounts
    (gc : GoodCycle ⟨rs2222, f⟩)
    (hnot2 : ¬ ∀ p : Fin 4, gc.fireCount p = 2)
    (hnot4 : ¬ ∀ p : Fin 4, gc.fireCount p = 4) :
    ∃ p q : Fin 4,
      4 ≤ gc.fireCount p ∧ gc.fireCount q = 2 ∧
      (q = left p ∨ q = right p) := by
  obtain ⟨q, hq2⟩ := exists_fireCount_eq_two_of_not_all_four gc hnot4
  by_cases hL : 4 ≤ gc.fireCount (left q)
  · exact ⟨left q, q, hL, hq2, Or.inr (right_left_eq_self q).symm⟩
  by_cases hR : 4 ≤ gc.fireCount (right q)
  · exact ⟨right q, q, hR, hq2, Or.inl (left_right_eq_self q).symm⟩
  have hL2 : gc.fireCount (left q) = 2 := gc_fireCount_eq_two_of_not_ge_four gc (left q) hL
  have hR2 : gc.fireCount (right q) = 2 := gc_fireCount_eq_two_of_not_ge_four gc (right q) hR
  have hA4 : 4 ≤ gc.fireCount (anti4 q) := by
    by_contra hA
    have hA2 : gc.fireCount (anti4 q) = 2 :=
      gc_fireCount_eq_two_of_not_ge_four gc (anti4 q) hA
    have hall2 : ∀ p : Fin 4, gc.fireCount p = 2 := by
      intro p
      rcases Proc4_rel_cases q p with hp | hp | hp | hp
      · simpa [hp] using hq2
      · simpa [hp] using hR2
      · simpa [hp] using hA2
      · simpa [hp] using hL2
    exact hnot2 hall2
  have hrightAnti : left q = right (anti4 q) := by
    apply Fin.ext
    simp [right, right4, left, left4, anti4]
  exact ⟨anti4 q, left q, hA4, hL2, Or.inr hrightAnti⟩

private theorem exists_adjacent_high_low_zero_gap
    (gc : GoodCycle ⟨rs2222, f⟩)
    (hnot2 : ¬ ∀ p : Fin 4, gc.fireCount p = 2)
    (hnot4 : ¬ ∀ p : Fin 4, gc.fireCount p = 4) :
    ∃ p q : Fin 4, ∃ a b : Fin gc.configs.length,
      4 ≤ gc.fireCount p ∧
      gc.fireCount q = 2 ∧
      (q = left p ∨ q = right p) ∧
      a.val < b.val ∧
      gc.moverAt a = p ∧ gc.moverAt b = p ∧
      (∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p) ∧
      gc.intervalFireCount q a.val b.val = 0 := by
  obtain ⟨p, q, hp4, hq2, hqadj⟩ := exists_adjacent_high_low_fireCounts gc hnot2 hnot4
  obtain ⟨a, b, hab, ha, hb, hno, hgap0⟩ := exists_zero_gap_of_fireCount_two_vs_four gc p q hp4 hq2
  exact ⟨p, q, a, b, hp4, hq2, hqadj, hab, ha, hb, hno, hgap0⟩

private theorem gc_firings_isolated (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) :
    ∀ (a : Fin gc.configs.length),
      gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p := by
  have hfc : 2 ≤ gc.fireCount p := gc_fireCount_ge_two gc p
  rcases binary_isolated_firings_or_ec gc p (rs2222_m p) hfc with hec | hall | hiso
  · exact False.elim (entryConflict_impossible gc hec)
  · exfalso
    have hneq : right p ≠ p := by
      exact (show ∀ p : Fin 4, right p ≠ p from by decide) p
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair (right p)
    have hmov : gc.moverAt k = right p := by
      rw [← hj]
      exact (gc.moverAt_unique k j hpriv).symm
    exact hneq (by
      calc
        right p = gc.moverAt k := hmov.symm
        _ = p := hall k)
  · exact hiso

private theorem gc_next_mover_left_or_right (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Fin gc.configs.length) :
    gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) ∨
      gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k) := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · exact Or.inl hleft
  · exfalso
    exact gc_firings_isolated gc (gc.moverAt k) k rfl hself
  · exact Or.inr hright

private theorem gc_stepDir_ne_stay (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Fin gc.configs.length) :
    gc.stepDir k ≠ .stay := by
  intro hstay
  have hself := gc.eq_self_of_stepDir_eq_stay hstay
  exact gc_firings_isolated gc (gc.moverAt k) k rfl hself

private theorem gc_stepDir_cw_or_ccw (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Fin gc.configs.length) :
    gc.stepDir k = .cw ∨ gc.stepDir k = .ccw := by
  rcases gc.stepDir_cases k with hcw | hstay | hccw
  · exact Or.inl hcw
  · exact False.elim (gc_stepDir_ne_stay gc k hstay)
  · exact Or.inr hccw

private theorem gc_len_ge_8 (gc : GoodCycle ⟨rs2222, f⟩) :
    8 ≤ gc.configs.length := by
  have hsum := gc.sum_fireCount
  calc
    8 = ∑ p : Fin 4, 2 := by norm_num
    _ ≤ ∑ p : Fin 4, gc.fireCount p := by
      apply Finset.sum_le_sum
      intro p _
      exact gc_fireCount_ge_two gc p
    _ = gc.configs.length := hsum

private theorem gc_uniformCW_implies_isSweep (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) :
    gc.isSweep := by
  unfold GoodCycle.isSweep
  rw [gc.totalDisplacement_eq_length_of_uniformCW hCW]
  simpa [rs2222_n] using gc_len_ge_8 gc

private theorem gc_uniformCCW_implies_isSweep (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) :
    gc.isSweep := by
  unfold GoodCycle.isSweep
  rw [gc.totalDisplacement_eq_neg_length_of_uniformCCW hCCW, Int.natAbs_neg]
  simpa [rs2222_n] using gc_len_ge_8 gc

private theorem gc_not_sweep_not_uniformDirection (gc : GoodCycle ⟨rs2222, f⟩)
    (hns : ¬ gc.isSweep) :
    ¬ gc.uniformDirection := by
  intro hdir
  rcases hdir with hCW | hCCW
  · exact hns (gc_uniformCW_implies_isSweep gc hCW)
  · exact hns (gc_uniformCCW_implies_isSweep gc hCCW)

private theorem gc_not_sweep_has_cw_and_ccw (gc : GoodCycle ⟨rs2222, f⟩)
    (hns : ¬ gc.isSweep) :
    (∃ k : Fin gc.configs.length, gc.stepDir k = .cw) ∧
      (∃ k : Fin gc.configs.length, gc.stepDir k = .ccw) := by
  constructor
  · by_contra hnocw
    push_neg at hnocw
    have hccw : ∀ k : Fin gc.configs.length,
        gc.moverAt (nextIndex gc.configs k) = left (gc.moverAt k) := by
      intro k
      rcases gc_stepDir_cw_or_ccw gc k with hcw | hccw
      · exfalso
        exact hnocw k hcw
      · exact gc.eq_left_of_stepDir_eq_ccw hccw
    exact (gc_not_sweep_not_uniformDirection gc hns) (Or.inr hccw)
  · by_contra hnoccw
    push_neg at hnoccw
    have hcw : ∀ k : Fin gc.configs.length,
        gc.moverAt (nextIndex gc.configs k) = right (gc.moverAt k) := by
      intro k
      rcases gc_stepDir_cw_or_ccw gc k with hcw | hccw
      · exact gc.eq_right_of_stepDir_eq_cw hcw
      · exfalso
        exact hnoccw k hccw
    exact (gc_not_sweep_not_uniformDirection gc hns) (Or.inl hcw)

private theorem right_eq_right4 (j : Fin 4) : right j = right4 j := by
  apply Fin.ext
  simp [right, right4]

private theorem left_eq_left4 (j : Fin 4) : left j = left4 j := by
  apply Fin.ext
  simp [left, left4]

private theorem right_right_eq_anti4 (j : Fin 4) : right (right j) = anti4 j := by
  apply Fin.ext
  simp [right, anti4]

private theorem left_left_eq_anti4 (j : Fin 4) : left (left j) = anti4 j := by
  apply Fin.ext
  simp [left, anti4]
  omega

private theorem gc_nextIndex_eq_succ (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k + 1 < gc.configs.length) :
    nextIndex gc.configs ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
  apply Fin.ext
  simp [nextIndex, Nat.mod_eq_of_lt hk]

private theorem gcWordFrom_localNoStay (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + rem ≤ gc.configs.length),
      LocalNoStayWord4 (gcWordFrom gc k rem hkr)
  | k, 0, hkr => by
      simp [gcWordFrom, LocalNoStayWord4]
  | k, 1, hkr => by
      simp [gcWordFrom, LocalNoStayWord4]
  | k, rem + 2, hkr => by
      have hk : k < gc.configs.length := by omega
      have hk1 : k + 1 < gc.configs.length := by omega
      have hpair := gc_next_mover_left_or_right gc ⟨k, hk⟩
      rw [gc_nextIndex_eq_succ gc k hk1] at hpair
      rcases hpair with hleft | hright
      · refine ⟨Or.inl ?_, gcWordFrom_localNoStay gc (k + 1) (rem + 1) (by omega)⟩
        simpa [left_eq_left4] using hleft
      · refine ⟨Or.inr ?_, gcWordFrom_localNoStay gc (k + 1) (rem + 1) (by omega)⟩
        simpa [right_eq_right4] using hright

private theorem left4_val_parity_flip (j : Proc4) :
    (left4 j).val % 2 = 1 - (j.val % 2) := by
  fin_cases j <;> decide

private theorem right4_val_parity_flip (j : Proc4) :
    (right4 j).val % 2 = 1 - (j.val % 2) := by
  fin_cases j <;> decide

private theorem gc_mover_parity_add_eq
    (gc : GoodCycle ⟨rs2222, f⟩) (a : Nat) (ha : a < gc.configs.length) :
    ∀ (n : Nat) (hn : a + n < gc.configs.length),
      ((gc.moverAt ⟨a + n, hn⟩).val + (a + n)) % 2 =
        ((gc.moverAt ⟨a, ha⟩).val + a) % 2
  | 0, hn => by
      simp
  | n + 1, hn => by
      have hn' : a + n < gc.configs.length := by omega
      have hsucc :
          ((gc.moverAt ⟨a + (n + 1), hn⟩).val + (a + (n + 1))) % 2 =
            ((gc.moverAt ⟨a + n, hn'⟩).val + (a + n)) % 2 := by
        have hpair := gc_next_mover_left_or_right_early gc ⟨a + n, hn'⟩
        rw [gc_nextIndex_eq_succ_pre gc (a + n) hn] at hpair
        rcases hpair with hleft | hright
        · have hleft' :
              gc.moverAt ⟨a + (n + 1), hn⟩ = left (gc.moverAt ⟨a + n, hn'⟩) := by
            simpa [Nat.add_assoc] using hleft
          rw [hleft']
          rw [left_eq_left4]
          have hflip := left4_val_parity_flip (gc.moverAt ⟨a + n, hn'⟩)
          omega
        · have hright' :
              gc.moverAt ⟨a + (n + 1), hn⟩ = right (gc.moverAt ⟨a + n, hn'⟩) := by
            simpa [Nat.add_assoc] using hright
          rw [hright']
          rw [right_eq_right4]
          have hflip := right4_val_parity_flip (gc.moverAt ⟨a + n, hn'⟩)
          omega
      rw [hsucc, gc_mover_parity_add_eq gc a ha n hn']

private theorem gc_same_mover_gap_even
    (gc : GoodCycle ⟨rs2222, f⟩) (p : Fin 4) (a b : Fin gc.configs.length)
    (hab : a.val < b.val)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p) :
    Even (b.val - a.val) := by
  have hpar :=
    gc_mover_parity_add_eq gc a.val a.isLt (b.val - a.val) (by omega)
  have hpar' :
      ((gc.moverAt b).val + b.val) % 2 = ((gc.moverAt a).val + a.val) % 2 := by
    have hsum : a.val + (b.val - a.val) = b.val := by omega
    simpa [ha, hb, hsum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpar
  refine ⟨((b.val - a.val) / 2), ?_⟩
  omega

private theorem sum_prefixFireCount_eq
    (gc : GoodCycle ⟨rs2222, f⟩) (m : Nat) (hm : m ≤ gc.configs.length) :
    ∑ q : Fin 4, gc.prefixFireCount q m = m := by
  classical
  unfold GoodCycle.prefixFireCount
  rw [Finset.sum_comm]
  calc
    ∑ k ∈ Finset.range m, ∑ q : Fin 4, gc.fireIndicator q k
        = ∑ _k ∈ Finset.range m, 1 := by
            apply Finset.sum_congr rfl
            intro k hk
            exact gc.sum_fireIndicator_eq_one (Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) hm)
    _ = m := by
          simp

private theorem sum_intervalFireCount_eq
    (gc : GoodCycle ⟨rs2222, f⟩) (a b : Nat) (hab : a ≤ b) (hb : b ≤ gc.configs.length) :
    ∑ q : Fin 4, gc.intervalFireCount q a b = b - a := by
  have hmono : ∀ q : Fin 4, gc.prefixFireCount q a ≤ gc.prefixFireCount q b := by
    intro q
    unfold GoodCycle.prefixFireCount
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have hsum_b := sum_prefixFireCount_eq gc b hb
  have hsum_a := sum_prefixFireCount_eq gc a (by omega)
  have hmain :
      ∑ q : Fin 4, gc.intervalFireCount q a b =
        (∑ q : Fin 4, gc.prefixFireCount q b) -
          (∑ q : Fin 4, gc.prefixFireCount q a) := by
    simp only [GoodCycle.intervalFireCount]
    suffices
        ∑ q : Fin 4, (gc.prefixFireCount q b - gc.prefixFireCount q a) +
            ∑ q : Fin 4, gc.prefixFireCount q a =
          ∑ q : Fin 4, gc.prefixFireCount q b by
      have hle_sum :
          ∑ q : Fin 4, gc.prefixFireCount q a ≤
            ∑ q : Fin 4, gc.prefixFireCount q b :=
        Finset.sum_le_sum (fun q _ => hmono q)
      omega
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    have := hmono q
    omega
  rw [hmain, hsum_b, hsum_a]

private theorem gc_fireCount_pair_le_length
    (gc : GoodCycle ⟨rs2222, f⟩) (p q : Fin 4) (hpq : p ≠ q) :
    gc.fireCount p + gc.fireCount q ≤ gc.configs.length := by
  have hsum :
      (Finset.univ.sum fun r : Fin 4 => gc.fireCount r) = gc.configs.length := by
    simpa using gc.sum_fireCount
  have hsplit1 :
      (Finset.univ.sum fun r : Fin 4 => gc.fireCount r) =
        (Finset.sum (Finset.univ.erase p) fun r : Fin 4 => gc.fireCount r) + gc.fireCount p := by
    simpa using
      (Finset.sum_erase_add (s := Finset.univ) (a := p)
        (f := fun r : Fin 4 => gc.fireCount r) (by simp)).symm
  have hqmem : q ∈ Finset.univ.erase p := by
    exact Finset.mem_erase.mpr ⟨by
      intro h
      exact hpq h.symm, by simp⟩
  have hsplit2 :
      (Finset.sum (Finset.univ.erase p) fun r : Fin 4 => gc.fireCount r) =
        (Finset.sum ((Finset.univ.erase p).erase q) fun r : Fin 4 => gc.fireCount r) + gc.fireCount q := by
    simpa using
      (Finset.sum_erase_add (s := Finset.univ.erase p) (a := q)
        (f := fun r : Fin 4 => gc.fireCount r) hqmem).symm
  rw [hsplit1, hsplit2] at hsum
  have hnonneg :
      0 ≤ Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.fireCount r) := Nat.zero_le _
  omega

private theorem zero_gap_span_le_twelve
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hp4 : 4 ≤ gc.fireCount p) (hq2 : gc.fireCount q = 2)
    (hab : a.val < b.val)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0) :
    b.val ≤ a.val + 12 := by
  have hpq : p ≠ q := by
    intro hpq
    rw [hpq] at hp4
    omega
  have hseg_p : gc.intervalFireCount p a.val (b.val + 1) = 2 := by
    have hleft : gc.intervalFireCount p a.val (a.val + 1) = 1 := by
      rw [gc_intervalFireCount_single gc p a.isLt]
      simp [ha]
    have hmid0 : gc.intervalFireCount p (a.val + 1) b.val = 0 := by
      apply intervalFireCount_eq_zero_of_noFire gc p (by omega) (Nat.le_of_lt b.isLt)
      intro k hk1 hk2
      exact hno k (by omega) hk2
    have hright : gc.intervalFireCount p b.val (b.val + 1) = 1 := by
      rw [gc_intervalFireCount_single gc p b.isLt]
      simp [hb]
    calc
      gc.intervalFireCount p a.val (b.val + 1)
          = gc.intervalFireCount p a.val (a.val + 1) +
              gc.intervalFireCount p (a.val + 1) (b.val + 1) := by
                exact gc_intervalFireCount_split gc p (by omega) (by omega)
      _ = 1 + gc.intervalFireCount p (a.val + 1) (b.val + 1) := by
            rw [hleft]
      _ = 1 + (gc.intervalFireCount p (a.val + 1) b.val +
              gc.intervalFireCount p b.val (b.val + 1)) := by
            rw [gc_intervalFireCount_split gc p (a := a.val + 1) (b := b.val) (c := b.val + 1)
              (by omega) (by omega)]
      _ = 2 := by
            rw [hmid0, hright]
  have hseg_q : gc.intervalFireCount q a.val (b.val + 1) = 0 := by
    have hb_ne : gc.moverAt b ≠ q := by
      rw [hb]
      exact hpq
    calc
      gc.intervalFireCount q a.val (b.val + 1)
          = gc.intervalFireCount q a.val b.val +
              gc.intervalFireCount q b.val (b.val + 1) := by
                exact gc_intervalFireCount_split gc q (by omega) (by omega)
      _ = 0 + gc.intervalFireCount q b.val (b.val + 1) := by
            rw [hgap0]
      _ = 0 := by
            rw [gc_intervalFireCount_single gc q b.isLt]
            simp [hb_ne]
  let others : Finset (Fin 4) := (Finset.univ.erase p).erase q
  have hseg_sum :
      (Finset.univ.sum fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) = b.val + 1 - a.val :=
    sum_intervalFireCount_eq gc a.val (b.val + 1) (by omega) (by omega)
  have hseg_decomp :
      (Finset.univ.sum fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) =
        gc.intervalFireCount p a.val (b.val + 1) +
          (gc.intervalFireCount q a.val (b.val + 1) +
            Finset.sum others (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1))) := by
    unfold others
    have hqmem : q ∈ Finset.univ.erase p := by
      exact Finset.mem_erase.mpr ⟨by
        intro h
        exact hpq h.symm, by simp⟩
    have hsplit1 :
        Finset.univ.sum (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) =
          Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) +
            gc.intervalFireCount p a.val (b.val + 1) := by
      simpa using
        (Finset.sum_erase_add (s := Finset.univ) (a := p)
          (f := fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) (by simp)).symm
    have hsplit2 :
        Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) =
          Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) +
            gc.intervalFireCount q a.val (b.val + 1) := by
      simpa using
        (Finset.sum_erase_add (s := Finset.univ.erase p) (a := q)
          (f := fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) hqmem).symm
    calc
      Finset.univ.sum (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1))
          = Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) +
              gc.intervalFireCount p a.val (b.val + 1) := hsplit1
      _ = gc.intervalFireCount p a.val (b.val + 1) +
            Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) := by
              omega
      _ = gc.intervalFireCount p a.val (b.val + 1) +
            (Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1)) +
              gc.intervalFireCount q a.val (b.val + 1)) := by
              rw [hsplit2]
      _ = gc.intervalFireCount p a.val (b.val + 1) +
            (gc.intervalFireCount q a.val (b.val + 1) +
              Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1))) := by
              omega
      _ = _ := by
            simp [others]
  have hseg_others :
      (Finset.sum others (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1))) = b.val + 1 - a.val - 2 := by
    rw [hseg_decomp, hseg_p, hseg_q] at hseg_sum
    omega
  have hothers_le :
      (Finset.sum others (fun r : Fin 4 => gc.intervalFireCount r a.val (b.val + 1))) ≤
        (Finset.sum others (fun r : Fin 4 => gc.fireCount r)) := by
    apply Finset.sum_le_sum
    intro r hr
    exact gc_intervalFireCount_le_fireCount gc r (by omega) (by omega)
  have hfull_others :
      (Finset.sum others (fun r : Fin 4 => gc.fireCount r)) =
        gc.configs.length - (gc.fireCount p + gc.fireCount q) := by
    unfold others
    have hqmem : q ∈ Finset.univ.erase p := by
      exact Finset.mem_erase.mpr ⟨by
        intro h
        exact hpq h.symm, by simp⟩
    have hsum1 :
        Finset.univ.sum (fun r : Fin 4 => gc.fireCount r) =
          Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.fireCount r) + gc.fireCount p := by
      simpa using
        (Finset.sum_erase_add (s := Finset.univ) (a := p)
          (f := fun r : Fin 4 => gc.fireCount r) (by simp)).symm
    have hsum2 :
        Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.fireCount r) =
          Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.fireCount r) + gc.fireCount q := by
      simpa using
        (Finset.sum_erase_add (s := Finset.univ.erase p) (a := q)
          (f := fun r : Fin 4 => gc.fireCount r) hqmem).symm
    have hsum :
        gc.configs.length =
          gc.fireCount p + gc.fireCount q +
            Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.fireCount r) := by
      calc
        gc.configs.length = Finset.univ.sum (fun r : Fin 4 => gc.fireCount r) := by simpa using gc.sum_fireCount.symm
        _ = Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.fireCount r) + gc.fireCount p := hsum1
        _ = gc.fireCount p + Finset.sum (Finset.univ.erase p) (fun r : Fin 4 => gc.fireCount r) := by
              omega
        _ = gc.fireCount p + (Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.fireCount r) + gc.fireCount q) := by
              rw [hsum2]
        _ = gc.fireCount p + gc.fireCount q +
              Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.fireCount r) := by
              omega
    have hnonneg : 0 ≤ Finset.sum ((Finset.univ.erase p).erase q) (fun r : Fin 4 => gc.fireCount r) :=
      Nat.zero_le _
    omega
  have hother_bound :
      b.val + 1 - a.val - 2 ≤ gc.configs.length - (gc.fireCount p + gc.fireCount q) := by
    rw [← hseg_others, ← hfull_others]
    exact hothers_le
  have hspan :
      b.val + 1 - a.val ≤ gc.configs.length - (gc.fireCount p + gc.fireCount q) + 2 := by
    omega
  have hlen16 : gc.configs.length ≤ 16 := gc_len_le_16 gc
  omega

private theorem zero_gap_len4_shape_left
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen4 : b.val = a.val + 4) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = right p := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha2lt : a.val + 2 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h3neqq :
      gc.moverAt ⟨a.val + 3, ha3lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha3lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc a
    rw [gc_nextIndex_eq_succ gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h1neqq (by simpa [hq] using hleft)
    · exact hright
  have h2 : gc.moverAt ⟨a.val + 2, ha2lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 1, ha1lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 1) ha2lt, h1] at hpair
    rcases hpair with hleft | hright
    · exfalso
      have ha2ltb : a.val + 2 < b.val := by omega
      have ha_lt_a2 : a.val < a.val + 2 := by omega
      exact hno ⟨a.val + 2, ha2lt⟩ ha_lt_a2 ha2ltb
        (by simpa [left_right_eq_self] using hleft)
    · simpa [right_right_eq_anti4] using hright
  have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 2, ha2lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 2) ha3lt, h2] at hpair
    rcases hpair with hleft | hright
    · simpa [left_eq_left4, left4_anti4, right_eq_right4] using hleft
    · exfalso
      exact h3neqq (by simpa [hq, right_eq_right4, right4_anti4] using hright)
  exact ⟨h1, h2, h3⟩

private theorem zero_gap_len4_shape_right
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen4 : b.val = a.val + 4) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = left p := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha2lt : a.val + 2 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h3neqq :
      gc.moverAt ⟨a.val + 3, ha3lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha3lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc a
    rw [gc_nextIndex_eq_succ gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exact hleft
    · exfalso
      exact h1neqq (by simpa [hq] using hright)
  have h2 : gc.moverAt ⟨a.val + 2, ha2lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 1, ha1lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 1) ha2lt, h1] at hpair
    rcases hpair with hleft | hright
    · simpa [left_left_eq_anti4] using hleft
    · exfalso
      have ha2ltb : a.val + 2 < b.val := by omega
      have ha_lt_a2 : a.val < a.val + 2 := by omega
      exact hno ⟨a.val + 2, ha2lt⟩ ha_lt_a2 ha2ltb
        (by simpa [right_left_eq_self] using hright)
  have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 2, ha2lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 2) ha3lt, h2] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h3neqq (by simpa [hq, left_eq_left4, left4_anti4] using hleft)
    · simpa [right_eq_right4, right4_anti4, left_eq_left4] using hright
  exact ⟨h1, h2, h3⟩

private theorem zero_gap_len4_false_left
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen4 : b.val = a.val + 4) : False := by
  obtain ⟨h1, h2, h3⟩ := zero_gap_len4_shape_left gc p q a b hq ha hb hno hgap0 hlen4
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, right p, anti4 p, right p, p] : Word4) ++
          gcWordFrom gc (a.val + 5) (gc.configs.length - (a.val + 5)) (by omega) := by
    let rem := gc.configs.length - (a.val + 5)
    have hb4 : (⟨a.val + 4, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen4.symm
    have hlenRem : gc.configs.length - a.val = rem + 5 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen4, ha, h1, h2, h3, hb4, hb] using
      (gcWordFrom_prefix_five gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_abcb_right_anti_right_self p
        (gcWordFrom gc (a.val + 5) (gc.configs.length - (a.val + 5)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_len4_false_right
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen4 : b.val = a.val + 4) : False := by
  obtain ⟨h1, h2, h3⟩ := zero_gap_len4_shape_right gc p q a b hq ha hb hno hgap0 hlen4
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, left p, anti4 p, left p, p] : Word4) ++
          gcWordFrom gc (a.val + 5) (gc.configs.length - (a.val + 5)) (by omega) := by
    let rem := gc.configs.length - (a.val + 5)
    have hb4 : (⟨a.val + 4, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen4.symm
    have hlenRem : gc.configs.length - a.val = rem + 5 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen4, ha, h1, h2, h3, hb4, hb] using
      (gcWordFrom_prefix_five gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_abcb_left_anti_left_self p
        (gcWordFrom gc (a.val + 5) (gc.configs.length - (a.val + 5)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_shape_left_up_to5
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 6 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = right p := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha2lt : a.val + 2 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h3neqq :
      gc.moverAt ⟨a.val + 3, ha3lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha3lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc a
    rw [gc_nextIndex_eq_succ gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h1neqq (by simpa [hq] using hleft)
    · exact hright
  have h2 : gc.moverAt ⟨a.val + 2, ha2lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 1, ha1lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 1) ha2lt, h1] at hpair
    rcases hpair with hleft | hright
    · exfalso
      have ha2ltb : a.val + 2 < b.val := by omega
      have ha_lt_a2 : a.val < a.val + 2 := by omega
      exact hno ⟨a.val + 2, ha2lt⟩ ha_lt_a2 ha2ltb
        (by simpa [left_right_eq_self] using hleft)
    · simpa [right_right_eq_anti4] using hright
  have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 2, ha2lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 2) ha3lt, h2] at hpair
    rcases hpair with hleft | hright
    · simpa [left_eq_left4, left4_anti4, right_eq_right4] using hleft
    · exfalso
      exact h3neqq (by simpa [hq, right_eq_right4, right4_anti4] using hright)
  have ha4lt : a.val + 4 < gc.configs.length := by omega
  have ha5lt : a.val + 5 < gc.configs.length := by omega
  have h5neqq :
      gc.moverAt ⟨a.val + 5, ha5lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha5lt
  have h4 : gc.moverAt ⟨a.val + 4, ha4lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 3, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 3) ha4lt, h3] at hpair
    rcases hpair with hleft | hright
    · exfalso
      have ha4ltb : a.val + 4 < b.val := by omega
      have ha_lt_a4 : a.val < a.val + 4 := by omega
      exact hno ⟨a.val + 4, ha4lt⟩ ha_lt_a4 ha4ltb
        (by simpa [left_right_eq_self] using hleft)
    · simpa [right_right_eq_anti4] using hright
  have h5 : gc.moverAt ⟨a.val + 5, ha5lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 4, ha4lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 4) ha5lt, h4] at hpair
    rcases hpair with hleft | hright
    · simpa [left_eq_left4, left4_anti4, right_eq_right4] using hleft
    · exfalso
      exact h5neqq (by simpa [hq, right_eq_right4, right4_anti4] using hright)
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem zero_gap_shape_right_up_to5
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 6 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = left p := by
  have ha1lt : a.val + 1 < gc.configs.length := by omega
  have ha2lt : a.val + 2 < gc.configs.length := by omega
  have ha3lt : a.val + 3 < gc.configs.length := by omega
  have h1neqq :
      gc.moverAt ⟨a.val + 1, ha1lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha1lt
  have h3neqq :
      gc.moverAt ⟨a.val + 3, ha3lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha3lt
  have h1 : gc.moverAt ⟨a.val + 1, ha1lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc a
    rw [gc_nextIndex_eq_succ gc a.val ha1lt, ha] at hpair
    rcases hpair with hleft | hright
    · exact hleft
    · exfalso
      exact h1neqq (by simpa [hq] using hright)
  have h2 : gc.moverAt ⟨a.val + 2, ha2lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 1, ha1lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 1) ha2lt, h1] at hpair
    rcases hpair with hleft | hright
    · simpa [left_left_eq_anti4] using hleft
    · exfalso
      have ha2ltb : a.val + 2 < b.val := by omega
      have ha_lt_a2 : a.val < a.val + 2 := by omega
      exact hno ⟨a.val + 2, ha2lt⟩ ha_lt_a2 ha2ltb
        (by simpa [right_left_eq_self] using hright)
  have h3 : gc.moverAt ⟨a.val + 3, ha3lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 2, ha2lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 2) ha3lt, h2] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h3neqq (by simpa [hq, left_eq_left4, left4_anti4] using hleft)
    · simpa [right_eq_right4, right4_anti4, left_eq_left4] using hright
  have ha4lt : a.val + 4 < gc.configs.length := by omega
  have ha5lt : a.val + 5 < gc.configs.length := by omega
  have h5neqq :
      gc.moverAt ⟨a.val + 5, ha5lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha5lt
  have h4 : gc.moverAt ⟨a.val + 4, ha4lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 3, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 3) ha4lt, h3] at hpair
    rcases hpair with hleft | hright
    · simpa [left_left_eq_anti4] using hleft
    · exfalso
      have ha4ltb : a.val + 4 < b.val := by omega
      have ha_lt_a4 : a.val < a.val + 4 := by omega
      exact hno ⟨a.val + 4, ha4lt⟩ ha_lt_a4 ha4ltb
        (by simpa [right_left_eq_self] using hright)
  have h5 : gc.moverAt ⟨a.val + 5, ha5lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 4, ha4lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 4) ha5lt, h4] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h5neqq (by simpa [hq, left_eq_left4, left4_anti4] using hleft)
    · simpa [right_eq_right4, right4_anti4, left_eq_left4] using hright
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem zero_gap_len6_false_left
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen6 : b.val = a.val + 6) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    zero_gap_shape_left_up_to5 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, right p, anti4 p, right p, anti4 p, right p, p] : Word4) ++
          gcWordFrom gc (a.val + 7) (gc.configs.length - (a.val + 7)) (by omega) := by
    let rem := gc.configs.length - (a.val + 7)
    have hb6 : (⟨a.val + 6, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen6.symm
    have hlenRem : gc.configs.length - a.val = rem + 7 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen6, ha, h1, h2, h3, h4, h5, hb6, hb] using
      (gcWordFrom_prefix_seven gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_right_long p
        (gcWordFrom gc (a.val + 7) (gc.configs.length - (a.val + 7)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_len6_false_right
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen6 : b.val = a.val + 6) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    zero_gap_shape_right_up_to5 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, left p, anti4 p, left p, anti4 p, left p, p] : Word4) ++
          gcWordFrom gc (a.val + 7) (gc.configs.length - (a.val + 7)) (by omega) := by
    let rem := gc.configs.length - (a.val + 7)
    have hb6 : (⟨a.val + 6, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen6.symm
    have hlenRem : gc.configs.length - a.val = rem + 7 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen6, ha, h1, h2, h3, h4, h5, hb6, hb] using
      (gcWordFrom_prefix_seven gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_left_long p
        (gcWordFrom gc (a.val + 7) (gc.configs.length - (a.val + 7)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_shape_left_up_to7
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 8 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 6, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 7, by omega⟩ = right p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    zero_gap_shape_left_up_to5 gc p q a b hq ha hno hgap0 (by omega)
  have ha6lt : a.val + 6 < gc.configs.length := by omega
  have ha7lt : a.val + 7 < gc.configs.length := by omega
  have h7neqq :
      gc.moverAt ⟨a.val + 7, ha7lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha7lt
  have h6 : gc.moverAt ⟨a.val + 6, ha6lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 5, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 5) ha6lt, h5] at hpair
    rcases hpair with hleft | hright
    · exfalso
      have ha6ltb : a.val + 6 < b.val := by omega
      have ha_lt_a6 : a.val < a.val + 6 := by omega
      exact hno ⟨a.val + 6, ha6lt⟩ ha_lt_a6 ha6ltb
        (by simpa [left_right_eq_self] using hleft)
    · simpa [right_right_eq_anti4] using hright
  have h7 : gc.moverAt ⟨a.val + 7, ha7lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 6, ha6lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 6) ha7lt, h6] at hpair
    rcases hpair with hleft | hright
    · simpa [left_eq_left4, left4_anti4, right_eq_right4] using hleft
    · exfalso
      exact h7neqq (by simpa [hq, right_eq_right4, right4_anti4] using hright)
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private theorem zero_gap_shape_right_up_to7
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 8 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 6, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 7, by omega⟩ = left p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    zero_gap_shape_right_up_to5 gc p q a b hq ha hno hgap0 (by omega)
  have ha6lt : a.val + 6 < gc.configs.length := by omega
  have ha7lt : a.val + 7 < gc.configs.length := by omega
  have h7neqq :
      gc.moverAt ⟨a.val + 7, ha7lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha7lt
  have h6 : gc.moverAt ⟨a.val + 6, ha6lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 5, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 5) ha6lt, h5] at hpair
    rcases hpair with hleft | hright
    · simpa [left_left_eq_anti4] using hleft
    · exfalso
      have ha6ltb : a.val + 6 < b.val := by omega
      have ha_lt_a6 : a.val < a.val + 6 := by omega
      exact hno ⟨a.val + 6, ha6lt⟩ ha_lt_a6 ha6ltb
        (by simpa [right_left_eq_self] using hright)
  have h7 : gc.moverAt ⟨a.val + 7, ha7lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 6, ha6lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 6) ha7lt, h6] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h7neqq (by simpa [hq, left_eq_left4, left4_anti4] using hleft)
    · simpa [right_eq_right4, right4_anti4, left_eq_left4] using hright
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private theorem zero_gap_len8_false_left
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen8 : b.val = a.val + 8) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    zero_gap_shape_left_up_to7 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, right p, anti4 p, right p, anti4 p, right p, anti4 p, right p, p] : Word4) ++
          gcWordFrom gc (a.val + 9) (gc.configs.length - (a.val + 9)) (by omega) := by
    let rem := gc.configs.length - (a.val + 9)
    have hb8 : (⟨a.val + 8, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen8.symm
    have hlenRem : gc.configs.length - a.val = rem + 9 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen8, ha, h1, h2, h3, h4, h5, h6, h7, hb8, hb] using
      (gcWordFrom_prefix_nine gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_right_longer p
        (gcWordFrom gc (a.val + 9) (gc.configs.length - (a.val + 9)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_len8_false_right
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen8 : b.val = a.val + 8) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    zero_gap_shape_right_up_to7 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, left p, anti4 p, left p, anti4 p, left p, anti4 p, left p, p] : Word4) ++
          gcWordFrom gc (a.val + 9) (gc.configs.length - (a.val + 9)) (by omega) := by
    let rem := gc.configs.length - (a.val + 9)
    have hb8 : (⟨a.val + 8, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen8.symm
    have hlenRem : gc.configs.length - a.val = rem + 9 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen8, ha, h1, h2, h3, h4, h5, h6, h7, hb8, hb] using
      (gcWordFrom_prefix_nine gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_left_longer p
        (gcWordFrom gc (a.val + 9) (gc.configs.length - (a.val + 9)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_shape_left_up_to9
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 10 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 6, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 7, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 8, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 9, by omega⟩ = right p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    zero_gap_shape_left_up_to7 gc p q a b hq ha hno hgap0 (by omega)
  have ha8lt : a.val + 8 < gc.configs.length := by omega
  have ha9lt : a.val + 9 < gc.configs.length := by omega
  have h9neqq :
      gc.moverAt ⟨a.val + 9, ha9lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha9lt
  have h8 : gc.moverAt ⟨a.val + 8, ha8lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 7, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 7) ha8lt, h7] at hpair
    rcases hpair with hleft | hright
    · exfalso
      have ha8ltb : a.val + 8 < b.val := by omega
      have ha_lt_a8 : a.val < a.val + 8 := by omega
      exact hno ⟨a.val + 8, ha8lt⟩ ha_lt_a8 ha8ltb
        (by simpa [left_right_eq_self] using hleft)
    · simpa [right_right_eq_anti4] using hright
  have h9 : gc.moverAt ⟨a.val + 9, ha9lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 8, ha8lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 8) ha9lt, h8] at hpair
    rcases hpair with hleft | hright
    · simpa [left_eq_left4, left4_anti4, right_eq_right4] using hleft
    · exfalso
      exact h9neqq (by simpa [hq, right_eq_right4, right4_anti4] using hright)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private theorem zero_gap_shape_left_up_to11
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 12 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 6, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 7, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 8, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 9, by omega⟩ = right p ∧
      gc.moverAt ⟨a.val + 10, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 11, by omega⟩ = right p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    zero_gap_shape_left_up_to9 gc p q a b hq ha hno hgap0 (by omega)
  have ha10lt : a.val + 10 < gc.configs.length := by omega
  have ha11lt : a.val + 11 < gc.configs.length := by omega
  have h11neqq :
      gc.moverAt ⟨a.val + 11, ha11lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha11lt
  have h10 : gc.moverAt ⟨a.val + 10, ha10lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 9, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 9) ha10lt, h9] at hpair
    rcases hpair with hleft | hright
    · exfalso
      have ha10ltb : a.val + 10 < b.val := by omega
      have ha_lt_a10 : a.val < a.val + 10 := by omega
      exact hno ⟨a.val + 10, ha10lt⟩ ha_lt_a10 ha10ltb
        (by simpa [left_right_eq_self] using hleft)
    · simpa [right_right_eq_anti4] using hright
  have h11 : gc.moverAt ⟨a.val + 11, ha11lt⟩ = right p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 10, ha10lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 10) ha11lt, h10] at hpair
    rcases hpair with hleft | hright
    · simpa [left_eq_left4, left4_anti4, right_eq_right4] using hleft
    · exfalso
      exact h11neqq (by simpa [hq, right_eq_right4, right4_anti4] using hright)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

private theorem zero_gap_shape_right_up_to9
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 10 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 6, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 7, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 8, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 9, by omega⟩ = left p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    zero_gap_shape_right_up_to7 gc p q a b hq ha hno hgap0 (by omega)
  have ha8lt : a.val + 8 < gc.configs.length := by omega
  have ha9lt : a.val + 9 < gc.configs.length := by omega
  have h9neqq :
      gc.moverAt ⟨a.val + 9, ha9lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha9lt
  have h8 : gc.moverAt ⟨a.val + 8, ha8lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 7, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 7) ha8lt, h7] at hpair
    rcases hpair with hleft | hright
    · simpa [left_left_eq_anti4] using hleft
    · exfalso
      have ha8ltb : a.val + 8 < b.val := by omega
      have ha_lt_a8 : a.val < a.val + 8 := by omega
      exact hno ⟨a.val + 8, ha8lt⟩ ha_lt_a8 ha8ltb
        (by simpa [right_left_eq_self] using hright)
  have h9 : gc.moverAt ⟨a.val + 9, ha9lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 8, ha8lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 8) ha9lt, h8] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h9neqq (by simpa [hq, left_eq_left4, left4_anti4] using hleft)
    · simpa [right_eq_right4, right4_anti4, left_eq_left4] using hright
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private theorem zero_gap_shape_right_up_to11
    (gc : GoodCycle ⟨rs2222, f⟩)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hspan : a.val + 12 ≤ b.val) :
    gc.moverAt ⟨a.val + 1, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 2, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 3, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 4, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 5, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 6, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 7, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 8, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 9, by omega⟩ = left p ∧
      gc.moverAt ⟨a.val + 10, by omega⟩ = anti4 p ∧
      gc.moverAt ⟨a.val + 11, by omega⟩ = left p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    zero_gap_shape_right_up_to9 gc p q a b hq ha hno hgap0 (by omega)
  have ha10lt : a.val + 10 < gc.configs.length := by omega
  have ha11lt : a.val + 11 < gc.configs.length := by omega
  have h11neqq :
      gc.moverAt ⟨a.val + 11, ha11lt⟩ ≠ q :=
    gc_intervalFireCount_eq_zero_not_mover gc q hgap0 (by omega) (by omega) ha11lt
  have h10 : gc.moverAt ⟨a.val + 10, ha10lt⟩ = anti4 p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 9, by omega⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 9) ha10lt, h9] at hpair
    rcases hpair with hleft | hright
    · simpa [left_left_eq_anti4] using hleft
    · exfalso
      have ha10ltb : a.val + 10 < b.val := by omega
      have ha_lt_a10 : a.val < a.val + 10 := by omega
      exact hno ⟨a.val + 10, ha10lt⟩ ha_lt_a10 ha10ltb
        (by simpa [right_left_eq_self] using hright)
  have h11 : gc.moverAt ⟨a.val + 11, ha11lt⟩ = left p := by
    have hpair := gc_next_mover_left_or_right gc ⟨a.val + 10, ha10lt⟩
    rw [gc_nextIndex_eq_succ gc (a.val + 10) ha11lt, h10] at hpair
    rcases hpair with hleft | hright
    · exfalso
      exact h11neqq (by simpa [hq, left_eq_left4, left4_anti4] using hleft)
    · simpa [right_eq_right4, right4_anti4, left_eq_left4] using hright
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

private theorem zero_gap_len10_false_left
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen10 : b.val = a.val + 10) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    zero_gap_shape_left_up_to9 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, right p, anti4 p, right p, anti4 p, right p, anti4 p, right p, anti4 p, right p, p] : Word4) ++
          gcWordFrom gc (a.val + 11) (gc.configs.length - (a.val + 11)) (by omega) := by
    let rem := gc.configs.length - (a.val + 11)
    have hb10 : (⟨a.val + 10, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen10.symm
    have hlenRem : gc.configs.length - a.val = rem + 11 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen10, ha, h1, h2, h3, h4, h5, h6, h7, h8, h9, hb10, hb] using
      (gcWordFrom_prefix_eleven gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_right_longest p
        (gcWordFrom gc (a.val + 11) (gc.configs.length - (a.val + 11)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_len10_false_right
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen10 : b.val = a.val + 10) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    zero_gap_shape_right_up_to9 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, left p, anti4 p, left p, anti4 p, left p, anti4 p, left p, anti4 p, left p, p] : Word4) ++
          gcWordFrom gc (a.val + 11) (gc.configs.length - (a.val + 11)) (by omega) := by
    let rem := gc.configs.length - (a.val + 11)
    have hb10 : (⟨a.val + 10, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen10.symm
    have hlenRem : gc.configs.length - a.val = rem + 11 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen10, ha, h1, h2, h3, h4, h5, h6, h7, h8, h9, hb10, hb] using
      (gcWordFrom_prefix_eleven gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_left_longest p
        (gcWordFrom gc (a.val + 11) (gc.configs.length - (a.val + 11)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_len12_false_left
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = left p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen12 : b.val = a.val + 12) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    zero_gap_shape_left_up_to11 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, right p, anti4 p, right p, anti4 p, right p, anti4 p, right p, anti4 p, right p, anti4 p, right p, p] : Word4) ++
          gcWordFrom gc (a.val + 13) (gc.configs.length - (a.val + 13)) (by omega) := by
    let rem := gc.configs.length - (a.val + 13)
    have hb12 : (⟨a.val + 12, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen12.symm
    have hlenRem : gc.configs.length - a.val = rem + 13 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen12, ha, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb12, hb] using
      (gcWordFrom_prefix_thirteen gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_right_len12 p
        (gcWordFrom gc (a.val + 13) (gc.configs.length - (a.val + 13)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem zero_gap_len12_false_right
    (gc : GoodCycle ⟨rs2222, f⟩)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (p q : Fin 4) (a b : Fin gc.configs.length)
    (hq : q = right p)
    (ha : gc.moverAt a = p) (hb : gc.moverAt b = p)
    (hno : ∀ k : Fin gc.configs.length, a.val < k.val → k.val < b.val → gc.moverAt k ≠ p)
    (hgap0 : gc.intervalFireCount q a.val b.val = 0)
    (hlen12 : b.val = a.val + 12) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    zero_gap_shape_right_up_to11 gc p q a b hq ha hno hgap0 (by omega)
  have hsplit :
      gcWordFrom gc 0 gc.configs.length (by omega) =
        gcWordFrom gc 0 a.val (by omega) ++
          gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (gcWordFrom_append gc 0 a.val (gc.configs.length - a.val) (by omega))
  have hsuf :
      gcWordFrom gc a.val (gc.configs.length - a.val) (by omega) =
        ([p, left p, anti4 p, left p, anti4 p, left p, anti4 p, left p, anti4 p, left p, anti4 p, left p, p] : Word4) ++
          gcWordFrom gc (a.val + 13) (gc.configs.length - (a.val + 13)) (by omega) := by
    let rem := gc.configs.length - (a.val + 13)
    have hb12 : (⟨a.val + 12, by omega⟩ : Fin gc.configs.length) = b := by
      apply Fin.ext
      exact hlen12.symm
    have hlenRem : gc.configs.length - a.val = rem + 13 := by
      unfold rem
      omega
    simpa [rem, hlenRem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hlen12, ha, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb12, hb] using
      (gcWordFrom_prefix_thirteen gc a.val rem (by omega))
  have hsigma :
      sigConflict4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
    rw [hsplit, hsuf]
    apply sigConflict4_append_suffix
    simpa [List.cons_append] using
      sigConflict4_oneSided_left_len12 p
        (gcWordFrom gc (a.val + 13) (gc.configs.length - (a.val + 13)) (by omega))
  have htfTrue :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 gc.configs.length (by omega))) = true :=
    sigConflict4_imp_isTFBlocked (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) hsigma
  have htfTrue' : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
    simpa [gcPathN_eq_pathFromWord4 gc] using htfTrue
  rw [htf] at htfTrue'
  contradiction

private theorem gcWordFrom_simple (gc : GoodCycle ⟨rs2222, f⟩) :
    SimpleWord4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
  intro t u htu hu hEq
  have hword_len :
      (gcWordFrom gc 0 gc.configs.length (by omega)).length = gc.configs.length := by
    simpa using gcWordFrom_length gc 0 gc.configs.length (by omega)
  have hu_lt : u < gc.configs.length := by
    simpa [hword_len] using hu
  have ht_lt : t < gc.configs.length := lt_trans htu hu_lt
  have hEqFrom :
      prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (gcWordFrom gc 0 gc.configs.length (by omega)) t =
      prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (gcWordFrom gc 0 gc.configs.length (by omega)) u := by
    rw [prefixState4From_eq_xor_prefixState4, prefixState4From_eq_xor_prefixState4]
    simp [hEq]
  have hcfg_t0 :
      gcCfgAt gc (0 + t) (by omega) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) t) :=
    gcCfgAt_eq_cfgFromBits4_prefixState4From gc 0 gc.configs.length
      (by omega) t (Nat.le_of_lt ht_lt)
  have hcfg_t1 :
      gc.configs.get ⟨0 + t, by omega⟩ =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) t) := by
    simpa [gcCfgAt_of_lt gc (0 + t) (by omega)] using hcfg_t0
  have hcfg_t :
      gcCfgAt gc t (Nat.le_of_lt ht_lt) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) t) := by
    rw [gcCfgAt_of_lt gc t ht_lt]
    simpa [Nat.zero_add] using hcfg_t1
  have hcfg_u0 :
      gcCfgAt gc (0 + u) (by omega) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) u) :=
    gcCfgAt_eq_cfgFromBits4_prefixState4From gc 0 gc.configs.length
      (by omega) u (Nat.le_of_lt hu_lt)
  have hcfg_u1 :
      gc.configs.get ⟨0 + u, by omega⟩ =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) u) := by
    simpa [gcCfgAt_of_lt gc (0 + u) (by omega)] using hcfg_u0
  have hcfg_u :
      gcCfgAt gc u (Nat.le_of_lt hu_lt) =
        cfgFromBits4
          (prefixState4From (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
            (gcWordFrom gc 0 gc.configs.length (by omega)) u) := by
    rw [gcCfgAt_of_lt gc u hu_lt]
    simpa [Nat.zero_add] using hcfg_u1
  have hcfgEq : gcCfgAt gc t (Nat.le_of_lt ht_lt) = gcCfgAt gc u (Nat.le_of_lt hu_lt) := by
    rw [hcfg_t, hcfg_u, hEqFrom]
  rw [gcCfgAt_of_lt gc t ht_lt, gcCfgAt_of_lt gc u hu_lt] at hcfgEq
  have hidx : (⟨t, ht_lt⟩ : Fin gc.configs.length) = ⟨u, hu_lt⟩ :=
    gc.distinct ⟨t, ht_lt⟩ ⟨u, hu_lt⟩ hcfgEq
  exact (Nat.ne_of_lt htu) (congrArg Fin.val hidx)

private theorem gcWordFrom_zero_eight_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) :
    gcWordFrom gc 0 8 (by simpa using gc_len_ge_8 gc) =
      forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) := by
  let a : Fin 4 := gc.moverAt ⟨0, gc_len_ge_1 gc⟩
  have h1lt : 1 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h2lt : 2 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h3lt : 3 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h4lt : 4 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h5lt : 5 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h6lt : 6 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h7lt : 7 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h1 :
      gc.moverAt ⟨1, h1lt⟩ = right4 a := by
    simpa [a, gc_nextIndex_eq_succ gc 0 h1lt, right_eq_right4] using hCW ⟨0, gc_len_ge_1 gc⟩
  have h2 :
      gc.moverAt ⟨2, h2lt⟩ = anti4 a := by
    have h := hCW ⟨1, h1lt⟩
    have hstep :
        gc.moverAt ⟨2, h2lt⟩ = right (gc.moverAt ⟨1, h1lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 1 h2lt] using h
    rw [h1] at hstep
    simpa [right_eq_right4, right4_right4] using hstep
  have h3 :
      gc.moverAt ⟨3, h3lt⟩ = left4 a := by
    have h := hCW ⟨2, h2lt⟩
    have hstep :
        gc.moverAt ⟨3, h3lt⟩ = right (gc.moverAt ⟨2, h2lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 2 h3lt] using h
    rw [h2] at hstep
    simpa [right_eq_right4, right4_anti4] using hstep
  have h4 :
      gc.moverAt ⟨4, h4lt⟩ = a := by
    have h := hCW ⟨3, h3lt⟩
    have hstep :
        gc.moverAt ⟨4, h4lt⟩ = right (gc.moverAt ⟨3, h3lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 3 h4lt] using h
    rw [h3] at hstep
    simpa [right_eq_right4, right4_left4] using hstep
  have h5 :
      gc.moverAt ⟨5, h5lt⟩ = right4 a := by
    have h := hCW ⟨4, h4lt⟩
    have hstep :
        gc.moverAt ⟨5, h5lt⟩ = right (gc.moverAt ⟨4, h4lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 4 h5lt] using h
    rw [h4] at hstep
    simpa [right_eq_right4] using hstep
  have h6 :
      gc.moverAt ⟨6, h6lt⟩ = anti4 a := by
    have h := hCW ⟨5, h5lt⟩
    have hstep :
        gc.moverAt ⟨6, h6lt⟩ = right (gc.moverAt ⟨5, h5lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 5 h6lt] using h
    rw [h5] at hstep
    simpa [right_eq_right4, right4_right4] using hstep
  have h7 :
      gc.moverAt ⟨7, h7lt⟩ = left4 a := by
    have h := hCW ⟨6, h6lt⟩
    have hstep :
        gc.moverAt ⟨7, h7lt⟩ = right (gc.moverAt ⟨6, h6lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 6 h7lt] using h
    rw [h6] at hstep
    simpa [right_eq_right4, right4_anti4] using hstep
  simp [gcWordFrom, a, h1, h2, h3, h4, h5, h6, h7, forwardSweepWord4]

private theorem gcWordFrom_zero_eight_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) :
    gcWordFrom gc 0 8 (by simpa using gc_len_ge_8 gc) =
      [gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
        left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
        left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)] := by
  let a : Fin 4 := gc.moverAt ⟨0, gc_len_ge_1 gc⟩
  have h1lt : 1 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h2lt : 2 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h3lt : 3 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h4lt : 4 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h5lt : 5 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h6lt : 6 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h7lt : 7 < gc.configs.length := by
    have := gc_len_ge_8 gc
    omega
  have h1 :
      gc.moverAt ⟨1, h1lt⟩ = left4 a := by
    simpa [a, gc_nextIndex_eq_succ gc 0 h1lt, left_eq_left4] using hCCW ⟨0, gc_len_ge_1 gc⟩
  have h2 :
      gc.moverAt ⟨2, h2lt⟩ = anti4 a := by
    have h := hCCW ⟨1, h1lt⟩
    have hstep :
        gc.moverAt ⟨2, h2lt⟩ = left (gc.moverAt ⟨1, h1lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 1 h2lt] using h
    rw [h1] at hstep
    simpa [left_eq_left4, left4_left4] using hstep
  have h3 :
      gc.moverAt ⟨3, h3lt⟩ = right4 a := by
    have h := hCCW ⟨2, h2lt⟩
    have hstep :
        gc.moverAt ⟨3, h3lt⟩ = left (gc.moverAt ⟨2, h2lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 2 h3lt] using h
    rw [h2] at hstep
    simpa [left_eq_left4, left4_anti4] using hstep
  have h4 :
      gc.moverAt ⟨4, h4lt⟩ = a := by
    have h := hCCW ⟨3, h3lt⟩
    have hstep :
        gc.moverAt ⟨4, h4lt⟩ = left (gc.moverAt ⟨3, h3lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 3 h4lt] using h
    rw [h3] at hstep
    simpa [left_eq_left4, left4_right4] using hstep
  have h5 :
      gc.moverAt ⟨5, h5lt⟩ = left4 a := by
    have h := hCCW ⟨4, h4lt⟩
    have hstep :
        gc.moverAt ⟨5, h5lt⟩ = left (gc.moverAt ⟨4, h4lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 4 h5lt] using h
    rw [h4] at hstep
    simpa [left_eq_left4] using hstep
  have h6 :
      gc.moverAt ⟨6, h6lt⟩ = anti4 a := by
    have h := hCCW ⟨5, h5lt⟩
    have hstep :
        gc.moverAt ⟨6, h6lt⟩ = left (gc.moverAt ⟨5, h5lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 5 h6lt] using h
    rw [h5] at hstep
    simpa [left_eq_left4, left4_left4] using hstep
  have h7 :
      gc.moverAt ⟨7, h7lt⟩ = right4 a := by
    have h := hCCW ⟨6, h6lt⟩
    have hstep :
        gc.moverAt ⟨7, h7lt⟩ = left (gc.moverAt ⟨6, h6lt⟩) := by
      simpa [gc_nextIndex_eq_succ gc 6 h7lt] using h
    rw [h6] at hstep
    simpa [left_eq_left4, left4_anti4] using hstep
  simp [gcWordFrom, a, h1, h2, h3, h4, h5, h6, h7]

private theorem count_reverseSweepPrefix_eq_one (a j : Fin 4) :
    [a, left4 a, anti4 a, right4 a].count j = 1 := by
  have hpermTail1 :
      [left4 a, anti4 a, right4 a].Perm [anti4 a, left4 a, right4 a] :=
    List.Perm.swap _ _ _
  have hpermTail2 :
      [anti4 a, left4 a, right4 a].Perm [anti4 a, right4 a, left4 a] :=
    List.Perm.cons _ (List.Perm.swap _ _ _)
  have hpermTail3 :
      [anti4 a, right4 a, left4 a].Perm [right4 a, anti4 a, left4 a] :=
    List.Perm.swap _ _ _
  have hpermTail :
      [left4 a, anti4 a, right4 a].Perm [right4 a, anti4 a, left4 a] :=
    hpermTail1.trans (hpermTail2.trans hpermTail3)
  have hperm :
      [a, left4 a, anti4 a, right4 a].Perm [a, right4 a, anti4 a, left4 a] :=
    List.Perm.cons _ hpermTail
  calc
    [a, left4 a, anti4 a, right4 a].count j =
        [a, right4 a, anti4 a, left4 a].count j := hperm.count_eq j
    _ = 1 := count_sweep_prefix_eq_one a j

private theorem count_forwardSweepWord4_self (a j : Fin 4) :
    (forwardSweepWord4 a a).count j = 2 := by
  rw [show forwardSweepWord4 a a =
      [a, right4 a, anti4 a, left4 a] ++ [a, right4 a, anti4 a, left4 a] by rfl]
  rw [List.count_append, count_sweep_prefix_eq_one a j]

private theorem count_reverseSweepWord4_self (a j : Fin 4) :
    ([a, left4 a, anti4 a, right4 a, a, left4 a, anti4 a, right4 a] : Word4).count j = 2 := by
  rw [show ([a, left4 a, anti4 a, right4 a, a, left4 a, anti4 a, right4 a] : Word4) =
      [a, left4 a, anti4 a, right4 a] ++ [a, left4 a, anti4 a, right4 a] by rfl]
  rw [List.count_append, count_reverseSweepPrefix_eq_one a j]

private theorem gc_prefixFireCount_eq_count_gcWordFrom (gc : GoodCycle ⟨rs2222, f⟩)
    (p : Fin 4) :
    ∀ (m : Nat) (hm : m ≤ gc.configs.length),
      gc.prefixFireCount p m = (gcWordFrom gc 0 m (by simpa using hm)).count p
  | 0, hm => by
      simp [GoodCycle.prefixFireCount, gcWordFrom]
  | m + 1, hm => by
      have hm' : m ≤ gc.configs.length := by omega
      have hm_lt : m < gc.configs.length := by omega
      rw [gc.prefixFireCount_succ]
      rw [gc_prefixFireCount_eq_count_gcWordFrom gc p m hm']
      rw [gcWordFrom_snoc gc 0 m (by simpa using hm)]
      rw [gc.fireIndicator_of_lt p hm_lt]
      by_cases hmov : gc.moverAt ⟨m, hm_lt⟩ = p
      · simp [List.count_append, hmov]
      · simp [List.count_append, hmov]

private theorem gc_prefixFireCount_eight_eq_two_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) (p : Fin 4) :
    gc.prefixFireCount p 8 = 2 := by
  rw [gc_prefixFireCount_eq_count_gcWordFrom gc p 8 (by simpa using gc_len_ge_8 gc)]
  rw [gcWordFrom_zero_eight_of_uniformCW gc hCW]
  exact count_forwardSweepWord4_self _ _

private theorem gc_prefixFireCount_eight_eq_two_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) (p : Fin 4) :
    gc.prefixFireCount p 8 = 2 := by
  rw [gc_prefixFireCount_eq_count_gcWordFrom gc p 8 (by simpa using gc_len_ge_8 gc)]
  rw [gcWordFrom_zero_eight_of_uniformCCW gc hCCW]
  exact count_reverseSweepWord4_self _ _

private theorem gc_config8_eq_start_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) (h8lt : 8 < gc.configs.length) :
    gc.configs.get ⟨8, h8lt⟩ = gc.configs.get ⟨0, gc_len_ge_1 gc⟩ := by
  funext p
  have hstate :=
    gc.binary_stateAfter_eq_stateAfter_zero_of_prefixFireCount_even p (rs2222_m p)
      (m := 8) (by omega) (by
        rw [gc_prefixFireCount_eight_eq_two_of_uniformCW gc hCW p]
        exact ⟨1, by omega⟩)
  rw [gc.stateAfter_of_lt p h8lt, gc.stateAfter_of_lt p (gc_len_ge_1 gc)] at hstate
  simpa using hstate

private theorem gc_config8_eq_start_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) (h8lt : 8 < gc.configs.length) :
    gc.configs.get ⟨8, h8lt⟩ = gc.configs.get ⟨0, gc_len_ge_1 gc⟩ := by
  funext p
  have hstate :=
    gc.binary_stateAfter_eq_stateAfter_zero_of_prefixFireCount_even p (rs2222_m p)
      (m := 8) (by omega) (by
        rw [gc_prefixFireCount_eight_eq_two_of_uniformCCW gc hCCW p]
        exact ⟨1, by omega⟩)
  rw [gc.stateAfter_of_lt p h8lt, gc.stateAfter_of_lt p (gc_len_ge_1 gc)] at hstate
  simpa using hstate

private theorem gc_len_eq_8_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) :
    gc.configs.length = 8 := by
  have hge : 8 ≤ gc.configs.length := gc_len_ge_8 gc
  by_contra hne
  have h8lt : 8 < gc.configs.length := by omega
  have hcfg := gc_config8_eq_start_of_uniformCW gc hCW h8lt
  have hidx : (⟨8, h8lt⟩ : Fin gc.configs.length) = ⟨0, gc_len_ge_1 gc⟩ :=
    gc.distinct ⟨8, h8lt⟩ ⟨0, gc_len_ge_1 gc⟩ hcfg
  have : (8 : Nat) = 0 := by simpa using congrArg Fin.val hidx
  omega

private theorem gc_len_eq_8_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) :
    gc.configs.length = 8 := by
  have hge : 8 ≤ gc.configs.length := gc_len_ge_8 gc
  by_contra hne
  have h8lt : 8 < gc.configs.length := by omega
  have hcfg := gc_config8_eq_start_of_uniformCCW gc hCCW h8lt
  have hidx : (⟨8, h8lt⟩ : Fin gc.configs.length) = ⟨0, gc_len_ge_1 gc⟩ :=
    gc.distinct ⟨8, h8lt⟩ ⟨0, gc_len_ge_1 gc⟩ hcfg
  have : (8 : Nat) = 0 := by simpa using congrArg Fin.val hidx
  omega

private theorem gcPathN_eq_forwardSweepPath_of_uniformCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCW : gc.uniformCW) :
    gcPathN gc gc.configs.length (le_refl _) =
      pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)) := by
  have hlen : gc.configs.length = 8 := gc_len_eq_8_of_uniformCW gc hCW
  have hpath : gcPathN gc 8 (by omega) =
      pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (gcWordFrom gc 0 8 (by omega)) := by
    simpa [hlen] using (gcPathN_eq_pathFromWord4 gc)
  calc
    gcPathN gc gc.configs.length (le_refl _) = gcPathN gc 8 (by omega) := by
      exact gcPathN_eq gc gc.configs.length 8 (le_refl _) (by omega) hlen
    _ = pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 8 (by omega)) := hpath
    _ = pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)) := by
      rw [gcWordFrom_zero_eight_of_uniformCW gc hCW]

private theorem gcPathN_eq_reverseSweepPath_of_uniformCCW (gc : GoodCycle ⟨rs2222, f⟩)
    (hCCW : gc.uniformCCW) :
    gcPathN gc gc.configs.length (le_refl _) =
      pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        ([gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)]) := by
  have hlen : gc.configs.length = 8 := gc_len_eq_8_of_uniformCCW gc hCCW
  have hpath : gcPathN gc 8 (by omega) =
      pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
        (gcWordFrom gc 0 8 (by omega)) := by
    simpa [hlen] using (gcPathN_eq_pathFromWord4 gc)
  calc
    gcPathN gc gc.configs.length (le_refl _) = gcPathN gc 8 (by omega) := by
      exact gcPathN_eq gc gc.configs.length 8 (le_refl _) (by omega) hlen
    _ = pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          (gcWordFrom gc 0 8 (by omega)) := hpath
    _ = pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
          ([gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
            left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
            left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)]) := by
      rw [gcWordFrom_zero_eight_of_uniformCCW gc hCCW]

private theorem gcWordFrom_get (gc : GoodCycle ⟨rs2222, f⟩) :
    ∀ (k rem : Nat) (hkr : k + rem ≤ gc.configs.length) (t : Nat) (ht : t < rem),
      (gcWordFrom gc k rem hkr).get ⟨t, by simpa using ht⟩ =
        gc.moverAt ⟨k + t, by omega⟩
  | k, 0, hkr, t, ht => False.elim (Nat.not_lt_zero _ ht)
  | k, rem + 1, hkr, 0, ht => by
      simp [gcWordFrom]
  | k, rem + 1, hkr, t + 1, ht => by
      have ht' : t < rem := by omega
      simpa [gcWordFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (gcWordFrom_get gc (k + 1) rem (by omega) t ht')

private theorem gc_len_eq_8_of_allFireCount_two (gc : GoodCycle ⟨rs2222, f⟩)
    (hfc2 : ∀ p : Fin 4, gc.fireCount p = 2) :
    gc.configs.length = 8 := by
  have hsum := gc.sum_fireCount
  calc
    gc.configs.length = ∑ p : Fin 4, gc.fireCount p := hsum.symm
    _ = ∑ _p : Fin 4, 2 := by
      apply Finset.sum_congr rfl
      intro p _
      exact hfc2 p
    _ = 8 := by norm_num

private theorem gcWordFrom_balanced_of_allFireCount_two (gc : GoodCycle ⟨rs2222, f⟩)
    (hfc2 : ∀ p : Fin 4, gc.fireCount p = 2) :
    BalancedWord4 (gcWordFrom gc 0 gc.configs.length (by omega)) := by
  intro p
  rw [← gc_prefixFireCount_eq_count_gcWordFrom gc p gc.configs.length
    (by omega)]
  simpa [GoodCycle.fireCount] using hfc2 p

private theorem gcWordFrom_sweep_or_reverse_of_allFireCount_two
    (gc : GoodCycle ⟨rs2222, f⟩)
    (hfc2 : ∀ p : Fin 4, gc.fireCount p = 2)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false) :
    (gcWordFrom gc 0 gc.configs.length (by omega) =
        forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)) ∨
      (gcWordFrom gc 0 gc.configs.length (by omega) =
        [gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)]) := by
  have hlen : gc.configs.length = 8 := gc_len_eq_8_of_allFireCount_two gc hfc2
  have h1lt : 1 < gc.configs.length := by omega
  have h2lt : 2 < gc.configs.length := by omega
  have h3lt : 3 < gc.configs.length := by omega
  have h4lt : 4 < gc.configs.length := by omega
  have h5lt : 5 < gc.configs.length := by omega
  have h6lt : 6 < gc.configs.length := by omega
  have h7lt : 7 < gc.configs.length := by omega
  let w8 : Word4 :=
    [gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
      gc.moverAt ⟨1, h1lt⟩,
      gc.moverAt ⟨2, h2lt⟩,
      gc.moverAt ⟨3, h3lt⟩,
      gc.moverAt ⟨4, h4lt⟩,
      gc.moverAt ⟨5, h5lt⟩,
      gc.moverAt ⟨6, h6lt⟩,
      gc.moverAt ⟨7, h7lt⟩]
  have hw8 : gcWordFrom gc 0 gc.configs.length (by omega) = w8 := by
    simpa [w8, gcWordFrom, hlen]
  have hbal : BalancedWord4 w8 := by
    rw [← hw8]
    exact gcWordFrom_balanced_of_allFireCount_two gc hfc2
  have hsimple : SimpleWord4 w8 := by
    rw [← hw8]
    exact gcWordFrom_simple gc
  have htf' :
      isTFBlocked
        (pathFromWord4 (bitsOfCfg4 (gcCfgAt gc 0 (by omega))) w8) = false := by
    rw [← hw8]
    simpa [gcPathN_eq_pathFromWord4 gc] using htf
  have hshape :=
    eight_word_sweep_of_isTFBlocked_false
      (bits0 := bitsOfCfg4 (gcCfgAt gc 0 (by omega)))
      (a := gc.moverAt ⟨0, gc_len_ge_1 gc⟩)
      (b := gc.moverAt ⟨1, h1lt⟩)
      (c := gc.moverAt ⟨2, h2lt⟩)
      (d := gc.moverAt ⟨3, h3lt⟩)
      (e := gc.moverAt ⟨4, h4lt⟩)
      (f := gc.moverAt ⟨5, h5lt⟩)
      (g := gc.moverAt ⟨6, h6lt⟩)
      (h := gc.moverAt ⟨7, h7lt⟩)
      hsimple hbal htf'
  simpa [w8, gcWordFrom, hlen] using hshape

private theorem forwardSweepWord4_next_right (a : Proc4) (k : Fin 8) :
    (forwardSweepWord4 a a).get
        ⟨(k.val + 1) % 8, by
          have hmod : (k.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
          simpa [forwardSweepWord4] using hmod⟩ =
      right4 ((forwardSweepWord4 a a).get k) := by
  fin_cases k <;> simp [forwardSweepWord4, right4_right4, right4_anti4, right4_left4]

private theorem repeatLeftSweepWord4_next_left (a : Proc4) (k : Fin 8) :
    ([a, left4 a, anti4 a, right4 a, a, left4 a, anti4 a, right4 a] : Word4).get
        ⟨(k.val + 1) % 8, by
          have hmod : (k.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
          simpa using hmod⟩ =
      left4 (([a, left4 a, anti4 a, right4 a, a, left4 a, anti4 a, right4 a] : Word4).get k) := by
  fin_cases k <;> simp [left4_left4, left4_anti4, left4_right4]

private theorem uniformCW_of_allFireCount_two_forward
    (gc : GoodCycle ⟨rs2222, f⟩)
    (hfc2 : ∀ p : Fin 4, gc.fireCount p = 2)
    (hw : gcWordFrom gc 0 gc.configs.length (by omega) =
      forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)) :
    gc.uniformCW := by
  have hlen : gc.configs.length = 8 := gc_len_eq_8_of_allFireCount_two gc hfc2
  intro k
  let k8 : Fin 8 := ⟨k.val, by simpa [hlen] using k.isLt⟩
  have hk_eq : Fin.cast hlen.symm k8 = k := by
    apply Fin.ext
    simp [k8]
  have hcur_word :
      (forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)).get k8 =
        gc.moverAt k := by
    have hget :=
      gcWordFrom_get gc 0 gc.configs.length (by omega) k8.val (by simpa [k8] using k8.isLt)
    simpa [hw, hk_eq, k8] using hget
  have hnext_eq :
      (⟨(nextIndex gc.configs k).val, by simpa [hlen] using (nextIndex gc.configs k).isLt⟩ : Fin 8) =
        ⟨(k8.val + 1) % 8, by
          have hmod : (k8.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
          simpa using hmod⟩ := by
    apply Fin.ext
    simp [k8, nextIndex, hlen]
  have hnext_word :
      (forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩) (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)).get
          ⟨(k8.val + 1) % 8, by
            have hmod : (k8.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
            simpa [forwardSweepWord4] using hmod⟩ =
        gc.moverAt (nextIndex gc.configs k) := by
    have hget :=
      gcWordFrom_get gc 0 gc.configs.length (by omega)
        (nextIndex gc.configs k).val (by simpa [hlen] using (nextIndex gc.configs k).isLt)
    have hget' :
        (forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)
          (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)).get
            (⟨(nextIndex gc.configs k).val,
              by simpa [hlen] using (nextIndex gc.configs k).isLt⟩ : Fin 8) =
          gc.moverAt (nextIndex gc.configs k) := by
      simpa [hw] using hget
    simpa [hnext_eq] using hget'
  calc
    gc.moverAt (nextIndex gc.configs k)
      = (forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)
          (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)).get ⟨(k8.val + 1) % 8, by
            have hmod : (k8.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
            simpa [forwardSweepWord4] using hmod⟩ := hnext_word.symm
    _ = right4
          ((forwardSweepWord4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)
            (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)).get k8) :=
          forwardSweepWord4_next_right _ k8
    _ = right4 (gc.moverAt k) := by rw [hcur_word]
    _ = right (gc.moverAt k) := by simp [right_eq_right4]

private theorem uniformCCW_of_allFireCount_two_reverse
    (gc : GoodCycle ⟨rs2222, f⟩)
    (hfc2 : ∀ p : Fin 4, gc.fireCount p = 2)
    (hw : gcWordFrom gc 0 gc.configs.length (by omega) =
      [gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
        left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
        left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
        right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)]) :
    gc.uniformCCW := by
  have hlen : gc.configs.length = 8 := gc_len_eq_8_of_allFireCount_two gc hfc2
  intro k
  let k8 : Fin 8 := ⟨k.val, by simpa [hlen] using k.isLt⟩
  have hk_eq : Fin.cast hlen.symm k8 = k := by
    apply Fin.ext
    simp [k8]
  have hcur_word :
      ([gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)] : Word4).get k8 =
        gc.moverAt k := by
    have hget :=
      gcWordFrom_get gc 0 gc.configs.length (by omega) k8.val (by simpa [k8] using k8.isLt)
    simpa [hw, hk_eq, k8] using hget
  have hnext_eq :
      (⟨(nextIndex gc.configs k).val, by simpa [hlen] using (nextIndex gc.configs k).isLt⟩ : Fin 8) =
        ⟨(k8.val + 1) % 8, by
          have hmod : (k8.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
          simpa using hmod⟩ := by
    apply Fin.ext
    simp [k8, nextIndex, hlen]
  have hnext_word :
      ([gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
          left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
          right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)] : Word4).get ⟨(k8.val + 1) % 8, by
            have hmod : (k8.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
            simpa using hmod⟩ =
        gc.moverAt (nextIndex gc.configs k) := by
    have hget :=
      gcWordFrom_get gc 0 gc.configs.length (by omega)
        (nextIndex gc.configs k).val (by simpa [hlen] using (nextIndex gc.configs k).isLt)
    have hget' :
        ([gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
            left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
            left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)] : Word4).get
            (⟨(nextIndex gc.configs k).val,
              by simpa [hlen] using (nextIndex gc.configs k).isLt⟩ : Fin 8) =
          gc.moverAt (nextIndex gc.configs k) := by
      simpa [hw] using hget
    simpa [hnext_eq] using hget'
  calc
    gc.moverAt (nextIndex gc.configs k)
      = ([gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
            left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
            left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
            right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)] : Word4).get ⟨(k8.val + 1) % 8, by
              have hmod : (k8.val + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
              simpa using hmod⟩ :=
          hnext_word.symm
    _ = left4
          (([gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
              left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
              anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
              right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
              gc.moverAt ⟨0, gc_len_ge_1 gc⟩,
              left4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
              anti4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩),
              right4 (gc.moverAt ⟨0, gc_len_ge_1 gc⟩)] : Word4).get k8) :=
          repeatLeftSweepWord4_next_left _ k8
    _ = left4 (gc.moverAt k) := by rw [hcur_word]
    _ = left (gc.moverAt k) := by simp [left_eq_left4]

private theorem uniformDirection_of_allFireCount_two
    (gc : GoodCycle ⟨rs2222, f⟩)
    (hfc2 : ∀ p : Fin 4, gc.fireCount p = 2)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false) :
    gc.uniformDirection := by
  rcases gcWordFrom_sweep_or_reverse_of_allFireCount_two gc hfc2 htf with hw | hw
  · exact Or.inl (uniformCW_of_allFireCount_two_forward gc hfc2 hw)
  · exact Or.inr (uniformCCW_of_allFireCount_two_reverse gc hfc2 hw)

private theorem partnerIdx_next3_of_uniform_len8 (gc : GoodCycle ⟨rs2222, f⟩)
    (hlen : gc.configs.length = 8) (t : Fin 8) :
    let idx : Fin gc.configs.length := Fin.cast hlen.symm ⟨(3 * t.val) % 8, by omega⟩
    let idxNext : Fin gc.configs.length :=
      Fin.cast hlen.symm ⟨(3 * ((t.val + 1) % 8)) % 8, by omega⟩
    nextIndex gc.configs (nextIndex gc.configs (nextIndex gc.configs idx)) = idxNext := by
  apply Fin.ext
  simp [nextIndex, hlen]
  omega

private theorem uniformCW_false (gc : GoodCycle ⟨rs2222, f⟩)
    (hconv : converges ⟨rs2222, f⟩ gc) (hCW : gc.uniformCW) : False := by
  have hlen : gc.configs.length = 8 := gc_len_eq_8_of_uniformCW gc hCW
  let cyc : Fin 8 → Config rs2222 := fun t =>
    partnerCfg gc (Fin.cast hlen.symm ⟨(3 * t.val) % 8, by omega⟩)
  have hcycle :
      ∀ t : Fin 8,
        badStep ⟨rs2222, f⟩ gc
          (cyc ⟨(t.val + 1) % 8, by omega⟩) (cyc t) := by
    intro t
    let idx : Fin gc.configs.length := Fin.cast hlen.symm ⟨(3 * t.val) % 8, by omega⟩
    let idxNext : Fin gc.configs.length :=
      Fin.cast hlen.symm ⟨(3 * ((t.val + 1) % 8)) % 8, by omega⟩
    have hidx :
        nextIndex gc.configs (nextIndex gc.configs (nextIndex gc.configs idx)) = idxNext := by
      simpa [idx, idxNext] using partnerIdx_next3_of_uniform_len8 gc hlen t
    have hstep3 :
        flipCfg (partnerCfg gc idx) (gcMover gc idx) = partnerCfg gc idxNext := by
      simpa [idxNext, hidx] using partner_step3_of_uniformCW gc hCW idx
    refine ⟨partner_not_mem_of_uniformCW gc hCW idx,
      partner_not_mem_of_uniformCW gc hCW idxNext, ?_⟩
    refine ⟨gcMover gc idx, partner_priv gc idx, ?_⟩
    rw [move_eq_flipCfg (partner_priv gc idx)]
    simpa [cyc, idx, idxNext] using hstep3.symm
  have hacc : Acc (badStep ⟨rs2222, f⟩ gc) (cyc ⟨0, by decide⟩) := hconv.apply _
  exact not_acc_of_finite_cycle' (α := Config rs2222) (r := badStep ⟨rs2222, f⟩ gc)
    (n := 8) (by decide) cyc hcycle ⟨0, by decide⟩ hacc

private theorem uniformCCW_false (gc : GoodCycle ⟨rs2222, f⟩)
    (hconv : converges ⟨rs2222, f⟩ gc) (hCCW : gc.uniformCCW) : False := by
  have hlen : gc.configs.length = 8 := gc_len_eq_8_of_uniformCCW gc hCCW
  let cyc : Fin 8 → Config rs2222 := fun t =>
    partnerCfg gc (Fin.cast hlen.symm ⟨(3 * t.val) % 8, by omega⟩)
  have hcycle :
      ∀ t : Fin 8,
        badStep ⟨rs2222, f⟩ gc
          (cyc ⟨(t.val + 1) % 8, by omega⟩) (cyc t) := by
    intro t
    let idx : Fin gc.configs.length := Fin.cast hlen.symm ⟨(3 * t.val) % 8, by omega⟩
    let idxNext : Fin gc.configs.length :=
      Fin.cast hlen.symm ⟨(3 * ((t.val + 1) % 8)) % 8, by omega⟩
    have hidx :
        nextIndex gc.configs (nextIndex gc.configs (nextIndex gc.configs idx)) = idxNext := by
      simpa [idx, idxNext] using partnerIdx_next3_of_uniform_len8 gc hlen t
    have hstep3 :
        flipCfg (partnerCfg gc idx) (gcMover gc idx) = partnerCfg gc idxNext := by
      simpa [idxNext, hidx] using partner_step3_of_uniformCCW gc hCCW idx
    refine ⟨partner_not_mem_of_uniformCCW gc hCCW idx,
      partner_not_mem_of_uniformCCW gc hCCW idxNext, ?_⟩
    refine ⟨gcMover gc idx, partner_priv gc idx, ?_⟩
    rw [move_eq_flipCfg (partner_priv gc idx)]
    simpa [cyc, idx, idxNext] using hstep3.symm
  have hacc : Acc (badStep ⟨rs2222, f⟩ gc) (cyc ⟨0, by decide⟩) := hconv.apply _
  exact not_acc_of_finite_cycle' (α := Config rs2222) (r := badStep ⟨rs2222, f⟩ gc)
    (n := 8) (by decide) cyc hcycle ⟨0, by decide⟩ hacc

private theorem uniformDirection_false (gc : GoodCycle ⟨rs2222, f⟩)
    (hconv : converges ⟨rs2222, f⟩ gc) (hdir : gc.uniformDirection) : False := by
  rcases hdir with hCW | hCCW
  · exact uniformCW_false gc hconv hCW
  · exact uniformCCW_false gc hconv hCCW

/-- gcFair at step k+1 extends gcFair at step k. -/
private theorem gcFair_succ (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length) :
    gcFair gc (k + 1) (by omega) =
      gcFair gc k (by omega) ||| (1 <<< (gcMover gc ⟨k, hk⟩).val) := by
  simp only [gcFair, show k < gc.configs.length from hk, dite_true]

/-- gcMask at step k+1 extends gcMask at step k. -/
private theorem gcMask_succ (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length) :
    gcMask gc (k + 1) (by omega) =
      gcMask gc k (by omega) ||| (1 <<< (encCfg (gc.configs.get ⟨k, hk⟩)).val) := by
  simp only [gcMask, show k < gc.configs.length from hk, dite_true]

/-- The fair mask bit for proc p is set when p appears as a mover in steps 0..k-1. -/
private theorem gcFair_bit_set (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k ≤ gc.configs.length) (p : Fin 4)
    (j : Nat) (hj : j < k) (hjL : j < gc.configs.length) (hmov : gcMover gc ⟨j, hjL⟩ = p) :
    (gcFair gc k hk >>> p.val) &&& 1 = 1 := by
  induction k with
  | zero => omega
  | succ n ih =>
    rw [gcFair_succ gc n (by omega)]
    by_cases hjn : j = n
    · -- j = n: the last OR'd term is (1 <<< mover(j)), and mover(j) = p
      subst hjn
      rw [shr_and1_eq_one]
      simp only [Nat.testBit_or, Bool.or_eq_true]
      right
      have : (gcMover gc ⟨j, by omega⟩) = p := by
        have : (⟨j, hjL⟩ : Fin gc.configs.length) = ⟨j, by omega⟩ := Fin.ext rfl
        rw [← this]; exact hmov
      rw [Nat.one_shiftLeft, this, Nat.testBit_two_pow_self]
    · -- j < n: use induction hypothesis
      rw [shr_and1_eq_one]
      simp only [Nat.testBit_or, Bool.or_eq_true]
      left
      rw [← shr_and1_eq_one]
      exact ih (by omega) (by omega)

/-- The fair mask at cycle end = 15. -/
private theorem gcFair_complete (gc : GoodCycle ⟨rs2222, f⟩) :
    gcFair gc gc.configs.length (le_refl _) = 15 := by
  -- All 4 bits are set. Show each bit p ∈ {0,1,2,3} is set.
  -- By gc.fair, each proc p has some step where it's the mover.
  -- Use gcFair_bit_set for each.
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi3 : i ≥ 4
  · -- Bits ≥ 4 are 0 in both the fair mask and 15.
    -- 15.testBit i = false for i ≥ 4:
    have h15 : (15 : Nat).testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      calc (15 : Nat) < 16 := by omega
        _ = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi3
    rw [h15]
    -- gcFair has no bits ≥ 4 set. Prove by induction.
    suffices h : ∀ (k : Nat) (hk : k ≤ gc.configs.length),
        (gcFair gc k hk).testBit i = false from h _ _
    intro k hk
    induction k with
    | zero => simp [gcFair]
    | succ n ih =>
      rw [gcFair_succ gc n (by omega)]
      simp only [Nat.testBit_or]
      have := ih (by omega)
      rw [this, Bool.false_or]
      -- (1 <<< p).testBit i = false for p < 4, i ≥ 4
      rw [Nat.one_shiftLeft]
      apply Nat.testBit_two_pow_of_ne
      have : (gcMover gc ⟨n, by omega⟩).val < 4 := (gcMover gc ⟨n, by omega⟩).isLt
      omega
  · push_neg at hi3
    -- i < 4, so bit i must be true in the fair mask.
    have hfair := gc.fair ⟨i, by show i < 4; omega⟩
    obtain ⟨k, j, hpriv, _, hjp⟩ := hfair
    -- j = ⟨i, ...⟩ is the proc that fires at step k.
    -- gcMover gc k = j (by unique_privileged).
    have hmov : gcMover gc k = ⟨i, by show i < 4; omega⟩ := by
      have huniq := gc.unique_privileged (gc.configs.get k) (List.get_mem _ _)
      exact huniq.unique (gcMover_priv gc k) (hjp ▸ hpriv)
    -- 15.testBit i = true for i < 4
    have h15 : (15 : Nat).testBit i = true := by
      interval_cases i <;> decide
    rw [h15]
    -- gcFair has bit i set because mover at step k = ⟨i, ...⟩
    have hset := gcFair_bit_set gc gc.configs.length (le_refl _) ⟨i, by show i < 4; omega⟩
      k.val k.isLt k.isLt hmov
    rw [shr_and1_eq_one] at hset
    exact hset

/-- DFS induction: following the GoodCycle's mover sequence through the DFS.
    At each step k, we have the DFS returning true, and extract the GoodCycle's
    mover to step forward. At the end, isBlocked returns true for the full cycle. -/
private theorem dfs_follows_gc (gc : GoodCycle ⟨rs2222, f⟩)
    -- remaining steps from k to the end of the cycle
    (rem k : Nat) (hk : k < gc.configs.length) (hrem : rem + k + 1 = gc.configs.length)
    -- fuel for DFS
    (fuel : Nat) (hfuel : rem + 1 ≤ fuel)
    -- DFS returns true at the current state
    (hdfs : dfsBlocked fuel
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨k, hk⟩)).val
      (gcMask gc (k + 1) (by omega))
      (gcPathN gc k (by omega))
      (gcFair gc k (by omega)) = true) :
    -- Conclusion: the full encoded cycle is blocked
    isBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
  induction rem generalizing k fuel with
  | zero =>
    -- k is the LAST step. next config = c_0 = start.
    have hkL : k + 1 = gc.configs.length := by omega
    -- Extract the mover at step k
    have hproc := gcMover_lt_4 gc ⟨k, hk⟩
    -- Use dfs_branch to extract one step
    have hfuelp : fuel = fuel - 1 + 1 := by omega
    rw [hfuelp] at hdfs
    have hbr := dfs_branch (fuel - 1)
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨k, hk⟩)).val
      (gcMask gc (k + 1) (by omega))
      (gcPathN gc k (by omega))
      (gcFair gc k (by omega))
      (gcMover gc ⟨k, hk⟩).val
      hproc hdfs
    -- next = flipBit(enc(c_k), m_k) = enc(c_{k+1}) = enc(c_0) (cycle wraps)
    have hni : nextIndex gc.configs ⟨k, hk⟩ = ⟨0, gc_len_ge_1 gc⟩ := by
      simp only [nextIndex, hkL, Nat.mod_self]
    have hnext : flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val =
        (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val := by
      rw [← gcEnc_step gc ⟨k, hk⟩, hni]
    -- Apply branch case 1 (next = start)
    have hblocked := hbr.1 hnext
    -- newFair = gcFair gc (k+1) = gcFair gc L = 15
    have hfair : gcFair gc k (by omega) ||| (1 <<< (gcMover gc ⟨k, hk⟩).val) = 15 := by
      have h1 := gcFair_succ gc k hk
      rw [← h1]
      rw [gcFair_eq gc (k + 1) gc.configs.length (by omega) (le_refl _) hkL]
      exact gcFair_complete gc
    have hblocked := hblocked hfair
    -- newPath = gcPathN gc (k+1) = gcPathN gc L
    have hpath1 := gcPathN_succ gc k hk
    rw [← hpath1] at hblocked
    rw [gcPathN_eq gc (k + 1) gc.configs.length (by omega) (le_refl _) hkL] at hblocked
    exact hblocked
  | succ rem' ih =>
    -- k is not the last step. Extract mover, step forward, use IH.
    have hproc := gcMover_lt_4 gc ⟨k, hk⟩
    have hfuelp : fuel = (fuel - 1) + 1 := by omega
    rw [hfuelp] at hdfs
    have hbr := dfs_branch (fuel - 1)
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨k, hk⟩)).val
      (gcMask gc (k + 1) (by omega))
      (gcPathN gc k (by omega))
      (gcFair gc k (by omega))
      (gcMover gc ⟨k, hk⟩).val
      hproc hdfs
    -- next = enc(c_{k+1}), which is ≠ start and unvisited
    have hk1 : k + 1 < gc.configs.length := by omega
    have hni : nextIndex gc.configs ⟨k, hk⟩ = ⟨k + 1, hk1⟩ := by
      simp only [nextIndex, Nat.mod_eq_of_lt hk1]
    have hnext_eq : flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val =
        (encCfg (gc.configs.get ⟨k + 1, hk1⟩)).val := by
      rw [← gcEnc_step gc ⟨k, hk⟩, hni]
    -- next ≠ start (c_{k+1} ≠ c_0 since k+1 > 0 and configs are distinct)
    have hne_start : flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val ≠
        (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val := by
      rw [hnext_eq]
      apply gcEnc_ne gc ⟨k + 1, hk1⟩ ⟨0, gc_len_ge_1 gc⟩
      intro h; simp [Fin.ext_iff] at h
    -- next is unvisited
    have hunvis : (gcMask gc (k + 1) (by omega) >>>
        flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val) &&& 1 = 0 := by
      rw [hnext_eq]
      exact gcMask_unset gc (k + 1) (by omega) (k + 1) hk1 (by omega)
    -- Apply branch case 2
    have hdfs' := hbr.2 hne_start hunvis
    -- Rewrite the DFS arguments to match the induction hypothesis
    -- New visited = gcMask gc (k+1) ||| (1 <<< enc(c_{k+1})) = gcMask gc (k+2)
    -- New path = gcPathN gc (k+1)
    -- New fair = gcFair gc (k+1)
    rw [hnext_eq] at hdfs'
    have hmask_eq : gcMask gc (k + 1) (by omega) |||
        (1 <<< (encCfg (gc.configs.get ⟨k + 1, hk1⟩)).val) =
        gcMask gc (k + 2) (by omega) := by
      rw [gcMask_succ gc (k + 1) hk1]
    have hpath_eq : gcPathN gc k (by omega) ++
        [((encCfg (gc.configs.get ⟨k, hk⟩)).val, (gcMover gc ⟨k, hk⟩).val)] =
        gcPathN gc (k + 1) (by omega) := by
      rw [gcPathN_succ gc k hk]
    have hfair_eq : gcFair gc k (by omega) ||| (1 <<< (gcMover gc ⟨k, hk⟩).val) =
        gcFair gc (k + 1) (by omega) := by
      rw [gcFair_succ gc k hk]
    rw [hmask_eq, hpath_eq, hfair_eq] at hdfs'
    exact ih (k + 1) hk1 (by omega) (fuel - 1) (by omega) hdfs'

/-- Core bridge: the encoded GoodCycle is blocked. -/
private theorem gc_encoded_blocked (gc : GoodCycle ⟨rs2222, f⟩) :
    isBlocked (gcPathN gc gc.configs.length (le_refl _)) = true := by
  -- Start the DFS at config 0
  have hstart := dfs_start gc
  -- The DFS starts with: fuel=15, visited = 1<<<enc(c_0), path=[], fairMask=0
  -- We need: visited = gcMask gc 1, path = gcPathN gc 0, fairMask = gcFair gc 0
  -- The DFS starts with: fuel=15, visited = 1<<<enc(c_0), path=[], fairMask=0
  -- Rewrite to match gcMask/gcPathN/gcFair at step 1/0/0.
  -- Rewrite hstart to use gcMask/gcPathN/gcFair forms
  have hv : (1 <<< (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val) =
      gcMask gc 1 (gc_len_ge_1 gc) := by simp [gcMask]
  have hlen := gc_len_ge_1 gc
  have hle16 := gc_len_le_16 gc
  have hrem : gc.configs.length - 1 + 0 + 1 = gc.configs.length := by
    clear hv hstart; omega
  have hfuel : gc.configs.length - 1 + 1 ≤ 16 := by
    clear hv hstart; omega
  have hp : ([] : List (Nat × Nat)) = gcPathN gc 0 (by omega) := by simp [gcPathN]
  have hf : (0 : Nat) = gcFair gc 0 (by omega) := by simp [gcFair]
  have hstart' : dfsBlocked 16
      (encCfg (gc.configs.get ⟨0, hlen⟩)).val
      (encCfg (gc.configs.get ⟨0, hlen⟩)).val
      (gcMask gc 1 hlen)
      (gcPathN gc 0 (by omega))
      (gcFair gc 0 (by omega)) = true := by
    rwa [← hv, ← hp, ← hf]
  exact dfs_follows_gc gc (gc.configs.length - 1) 0 hlen hrem 16 hfuel hstart'

/-! ### isBlocked soundness: isBlocked = true → False -/

/-- tfKeyNat on encCfg gives the correct TF key. -/
private theorem tfKeyNat_encCfg (c : Config rs2222) (j : Fin 4) :
    tfKeyNat (encCfg c).val j.val =
      j.val * 8 + (c (left j)).val * 4 + (c j).val * 2 + (c (right j)).val := by
  unfold tfKeyNat
  have hL : getBit (encCfg c).val (leftP j.val) = (c (left j)).val := by
    rw [leftP_eq_left]; exact getBit_encCfg c (left j)
  have hS : getBit (encCfg c).val j.val = (c j).val := getBit_encCfg c j
  have hR : getBit (encCfg c).val (rightP j.val) = (c (right j)).val := by
    rw [rightP_eq_right]; exact getBit_encCfg c (right j)
  rw [hL, hS, hR]

/-- collectTF distributes over append. -/
private theorem collectTF_append (a b : List (Nat × Nat)) :
    collectTF (a ++ b) = collectTF a ++ collectTF b := by
  induction a with
  | nil => simp [collectTF]
  | cons hd tl ih =>
    obtain ⟨cfg, proc⟩ := hd
    simp only [List.cons_append, collectTF, ih, List.cons_append, List.append_assoc]

/-- Every entry in collectTF of a single step corresponds to a constraint on f. -/
private theorem collectTF_single_valid (gc : GoodCycle ⟨rs2222, f⟩)
    (k : Nat) (hk : k < gc.configs.length)
    (entry : Nat × Nat)
    (hmem : entry ∈ collectTF [((encCfg (gc.configs.get ⟨k, hk⟩)).val,
                                 (gcMover gc ⟨k, hk⟩).val)]) :
    ∃ (j : Fin 4),
      entry.1 = tfKeyNat (encCfg (gc.configs.get ⟨k, hk⟩)).val j.val ∧
      entry.2 = ((⟨rs2222, f⟩ : System).f j
        ((gc.configs.get ⟨k, hk⟩) (left j)) ((gc.configs.get ⟨k, hk⟩) j)
        ((gc.configs.get ⟨k, hk⟩) (right j))).val := by
  -- Unfold collectTF on a singleton list
  simp only [collectTF] at hmem
  set c := gc.configs.get ⟨k, hk⟩
  set m := gcMover gc ⟨k, hk⟩
  -- After unfolding, hmem says entry is in:
  --   (tfKeyNat enc m, 1 - getBit enc m) :: (filterMap ... ++ [])
  simp only [List.filterMap_nil, List.append_nil] at hmem
  rw [List.mem_cons] at hmem
  cases hmem with
  | inl h =>
    -- entry is the mover constraint: (tfKeyNat enc m, 1 - getBit enc m)
    refine ⟨m, ?_, ?_⟩
    · exact congrArg Prod.fst h
    · -- value = 1 - getBit enc m = 1 - (c m).val = f_m(L,S,R).val
      have hval : entry.2 = 1 - getBit (encCfg c).val m.val := congrArg Prod.snd h
      rw [hval, getBit_encCfg]
      exact (binary_priv_val (gcMover_priv gc ⟨k, hk⟩) (rs2222_m m)).symm
  | inr h =>
    -- entry is in the non-mover constraints (filterMap result)
    rw [List.mem_filterMap] at h
    obtain ⟨p, hp_range, hp_entry⟩ := h
    rw [List.mem_range] at hp_range
    split at hp_entry
    · exact absurd hp_entry (Option.not_mem_none _)
    · next hne =>
      simp only [Option.some.injEq] at hp_entry
      have hpne : p ≠ m.val := by
        intro heq; rw [heq, beq_self_eq_true] at hne; exact absurd rfl hne
      refine ⟨⟨p, hp_range⟩, ?_, ?_⟩
      · exact (congrArg Prod.fst hp_entry).symm
      · -- value = getBit enc p = (c p).val = f_p(L,S,R).val (since p not privileged)
        have hval : entry.2 = getBit (encCfg c).val p :=
          (congrArg Prod.snd hp_entry).symm
        -- p is not the mover, so p is not privileged → f_p = c_p
        have hpfin : (⟨p, hp_range⟩ : Fin 4) ≠ m := Fin.ne_of_val_ne hpne
        have hmem_cfg : c ∈ gc.configs := List.get_mem _ _
        have huniq := gc.unique_privileged c hmem_cfg
        have hpriv_m := gcMover_priv gc ⟨k, hk⟩
        have hnp : ¬privileged ⟨rs2222, f⟩ c (⟨p, hp_range⟩ : Fin 4) := by
          intro hp
          exact hpfin (huniq.unique hp hpriv_m)
        -- ¬privileged means f_p(L,S,R) = c_p
        unfold privileged at hnp; push_neg at hnp
        -- hnp : f ⟨p,...⟩ (c (left ...)) (c ...) (c (right ...)) = c ⟨p,...⟩
        -- Chain: entry.2 = getBit enc p = (c ⟨p,...⟩).val = f(...).val
        have hgb := getBit_encCfg c ⟨p, hp_range⟩
        rw [Fin.ext_iff] at hnp
        rw [hval, hgb]; exact hnp.symm

/-- Every entry in collectTF of the encoded cycle corresponds to a valid
    constraint on f: either a mover constraint or a non-mover constraint.

    Specifically, entry.2 = f_j(c(left j), c(j), c(right j)).val where j and c
    come from a cycle step, and entry.1 = tfKeyNat (encCfg c) j.val.  -/
private theorem collectTF_valid (gc : GoodCycle ⟨rs2222, f⟩)
    (entry : Nat × Nat)
    (hmem : entry ∈ collectTF (gcPathN gc gc.configs.length (le_refl _))) :
    ∃ (k : Fin gc.configs.length) (j : Fin 4),
      entry.1 = tfKeyNat (encCfg (gc.configs.get k)).val j.val ∧
      entry.2 = ((⟨rs2222, f⟩ : System).f j
        ((gc.configs.get k) (left j)) ((gc.configs.get k) j)
        ((gc.configs.get k) (right j))).val := by
  -- Induct on L = gc.configs.length, building gcPathN step by step
  suffices h : ∀ (L : Nat) (hL : L ≤ gc.configs.length),
      entry ∈ collectTF (gcPathN gc L hL) →
      ∃ (k : Fin gc.configs.length) (j : Fin 4),
        entry.1 = tfKeyNat (encCfg (gc.configs.get k)).val j.val ∧
        entry.2 = ((⟨rs2222, f⟩ : System).f j
          ((gc.configs.get k) (left j)) ((gc.configs.get k) j)
          ((gc.configs.get k) (right j))).val from
    h gc.configs.length (le_refl _) hmem
  intro L hL hmemL
  induction L with
  | zero => simp [gcPathN, collectTF] at hmemL
  | succ n ih =>
    -- gcPathN gc (n+1) = gcPathN gc n ++ [(enc_n, m_n)]
    rw [gcPathN] at hmemL
    rw [collectTF_append] at hmemL
    rw [List.mem_append] at hmemL
    cases hmemL with
    | inl h_old =>
      -- entry comes from the first n steps
      exact ih (by omega) h_old
    | inr h_new =>
      -- entry comes from the new single step
      obtain ⟨j, hkey, hval⟩ := collectTF_single_valid gc n (by omega) entry h_new
      exact ⟨⟨n, by omega⟩, j, hkey, hval⟩

/-- TF conflict in the encoded cycle → contradiction with f being a function. -/
private theorem isTFBlocked_sound (gc : GoodCycle ⟨rs2222, f⟩)
    (h : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = true) : False := by
  -- isTFBlocked finds two entries with same key but different values.
  unfold isTFBlocked at h
  unfold hasTFConflict at h
  -- Extract conflicting entries
  rw [List.any_eq_true] at h
  obtain ⟨⟨k1, v1⟩, hm1, h1⟩ := h
  rw [List.any_eq_true] at h1
  obtain ⟨⟨k2, v2⟩, hm2, h2⟩ := h1
  -- h2 : (k1 == k2 && !(v1 == v2)) = true
  have ⟨h2a, h2b⟩ := Bool.and_eq_true_iff.mp h2
  have hkeq : k1 = k2 := beq_iff_eq.mp h2a
  have hveq : v1 ≠ v2 := by
    intro heq; subst heq
    simp at h2b
  -- Both entries are valid constraints on f
  obtain ⟨step1, j1, hkey1, hval1⟩ := collectTF_valid gc (k1, v1) hm1
  obtain ⟨step2, j2, hkey2, hval2⟩ := collectTF_valid gc (k2, v2) hm2
  -- Same key means same proc and TF context
  -- The key = proc * 8 + L * 4 + S * 2 + R uniquely determines (proc, L, S, R)
  -- So j1 = j2 and the TF contexts match.
  -- Then f evaluated on the same args gives both v1 and v2, with v1 ≠ v2.
  simp only [Prod.fst, Prod.snd] at hkey1 hkey2 hval1 hval2
  rw [hkey1, hkey2] at hkeq
  -- From hkeq, derive j1 = j2 and matching TF contexts, then f outputs match.
  -- Unfold tfKeyNat in hkeq
  simp only [tfKeyNat] at hkeq
  -- getBit bounds: each getBit value is ≤ 1
  have hgb (cfg j : Nat) : getBit cfg j ≤ 1 := by
    simp only [getBit]; exact Nat.and_le_right
  -- Proc and bound values from both steps
  have hj1 := j1.isLt
  have hj2 := j2.isLt
  have hL1 := hgb (encCfg (gc.configs.get step1)).val (leftP j1.val)
  have hS1 := hgb (encCfg (gc.configs.get step1)).val j1.val
  have hR1 := hgb (encCfg (gc.configs.get step1)).val (rightP j1.val)
  have hL2 := hgb (encCfg (gc.configs.get step2)).val (leftP j2.val)
  have hS2 := hgb (encCfg (gc.configs.get step2)).val j2.val
  have hR2 := hgb (encCfg (gc.configs.get step2)).val (rightP j2.val)
  -- From the encoding equality and bounds, derive component equalities
  have heqj : j1.val = j2.val := by omega
  have heqL : getBit (encCfg (gc.configs.get step1)).val (leftP j1.val) =
              getBit (encCfg (gc.configs.get step2)).val (leftP j2.val) := by omega
  have heqS : getBit (encCfg (gc.configs.get step1)).val j1.val =
              getBit (encCfg (gc.configs.get step2)).val j2.val := by omega
  have heqR : getBit (encCfg (gc.configs.get step1)).val (rightP j1.val) =
              getBit (encCfg (gc.configs.get step2)).val (rightP j2.val) := by omega
  -- Convert getBit equalities to Config equalities via getBit_encCfg
  have hj12 : j1 = j2 := Fin.ext heqj
  subst hj12
  -- Now j1 = j2. Convert getBit to config values.
  -- getBit (encCfg c).val p.val = (c p).val (from getBit_encCfg)
  -- So equal getBit → equal config values → equal f inputs → equal f outputs
  -- → v1 = v2 → contradiction with hveq
  rw [hval1, hval2] at hveq
  apply hveq
  -- f applied to same args gives same result. Show the args match.
  -- Convert getBit to config values via leftP_eq_left, rightP_eq_right, getBit_encCfg
  have hL1' : getBit (encCfg (gc.configs.get step1)).val (leftP j1.val) =
    (gc.configs.get step1 (left j1)).val := by
    rw [leftP_eq_left, getBit_encCfg]
  have hL2' : getBit (encCfg (gc.configs.get step2)).val (leftP j1.val) =
    (gc.configs.get step2 (left j1)).val := by
    rw [leftP_eq_left, getBit_encCfg]
  have hS1' : getBit (encCfg (gc.configs.get step1)).val j1.val =
    (gc.configs.get step1 j1).val := getBit_encCfg _ j1
  have hS2' : getBit (encCfg (gc.configs.get step2)).val j1.val =
    (gc.configs.get step2 j1).val := getBit_encCfg _ j1
  have hR1' : getBit (encCfg (gc.configs.get step1)).val (rightP j1.val) =
    (gc.configs.get step1 (right j1)).val := by
    rw [rightP_eq_right, getBit_encCfg]
  have hR2' : getBit (encCfg (gc.configs.get step2)).val (rightP j1.val) =
    (gc.configs.get step2 (right j1)).val := by
    rw [rightP_eq_right, getBit_encCfg]
  -- Now derive Config-level equalities
  have hLeq : gc.configs.get step1 (left j1) = gc.configs.get step2 (left j1) :=
    Fin.ext (by rw [← hL1', ← hL2']; exact heqL)
  have hSeq : gc.configs.get step1 j1 = gc.configs.get step2 j1 :=
    Fin.ext (by rw [← hS1', ← hS2']; exact heqS)
  have hReq : gc.configs.get step1 (right j1) = gc.configs.get step2 (right j1) :=
    Fin.ext (by rw [← hR1', ← hR2']; exact heqR)
  -- f with same args gives same result
  rw [hLeq, hSeq, hReq]

/-- Helper to handle the buildTF if-then-else after match on assocLookup. -/
private theorem buildTF_step_some (hv v' : Nat) (tl : List (Nat × Nat))
    (acc result : List (Nat × Nat))
    (hbuild : (if hv == v' then buildTF tl acc else none) = some result) :
    buildTF tl acc = some result := by
  cases h : (hv == v') <;> simp [h] at hbuild <;> exact hbuild

/-- assocLookup found in acc is preserved by buildTF. -/
private theorem buildTF_preserves (entries acc result : List (Nat × Nat))
    (hbuild : buildTF entries acc = some result)
    (k v : Nat) (hlook : assocLookup k acc = some v) :
    assocLookup k result = some v := by
  induction entries generalizing acc with
  | nil => simp [buildTF] at hbuild; subst hbuild; exact hlook
  | cons hd tl ih =>
    simp only [buildTF] at hbuild
    cases hm : assocLookup hd.1 acc <;> rw [hm] at hbuild
    · -- none: buildTF tl ((hd.1, hd.2) :: acc) = some result
      apply ih ((hd.1, hd.2) :: acc) hbuild
      simp only [assocLookup]
      cases hkk : (hd.1 == k) <;> simp [hkk]
      · exact hlook
      · rw [beq_iff_eq] at hkk; subst hkk; rw [hm] at hlook
        simp at hlook
    · -- some: if hd.2 == v' then buildTF tl acc else none = some result
      exact ih acc (buildTF_step_some hd.2 _ tl acc result hbuild) hlook

/-- buildTF maps each input entry's key to its value in the result. -/
private theorem buildTF_sound (entries acc result : List (Nat × Nat))
    (hbuild : buildTF entries acc = some result)
    (k v : Nat) (hmem : (k, v) ∈ entries) :
    assocLookup k result = some v := by
  induction entries generalizing acc with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [buildTF] at hbuild
    rw [List.mem_cons] at hmem
    cases hm : assocLookup hd.1 acc <;> rw [hm] at hbuild
    · -- none: buildTF tl ((hd.1, hd.2) :: acc) = some result
      cases hmem with
      | inl heq =>
        have hkeq := congrArg Prod.fst heq; simp at hkeq; subst hkeq
        have hveq := congrArg Prod.snd heq; simp at hveq; subst hveq
        apply buildTF_preserves tl ((hd.1, hd.2) :: acc) result hbuild hd.1 hd.2
        simp only [assocLookup]
        simp [beq_self_eq_true]
      | inr hmem_tl => exact ih ((hd.1, hd.2) :: acc) hbuild hmem_tl
    · -- some v': if hd.2 == v' then buildTF tl acc else none = some result
      rename_i v'
      have hbuild' := buildTF_step_some hd.2 v' tl acc result hbuild
      cases hmem with
      | inl heq =>
        have hkeq := congrArg Prod.fst heq; simp at hkeq; subst hkeq
        have hveq := congrArg Prod.snd heq; simp at hveq; subst hveq
        -- hd.2 == v' must be true (from buildTF_step_some)
        -- so hd.2 = v', and assocLookup hd.1 acc = some v' = some hd.2
        have : (hd.2 == v') = true := by
          by_contra h; push_neg at h
          cases hh : (hd.2 == v') <;> simp [hh] at hbuild h
        rw [beq_iff_eq.mp this]
        exact buildTF_preserves tl acc result hbuild' hd.1 v' hm
      | inr hmem_tl => exact ih acc hbuild' hmem_tl

/-- Find a forced target from a complement config using tfMap.
    Returns some target if cfg has a privileged proc whose target is in complement. -/
def findForcedTarget (tfMap : List (Nat × Nat)) (cycleMask : Nat) (cfg : Nat) : Option (Nat × Nat) :=
  (List.range 4).foldl (fun acc proc =>
    match acc with
    | some r => some r
    | none =>
      match assocLookup (tfKeyNat cfg proc) tfMap with
      | some val =>
        if val != getBit cfg proc then
          let target := flipBit cfg proc
          if (cycleMask >>> target) &&& 1 == 0 then some (target, proc)
          else none
        else none
      | none => none) none

/-- Follow forced moves for fuel steps. Returns true if a cycle is detected. -/
def followForced (tfMap : List (Nat × Nat)) (cycleMask : Nat) :
    Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, visited =>
    if (visited >>> cfg) &&& 1 == 1 then true
    else match findForcedTarget tfMap cycleMask cfg with
      | none => false
      | some (target, _) =>
        followForced tfMap cycleMask fuel target (visited ||| (1 <<< cfg))

/-- Check for an explicit bad cycle: from any complement config, follow forced
    moves and check if we revisit (cycle in complement → badStep cycle). -/
def hasExplicitBadCycle (cycle : List (Nat × Nat)) : Bool :=
  match buildTF (collectTF cycle) [] with
  | none => true
  | some tfMap =>
    let cycleMask := cycle.foldl (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0
    (List.range 16).any (fun cfg =>
      if (cycleMask >>> cfg) &&& 1 == 1 then false
      else followForced tfMap cycleMask 17 cfg 0)

/-- V2 blocking check: TF conflict or explicit bad cycle. -/
def isBlockedV2 (cycle : List (Nat × Nat)) : Bool :=
  isTFBlocked cycle || hasExplicitBadCycle cycle

def dfsBlockedV2 : Nat → Nat → Nat → Nat → List (Nat × Nat) → Nat → Bool
  | 0, _, _, _, _, _ => true
  | fuel + 1, start, cur, visited, path, fairMask =>
    (List.range 4).all (fun proc =>
      let next := flipBit cur proc
      let newFair := fairMask ||| (1 <<< proc)
      let newPath := path ++ [(cur, proc)]
      if next == start then
        if newFair == 15 then isBlockedV2 newPath
        else true
      else if (visited >>> next) &&& 1 == 1 then true
      else dfsBlockedV2 fuel start next (visited ||| (1 <<< next)) newPath newFair)

def allQ4CyclesBlockedV2 : Bool :=
  (List.range 16).all (fun s => dfsBlockedV2 16 s s (1 <<< s) [] 0)

/-- All fair Q₄ cycles are blocked by TF conflict or explicit bad cycle. -/
theorem allQ4CyclesBlockedV2_eq_true : allQ4CyclesBlockedV2 = true := by native_decide

private def wordFromChoiceFun4 (a : Proc4) (ds : Fin 15 → Bool) : Word4 :=
  wordFromChoices4 a (List.ofFn ds)

private theorem hasExplicitBadCycle_of_wordFromChoiceFun4_len15_count4
    (bits0 : Proc4 → Bool) (a : Proc4) (ds : Fin 15 → Bool)
    (hcount : ∀ j : Proc4, (wordFromChoiceFun4 a ds).count j = 4) :
    hasExplicitBadCycle (pathFromWord4 bits0 (wordFromChoiceFun4 a ds)) = true := by
  revert bits0 a ds hcount
  native_decide

private theorem hasExplicitBadCycle_of_wordFromChoices4_len15_count4
    (bits0 : Proc4 → Bool) (a : Proc4) (ds : List Bool)
    (hds : ds.length = 15)
    (hcount : ∀ j : Proc4, (wordFromChoices4 a ds).count j = 4) :
    hasExplicitBadCycle (pathFromWord4 bits0 (wordFromChoices4 a ds)) = true := by
  let dsf : Fin 15 → Bool := fun i => ds.get (Fin.cast hds.symm i)
  have hds_eq : List.ofFn dsf = ds := by
    have htmp : ds = List.ofFn dsf := by
      rw [← List.ofFn_get ds]
      simpa [dsf] using (List.ofFn_congr hds (List.get ds))
    exact htmp.symm
  have hw : wordFromChoiceFun4 a dsf = wordFromChoices4 a ds := by
    change wordFromChoices4 a (List.ofFn dsf) = wordFromChoices4 a ds
    rw [hds_eq]
  have hcount' : ∀ j : Proc4, (wordFromChoiceFun4 a dsf).count j = 4 := by
    intro j
    rw [hw]
    exact hcount j
  rw [← hw]
  exact hasExplicitBadCycle_of_wordFromChoiceFun4_len15_count4 bits0 a dsf hcount'

/-- One-step DFS extraction for V2. -/
private theorem dfs_branchV2 (fuel start cur visited : Nat) (path : List (Nat × Nat))
    (fairMask proc : Nat) (hproc : proc < 4)
    (hdfs : dfsBlockedV2 (fuel + 1) start cur visited path fairMask = true) :
    let next := flipBit cur proc
    let newPath := path ++ [(cur, proc)]
    let newFair := fairMask ||| (1 <<< proc)
    (next = start → newFair = 15 → isBlockedV2 newPath = true) ∧
    (next ≠ start → (visited >>> next) &&& 1 = 0 →
      dfsBlockedV2 fuel start next (visited ||| (1 <<< next)) newPath newFair = true) := by
  simp only [dfsBlockedV2] at hdfs
  have hb := (List.all_eq_true).mp hdfs proc (List.mem_range.mpr hproc)
  constructor
  · intro heq hfair
    have h1 : (flipBit cur proc == start) = true := beq_iff_eq.mpr heq
    have h2 : (fairMask ||| 1 <<< proc == 15) = true := beq_iff_eq.mpr hfair
    simp only [h1, h2, ite_true] at hb; exact hb
  · intro hne hvis
    have h1 : (flipBit cur proc == start) = false := beq_eq_false_iff_ne.mpr hne
    have h2 : ((visited >>> flipBit cur proc) &&& 1 == 1) = false :=
      beq_eq_false_iff_ne.mpr (by omega)
    simp only [h1, h2, ite_false, Bool.false_eq_true, ↓reduceIte] at hb
    exact hb

/-- V2 DFS starting from enc(c₀). -/
private theorem dfs_startV2 (gc : GoodCycle ⟨rs2222, f⟩) :
    dfsBlockedV2 16
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (1 <<< (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val)
      []
      0 = true := by
  have h := allQ4CyclesBlockedV2_eq_true
  unfold allQ4CyclesBlockedV2 at h
  exact (List.all_eq_true).mp h
    (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
    (List.mem_range.mpr (gcEnc_lt_16 gc ⟨0, gc_len_ge_1 gc⟩))

/-- V2 DFS follows the GoodCycle (same structure as dfs_follows_gc but with V2). -/
private theorem dfs_follows_gcV2 (gc : GoodCycle ⟨rs2222, f⟩)
    (rem k : Nat) (hk : k < gc.configs.length) (hrem : rem + k + 1 = gc.configs.length)
    (fuel : Nat) (hfuel : rem + 1 ≤ fuel)
    (hdfs : dfsBlockedV2 fuel
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨k, hk⟩)).val
      (gcMask gc (k + 1) (by omega))
      (gcPathN gc k (by omega))
      (gcFair gc k (by omega)) = true) :
    isBlockedV2 (gcPathN gc gc.configs.length (le_refl _)) = true := by
  induction rem generalizing k fuel with
  | zero =>
    have hkL : k + 1 = gc.configs.length := by omega
    have hproc := gcMover_lt_4 gc ⟨k, hk⟩
    have hfuelp : fuel = fuel - 1 + 1 := by omega
    rw [hfuelp] at hdfs
    have hbr := dfs_branchV2 (fuel - 1)
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨k, hk⟩)).val
      (gcMask gc (k + 1) (by omega))
      (gcPathN gc k (by omega))
      (gcFair gc k (by omega))
      (gcMover gc ⟨k, hk⟩).val
      hproc hdfs
    have hni : nextIndex gc.configs ⟨k, hk⟩ = ⟨0, gc_len_ge_1 gc⟩ := by
      simp only [nextIndex, hkL, Nat.mod_self]
    have hnext : flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val =
        (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val := by
      rw [← gcEnc_step gc ⟨k, hk⟩, hni]
    have hblocked := hbr.1 hnext
    have hfair : gcFair gc k (by omega) ||| (1 <<< (gcMover gc ⟨k, hk⟩).val) = 15 := by
      have h1 := gcFair_succ gc k hk
      rw [← h1]
      rw [gcFair_eq gc (k + 1) gc.configs.length (by omega) (le_refl _) hkL]
      exact gcFair_complete gc
    have hblocked := hblocked hfair
    have hpath1 := gcPathN_succ gc k hk
    rw [← hpath1] at hblocked
    rw [gcPathN_eq gc (k + 1) gc.configs.length (by omega) (le_refl _) hkL] at hblocked
    exact hblocked
  | succ rem' ih =>
    have hproc := gcMover_lt_4 gc ⟨k, hk⟩
    have hfuelp : fuel = (fuel - 1) + 1 := by omega
    rw [hfuelp] at hdfs
    have hbr := dfs_branchV2 (fuel - 1)
      (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val
      (encCfg (gc.configs.get ⟨k, hk⟩)).val
      (gcMask gc (k + 1) (by omega))
      (gcPathN gc k (by omega))
      (gcFair gc k (by omega))
      (gcMover gc ⟨k, hk⟩).val
      hproc hdfs
    have hk1 : k + 1 < gc.configs.length := by omega
    have hni : nextIndex gc.configs ⟨k, hk⟩ = ⟨k + 1, hk1⟩ := by
      simp only [nextIndex, Nat.mod_eq_of_lt hk1]
    have hnext_eq : flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val =
        (encCfg (gc.configs.get ⟨k + 1, hk1⟩)).val := by
      rw [← gcEnc_step gc ⟨k, hk⟩, hni]
    have hne_start : flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val ≠
        (encCfg (gc.configs.get ⟨0, gc_len_ge_1 gc⟩)).val := by
      rw [hnext_eq]
      apply gcEnc_ne gc ⟨k + 1, hk1⟩ ⟨0, gc_len_ge_1 gc⟩
      intro h; simp [Fin.ext_iff] at h
    have hunvis : (gcMask gc (k + 1) (by omega) >>>
        flipBit (encCfg (gc.configs.get ⟨k, hk⟩)).val (gcMover gc ⟨k, hk⟩).val) &&& 1 = 0 := by
      rw [hnext_eq]
      exact gcMask_unset gc (k + 1) (by omega) (k + 1) hk1 (by omega)
    have hdfs' := hbr.2 hne_start hunvis
    rw [hnext_eq] at hdfs'
    have hmask_eq : gcMask gc (k + 1) (by omega) |||
        (1 <<< (encCfg (gc.configs.get ⟨k + 1, hk1⟩)).val) =
        gcMask gc (k + 2) (by omega) := by
      rw [gcMask_succ gc (k + 1) hk1]
    have hpath_eq : gcPathN gc k (by omega) ++
        [((encCfg (gc.configs.get ⟨k, hk⟩)).val, (gcMover gc ⟨k, hk⟩).val)] =
        gcPathN gc (k + 1) (by omega) := by
      rw [gcPathN_succ gc k hk]
    have hfair_eq : gcFair gc k (by omega) ||| (1 <<< (gcMover gc ⟨k, hk⟩).val) =
        gcFair gc (k + 1) (by omega) := by
      rw [gcFair_succ gc k hk]
    rw [hmask_eq, hpath_eq, hfair_eq] at hdfs'
    exact ih (k + 1) hk1 (by omega) (fuel - 1) (by omega) hdfs'

/-- The V2-encoded GoodCycle is blocked. -/
private theorem gc_encoded_blockedV2 (gc : GoodCycle ⟨rs2222, f⟩) :
    isBlockedV2 (gcPathN gc gc.configs.length (le_refl _)) = true := by
  have hstart := dfs_startV2 gc
  have hlen := gc_len_ge_1 gc
  have hle16 := gc_len_le_16 gc
  have hrem : gc.configs.length - 1 + 0 + 1 = gc.configs.length := by omega
  have hfuel : gc.configs.length - 1 + 1 ≤ 16 := by omega
  have hp : ([] : List (Nat × Nat)) = gcPathN gc 0 (by omega) := by simp [gcPathN]
  have hf : (0 : Nat) = gcFair gc 0 (by omega) := by simp [gcFair]
  have hv : (1 <<< (encCfg (gc.configs.get ⟨0, hlen⟩)).val) =
      gcMask gc 1 hlen := by simp [gcMask]
  have hstart' : dfsBlockedV2 16
      (encCfg (gc.configs.get ⟨0, hlen⟩)).val
      (encCfg (gc.configs.get ⟨0, hlen⟩)).val
      (gcMask gc 1 hlen)
      (gcPathN gc 0 (by omega))
      (gcFair gc 0 (by omega)) = true := by
    rwa [← hv, ← hp, ← hf]
  exact dfs_follows_gcV2 gc (gc.configs.length - 1) 0 hlen hrem 16 hfuel hstart'

/-- cycleMask bit set ↔ config is in gc.configs. Specifically:
    bit n is set in cycleMask iff decCfg n ∈ gc.configs (for n < 16). -/
private theorem cycleMask_bit_iff_mem (gc : GoodCycle ⟨rs2222, f⟩)
    (cycleMask : Nat)
    (hcm : cycleMask = (gcPathN gc gc.configs.length (le_refl _)).foldl
      (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0)
    (n : Nat) (hn : n < 16) :
    ((cycleMask >>> n) &&& 1 = 1) ↔ (decCfg ⟨n, hn⟩ ∈ gc.configs) := by
  -- gcPathN gc L le_refl contains ((encCfg c_k).val, (gcMover gc k).val) for k ∈ {0,..,L-1}
  -- cycleMask = foldl over these, ORing (1 <<< cfg) for each (cfg, _)
  -- So bit n is set iff n = (encCfg c_k).val for some k.
  -- And decCfg ⟨n, _⟩ ∈ gc.configs iff n = (encCfg c_k).val for some k (via enc_dec/dec_enc).
  subst hcm
  -- First, show that the foldl over gcPathN sets exactly the bits for encoded configs.
  -- We prove both directions via a general lemma about foldl ||| over gcPathN.
  suffices hfold : ∀ (L : Nat) (hL : L ≤ gc.configs.length) (init : Nat),
      (((gcPathN gc L hL).foldl (fun mask (cfg, _) => mask ||| (1 <<< cfg)) init >>> n) &&& 1 = 1)
      ↔ ((init >>> n) &&& 1 = 1 ∨ ∃ k : Fin gc.configs.length, k.val < L ∧
          n = (encCfg (gc.configs.get k)).val) by
    rw [hfold gc.configs.length (le_refl _) 0]
    constructor
    · -- (→): bit set → decCfg in configs
      rintro (habs | ⟨k, _, hkn⟩)
      · -- 0 >>> n &&& 1 = 1 is absurd
        simp at habs
      · -- n = encCfg(c_k).val, so decCfg ⟨n, hn⟩ = decCfg (encCfg c_k) = c_k
        have : decCfg ⟨n, hn⟩ = gc.configs.get k := by
          have heq : (⟨n, hn⟩ : Fin 16) = encCfg (gc.configs.get k) := Fin.ext hkn
          rw [heq, dec_enc]
        rw [this]; exact List.get_mem _ _
    · -- (←): decCfg in configs → bit set
      intro hmem
      right
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
      refine ⟨k, k.isLt, ?_⟩
      have := congr_arg encCfg hk
      rw [enc_dec] at this
      exact (Fin.ext_iff.mp this).symm
  intro L
  induction L with
  | zero =>
    intro hL init; simp only [gcPathN, List.foldl_nil]
    constructor
    · intro h; left; exact h
    · rintro (h | ⟨k, hkL, _⟩); exact h; omega
  | succ m ih =>
    intro hL init
    rw [gcPathN, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [shr_and1_eq_one]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    rw [← shr_and1_eq_one]
    rw [ih (by omega) init]
    constructor
    · -- (→)
      rintro ((h | ⟨k, hkL, hkn⟩) | hbit)
      · left; exact h
      · right; exact ⟨k, by omega, hkn⟩
      · -- bit set from the new entry at position m
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hbit
        simp only [decide_eq_true_eq] at hbit
        right; refine ⟨⟨m, by omega⟩, ?_, hbit.symm⟩; simp
    · -- (←)
      rintro (h | ⟨k, hkL, hkn⟩)
      · left; left; exact h
      · by_cases hkm : k.val < m
        · left; right; exact ⟨k, hkm, hkn⟩
        · have hm_lt : m < gc.configs.length := by omega
          have hk_val : k.val = m := by omega
          have hkeq : k = ⟨m, hm_lt⟩ := Fin.ext hk_val
          right
          rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
          simp only [decide_eq_true_eq]
          rw [hkn, hkeq]


/-- Helper: foldl with some acc always returns that some value. -/
private theorem foldl_some_propagate (tfMap : List (Nat × Nat)) (cycleMask cfg : Nat)
    (procs : List Nat) (r : Nat × Nat) :
    procs.foldl (fun acc proc =>
      match acc with
      | some r => some r
      | none =>
        match assocLookup (tfKeyNat cfg proc) tfMap with
        | some val =>
          if val != getBit cfg proc then
            let target := flipBit cfg proc
            if (cycleMask >>> target) &&& 1 == 0 then some (target, proc)
            else none
          else none
        | none => none) (some r) = some r := by
  induction procs with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl]; exact ih

/-- Helper: the one-step function applied when acc = none. -/
private def fftStep (tfMap : List (Nat × Nat)) (cycleMask cfg proc : Nat) : Option (Nat × Nat) :=
  match assocLookup (tfKeyNat cfg proc) tfMap with
  | some val =>
    if val != getBit cfg proc then
      let target := flipBit cfg proc
      if (cycleMask >>> target) &&& 1 == 0 then some (target, proc)
      else none
    else none
  | none => none

/-- When fftStep returns some, the match conditions hold. -/
private theorem fftStep_sound (tfMap : List (Nat × Nat)) (cycleMask cfg proc target proc' : Nat)
    (h : fftStep tfMap cycleMask cfg proc = some (target, proc')) :
    proc' = proc ∧
    ∃ val, assocLookup (tfKeyNat cfg proc) tfMap = some val ∧
      val ≠ getBit cfg proc ∧
      target = flipBit cfg proc ∧
      (cycleMask >>> target) &&& 1 = 0 := by
  unfold fftStep at h
  cases hlook : assocLookup (tfKeyNat cfg proc) tfMap with
  | none =>
    simp [hlook] at h
  | some val =>
    by_cases hne : val = getBit cfg proc
    · have hbne : (val != getBit cfg proc) = false := bne_eq_false_iff_eq.mpr hne
      simp [hlook, hbne] at h
    · have hbne : (val != getBit cfg proc) = true := bne_iff_ne.mpr hne
      by_cases hcm : (cycleMask >>> flipBit cfg proc) &&& 1 = 0
      · have hbeq : ((cycleMask >>> flipBit cfg proc) &&& 1 == 0) = true :=
          beq_iff_eq.mpr hcm
        have hsimp : (cycleMask >>> flipBit cfg proc) &&& 1 = 0 ∧
            flipBit cfg proc = target ∧ proc = proc' := by
          simpa [fftStep, hlook, hbne, hbeq] using h
        rcases hsimp with ⟨_, ht, hp⟩
        refine ⟨hp.symm, ?_⟩
        refine ⟨val, rfl, hne, ht.symm, ?_⟩
        simpa [ht] using hcm
      · have hbeq : ((cycleMask >>> flipBit cfg proc) &&& 1 == 0) = false :=
          beq_eq_false_iff_ne.mpr hcm
        have hsimp : (cycleMask >>> flipBit cfg proc) &&& 1 = 0 ∧
            flipBit cfg proc = target ∧ proc = proc' := by
          simpa [fftStep, hlook, hbne, hbeq] using h
        exact (hcm hsimp.1).elim

/-- Characterization: foldl starting from none returns some iff some step matched. -/
private theorem findForcedTarget_foldl_sound
    (tfMap : List (Nat × Nat)) (cycleMask cfg : Nat) (procs : List Nat)
    (target proc : Nat)
    (hff : procs.foldl (fun acc p =>
      match acc with
      | some r => some r
      | none => fftStep tfMap cycleMask cfg p) none = some (target, proc)) :
    proc ∈ procs ∧
    (∃ val, assocLookup (tfKeyNat cfg proc) tfMap = some val ∧
      val ≠ getBit cfg proc ∧
      target = flipBit cfg proc ∧
      (cycleMask >>> target) &&& 1 = 0) := by
  induction procs with
  | nil => simp [List.foldl] at hff
  | cons p ps ih =>
    simp only [List.foldl] at hff
    cases hstep : fftStep tfMap cycleMask cfg p with
    | none =>
      rw [hstep] at hff
      have ⟨hpm, hconds⟩ := ih hff
      exact ⟨List.mem_cons.mpr (Or.inr hpm), hconds⟩
    | some r =>
      rw [hstep] at hff
      have hprop : ∀ (r' : Nat × Nat) (qs : List Nat),
          qs.foldl (fun acc q =>
            match acc with
            | some r => some r
            | none => fftStep tfMap cycleMask cfg q) (some r') = some r' := by
        intro r' qs
        induction qs with
        | nil => rfl
        | cons _ _ ih_qs => simp only [List.foldl]; exact ih_qs
      rw [hprop] at hff
      have hinj : r = (target, proc) := Option.some.inj hff
      rw [hinj] at hstep
      have ⟨hp_eq, hconds⟩ := fftStep_sound tfMap cycleMask cfg p target proc hstep
      cases hp_eq
      exact ⟨List.mem_cons.mpr (Or.inl rfl), hconds⟩

/-- buildTF result lookup traces back to entries or acc. -/
private theorem buildTF_lookup_source (entries acc result : List (Nat × Nat))
    (hb : buildTF entries acc = some result) (k v : Nat)
    (hl : assocLookup k result = some v) :
    (∃ e ∈ entries, e.1 = k ∧ e.2 = v) ∨ assocLookup k acc = some v := by
  induction entries generalizing acc with
  | nil =>
    simp [buildTF] at hb
    subst hb
    exact Or.inr hl
  | cons hd tl ih =>
    unfold buildTF at hb
    cases hm : assocLookup hd.1 acc with
    | none =>
      rw [hm] at hb
      have hrec := ih ((hd.1, hd.2) :: acc) hb
      rcases hrec with ⟨e, he_mem, he_key, he_val⟩ | hacc
      ·
        exact Or.inl ⟨e, List.mem_cons.mpr (Or.inr he_mem), he_key, he_val⟩
      ·
        unfold assocLookup at hacc
        by_cases hkh : hd.1 == k
        · left
          rw [beq_iff_eq] at hkh
          refine ⟨hd, List.mem_cons.mpr (Or.inl rfl), hkh, ?_⟩
          simp [hkh] at hacc
          exact hacc
        · right
          simp [hkh] at hacc
          exact hacc
    | some v' =>
      rw [hm] at hb
      have hb' := buildTF_step_some hd.2 v' tl acc result hb
      have hrec := ih acc hb'
      rcases hrec with ⟨e, he_mem, he_key, he_val⟩ | hacc
      ·
        exact Or.inl ⟨e, List.mem_cons.mpr (Or.inr he_mem), he_key, he_val⟩
      ·
        by_cases hkh : hd.1 = k
        · left
          rw [← hkh] at hacc
          rw [hm] at hacc
          have hv : v' = v := Option.some.inj hacc
          have hd2v : hd.2 = v' := by
            by_contra h_ne
            have : (hd.2 == v') = false := beq_eq_false_iff_ne.mpr h_ne
            simp [this] at hb
          refine ⟨hd, List.mem_cons.mpr (Or.inl rfl), hkh, ?_⟩
          exact hd2v.trans hv
        · exact Or.inr hacc

/-- findForcedTarget soundness: when it returns some (target, proc), proc is
    privileged at decCfg cfg and target = flipBit cfg proc, with target in complement. -/
private theorem findForcedTarget_sound (gc : GoodCycle ⟨rs2222, f⟩)
    (tfMap : List (Nat × Nat))
    (hbuild : buildTF (collectTF (gcPathN gc gc.configs.length (le_refl _))) [] = some tfMap)
    (cycleMask : Nat)
    (hcm : cycleMask = (gcPathN gc gc.configs.length (le_refl _)).foldl
      (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0)
    (cfg : Nat) (hcfg : cfg < 16) (target proc : Nat)
    (hff : findForcedTarget tfMap cycleMask cfg = some (target, proc))
    (hcomp : (cycleMask >>> cfg) &&& 1 = 0) :
    proc < 4 ∧ target = flipBit cfg proc ∧ target < 16 ∧
    (cycleMask >>> target) &&& 1 = 0 ∧
    ∀ (hp4 : proc < 4), privileged ⟨rs2222, f⟩ (decCfg ⟨cfg, hcfg⟩) ⟨proc, hp4⟩ := by
  -- Connect findForcedTarget to fftStep-based foldl
  have hff_eq : findForcedTarget tfMap cycleMask cfg =
      (List.range 4).foldl (fun acc p =>
        match acc with
        | some r => some r
        | none => fftStep tfMap cycleMask cfg p) none := by
    simp only [findForcedTarget, fftStep]
  rw [hff_eq] at hff
  have ⟨hmem, val, hlook, hne, htarget, hcmask⟩ :=
    findForcedTarget_foldl_sound tfMap cycleMask cfg (List.range 4) target proc hff
  have hp4 : proc < 4 := List.mem_range.mp hmem
  refine ⟨hp4, htarget, ?_, hcmask, ?_⟩
  · rw [htarget]
    have henc :
        flipBit cfg proc =
          (encCfg (flipCfg (decCfg ⟨cfg, hcfg⟩) ⟨proc, hp4⟩)).val := by
      rw [encCfg_flipCfg, enc_dec]
      rfl
    rw [henc]
    exact (encCfg (flipCfg (decCfg ⟨cfg, hcfg⟩) ⟨proc, hp4⟩)).isLt
  · -- privileged
    intro hp4'
    rcases buildTF_lookup_source _ _ _ hbuild (tfKeyNat cfg proc) val hlook with
      ⟨e, he_mem, he_key, he_val⟩ | hacc
    ·
      have ⟨step, j, hkey_j, hval_j⟩ := collectTF_valid gc e he_mem
      rw [he_key] at hkey_j
      -- Decode tfKeyNat equality to get j = proc and matching contexts
      simp only [tfKeyNat] at hkey_j
      have hgb (c j : Nat) : getBit c j ≤ 1 := by
        simp only [getBit]; exact Nat.and_le_right
      have hL1 := hgb cfg (leftP proc)
      have hS1 := hgb cfg proc
      have hR1 := hgb cfg (rightP proc)
      have hL2 := hgb (encCfg (gc.configs.get step)).val (leftP j.val)
      have hS2 := hgb (encCfg (gc.configs.get step)).val j.val
      have hR2 := hgb (encCfg (gc.configs.get step)).val (rightP j.val)
      have heqj : j.val = proc := by omega
      have heqL : getBit cfg (leftP proc) =
          getBit (encCfg (gc.configs.get step)).val (leftP j.val) := by omega
      have heqS : getBit cfg proc =
          getBit (encCfg (gc.configs.get step)).val j.val := by omega
      have heqR : getBit cfg (rightP proc) =
          getBit (encCfg (gc.configs.get step)).val (rightP j.val) := by omega
      have hj_eq : j = ⟨proc, hp4'⟩ := Fin.ext heqj
      subst hj_eq
      have hleft_proc : leftP proc = (left (⟨proc, hp4'⟩ : Fin 4)).val :=
        leftP_eq_left (⟨proc, hp4'⟩ : Fin 4)
      have hright_proc : rightP proc = (right (⟨proc, hp4'⟩ : Fin 4)).val :=
        rightP_eq_right (⟨proc, hp4'⟩ : Fin 4)
      rw [hleft_proc] at heqL
      rw [hright_proc] at heqR
      rw [getBit_encCfg] at heqL heqS heqR
      -- getBit cfg p = (decCfg cfg p).val
      have hdL : getBit cfg (left (⟨proc, hp4'⟩ : Fin 4)).val =
          (decCfg ⟨cfg, hcfg⟩ (left ⟨proc, hp4'⟩)).val := by
        simp only [decCfg, getBit]
      have hdS : getBit cfg proc = (decCfg ⟨cfg, hcfg⟩ ⟨proc, hp4'⟩).val := by
        simp only [decCfg, getBit]
      have hdR : getBit cfg (right (⟨proc, hp4'⟩ : Fin 4)).val =
          (decCfg ⟨cfg, hcfg⟩ (right ⟨proc, hp4'⟩)).val := by
        simp only [decCfg, getBit]
      -- c_step and decCfg cfg have same TF context at proc
      have hfL : (gc.configs.get step) (left ⟨proc, hp4'⟩) =
          (decCfg ⟨cfg, hcfg⟩) (left ⟨proc, hp4'⟩) :=
        Fin.ext (by rw [← heqL, ← hdL])
      have hfS : (gc.configs.get step) ⟨proc, hp4'⟩ =
          (decCfg ⟨cfg, hcfg⟩) ⟨proc, hp4'⟩ :=
        Fin.ext (by rw [← heqS, ← hdS])
      have hfR : (gc.configs.get step) (right ⟨proc, hp4'⟩) =
          (decCfg ⟨cfg, hcfg⟩) (right ⟨proc, hp4'⟩) :=
        Fin.ext (by rw [← heqR, ← hdR])
      rw [hfL, hfS, hfR] at hval_j
      rw [he_val] at hval_j
      -- hval_j : val = f(...).val, hne : val ≠ getBit cfg proc, hdS : getBit cfg proc = decCfg.val
      intro heq_priv
      rw [Fin.ext_iff] at heq_priv
      rw [← hval_j] at heq_priv
      rw [← hdS] at heq_priv
      exact hne heq_priv
    · simp [assocLookup] at hacc

private def listMask : List Nat → Nat
  | [] => 0
  | x :: xs => listMask xs ||| (1 <<< x)

private theorem listMask_snoc (xs : List Nat) (x : Nat) :
    listMask (xs ++ [x]) = listMask xs ||| (1 <<< x) := by
  induction xs with
  | nil =>
      simp [listMask]
  | cons y ys ih =>
      simp [listMask, ih, Nat.or_assoc, Nat.or_left_comm, Nat.or_comm]

private theorem listMask_bit_iff_mem : ∀ (xs : List Nat) (n : Nat),
    ((listMask xs >>> n) &&& 1 = 1) ↔ n ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro n
      simp [listMask]
  | cons x xs ih =>
      intro n
      constructor
      · intro h
        by_cases hxn : x = n
        · exact List.mem_cons.mpr (Or.inl hxn.symm)
        · have hrest : ((listMask xs >>> n) &&& 1 = 1) := by
            rw [shr_and1_eq_one] at h ⊢
            have hxbit : (1 <<< x).testBit n = false := by
              rw [Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne]
              intro hEq
              exact hxn hEq
            rw [listMask, Nat.testBit_or, hxbit, Bool.or_false] at h
            exact h
          exact List.mem_cons.mpr (Or.inr ((ih n).mp hrest))
      · intro h
        rw [List.mem_cons] at h
        cases h with
        | inl hxn =>
            subst hxn
            rw [listMask, shr_and1_eq_one, Nat.testBit_or,
              Nat.one_shiftLeft, Nat.testBit_two_pow_self]
            simp
        | inr hmem =>
            have hrest : ((listMask xs >>> n) &&& 1 = 1) := (ih n).mpr hmem
            rw [shr_and1_eq_one] at hrest ⊢
            rw [listMask, Nat.testBit_or]
            simp [hrest]

private def ForcedRel (tfMap : List (Nat × Nat)) (cycleMask : Nat) :
    Nat → Nat → Prop :=
  fun target cfg => ∃ proc, findForcedTarget tfMap cycleMask cfg = some (target, proc)

private def RChain {α : Type*} (r : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => r y x ∧ RChain r (y :: xs)

private theorem rchain_tail {α : Type*} {r : α → α → Prop} {x : α} {xs : List α}
    (h : RChain r (x :: xs)) : RChain r xs := by
  cases xs with
  | nil =>
      simp [RChain]
  | cons y ys =>
      simpa [RChain] using h.2

private theorem rchain_suffix {α : Type*} {r : α → α → Prop}
    {pref suff : List α} (hchain : RChain r (pref ++ suff)) :
    RChain r suff := by
  induction pref generalizing suff with
  | nil =>
      simpa using hchain
  | cons a pref ih =>
      have htail : RChain r (pref ++ suff) := by
        simpa using (rchain_tail (x := a) (xs := pref ++ suff) hchain)
      exact ih htail

private theorem rchain_snoc {α : Type*} {r : α → α → Prop} :
    ∀ (xs : List α) (x y : α),
      RChain r (xs ++ [x]) → r y x → RChain r (xs ++ [x, y]) := by
  intro xs
  induction xs with
  | nil =>
      intro x y _ hxy
      simp [RChain, hxy]
  | cons a xs ih =>
      intro x y hchain hxy
      cases xs with
      | nil =>
          have hax : r x a := by
            simpa [RChain] using hchain
          simp [RChain, hax, hxy]
      | cons b xs =>
          simp [RChain] at hchain ⊢
          exact ⟨hchain.1, ih _ _ hchain.2 hxy⟩

private theorem rchain_get {α : Type*} {r : α → α → Prop} {xs : List α}
    (hchain : RChain r xs) :
    ∀ i (hi : i + 1 < xs.length),
      r (xs.get ⟨i + 1, hi⟩) (xs.get ⟨i, by omega⟩) := by
  intro i
  induction i generalizing xs with
  | zero =>
      intro hi
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
              simpa [RChain] using hchain.1
  | succ i ih =>
      intro hi
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          have htail : RChain r xs := rchain_tail (x := x) (xs := xs) hchain
          have hi' : i + 1 < xs.length := by
            simpa using hi
          exact ih (xs := xs) htail hi'

private theorem split_mem {α : Type*} {x : α} :
    ∀ {xs : List α}, x ∈ xs → ∃ pre suf, xs = pre ++ x :: suf
  | [], h => by cases h
  | y :: ys, h => by
      rw [List.mem_cons] at h
      cases h with
      | inl hy =>
          subst hy
          exact ⟨[], ys, rfl⟩
      | inr hmem =>
          rcases split_mem hmem with ⟨pre, suf, hs⟩
          exact ⟨y :: pre, suf, by simp [hs]⟩

private theorem forcedRel_badStep
    (gc : GoodCycle ⟨rs2222, f⟩)
    (tfMap : List (Nat × Nat))
    (hbuild : buildTF (collectTF (gcPathN gc gc.configs.length (le_refl _))) [] = some tfMap)
    (cycleMask : Nat)
    (hcm : cycleMask = (gcPathN gc gc.configs.length (le_refl _)).foldl
      (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0)
    (cfg : Nat) (hcfg : cfg < 16)
    (target : Nat) (htarget : target < 16)
    (hrel : ForcedRel tfMap cycleMask target cfg)
    (hcomp : (cycleMask >>> cfg) &&& 1 = 0) :
    badStep ⟨rs2222, f⟩ gc (decCfg ⟨target, htarget⟩) (decCfg ⟨cfg, hcfg⟩) := by
  rcases hrel with ⟨proc, hfind⟩
  have ⟨hp4, htarget_eq, _, hcomp_target, hpriv⟩ :=
    findForcedTarget_sound gc tfMap hbuild cycleMask hcm cfg hcfg target proc hfind hcomp
  have hcfg_not_mem : decCfg ⟨cfg, hcfg⟩ ∉ gc.configs := by
    intro hmem
    have hbit : (cycleMask >>> cfg) &&& 1 = 1 :=
      (cycleMask_bit_iff_mem gc cycleMask hcm cfg hcfg).2 hmem
    omega
  have htarget_not_mem : decCfg ⟨target, htarget⟩ ∉ gc.configs := by
    intro hmem
    have hbit : (cycleMask >>> target) &&& 1 = 1 :=
      (cycleMask_bit_iff_mem gc cycleMask hcm target htarget).2 hmem
    omega
  refine ⟨hcfg_not_mem, htarget_not_mem, ?_⟩
  refine ⟨⟨proc, hp4⟩, hpriv hp4, ?_⟩
  apply encCfg_injective
  apply Fin.ext
  rw [enc_dec, encCfg_move (hpriv hp4), enc_dec]
  simpa [flipBit] using htarget_eq

private theorem forcedSelfLoop_false
    (gc : GoodCycle ⟨rs2222, f⟩) (hconv : converges ⟨rs2222, f⟩ gc)
    (tfMap : List (Nat × Nat))
    (hbuild : buildTF (collectTF (gcPathN gc gc.configs.length (le_refl _))) [] = some tfMap)
    (cycleMask : Nat)
    (hcm : cycleMask = (gcPathN gc gc.configs.length (le_refl _)).foldl
      (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0)
    (cfg : Nat) (hcfg : cfg < 16)
    (hrel : ForcedRel tfMap cycleMask cfg cfg)
    (hcomp : (cycleMask >>> cfg) &&& 1 = 0) :
    False := by
  have hbad := forcedRel_badStep gc tfMap hbuild cycleMask hcm
    cfg hcfg cfg hcfg hrel hcomp
  let cyc : Fin 1 → Config rs2222 := fun _ => decCfg ⟨cfg, hcfg⟩
  have hcycle : ∀ k : Fin 1, badStep ⟨rs2222, f⟩ gc (cyc ⟨0, by decide⟩) (cyc k) := by
    intro k
    fin_cases k
    simpa [cyc] using hbad
  have hnot := not_acc_of_finite_cycle' (α := Config rs2222)
    (r := badStep ⟨rs2222, f⟩ gc) (n := 1) (by decide) cyc hcycle
  exact hnot ⟨0, by decide⟩ (hconv.apply (cyc ⟨0, by decide⟩))

private theorem forcedSegment_false
    (gc : GoodCycle ⟨rs2222, f⟩) (hconv : converges ⟨rs2222, f⟩ gc)
    (tfMap : List (Nat × Nat))
    (hbuild : buildTF (collectTF (gcPathN gc gc.configs.length (le_refl _))) [] = some tfMap)
    (cycleMask : Nat)
    (hcm : cycleMask = (gcPathN gc gc.configs.length (le_refl _)).foldl
      (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0)
    (start last : Nat) (mid : List Nat)
    (hchain : RChain (ForcedRel tfMap cycleMask) (start :: mid ++ [last]))
    (hclose : ForcedRel tfMap cycleMask start last)
    (hbound : ∀ x ∈ start :: mid ++ [last], x < 16)
    (hcomp : ∀ x ∈ start :: mid ++ [last], (cycleMask >>> x) &&& 1 = 0) :
    False := by
  let xs := start :: mid ++ [last]
  have hlen : 0 < xs.length := by
    simp [xs]
  let cyc : Fin xs.length → Config rs2222 := fun k =>
    decCfg ⟨xs.get k, hbound _ (List.get_mem _ _)⟩
  have hstep :
      ∀ i (hi : i + 1 < xs.length),
        badStep ⟨rs2222, f⟩ gc
          (decCfg ⟨xs.get ⟨i + 1, hi⟩, hbound _ (List.get_mem _ _)⟩)
          (decCfg ⟨xs.get ⟨i, by omega⟩, hbound _ (List.get_mem _ _)⟩) := by
    intro i hi
    have hedge := rchain_get (xs := xs) hchain i hi
    exact forcedRel_badStep gc tfMap hbuild cycleMask hcm
      (xs.get ⟨i, by omega⟩) (hbound _ (List.get_mem _ _))
      (xs.get ⟨i + 1, hi⟩) (hbound _ (List.get_mem _ _))
      hedge (hcomp _ (List.get_mem _ _))
  have hclose_bad :
      badStep ⟨rs2222, f⟩ gc
        (decCfg ⟨start, hbound _ (by simp [xs])⟩)
        (decCfg ⟨last, hbound _ (by simp [xs])⟩) := by
    exact forcedRel_badStep gc tfMap hbuild cycleMask hcm
      last (hbound _ (by simp [xs]))
      start (hbound _ (by simp [xs]))
      hclose (hcomp _ (by simp [xs]))
  have hcycle : ∀ k : Fin xs.length,
      badStep ⟨rs2222, f⟩ gc
        (cyc ⟨(k.val + 1) % xs.length, Nat.mod_lt _ hlen⟩) (cyc k) := by
    intro k
    by_cases hk : k.val + 1 < xs.length
    · have hnext :
          (⟨(k.val + 1) % xs.length, Nat.mod_lt _ hlen⟩ : Fin xs.length) =
            ⟨k.val + 1, hk⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hk
      rw [hnext]
      exact hstep k.val hk
    · have hkval : k.val = xs.length - 1 := by
        omega
      have hk_last : k = ⟨xs.length - 1, by omega⟩ := Fin.ext hkval
      have hsum : k.val + 1 = xs.length := by
        omega
      have hnext :
          (⟨(k.val + 1) % xs.length, Nat.mod_lt _ hlen⟩ : Fin xs.length) =
            ⟨0, hlen⟩ := by
        apply Fin.ext
        have hmod : ((k.val + 1) % xs.length) = 0 := by
          rw [hsum, Nat.mod_self]
        simpa using hmod
      rw [hnext, hk_last]
      simpa [cyc, xs] using hclose_bad
  have hnot := not_acc_of_finite_cycle' (α := Config rs2222)
    (r := badStep ⟨rs2222, f⟩ gc) hlen cyc hcycle
  exact hnot ⟨0, hlen⟩ (hconv.apply (cyc ⟨0, hlen⟩))

private theorem followForced_false_aux
    (gc : GoodCycle ⟨rs2222, f⟩) (hconv : converges ⟨rs2222, f⟩ gc)
    (tfMap : List (Nat × Nat))
    (hbuild : buildTF (collectTF (gcPathN gc gc.configs.length (le_refl _))) [] = some tfMap)
    (cycleMask : Nat)
    (hcm : cycleMask = (gcPathN gc gc.configs.length (le_refl _)).foldl
      (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0) :
    ∀ (fuel : Nat) (path : List Nat) (cfg : Nat),
      cfg ∉ path →
      RChain (ForcedRel tfMap cycleMask) (path ++ [cfg]) →
      (∀ x ∈ path ++ [cfg], x < 16) →
      (∀ x ∈ path ++ [cfg], (cycleMask >>> x) &&& 1 = 0) →
      followForced tfMap cycleMask fuel cfg (listMask path) = true →
      False
  | 0, path, cfg, hnotmem, hchain, hbound, hcomp, hff => by
      simp [followForced] at hff
  | fuel + 1, path, cfg, hnotmem, hchain, hbound, hcomp, hff => by
      have hbit_ne : (listMask path >>> cfg) &&& 1 ≠ 1 := by
        intro hbit
        exact hnotmem ((listMask_bit_iff_mem path cfg).1 hbit)
      have hvisit_false : ((listMask path >>> cfg) &&& 1 == 1) = false :=
        beq_eq_false_iff_ne.mpr hbit_ne
      rw [followForced, hvisit_false] at hff
      cases hfind : findForcedTarget tfMap cycleMask cfg with
      | none =>
          simp [hfind] at hff
      | some edge =>
          rcases edge with ⟨target, proc⟩
          simp [hfind] at hff
          have hcfg_lt : cfg < 16 := hbound cfg (by simp)
          have hcfg_comp : (cycleMask >>> cfg) &&& 1 = 0 := hcomp cfg (by simp)
          have hrel : ForcedRel tfMap cycleMask target cfg := ⟨proc, hfind⟩
          have ⟨_, _, htarget_lt, hcomp_target, _⟩ :=
            findForcedTarget_sound gc tfMap hbuild cycleMask hcm
              cfg hcfg_lt target proc hfind hcfg_comp
          by_cases hmem : target ∈ path
          · obtain ⟨pre, mid, hsplit⟩ := split_mem hmem
            have hchain_cycle :
                RChain (ForcedRel tfMap cycleMask) (target :: mid ++ [cfg]) := by
              have hfull :
                  RChain (ForcedRel tfMap cycleMask)
                    (pre ++ (target :: mid ++ [cfg])) := by
                simpa [hsplit, List.append_assoc] using hchain
              exact rchain_suffix (pref := pre) (suff := target :: mid ++ [cfg]) hfull
            have hbound_cycle : ∀ x ∈ target :: mid ++ [cfg], x < 16 := by
              intro x hx
              exact hbound x (by
                rw [hsplit, List.append_assoc]
                exact List.mem_append.mpr (Or.inr hx))
            have hcomp_cycle :
                ∀ x ∈ target :: mid ++ [cfg], (cycleMask >>> x) &&& 1 = 0 := by
              intro x hx
              exact hcomp x (by
                rw [hsplit, List.append_assoc]
                exact List.mem_append.mpr (Or.inr hx))
            exact forcedSegment_false gc hconv tfMap hbuild cycleMask hcm
              target cfg mid hchain_cycle hrel hbound_cycle hcomp_cycle
          · by_cases hself : target = cfg
            · have hrel_self : ForcedRel tfMap cycleMask cfg cfg := by
                refine ⟨proc, ?_⟩
                rw [hself] at hfind
                simpa using hfind
              exact forcedSelfLoop_false gc hconv tfMap hbuild cycleMask hcm
                cfg hcfg_lt hrel_self hcfg_comp
            · have htarget_not_mem : target ∉ path ++ [cfg] := by
                intro hmem'
                rw [List.mem_append, List.mem_singleton] at hmem'
                cases hmem' with
                | inl hmem_path => exact hmem hmem_path
                | inr hmem_cfg => exact hself hmem_cfg
              have hchain' :
                  RChain (ForcedRel tfMap cycleMask) ((path ++ [cfg]) ++ [target]) := by
                simpa [List.append_assoc] using rchain_snoc path cfg target hchain hrel
              have hbound' : ∀ x ∈ (path ++ [cfg]) ++ [target], x < 16 := by
                intro x hx
                rw [List.mem_append, List.mem_singleton] at hx
                cases hx with
                | inl hx_old => exact hbound x hx_old
                | inr hx_target =>
                    subst hx_target
                    exact htarget_lt
              have hcomp' :
                  ∀ x ∈ (path ++ [cfg]) ++ [target], (cycleMask >>> x) &&& 1 = 0 := by
                intro x hx
                rw [List.mem_append, List.mem_singleton] at hx
                cases hx with
                | inl hx_old => exact hcomp x hx_old
                | inr hx_target =>
                    subst hx_target
                    exact hcomp_target
              rw [← listMask_snoc path cfg] at hff
              exact followForced_false_aux gc hconv tfMap hbuild cycleMask hcm
                fuel (path ++ [cfg]) target htarget_not_mem hchain' hbound' hcomp' hff

/-- followForced + any soundness: when the explicit bad cycle check returns true
    (from the some tfMap branch), derive False from convergence. -/
private theorem followForced_any_false
    (gc : GoodCycle ⟨rs2222, f⟩) (hconv : converges ⟨rs2222, f⟩ gc)
    (tfMap : List (Nat × Nat))
    (hbuild : buildTF (collectTF (gcPathN gc gc.configs.length (le_refl _))) [] = some tfMap)
    (cycleMask : Nat)
    (hcm : cycleMask = (gcPathN gc gc.configs.length (le_refl _)).foldl
      (fun mask (cfg, _) => mask ||| (1 <<< cfg)) 0)
    (h : (List.range 16).any (fun cfg =>
      if (cycleMask >>> cfg) &&& 1 == 1 then false
      else followForced tfMap cycleMask 17 cfg 0) = true) :
    False := by
  rcases List.any_eq_true.mp h with ⟨cfg, hcfg_mem, hcfg_any⟩
  have hcfg_lt : cfg < 16 := List.mem_range.mp hcfg_mem
  have hbit_le : (cycleMask >>> cfg) &&& 1 ≤ 1 := Nat.and_le_right
  have hcfg_comp : (cycleMask >>> cfg) &&& 1 = 0 := by
    by_cases hbit : (cycleMask >>> cfg) &&& 1 = 1
    · simp [hbit] at hcfg_any
    · omega
  have hvisit_false : ((cycleMask >>> cfg) &&& 1 == 1) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  simp [hvisit_false] at hcfg_any
  have hfollow : followForced tfMap cycleMask 17 cfg (listMask []) = true := by
    simpa [listMask] using hcfg_any.2
  have hchain0 : RChain (ForcedRel tfMap cycleMask) ([] ++ [cfg]) := by
    simp [RChain]
  have hbound0 : ∀ x ∈ ([] : List Nat) ++ [cfg], x < 16 := by
    intro x hx
    simp at hx
    simpa [hx] using hcfg_lt
  have hcomp0 : ∀ x ∈ ([] : List Nat) ++ [cfg], (cycleMask >>> x) &&& 1 = 0 := by
    intro x hx
    simp at hx
    simpa [hx] using hcfg_comp
  exact followForced_false_aux gc hconv tfMap hbuild cycleMask hcm
    17 [] cfg (by simp) hchain0 hbound0 hcomp0 hfollow

/-- hasExplicitBadCycle soundness: when the check finds an explicit bad cycle,
    we derive False from convergence. -/
private theorem hasExplicitBadCycle_sound (gc : GoodCycle ⟨rs2222, f⟩)
    (hconv : converges ⟨rs2222, f⟩ gc)
    (htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) = false)
    (h : hasExplicitBadCycle (gcPathN gc gc.configs.length (le_refl _)) = true) : False := by
  set path := gcPathN gc gc.configs.length (le_refl _) with hpath_def
  -- hasExplicitBadCycle unfolds to buildTF + followForced
  simp only [hasExplicitBadCycle] at h
  -- Since isTFBlocked = false, hasTFConflict = false, so buildTF succeeds
  -- We case split on buildTF
  cases hbuild : buildTF (collectTF path) [] with
  | none =>
    -- buildTF failed. But isTFBlocked = false means no conflict.
    -- Derive False: hasTFConflict = false → buildTF ≠ none.
    -- Actually, buildTF none → hasTFConflict true → isTFBlocked true → contradiction with htf.
    -- For now, just note that h simplifies to true = true, giving no info.
    -- We derive the contradiction from the TF conflict.
    -- buildTF = none means a conflict exists in collectTF path.
    -- Use isTFBlocked_sound with htf = false is a contradiction... no, htf = false.
    -- We need: buildTF none → isTFBlocked true → contradiction with htf.
    simp [hbuild] at h
    -- h was hasExplicitBadCycle path = true. After simp with buildTF = none,
    -- hasExplicitBadCycle returns true (the none => true branch).
    -- But we have htf : isTFBlocked path = false.
    -- We need: buildTF none → hasTFConflict true → isTFBlocked true.
    -- isTFBlocked = hasTFConflict (collectTF path).
    -- buildTF (collectTF path) [] = none means there's a conflict in collectTF.
    -- hasTFConflict checks all pairs for conflicts. buildTF checks incrementally.
    -- They detect the same conflicts. So buildTF = none → hasTFConflict = true.
    -- Then isTFBlocked = hasTFConflict = true, contradicting htf.
    exfalso
    -- Prove: hasTFConflict = false → buildTF ≠ none (contrapositive)
    -- Then: htf gives hasTFConflict = false → buildTF ≠ none → contradiction with hbuild
    suffices hne_none : buildTF (collectTF path) [] ≠ none by exact hne_none hbuild
    -- Prove contrapositive: ¬hasTFConflict → buildTF succeeds
    -- Actually simpler: just prove hasTFConflict (collectTF path) = false → buildTF ≠ none
    -- htf : isTFBlocked path = false, which means hasTFConflict (collectTF path) = false
    unfold isTFBlocked at htf
    -- htf : hasTFConflict (collectTF path) = false
    -- Prove: hasTFConflict entries = false → ∀ acc consistent with entries,
    --   buildTF entries acc ≠ none
    -- Key: hasTFConflict = false means no two entries (k,v1) (k,v2) with v1≠v2.
    -- So all entries with same key have same value.
    -- buildTF only fails when it finds same key with different value. Can't happen.
    suffices hsuff : ∀ (entries acc : List (Nat × Nat)),
        (∀ e1 ∈ entries, ∀ e2 ∈ entries, e1.1 = e2.1 → e1.2 = e2.2) →
        (∀ e1 ∈ entries, ∀ e2 ∈ acc, e1.1 = e2.1 → e1.2 = e2.2) →
        buildTF entries acc ≠ none by
      apply hsuff
      · -- entries consistent: from hasTFConflict = false
        intro e1 he1 e2 he2 hkey
        by_contra hval
        have : hasTFConflict (collectTF path) = true := by
          unfold hasTFConflict
          rw [List.any_eq_true]
          exact ⟨e1, he1, List.any_eq_true.mpr ⟨e2, he2, by
            simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
            exact ⟨hkey, hval⟩⟩⟩
        rw [this] at htf; simp at htf
      · -- no acc entries initially (acc = [])
        intro e1 _ e2 he2; simp at he2
    intro entries
    induction entries with
    | nil => intro _ _ _; simp [buildTF]
    | cons hd tl ih =>
      intro acc hcons hcross
      simp only [buildTF]
      cases hm : assocLookup hd.1 acc with
      | none =>
        apply ih ((hd.1, hd.2) :: acc)
        · intro e1 he1 e2 he2; exact hcons e1 (List.mem_cons.mpr (Or.inr he1))
            e2 (List.mem_cons.mpr (Or.inr he2))
        · intro e1 he1 e2 he2
          rw [List.mem_cons] at he2
          cases he2 with
          | inl heq =>
            rw [heq]; intro hkey
            exact hcons e1 (List.mem_cons.mpr (Or.inr he1))
              hd (List.mem_cons.mpr (Or.inl rfl)) hkey
          | inr hmem =>
            exact hcross e1 (List.mem_cons.mpr (Or.inr he1)) e2 hmem
      | some v' =>
        have hv_eq : hd.2 = v' := by
          -- v' is in acc via assocLookup. The cross consistency gives hd.2 = v'.
          -- Actually we need (hd.1, v') ∈ acc... Not quite.
          -- We need: hd.2 = v'. By cross consistency: hd ∈ entries, and there exists
          -- an entry in acc with key hd.1 and value v'.
          -- From hcons, hd is consistent with itself (trivially).
          -- From hcross, hd ∈ (hd :: tl) and (hd.1, v') effectively in acc.
          -- Actually, assocLookup hd.1 acc = some v' means there's some (hd.1, v') in acc.
          -- But we need: hd.2 = v'.
          -- hcross says: ∀ e1 ∈ (hd :: tl), ∀ e2 ∈ acc, e1.1 = e2.1 → e1.2 = e2.2
          -- We need (hd.1, v') ∈ acc to apply hcross with e1 = hd, e2 = (hd.1, v').
          -- assocLookup_mem would give us this.
          suffices hmem_acc : (hd.1, v') ∈ acc by
            exact hcross hd (List.mem_cons.mpr (Or.inl rfl)) (hd.1, v') hmem_acc rfl
          -- Prove assocLookup k xs = some v → (k, v) ∈ xs, inline
          have : ∀ (xs : List (Nat × Nat)) (k v : Nat),
              assocLookup k xs = some v → (k, v) ∈ xs := by
            intro xs; induction xs with
            | nil => intro k v hh; simp [assocLookup] at hh
            | cons a rest ih_a =>
              intro k v hh; simp only [assocLookup] at hh
              split at hh
              · rename_i heq; rw [beq_iff_eq] at heq
                have hav : v = a.2 := by
                  have := Option.some.inj hh
                  exact this.symm
                rw [show (k, v) = a from Prod.ext heq.symm hav]
                exact List.mem_cons.mpr (Or.inl rfl)
              · exact List.mem_cons.mpr (Or.inr (ih_a k v hh))
          exact this acc hd.1 v' hm
        simp [show (hd.2 == v') = true from beq_iff_eq.mpr hv_eq]
        apply ih acc
        · intro e1 he1 e2 he2; exact hcons e1 (List.mem_cons.mpr (Or.inr he1))
            e2 (List.mem_cons.mpr (Or.inr he2))
        · intro e1 he1; exact hcross e1 (List.mem_cons.mpr (Or.inr he1))
  | some tfMap =>
    rw [hbuild] at h
    -- h is now about (List.range 16).any (...)
    exact followForced_any_false gc hconv tfMap hbuild
      (path.foldl (fun mask x => mask ||| 1 <<< x.1) 0) rfl h

/-- V2 bridge: GoodCycle on rs2222 → False via V2 DFS + isBlockedV2 soundness. -/
theorem goodCycle_gives_blocked_q4_cycle
    (gc : GoodCycle ⟨rs2222, f⟩) (hconv : converges ⟨rs2222, f⟩ gc) : False := by
  by_cases hdir : gc.uniformDirection
  · exact uniformDirection_false gc hconv hdir
  cases htf : isTFBlocked (gcPathN gc gc.configs.length (le_refl _)) with
  | true => exact isTFBlocked_sound gc htf
  | false =>
    by_cases hfc2 : ∀ p : Fin 4, gc.fireCount p = 2
    · exact hdir (uniformDirection_of_allFireCount_two gc hfc2 htf)
    · by_cases hfc4 : ∀ p : Fin 4, gc.fireCount p = 4
      · have hlen16 : gc.configs.length = 16 := by
          have hsum := gc.sum_fireCount
          calc
            gc.configs.length = ∑ p : Fin 4, gc.fireCount p := hsum.symm
            _ = ∑ _p : Fin 4, 4 := by
              apply Finset.sum_congr rfl
              intro p _
              exact hfc4 p
            _ = 16 := by norm_num
        let bits0 : Proc4 → Bool := bitsOfCfg4 (gcCfgAt gc 0 (by omega))
        let w : Word4 := gcWordFrom gc 0 gc.configs.length (by omega)
        have hlenw : w.length = 16 := by
          simpa [w, hlen16] using gcWordFrom_length gc 0 gc.configs.length (by omega)
        have hlocal : LocalNoStayWord4 w := by
          exact gcWordFrom_localNoStay gc 0 gc.configs.length (by omega)
        have hne : w ≠ [] := by
          intro hnil
          rw [hnil] at hlenw
          simp at hlenw
        rcases exists_wordFromChoices4_of_localNoStay (w := w) hlocal hne with ⟨a, ds, hw⟩
        have hds15 : ds.length = 15 := by
          rw [hw, wordFromChoices4_length] at hlenw
          omega
        have hcount :
            ∀ j : Proc4, (wordFromChoices4 a ds).count j = 4 := by
          intro j
          rw [← hw, ← gc_prefixFireCount_eq_count_gcWordFrom gc j gc.configs.length (by omega)]
          simpa [GoodCycle.fireCount] using hfc4 j
        have hbad :
            hasExplicitBadCycle (pathFromWord4 bits0 (wordFromChoices4 a ds)) = true :=
          hasExplicitBadCycle_of_wordFromChoices4_len15_count4 bits0 a ds hds15 hcount
        have hbad' :
            hasExplicitBadCycle (gcPathN gc gc.configs.length (le_refl _)) = true := by
          simpa [bits0, w, hw, gcPathN_eq_pathFromWord4 gc] using hbad
        exact hasExplicitBadCycle_sound gc hconv htf hbad'
      · obtain ⟨p, q, hp4, hq2, hqadj⟩ := exists_adjacent_high_low_fireCounts gc hfc2 hfc4
        obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hno_ab, hno_bc, hno_cd, hzero_case⟩ :=
          exists_zero_gap_context_of_fireCount_two_vs_four gc p q hp4 hq2
        cases hzero_case with
        | inl hab0 =>
            have hspan_le12 := zero_gap_span_le_twelve gc p q a b hp4 hq2 hab ha hb hno_ab hab0
            have heven := gc_same_mover_gap_even gc p a b hab ha hb
            by_cases hlen4 : b.val = a.val + 4
            · cases hqadj with
              | inl hq =>
                  exact zero_gap_len4_false_left gc htf p q a b hq ha hb hno_ab hab0 hlen4
              | inr hq =>
                  exact zero_gap_len4_false_right gc htf p q a b hq ha hb hno_ab hab0 hlen4
            · by_cases hlen6 : b.val = a.val + 6
              · cases hqadj with
                | inl hq =>
                    exact zero_gap_len6_false_left gc htf p q a b hq ha hb hno_ab hab0 hlen6
                | inr hq =>
                    exact zero_gap_len6_false_right gc htf p q a b hq ha hb hno_ab hab0 hlen6
              · by_cases hlen8 : b.val = a.val + 8
                · cases hqadj with
                  | inl hq =>
                      exact zero_gap_len8_false_left gc htf p q a b hq ha hb hno_ab hab0 hlen8
                  | inr hq =>
                      exact zero_gap_len8_false_right gc htf p q a b hq ha hb hno_ab hab0 hlen8
                · by_cases hlen10 : b.val = a.val + 10
                  · cases hqadj with
                    | inl hq =>
                        exact zero_gap_len10_false_left gc htf p q a b hq ha hb hno_ab hab0 hlen10
                    | inr hq =>
                        exact zero_gap_len10_false_right gc htf p q a b hq ha hb hno_ab hab0 hlen10
                  · obtain ⟨m, hm⟩ := heven
                    have hgap2_or_12 : b.val = a.val + 2 ∨ b.val = a.val + 12 := by
                      omega
                    cases hgap2_or_12 with
                    | inl hgap2 =>
                        cases hqadj with
                        | inl hq =>
                            by_cases htail : a.val + 4 < gc.configs.length
                            · exact zero_gap_len2_false_left_core gc htf p q a b hq ha hb hab0 hgap2 htail
                            · have hend : a.val + 4 = gc.configs.length := by omega
                              exact zero_gap_len2_false_left_end gc htf p q a b hq ha hb hab0 hgap2 hend
                        | inr hq =>
                            by_cases htail : a.val + 4 < gc.configs.length
                            · exact zero_gap_len2_false_right_core gc htf p q a b hq ha hb hab0 hgap2 htail
                            · have hend : a.val + 4 = gc.configs.length := by omega
                              exact zero_gap_len2_false_right_end gc htf p q a b hq ha hb hab0 hgap2 hend
                    | inr hgap12 =>
                        cases hqadj with
                        | inl hq =>
                            exact zero_gap_len12_false_left gc htf p q a b hq ha hb hno_ab hab0 hgap12
                        | inr hq =>
                            exact zero_gap_len12_false_right gc htf p q a b hq ha hb hno_ab hab0 hgap12
        | inr hrest =>
            cases hrest with
            | inl hbc0 =>
                have hspan_le12 := zero_gap_span_le_twelve gc p q b c hp4 hq2 hbc hb hc hno_bc hbc0
                have heven := gc_same_mover_gap_even gc p b c hbc hb hc
                by_cases hlen4 : c.val = b.val + 4
                · cases hqadj with
                  | inl hq =>
                      exact zero_gap_len4_false_left gc htf p q b c hq hb hc hno_bc hbc0 hlen4
                  | inr hq =>
                      exact zero_gap_len4_false_right gc htf p q b c hq hb hc hno_bc hbc0 hlen4
                · by_cases hlen6 : c.val = b.val + 6
                  · cases hqadj with
                    | inl hq =>
                        exact zero_gap_len6_false_left gc htf p q b c hq hb hc hno_bc hbc0 hlen6
                    | inr hq =>
                        exact zero_gap_len6_false_right gc htf p q b c hq hb hc hno_bc hbc0 hlen6
                  · by_cases hlen8 : c.val = b.val + 8
                    · cases hqadj with
                      | inl hq =>
                          exact zero_gap_len8_false_left gc htf p q b c hq hb hc hno_bc hbc0 hlen8
                      | inr hq =>
                          exact zero_gap_len8_false_right gc htf p q b c hq hb hc hno_bc hbc0 hlen8
                    · by_cases hlen10 : c.val = b.val + 10
                      · cases hqadj with
                        | inl hq =>
                            exact zero_gap_len10_false_left gc htf p q b c hq hb hc hno_bc hbc0 hlen10
                        | inr hq =>
                            exact zero_gap_len10_false_right gc htf p q b c hq hb hc hno_bc hbc0 hlen10
                      · obtain ⟨m, hm⟩ := heven
                        have hgap2_or_12 : c.val = b.val + 2 ∨ c.val = b.val + 12 := by
                          omega
                        cases hgap2_or_12 with
                        | inl hgap2 =>
                            cases hqadj with
                            | inl hq =>
                                by_cases htail : b.val + 4 < gc.configs.length
                                · exact zero_gap_len2_false_left_core gc htf p q b c hq hb hc hbc0 hgap2 htail
                                · have hend : b.val + 4 = gc.configs.length := by omega
                                  exact zero_gap_len2_false_left_end gc htf p q b c hq hb hc hbc0 hgap2 hend
                            | inr hq =>
                                by_cases htail : b.val + 4 < gc.configs.length
                                · exact zero_gap_len2_false_right_core gc htf p q b c hq hb hc hbc0 hgap2 htail
                                · have hend : b.val + 4 = gc.configs.length := by omega
                                  exact zero_gap_len2_false_right_end gc htf p q b c hq hb hc hbc0 hgap2 hend
                        | inr hgap12 =>
                            cases hqadj with
                            | inl hq =>
                                exact zero_gap_len12_false_left gc htf p q b c hq hb hc hno_bc hbc0 hgap12
                            | inr hq =>
                                exact zero_gap_len12_false_right gc htf p q b c hq hb hc hno_bc hbc0 hgap12
            | inr hcd0 =>
                have hspan_le12 := zero_gap_span_le_twelve gc p q c d hp4 hq2 hcd hc hd hno_cd hcd0
                have heven := gc_same_mover_gap_even gc p c d hcd hc hd
                by_cases hlen4 : d.val = c.val + 4
                · cases hqadj with
                  | inl hq =>
                      exact zero_gap_len4_false_left gc htf p q c d hq hc hd hno_cd hcd0 hlen4
                  | inr hq =>
                      exact zero_gap_len4_false_right gc htf p q c d hq hc hd hno_cd hcd0 hlen4
                · by_cases hlen6 : d.val = c.val + 6
                  · cases hqadj with
                    | inl hq =>
                        exact zero_gap_len6_false_left gc htf p q c d hq hc hd hno_cd hcd0 hlen6
                    | inr hq =>
                        exact zero_gap_len6_false_right gc htf p q c d hq hc hd hno_cd hcd0 hlen6
                  · by_cases hlen8 : d.val = c.val + 8
                    · cases hqadj with
                      | inl hq =>
                          exact zero_gap_len8_false_left gc htf p q c d hq hc hd hno_cd hcd0 hlen8
                      | inr hq =>
                          exact zero_gap_len8_false_right gc htf p q c d hq hc hd hno_cd hcd0 hlen8
                    · by_cases hlen10 : d.val = c.val + 10
                      · cases hqadj with
                        | inl hq =>
                            exact zero_gap_len10_false_left gc htf p q c d hq hc hd hno_cd hcd0 hlen10
                        | inr hq =>
                            exact zero_gap_len10_false_right gc htf p q c d hq hc hd hno_cd hcd0 hlen10
                      · obtain ⟨m, hm⟩ := heven
                        have hgap2_or_12 : d.val = c.val + 2 ∨ d.val = c.val + 12 := by
                          omega
                        cases hgap2_or_12 with
                        | inl hgap2 =>
                            by_cases htail : c.val + 4 < gc.configs.length
                            · cases hqadj with
                              | inl hq =>
                                  exact zero_gap_len2_false_left_core gc htf p q c d hq hc hd hcd0 hgap2 htail
                              | inr hq =>
                                  exact zero_gap_len2_false_right_core gc htf p q c d hq hc hd hcd0 hgap2 htail
                            · by_cases hend : c.val + 4 = gc.configs.length
                              · cases hqadj with
                                | inl hq =>
                                    exact zero_gap_len2_false_left_end gc htf p q c d hq hc hd hcd0 hgap2 hend
                                | inr hq =>
                                    exact zero_gap_len2_false_right_end gc htf p q c d hq hc hd hcd0 hgap2 hend
                              · by_cases hab0' : gc.intervalFireCount q a.val b.val = 0
                                · cases hqadj with
                                  | inl hq =>
                                      have hspan_le12 := zero_gap_span_le_twelve gc p q a b hp4 hq2 hab ha hb hno_ab hab0'
                                      have heven_ab := gc_same_mover_gap_even gc p a b hab ha hb
                                      by_cases hlen4ab : b.val = a.val + 4
                                      · exact zero_gap_len4_false_left gc htf p q a b hq ha hb hno_ab hab0' hlen4ab
                                      · by_cases hlen6ab : b.val = a.val + 6
                                        · exact zero_gap_len6_false_left gc htf p q a b hq ha hb hno_ab hab0' hlen6ab
                                        · by_cases hlen8ab : b.val = a.val + 8
                                          · exact zero_gap_len8_false_left gc htf p q a b hq ha hb hno_ab hab0' hlen8ab
                                          · by_cases hlen10ab : b.val = a.val + 10
                                            · exact zero_gap_len10_false_left gc htf p q a b hq ha hb hno_ab hab0' hlen10ab
                                            · obtain ⟨mab, hmab⟩ := heven_ab
                                              have hgap2_or_12ab : b.val = a.val + 2 ∨ b.val = a.val + 12 := by
                                                omega
                                              cases hgap2_or_12ab with
                                              | inl hgap2ab =>
                                                  by_cases htailab : a.val + 4 < gc.configs.length
                                                  · exact zero_gap_len2_false_left_core gc htf p q a b hq ha hb hab0' hgap2ab htailab
                                                  · have hendab : a.val + 4 = gc.configs.length := by omega
                                                    exact zero_gap_len2_false_left_end gc htf p q a b hq ha hb hab0' hgap2ab hendab
                                              | inr hgap12ab =>
                                                  exact zero_gap_len12_false_left gc htf p q a b hq ha hb hno_ab hab0' hgap12ab
                                  | inr hq =>
                                      have hspan_le12 := zero_gap_span_le_twelve gc p q a b hp4 hq2 hab ha hb hno_ab hab0'
                                      have heven_ab := gc_same_mover_gap_even gc p a b hab ha hb
                                      by_cases hlen4ab : b.val = a.val + 4
                                      · exact zero_gap_len4_false_right gc htf p q a b hq ha hb hno_ab hab0' hlen4ab
                                      · by_cases hlen6ab : b.val = a.val + 6
                                        · exact zero_gap_len6_false_right gc htf p q a b hq ha hb hno_ab hab0' hlen6ab
                                        · by_cases hlen8ab : b.val = a.val + 8
                                          · exact zero_gap_len8_false_right gc htf p q a b hq ha hb hno_ab hab0' hlen8ab
                                          · by_cases hlen10ab : b.val = a.val + 10
                                            · exact zero_gap_len10_false_right gc htf p q a b hq ha hb hno_ab hab0' hlen10ab
                                            · obtain ⟨mab, hmab⟩ := heven_ab
                                              have hgap2_or_12ab : b.val = a.val + 2 ∨ b.val = a.val + 12 := by
                                                omega
                                              cases hgap2_or_12ab with
                                              | inl hgap2ab =>
                                                  by_cases htailab : a.val + 4 < gc.configs.length
                                                  · exact zero_gap_len2_false_right_core gc htf p q a b hq ha hb hab0' hgap2ab htailab
                                                  · have hendab : a.val + 4 = gc.configs.length := by omega
                                                    exact zero_gap_len2_false_right_end gc htf p q a b hq ha hb hab0' hgap2ab hendab
                                              | inr hgap12ab =>
                                                  exact zero_gap_len12_false_right gc htf p q a b hq ha hb hno_ab hab0' hgap12ab
                                · by_cases hbc0' : gc.intervalFireCount q b.val c.val = 0
                                  · cases hqadj with
                                    | inl hq =>
                                        have hspan_le12 := zero_gap_span_le_twelve gc p q b c hp4 hq2 hbc hb hc hno_bc hbc0'
                                        have heven_bc := gc_same_mover_gap_even gc p b c hbc hb hc
                                        by_cases hlen4bc : c.val = b.val + 4
                                        · exact zero_gap_len4_false_left gc htf p q b c hq hb hc hno_bc hbc0' hlen4bc
                                        · by_cases hlen6bc : c.val = b.val + 6
                                          · exact zero_gap_len6_false_left gc htf p q b c hq hb hc hno_bc hbc0' hlen6bc
                                          · by_cases hlen8bc : c.val = b.val + 8
                                            · exact zero_gap_len8_false_left gc htf p q b c hq hb hc hno_bc hbc0' hlen8bc
                                            · by_cases hlen10bc : c.val = b.val + 10
                                              · exact zero_gap_len10_false_left gc htf p q b c hq hb hc hno_bc hbc0' hlen10bc
                                              · obtain ⟨mbc, hmbc⟩ := heven_bc
                                                have hgap2_or_12bc : c.val = b.val + 2 ∨ c.val = b.val + 12 := by
                                                  omega
                                                cases hgap2_or_12bc with
                                                | inl hgap2bc =>
                                                    by_cases htailbc : b.val + 4 < gc.configs.length
                                                    · exact zero_gap_len2_false_left_core gc htf p q b c hq hb hc hbc0' hgap2bc htailbc
                                                    · have hendbc : b.val + 4 = gc.configs.length := by omega
                                                      exact zero_gap_len2_false_left_end gc htf p q b c hq hb hc hbc0' hgap2bc hendbc
                                                | inr hgap12bc =>
                                                    exact zero_gap_len12_false_left gc htf p q b c hq hb hc hno_bc hbc0' hgap12bc
                                    | inr hq =>
                                        have hspan_le12 := zero_gap_span_le_twelve gc p q b c hp4 hq2 hbc hb hc hno_bc hbc0'
                                        have heven_bc := gc_same_mover_gap_even gc p b c hbc hb hc
                                        by_cases hlen4bc : c.val = b.val + 4
                                        · exact zero_gap_len4_false_right gc htf p q b c hq hb hc hno_bc hbc0' hlen4bc
                                        · by_cases hlen6bc : c.val = b.val + 6
                                          · exact zero_gap_len6_false_right gc htf p q b c hq hb hc hno_bc hbc0' hlen6bc
                                          · by_cases hlen8bc : c.val = b.val + 8
                                            · exact zero_gap_len8_false_right gc htf p q b c hq hb hc hno_bc hbc0' hlen8bc
                                            · by_cases hlen10bc : c.val = b.val + 10
                                              · exact zero_gap_len10_false_right gc htf p q b c hq hb hc hno_bc hbc0' hlen10bc
                                              · obtain ⟨mbc, hmbc⟩ := heven_bc
                                                have hgap2_or_12bc : c.val = b.val + 2 ∨ c.val = b.val + 12 := by
                                                  omega
                                                cases hgap2_or_12bc with
                                                | inl hgap2bc =>
                                                    by_cases htailbc : b.val + 4 < gc.configs.length
                                                    · exact zero_gap_len2_false_right_core gc htf p q b c hq hb hc hbc0' hgap2bc htailbc
                                                    · have hendbc : b.val + 4 = gc.configs.length := by omega
                                                      exact zero_gap_len2_false_right_end gc htf p q b c hq hb hc hbc0' hgap2bc hendbc
                                                | inr hgap12bc =>
                                                    exact zero_gap_len12_false_right gc htf p q b c hq hb hc hno_bc hbc0' hgap12bc
                                  · have hwrap : gc.configs.length < c.val + 4 := by omega
                                    cases hqadj with
                                    | inl hq =>
                                        exact zero_gap_len2_false_left_wrap gc p q a b c d hq hab hbc ha hb hc hd hq2 hab0' hbc0' hcd0 hgap2 hwrap
                                    | inr hq =>
                                        exact zero_gap_len2_false_right_wrap gc p q a b c d hq hab hbc ha hb hc hd hq2 hab0' hbc0' hcd0 hgap2 hwrap
                        | inr hgap12 =>
                            cases hqadj with
                            | inl hq =>
                                exact zero_gap_len12_false_left gc htf p q c d hq hc hd hno_cd hcd0 hgap12
                            | inr hq =>
                                exact zero_gap_len12_false_right gc htf p q c d hq hc hd hno_cd hcd0 hgap12

/-- No valid system exists on rs2222. -/
theorem not_valid_rs2222_core (f : TransFn rs2222) : ¬valid ⟨rs2222, f⟩ := by
  intro ⟨gc, hconv⟩
  exact goodCycle_gives_blocked_q4_cycle gc hconv

theorem not_valid_rs2222 (sys : System) (hsys : sys.rs = rs2222) : ¬valid sys := by
  cases sys with | mk rs f =>
  simp only at hsys; subst hsys
  exact not_valid_rs2222_core f

/-! ## 5. Lifting to M_4 lower bound -/

theorem ringSpec_ext (rs₁ rs₂ : RingSpec) (hn : rs₁.n = rs₂.n)
    (hm : ∀ i : Fin rs₁.n, rs₁.m i = rs₂.m (Fin.cast hn i)) :
    rs₁ = rs₂ := by
  cases rs₁ with | mk n₁ hn₁ m₁ hm₁ =>
  cases rs₂ with | mk n₂ hn₂ m₂ hm₂ =>
  change n₁ = n₂ at hn; subst hn
  simp only [RingSpec.mk.injEq, heq_eq_eq, true_and]
  funext i; exact hm i

/-- For n=4, stateProduct < 24 forces rs = rs2222, so ¬valid. -/
theorem M_4_lower_proved (sys : System) (hn : sys.rs.n = 4)
    (hsub : stateProduct sys.rs < 24) : ¬valid sys := by
  have hrs : sys.rs = rs2222 := by
    apply ringSpec_ext _ _ hn
    intro i
    have hall := sub24_all_eq_2 sys.rs.n_ge_4 sys.rs.m sys.rs.m_pos hn hsub
    simp only [rs2222, Fin.cast]; exact hall i
  exact not_valid_rs2222 sys hrs

end LeanMn
