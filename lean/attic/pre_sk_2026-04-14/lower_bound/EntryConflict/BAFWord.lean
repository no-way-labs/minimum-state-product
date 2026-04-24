/-
  BAFWord.lean — BAF (Back-And-Forth) mover word state tracking

  Formalizes the core state-tracking argument for the palindromic entry
  conflict.  A BAF arc is a CW segment [j, j+1, ..., j+d] followed by
  a CCW segment [j+d, j+d-1, ..., j].  For an interior processor j in
  such an arc:

  • At the CW non-mover step (when j+1 fires CW past j), processor j
    has already fired but j-1 has not yet re-fired, so the context at j
    is (x_{j-1}, x_j, val_R).

  • At the CCW mover step (when j fires CCW back past j), j-1 still has
    value x_{j-1} (hasn't re-fired), j has value x_j (hasn't fired since
    the CW pass), and j+1 has returned to val_R (fired twice; for binary
    processors, two firings return to the original value).

  The context equality gives an entry conflict (same (L,S,R) at both a mover
  and a non-mover step), which contradicts entryConflict_impossible.

  Uses: configVal_eq_of_noFire_between from ContextBridge.lean.
-/
import LeanMn.LowerBound.EntryConflict.ContextBridge

namespace LeanMn

variable {sys : System}

/-! ### Helper: right ≠ self for n ≥ 4 -/

private theorem right_ne_self_baf {n : Nat} (hn : 4 ≤ n) (a : Fin n) :
    right a ≠ a := by
  intro h
  have hval := congrArg Fin.val h
  simp only [right_val] at hval
  have ha := a.isLt
  by_cases hp1 : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt hp1] at hval; omega
  · rw [show a.val + 1 = n from by omega, Nat.mod_self] at hval; omega

/-! ### BAF arc segment definition -/

/-- A BAF (back-and-forth) arc in a good cycle, capturing the step indices
    relevant to the entry conflict at an interior processor `proc`.

    The arc has four key steps in temporal order:
    1. `cwProcStep`:     proc fires during the CW pass
    2. `cwNeighborStep`: right(proc) fires during the CW pass (proc is non-mover)
    3. `ccwNeighborStep`: right(proc) fires during the CCW pass
    4. `ccwProcStep`:    proc fires during the CCW pass (proc is mover)

    Between steps 2 and 4, neither proc nor left(proc) fires.
    Between steps 2 and 3 (exclusive), right(proc) does not fire.
    In the standard BAF, step 4 = step 3 + 1 (adjacent CCW). -/
structure BAFArc (gc : GoodCycle sys) where
  /-- The interior processor where the conflict will occur -/
  proc : Fin sys.rs.n
  /-- Step index: proc fires CW (mover = proc) -/
  cwProcStep : Fin gc.configs.length
  /-- Step index: right(proc) fires CW (mover = right proc), proc is non-mover -/
  cwNeighborStep : Fin gc.configs.length
  /-- Step index: right(proc) fires CCW -/
  ccwNeighborStep : Fin gc.configs.length
  /-- Step index: proc fires CCW (mover = proc) -/
  ccwProcStep : Fin gc.configs.length
  /-- Temporal ordering: CW proc fires before CW neighbor -/
  cw_order : cwProcStep.val < cwNeighborStep.val
  /-- Temporal ordering: CW neighbor fires before CCW neighbor -/
  mid_order : cwNeighborStep.val < ccwNeighborStep.val
  /-- Temporal ordering: CCW neighbor fires before CCW proc -/
  ccw_order : ccwNeighborStep.val < ccwProcStep.val
  /-- At cwProcStep, the mover is proc (CW pass) -/
  cw_proc_mover : gc.moverAt cwProcStep = proc
  /-- At cwNeighborStep, the mover is right(proc) (CW pass) -/
  cw_neighbor_mover : gc.moverAt cwNeighborStep = right proc
  /-- At ccwNeighborStep, the mover is right(proc) (CCW pass) -/
  ccw_neighbor_mover : gc.moverAt ccwNeighborStep = right proc
  /-- At ccwProcStep, the mover is proc (CCW pass) -/
  ccw_proc_mover : gc.moverAt ccwProcStep = proc
  /-- Between cwNeighborStep and ccwProcStep: proc does not fire -/
  proc_noFire : ∀ k : Fin gc.configs.length,
    cwNeighborStep.val ≤ k.val → k.val < ccwProcStep.val →
      gc.moverAt k ≠ proc
  /-- Between cwNeighborStep and ccwProcStep: left(proc) does not fire -/
  leftProc_noFire : ∀ k : Fin gc.configs.length,
    cwNeighborStep.val ≤ k.val → k.val < ccwProcStep.val →
      gc.moverAt k ≠ left proc
  /-- Between cwNeighborStep and ccwNeighborStep (exclusive): right(proc) does not fire -/
  rightProc_noFire_mid : ∀ k : Fin gc.configs.length,
    cwNeighborStep.val < k.val → k.val < ccwNeighborStep.val →
      gc.moverAt k ≠ right proc

/-! ### State preservation through a BAF arc -/

/-- The value of `proc` is unchanged from step cwNeighborStep to step ccwProcStep,
    because proc does not fire in between. -/
theorem BAFArc.proc_val_preserved (arc : BAFArc gc) :
    (gc.configs.get arc.cwNeighborStep) arc.proc =
      (gc.configs.get arc.ccwProcStep) arc.proc :=
  configVal_eq_of_noFire_between gc arc.proc
    arc.cwNeighborStep.val arc.ccwProcStep.val
    (Nat.le_of_lt (Nat.lt_trans arc.mid_order arc.ccw_order))
    arc.ccwProcStep.isLt
    arc.proc_noFire

/-- The value of `left proc` is unchanged from step cwNeighborStep to step
    ccwProcStep, because left(proc) does not fire in between. -/
theorem BAFArc.leftProc_val_preserved (arc : BAFArc gc) :
    (gc.configs.get arc.cwNeighborStep) (left arc.proc) =
      (gc.configs.get arc.ccwProcStep) (left arc.proc) :=
  configVal_eq_of_noFire_between gc (left arc.proc)
    arc.cwNeighborStep.val arc.ccwProcStep.val
    (Nat.le_of_lt (Nat.lt_trans arc.mid_order arc.ccw_order))
    arc.ccwProcStep.isLt
    arc.leftProc_noFire

/-- The value of `right proc` is unchanged from step (cwNeighborStep + 1)
    to step ccwNeighborStep, because right(proc) does not fire in between. -/
theorem BAFArc.rightProc_val_preserved_mid
    (arc : BAFArc gc)
    (h_succ_lt : arc.cwNeighborStep.val + 1 < gc.configs.length) :
    (gc.configs.get ⟨arc.cwNeighborStep.val + 1, h_succ_lt⟩) (right arc.proc) =
      (gc.configs.get arc.ccwNeighborStep) (right arc.proc) :=
  configVal_eq_of_noFire_between gc (right arc.proc)
    (arc.cwNeighborStep.val + 1) arc.ccwNeighborStep.val
    arc.mid_order
    arc.ccwNeighborStep.isLt
    (fun k hk1 hk2 => arc.rightProc_noFire_mid k (by omega) hk2)

/-- **BAF Left-Self Context Equality.** The (L, S) part of the context at
    `proc` is preserved between the CW non-mover step and the CCW mover step.
    This follows purely from no-fire arguments. -/
theorem BAFArc.context_LS_eq (arc : BAFArc gc) :
    (gc.configs.get arc.cwNeighborStep) (left arc.proc) =
      (gc.configs.get arc.ccwProcStep) (left arc.proc) ∧
    (gc.configs.get arc.cwNeighborStep) arc.proc =
      (gc.configs.get arc.ccwProcStep) arc.proc :=
  ⟨arc.leftProc_val_preserved, arc.proc_val_preserved⟩

/-! ### BAF Arc with adjacent CCW steps -/

/-- An adjacent BAF arc: the CCW pass visits right(proc) immediately before
    proc, i.e., ccwProcStep = ccwNeighborStep + 1.  This is the standard
    case in a BAF (back-and-forth) mover word. -/
structure BAFArcAdj (gc : GoodCycle sys) extends BAFArc gc where
  /-- The CCW pass is adjacent: right(proc) fires one step before proc -/
  ccw_adjacent : ccwProcStep.val = ccwNeighborStep.val + 1

/-! ### Entry conflict from a BAFArcAdj -/

/-- For an adjacent BAF arc where the R component is preserved (given as a
    hypothesis), we get an entry conflict: proc sees the same (L, S, R)
    context as both non-mover (at cwNeighborStep) and mover (at ccwProcStep).

    At cwNeighborStep: mover = right(proc) ≠ proc, so proc is non-mover.
    At ccwProcStep: mover = proc, so proc is mover.
    Same (L, S, R) at both steps → entryConflict_impossible gives False. -/
theorem BAFArcAdj.elim
    {sys : System} {gc : GoodCycle sys}
    (arc : BAFArcAdj gc)
    (hR : (gc.configs.get arc.cwNeighborStep) (right arc.proc) =
          (gc.configs.get arc.ccwProcStep) (right arc.proc)) :
    False := by
  have hne : gc.moverAt arc.cwNeighborStep ≠ arc.proc := by
    rw [arc.cw_neighbor_mover]
    exact right_ne_self_baf sys.rs.n_ge_4 arc.proc
  exact entryConflict_impossible gc
    ⟨arc.ccwProcStep, arc.cwNeighborStep, arc.proc,
     arc.ccw_proc_mover, hne,
     arc.leftProc_val_preserved.symm,
     arc.proc_val_preserved.symm,
     hR.symm⟩

/-- A BAFArcAdj immediately yields an entry conflict (given R preservation). -/
theorem BAFArcAdj.hasEntryConflict
    {sys : System} {gc : GoodCycle sys}
    (arc : BAFArcAdj gc)
    (hR : (gc.configs.get arc.cwNeighborStep) (right arc.proc) =
          (gc.configs.get arc.ccwProcStep) (right arc.proc)) :
    hasEntryConflict gc := by
  have hne : gc.moverAt arc.cwNeighborStep ≠ arc.proc := by
    rw [arc.cw_neighbor_mover]
    exact right_ne_self_baf sys.rs.n_ge_4 arc.proc
  exact ⟨arc.ccwProcStep, arc.cwNeighborStep, arc.proc,
   arc.ccw_proc_mover, hne,
   arc.leftProc_val_preserved.symm,
   arc.proc_val_preserved.symm,
   hR.symm⟩

/-! ### Binary R-value return lemma -/

/-- For a binary processor that fires exactly at steps `a` and `b` (and nowhere
    else in `(a, b)`), its value at step `a` equals its value at step `b + 1`.
    Two firings of a binary processor toggle the value twice, returning to the
    original.

    Proof strategy: use the parity characterization from GoodCycleBasics.
    The prefix fire count increases by exactly 2 between steps a and b+1,
    so the parity is preserved, so the binary value is the same. -/
theorem binary_double_fire_returns
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a b : Nat)
    (ha : a < gc.configs.length)
    (hb_succ : b + 1 ≤ gc.configs.length)
    (hab : a < b)
    (ha_mover : gc.moverAt ⟨a, ha⟩ = p)
    (hb_mover : gc.moverAt ⟨b, by omega⟩ = p)
    (hno : ∀ k : Fin gc.configs.length,
      a < k.val → k.val < b → gc.moverAt k ≠ p) :
    gc.stateAfter p a = gc.stateAfter p (b + 1) := by
  rw [gc.binary_stateAfter_eq_iff_prefixFireCount_modEq p hbin
    (Nat.le_of_lt ha) hb_succ]
  -- Show: prefix fire count increases by exactly 2
  suffices h : gc.prefixFireCount p (b + 1) = gc.prefixFireCount p a + 2 by omega
  -- Decompose: prefix(b+1) = prefix(a) + sum over [a, b+1)
  have hdecomp : gc.prefixFireCount p (b + 1) =
      gc.prefixFireCount p a +
        ∑ k ∈ Finset.Ico a (b + 1), gc.fireIndicator p k := by
    unfold GoodCycle.prefixFireCount
    have hunion : Finset.range (b + 1) = Finset.range a ∪ Finset.Ico a (b + 1) := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    rw [hunion, Finset.sum_union]
    simp only [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_range] at hk1
    simp only [Finset.mem_Ico] at hk2
    omega
  rw [hdecomp]; congr 1
  -- Fire indicators: 1 at a, 0 in (a,b), 1 at b
  have hfire_a : gc.fireIndicator p a = 1 := by
    rw [gc.fireIndicator_of_lt p ha]; simp [ha_mover]
  have hfire_b : gc.fireIndicator p b = 1 := by
    rw [gc.fireIndicator_of_lt p (by omega)]; simp [hb_mover]
  -- Split [a, b+1) = [a, a+1) ∪ [a+1, b) ∪ [b, b+1)
  have hIco_a : Finset.Ico a (a + 1) = {a} := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  have hIco_b : Finset.Ico b (b + 1) = {b} := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  have hmid_zero : ∑ k ∈ Finset.Ico (a + 1) b, gc.fireIndicator p k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_Ico] at hk
    by_cases hk_lt : k < gc.configs.length
    · rw [gc.fireIndicator_of_lt p hk_lt]
      have hkfin : (⟨k, hk_lt⟩ : Fin gc.configs.length).val = k := rfl
      have : gc.moverAt ⟨k, hk_lt⟩ ≠ p := hno ⟨k, hk_lt⟩ (by rw [hkfin]; omega) hk.2
      simp [this]
    · exact gc.fireIndicator_of_ge p (by omega)
  calc ∑ k ∈ Finset.Ico a (b + 1), gc.fireIndicator p k
      = ∑ k ∈ Finset.Ico a (a + 1), gc.fireIndicator p k +
        ∑ k ∈ Finset.Ico (a + 1) (b + 1), gc.fireIndicator p k := by
        rw [← Finset.sum_Ico_consecutive _ (by omega : a ≤ a + 1) (by omega : a + 1 ≤ b + 1)]
    _ = ∑ k ∈ Finset.Ico (a + 1) b, gc.fireIndicator p k +
        ∑ k ∈ Finset.Ico b (b + 1), gc.fireIndicator p k +
        gc.fireIndicator p a := by
        rw [hIco_a, Finset.sum_singleton,
          ← Finset.sum_Ico_consecutive _ (by omega : a + 1 ≤ b) (by omega : b ≤ b + 1)]
        omega
    _ = 0 + gc.fireIndicator p b + gc.fireIndicator p a := by
        rw [hmid_zero, hIco_b, Finset.sum_singleton]
    _ = 2 := by rw [hfire_a, hfire_b]

/-- Config-indexed version: binary processor value at step `a` equals value
    at step `b + 1` when it fires exactly at `a` and `b`. -/
theorem binary_double_fire_returns_config
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (a b : Nat)
    (ha : a < gc.configs.length)
    (hb1 : b + 1 < gc.configs.length)
    (hab : a < b)
    (ha_mover : gc.moverAt ⟨a, ha⟩ = p)
    (hb_mover : gc.moverAt ⟨b, by omega⟩ = p)
    (hno : ∀ k : Fin gc.configs.length,
      a < k.val → k.val < b → gc.moverAt k ≠ p) :
    (gc.configs.get ⟨a, ha⟩) p =
      (gc.configs.get ⟨b + 1, hb1⟩) p := by
  have h := binary_double_fire_returns gc p hbin a b ha (by omega) hab
    ha_mover hb_mover hno
  simp [GoodCycle.stateAfter, ha, hb1] at h
  exact h

/-! ### Combining: BAFArcAdj with binary right(proc) gives contradiction -/

/-- **BAF Binary Entry Conflict.** For an adjacent BAF arc where `right(proc)`
    is binary:
    - L and S are preserved by no-fire (leftProc_noFire, proc_noFire).
    - R is preserved because right(proc) fires exactly twice (at cwNeighborStep
      and ccwNeighborStep) with no other firings in between.  Binary double-fire
      returns to the original value, so the R value at cwNeighborStep equals
      the R value at ccwNeighborStep + 1 = ccwProcStep.
    This yields an entry conflict and hence a contradiction. -/
theorem BAFArcAdj.elim_of_binary_right
    (arc : BAFArcAdj gc)
    (hbin : isBinary sys.rs (right arc.proc)) :
    False := by
  apply arc.elim
  -- Need: R value at cwNeighborStep = R value at ccwProcStep
  -- right(proc) fires at cwNeighborStep and ccwNeighborStep, nowhere in between
  have h_b1_lt : arc.ccwNeighborStep.val + 1 < gc.configs.length := by
    have h1 := arc.ccwProcStep.isLt
    have h2 := arc.ccw_adjacent
    omega
  have hR := binary_double_fire_returns_config gc (right arc.proc) hbin
    arc.cwNeighborStep.val arc.ccwNeighborStep.val
    arc.cwNeighborStep.isLt
    h_b1_lt
    arc.mid_order
    arc.cw_neighbor_mover
    arc.ccw_neighbor_mover
    arc.rightProc_noFire_mid
  -- hR : config[cwNeighborStep](right proc) = config[ccwNeighborStep + 1](right proc)
  -- ccwNeighborStep + 1 = ccwProcStep by adjacency
  have heq : (⟨arc.ccwNeighborStep.val + 1, h_b1_lt⟩ : Fin gc.configs.length) =
      arc.ccwProcStep := by
    ext; exact arc.ccw_adjacent.symm
  rw [heq] at hR
  exact hR

end LeanMn
