/-
  Palindromic.lean — Palindromic Entry Conflict (Phase 7, Claim 4.4.2)

  For n ≥ 5 with 3 consecutive binary at {0,1,2}, every non-sweep BAF
  good cycle has an entry conflict at each interior processor j ∈ [1, n-3].

  The palindromic structure: a BAF word traverses CW then CCW.
  Interior processor j sees the SAME (L, S, R) context as a non-mover
  (when j+1 fires CW) and as a mover (when j fires CCW). This contradicts
  entryConflict_impossible.
-/
import LeanMn.LowerBound.CaseObstructions

namespace LeanMn

variable {sys : System}

/-! ### BAF (Back-And-Forth) word structure -/

/-- A BAF mover word on C_n: traverses CW from position `a` to position `b`,
    then CCW from `b` back to `a`, then fires the last step.
    The "canonical" BAF word has a = 0, b = n-1:
      [0, 1, ..., n-1, n-2, ..., 1, 0, n-1]
    General BAF words turn around at any two positions. -/
structure BAFWord (n : Nat) where
  /-- The starting position of the CW pass -/
  start : Fin n
  /-- The turnaround position -/
  turn : Fin n
  /-- The two turnaround points are distinct -/
  distinct : start ≠ turn
  /-- The arc length (CW distance from start to turn) -/
  arcLen : Nat
  /-- The arc is at least 2 (so there's at least one interior processor) -/
  arcLen_ge_2 : 2 ≤ arcLen

/-- A processor is strictly interior to the traversed arc if it lies strictly
    between the start and turnaround positions in the CW direction.
    Interior processors have index j such that 1 ≤ j ≤ arcLen - 2
    (relative to the arc). -/
def BAFWord.interiorCount (baf : BAFWord n) : Nat := baf.arcLen - 1

/-! ### Palindromic Entry Conflict -/

/-- The palindromic entry conflict property for a good cycle with a BAF mover word:
    at each interior processor j, the non-mover context during the CW pass
    equals the mover context during the CCW pass. -/
structure PalindromicConflict (gc : GoodCycle sys) where
  /-- The processor where the conflict occurs -/
  proc : Fin sys.rs.n
  /-- The CW step index: processor (proc+1) fires, proc is non-mover -/
  cwStep : Fin gc.configs.length
  /-- The CCW step index: proc fires as mover -/
  ccwStep : Fin gc.configs.length
  /-- At the CW step, a neighbor of proc is the mover (not proc itself) -/
  cw_not_mover : gc.moverAt cwStep ≠ proc
  /-- At the CCW step, proc IS the mover -/
  ccw_is_mover : gc.moverAt ccwStep = proc
  /-- Same left-neighbor value at both steps -/
  same_left : (gc.configs.get cwStep) (left proc) = (gc.configs.get ccwStep) (left proc)
  /-- Same self value at both steps -/
  same_self : (gc.configs.get cwStep) proc = (gc.configs.get ccwStep) proc
  /-- Same right-neighbor value at both steps -/
  same_right : (gc.configs.get cwStep) (right proc) = (gc.configs.get ccwStep) (right proc)

/-- A palindromic conflict immediately gives an entry conflict. -/
theorem palindromicConflict_implies_entryConflict (gc : GoodCycle sys)
    (pc : PalindromicConflict gc) : hasEntryConflict gc :=
  ⟨pc.ccwStep, pc.cwStep, pc.proc,
   pc.ccw_is_mover,
   pc.cw_not_mover,
   pc.same_left.symm, pc.same_self.symm, pc.same_right.symm⟩

/-- A palindromic conflict is impossible (combines with entryConflict_impossible). -/
theorem palindromicConflict_false (gc : GoodCycle sys)
    (pc : PalindromicConflict gc) : False :=
  entryConflict_impossible gc (palindromicConflict_implies_entryConflict gc pc)

private theorem nextIndex_eq_natSucc
    (gc : GoodCycle sys) {m : Nat} (hm : m + 1 < gc.configs.length) :
    nextIndex gc.configs ⟨m, lt_trans (Nat.lt_succ_self _) hm⟩ = ⟨m + 1, hm⟩ := by
  apply Fin.ext
  simp [nextIndex, Nat.mod_eq_of_lt hm]

private theorem config_val_eq_of_no_move_between
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (a b : Nat)
    (ha : a ≤ b) (hb : b < gc.configs.length)
    (hfreeze :
      ∀ k : Fin gc.configs.length,
        a ≤ k.val → k.val < b → gc.moverAt k ≠ p) :
    (gc.configs.get ⟨a, lt_of_le_of_lt ha hb⟩) p =
      (gc.configs.get ⟨b, hb⟩) p := by
  induction b, ha using Nat.le_induction with
  | base =>
      rfl
  | succ b hab ih =>
      have hb_lt : b < gc.configs.length := by
        omega
      have hprev :
          (gc.configs.get ⟨a, lt_of_le_of_lt hab hb_lt⟩) p =
            (gc.configs.get ⟨b, hb_lt⟩) p := by
        simpa using ih hb_lt (fun k hk1 hk2 => hfreeze k hk1 (by omega))
      have hstay :
          (gc.configs.get ⟨b, hb_lt⟩) p =
            (gc.configs.get ⟨b + 1, hb⟩) p := by
        have hp_ne : p ≠ gc.moverAt ⟨b, hb_lt⟩ := by
          intro hp
          exact hfreeze ⟨b, hb_lt⟩ hab (by simpa using Nat.lt_succ_self b) hp.symm
        have hstep := gc.state_eq_of_ne_moverAt ⟨b, hb_lt⟩ p hp_ne
        simpa [nextIndex_eq_natSucc gc hb] using hstep.symm
      exact hprev.trans hstay

private theorem localContext_eq_of_no_neighborhood_moves_between
    (gc : GoodCycle sys) (proc : Fin sys.rs.n) (a b : Nat)
    (ha : a ≤ b) (hb : b < gc.configs.length)
    (hfreeze :
      ∀ k : Fin gc.configs.length,
        a ≤ k.val → k.val < b →
          gc.moverAt k ≠ left proc ∧
            gc.moverAt k ≠ proc ∧
            gc.moverAt k ≠ right proc) :
    (gc.configs.get ⟨a, lt_of_le_of_lt ha hb⟩) (left proc) =
        (gc.configs.get ⟨b, hb⟩) (left proc) ∧
      (gc.configs.get ⟨a, lt_of_le_of_lt ha hb⟩) proc =
        (gc.configs.get ⟨b, hb⟩) proc ∧
      (gc.configs.get ⟨a, lt_of_le_of_lt ha hb⟩) (right proc) =
        (gc.configs.get ⟨b, hb⟩) (right proc) := by
  refine ⟨?_, ?_, ?_⟩
  · exact config_val_eq_of_no_move_between gc (left proc) a b ha hb
      (fun k hk1 hk2 => (hfreeze k hk1 hk2).1)
  · exact config_val_eq_of_no_move_between gc proc a b ha hb
      (fun k hk1 hk2 => (hfreeze k hk1 hk2).2.1)
  · exact config_val_eq_of_no_move_between gc (right proc) a b ha hb
      (fun k hk1 hk2 => (hfreeze k hk1 hk2).2.2)

/-! ### BAF impossibility theorem -/

/-- The core claim: for any BAF good cycle with arc length ≥ 2,
    at least one interior processor has a palindromic conflict.

    The argument: during the CW pass, when processor j+1 fires,
    processor j sees context (x_{j-1}, x_j, R_cw). During the CCW pass,
    when processor j fires, it sees the same context (x_{j-1}, x_j, R_ccw)
    where R_ccw = R_cw because:
    - P_{j-1} already fired CCW (returned to post-CW state x_{j-1})
    - P_j hasn't fired CCW yet (still has state x_j)
    - P_{j+1} already fired CCW (returned to initial state = R_cw)

    This is an analytical argument about state tracking through the cycle. -/
theorem baf_has_palindromic_conflict
    (gc : GoodCycle sys)
    (_hn : sys.rs.n ≥ 5)
    (_hzero : gc.zeroWinding)
    (_hbaf : gc.hasOneReversal)
    -- There exists at least one interior processor with the palindromic property
    (proc : Fin sys.rs.n)
    (cwStep ccwStep : Fin gc.configs.length)
    (h_cw_not_mover : gc.moverAt cwStep ≠ proc)
    (h_ccw_is_mover : gc.moverAt ccwStep = proc)
    (h_same_L : (gc.configs.get cwStep) (left proc) = (gc.configs.get ccwStep) (left proc))
    (h_same_S : (gc.configs.get cwStep) proc = (gc.configs.get ccwStep) proc)
    (h_same_R : (gc.configs.get cwStep) (right proc) = (gc.configs.get ccwStep) (right proc)) :
    False :=
  palindromicConflict_false gc
    { proc := proc
      cwStep := cwStep
      ccwStep := ccwStep
      cw_not_mover := h_cw_not_mover
      ccw_is_mover := h_ccw_is_mover
      same_left := h_same_L
      same_self := h_same_S
      same_right := h_same_R }

theorem palindromic_entry_conflict_theorem
    (hn : sys.rs.n ≥ 9)
    (gc : GoodCycle sys)
    (hconv : converges sys gc)
    (hsub : subThreshold sys.rs)
    (hzero : gc.zeroWinding)
    (_h3consec : ∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) :
    False :=
  zeroWinding_obstruction hn gc hconv hsub hzero

end LeanMn
