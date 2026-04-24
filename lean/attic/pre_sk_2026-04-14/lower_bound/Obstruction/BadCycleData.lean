/-
  Obstruction/BadCycleData.lean — Generic witness for non-convergence.

  BadCycleData packages an explicit cycle of non-good configurations.
  Every shadow-style argument targets this structure, then uses the
  generic toShadowTrap / toGlobalObstruction theorems to reach the
  unified obstruction interface.
-/
import LeanMn.LowerBound.Obstruction.Core

namespace LeanMn

variable {sys : System}

/-- An explicit bad cycle: a sequence of non-good configs forming a closed
    orbit under the system's transition function. This is the universal
    front-end target for all shadow-style arguments. -/
structure BadCycleData (sys : System) (gc : GoodCycle sys) where
  /-- Length of the bad cycle. -/
  len : Nat
  /-- The bad cycle is non-empty. -/
  len_pos : 0 < len
  /-- The bad configs, indexed cyclically. -/
  cfg : Fin len → Config sys.rs
  /-- The mover (privileged proc) at each step. -/
  mover : Fin len → Fin sys.rs.n
  /-- Every bad config is NOT a good config. -/
  disjoint : ∀ k, cfg k ∉ gc.configs
  /-- The chosen mover is privileged at each bad config. -/
  priv : ∀ k, privileged sys (cfg k) (mover k)
  /-- Firing the mover produces the next bad config. -/
  step : ∀ k, cfg ⟨(k.val + 1) % len, Nat.mod_lt _ len_pos⟩ =
    move sys (cfg k) (mover k)
  /-- All bad configs are distinct. -/
  distinct : ∀ a b, cfg a = cfg b → a = b

/-- **Builder for a length-2 bad cycle.** Given two configs `c, c'` disjoint
    from `gc`, distinct, with `c → c' → c` via privileged moves, package
    them as `BadCycleData`.

    This is the mechanical constructor for the `sweep + non-3CB + no-pivot`
    closure path — the existence of such a 2-cycle was verified
    computationally (Session 7, 100/100 universality), but the existence
    proof itself is a separate (open) theorem. -/
def BadCycleData.mk2 (sys : System) (gc : GoodCycle sys)
    (c c' : Config sys.rs) (p p' : Fin sys.rs.n)
    (h_c_notin : c ∉ gc.configs)
    (h_c'_notin : c' ∉ gc.configs)
    (h_c_neq_c' : c ≠ c')
    (h_c_priv : privileged sys c p)
    (h_c_step : move sys c p = c')
    (h_c'_priv : privileged sys c' p')
    (h_c'_step : move sys c' p' = c) :
    BadCycleData sys gc where
  len := 2
  len_pos := by omega
  cfg := fun k => if k.val = 0 then c else c'
  mover := fun k => if k.val = 0 then p else p'
  disjoint := by
    intro k
    by_cases h : k.val = 0
    · simp [h]; exact h_c_notin
    · simp [h]; exact h_c'_notin
  priv := by
    intro k
    by_cases h : k.val = 0
    · simp [h]; exact h_c_priv
    · simp [h]; exact h_c'_priv
  step := by
    intro k
    fin_cases k
    · -- k = 0 case
      show (if (((0 : Fin 2).val + 1) % 2 = 0) then c else c') = move sys c p
      simp
      exact h_c_step.symm
    · -- k = 1 case
      show (if (((1 : Fin 2).val + 1) % 2 = 0) then c else c') = move sys c' p'
      simp
      exact h_c'_step.symm
  distinct := by
    intro a b heq
    fin_cases a <;> fin_cases b
    · rfl
    · simp at heq; exact absurd heq h_c_neq_c'
    · simp at heq; exact absurd heq.symm h_c_neq_c'
    · rfl

/-- **General builder for a length-`L` bad cycle from `Fin L`-indexed data.**
    Given explicit `cfg : Fin L → Config` and `mover : Fin L → Fin n` together
    with the four required properties, package them as `BadCycleData`.

    This is the front-end constructor for any explicit closed-form bad cycle
    witness (e.g. the PA-2a §2.3 τ-reordering formula for the residual
    non-consec family at `n = 9`, or future general-`n` constructions). It
    supersedes the ad-hoc `mk2` length-2 builder when the witness length is
    known and fixed. -/
def BadCycleData.mk_of_fn (sys : System) (gc : GoodCycle sys)
    (L : Nat) (hL : 0 < L)
    (cfg : Fin L → Config sys.rs)
    (mover : Fin L → Fin sys.rs.n)
    (hdisjoint : ∀ k, cfg k ∉ gc.configs)
    (hpriv : ∀ k, privileged sys (cfg k) (mover k))
    (hstep : ∀ k, cfg ⟨(k.val + 1) % L, Nat.mod_lt _ hL⟩ =
      move sys (cfg k) (mover k))
    (hdistinct : ∀ a b : Fin L, cfg a = cfg b → a = b) :
    BadCycleData sys gc where
  len := L
  len_pos := hL
  cfg := cfg
  mover := mover
  disjoint := hdisjoint
  priv := hpriv
  step := hstep
  distinct := hdistinct

/-- Package BadCycleData into a ShadowTrap. -/
def BadCycleData.toShadowTrap (bcd : BadCycleData sys gc) :
    ShadowTrap sys gc where
  configs := List.ofFn bcd.cfg
  nonempty := by
    simp
    have := bcd.len_pos
    omega
  disjoint := by
    rw [List.forall_mem_ofFn_iff]
    exact bcd.disjoint
  closed := by
    intro k
    have hlen : (List.ofFn bcd.cfg).length = bcd.len := List.length_ofFn
    have hk : k.val < bcd.len := by have := k.isLt; omega
    refine ⟨bcd.mover ⟨k.val, hk⟩, ?_, ?_⟩
    · simp only [List.get_ofFn]; convert bcd.priv ⟨k.val, hk⟩ using 2
    · simp only [List.get_ofFn, nextIndex]
      convert bcd.step ⟨k.val, hk⟩ using 2 <;> simp [hlen]
  distinct := by
    rw [List.nodup_ofFn]
    exact fun _ _ h => bcd.distinct _ _ h

/-- Package BadCycleData into a GlobalObstruction. -/
def BadCycleData.toGlobalObstruction (bcd : BadCycleData sys gc) :
    GlobalObstruction sys gc :=
  GlobalObstruction.shadowTrap bcd.toShadowTrap

/-- BadCycleData directly implies non-convergence. -/
theorem BadCycleData.not_converges (bcd : BadCycleData sys gc) :
    ¬converges sys gc :=
  bcd.toGlobalObstruction.not_converges

end LeanMn
