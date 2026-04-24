/-
  SmallN/Defs.lean — Witness system definitions for n = 4..8 (Phase 11)

  For each n ∈ {4,5,6,7,8}, defines the explicit witness system that achieves
  the minimum state product M_n = 32 · 3^(n-4).

  Each witness consists of:
    - State counts m_i for each processor
    - Transition function f_i(L, S, R) for each processor
    - Proof that stateProduct = M_n

  Validity is proved by explicit finite certificates:
    - the concrete good cycle
    - a concrete bad-rank function that strictly decreases on every bad step
-/
import LeanMn.Dijkstra

namespace LeanMn

/-! ### Witness n=4, ms=(2, 2, 2, 4), product=32 -/

def w4M (i : Fin 4) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | _ => 4

def w4Spec : RingSpec where
  n := 4
  n_ge_4 := by omega
  m := w4M
  m_pos := by intro i; fin_cases i <;> simp [w4M]

private def w4P0 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 0
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 0
  | 3, 0, 0 => 0
  | 3, 0, 1 => 0
  | 3, 1, 0 => 0
  | 3, 1, 1 => 0
  | _, _, _ => 0

private def w4P1 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | _, _, _ => 0

private def w4P2 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 1
  | 0, 0, 3 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 0, 1, 2 => 1
  | 0, 1, 3 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | _, _, _ => 0

private def w4P3 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 2
  | 0, 1, 1 => 0
  | 0, 2, 0 => 2
  | 0, 2, 1 => 0
  | 0, 3, 0 => 0
  | 0, 3, 1 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 2, 0 => 3
  | 1, 2, 1 => 0
  | 1, 3, 0 => 3
  | 1, 3, 1 => 0
  | _, _, _ => 0

def w4OutVal (i L S R : Nat) : Nat :=
  match i with
  | 0 => w4P0 L S R
  | 1 => w4P1 L S R
  | 2 => w4P2 L S R
  | _ => w4P3 L S R

private lemma w4OutVal_lt (i : Fin 4)
    (L : Fin (w4Spec.m (left i)))
    (S : Fin (w4Spec.m i))
    (R : Fin (w4Spec.m (right i))) :
    w4OutVal i.val L.val S.val R.val < w4Spec.m i := by
  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp_all [w4OutVal, w4P0, w4P1, w4P2, w4P3, w4Spec, w4M]

def w4Trans : TransFn w4Spec := by
  intro i L S R
  exact ⟨w4OutVal i.val L.val S.val R.val, w4OutVal_lt i L S R⟩

def w4System : System where
  rs := w4Spec
  f := w4Trans

theorem w4_stateProduct : stateProduct w4Spec = 32 := by
  simp [stateProduct, w4Spec, w4M, Fin.prod_univ_succ]

def w4Cfg (x0 : Fin 2) (x1 : Fin 2) (x2 : Fin 2) (x3 : Fin 4) : Config w4Spec
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3

def w4CfgCode (c : Config w4Spec) : Nat :=
  (c ⟨0, by decide⟩).1 + 2 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 2 * ((c ⟨3, by decide⟩).1)))

def w4CfgOfCode (k : Nat) : Config w4Spec :=
  w4Cfg
    ⟨(k / 1) % 2, by omega⟩
    ⟨(k / 2) % 2, by omega⟩
    ⟨(k / 4) % 2, by omega⟩
    ⟨(k / 8) % 4, by omega⟩

def w4GoodCycleCodes : List Nat := [0, 1, 3, 7, 15, 14, 12, 8, 16, 20, 28, 24]

def w4GoodCycleConfigs : List (Config w4Spec) :=
  w4GoodCycleCodes.map w4CfgOfCode

def w4RankVals : List Nat := [0, 0, 9, 0, 7, 6, 8, 0, 0, 4, 2, 3, 0, 5, 0, 0, 0, 8, 1, 2, 0, 7, 12, 13, 0, 12, 10, 11, 0, 13, 11, 12]

def w4BadRank (c : Config w4Spec) : Nat :=
  w4RankVals.getD (w4CfgCode c) 0

theorem w4GoodCycle_nonempty : w4GoodCycleConfigs ≠ [] := by
  decide

theorem w4GoodCycle_unique_privileged_aux :
    ∀ c ∈ w4GoodCycleConfigs,
      ∃ i, privileged w4System c i ∧
        ∀ j, privileged w4System c j → j = i := by
  native_decide

theorem w4GoodCycle_unique_privileged :
    ∀ c ∈ w4GoodCycleConfigs, ∃! i, privileged w4System c i := by
  intro c hc
  simpa [ExistsUnique] using w4GoodCycle_unique_privileged_aux c hc

theorem w4GoodCycle_closed :
    ∀ k : Fin w4GoodCycleConfigs.length,
      ∃ i,
        privileged w4System (w4GoodCycleConfigs.get k) i ∧
          w4GoodCycleConfigs.get (nextIndex w4GoodCycleConfigs k) =
            move w4System (w4GoodCycleConfigs.get k) i := by
  native_decide

theorem w4GoodCycle_distinct :
    ∀ j₁ j₂ : Fin w4GoodCycleConfigs.length,
      w4GoodCycleConfigs.get j₁ = w4GoodCycleConfigs.get j₂ → j₁ = j₂ := by
  native_decide

theorem w4GoodCycle_fair :
    ∀ i : Fin w4System.rs.n,
      ∃ k : Fin w4GoodCycleConfigs.length,
        ∃ j, privileged w4System (w4GoodCycleConfigs.get k) j ∧
          w4GoodCycleConfigs.get (nextIndex w4GoodCycleConfigs k) =
            move w4System (w4GoodCycleConfigs.get k) j ∧ j = i := by
  native_decide

def w4GoodCycle : GoodCycle w4System where
  configs := w4GoodCycleConfigs
  nonempty := w4GoodCycle_nonempty
  unique_privileged := w4GoodCycle_unique_privileged
  closed := w4GoodCycle_closed
  distinct := w4GoodCycle_distinct
  fair := w4GoodCycle_fair

theorem w4BadRank_decreases_from
    (c : Config w4Spec)
    (hbad : c ∉ w4GoodCycleConfigs)
    (i : Fin 4)
    (hpriv : privileged w4System c i)
    (hnext : move w4System c i ∉ w4GoodCycleConfigs) :
    w4BadRank (move w4System c i) < w4BadRank c := by
  native_decide +revert

theorem w4BadRank_decreases :
    ∀ {c' c : Config w4Spec},
      badStep w4System w4GoodCycle c' c → w4BadRank c' < w4BadRank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact w4BadRank_decreases_from c hbad i hpriv hnext

theorem w4_converges : converges w4System w4GoodCycle := by
  let f : Config w4Spec → Nat := w4BadRank
  let r : Config w4Spec → Config w4Spec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := by
    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)
  refine Subrelation.wf (r := r) ?_ hwf
  intro c' c hstep
  exact w4BadRank_decreases hstep

theorem w4_valid : valid w4System := by
  exact ⟨w4GoodCycle, w4_converges⟩

/-! ### Witness n=4 (optimal), ms=(2, 2, 2, 3), product=24 -/

def w4optM (i : Fin 4) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | _ => 3

def w4optSpec : RingSpec where
  n := 4
  n_ge_4 := by omega
  m := w4optM
  m_pos := by intro i; fin_cases i <;> simp [w4optM]

private def w4optP0 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 1
  | 1, 1, 0 => 0
  | 1, 1, 1 => 1
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 0
  | _, _, _ => 0

private def w4optP1 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | _, _, _ => 0

private def w4optP2 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 0, 2 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 0, 1, 2 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 0
  | _, _, _ => 0

private def w4optP3 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 2
  | 0, 2, 0 => 0
  | 0, 2, 1 => 2
  | 1, 0, 0 => 0
  | 1, 0, 1 => 1
  | 1, 1, 0 => 2
  | 1, 1, 1 => 1
  | 1, 2, 0 => 2
  | 1, 2, 1 => 0
  | _, _, _ => 0

def w4optTrans : TransFn w4optSpec := fun i L S R =>
  let v := match i.val with
    | 0 => w4optP0 L.val S.val R.val
    | 1 => w4optP1 L.val S.val R.val
    | 2 => w4optP2 L.val S.val R.val
    | 3 => w4optP3 L.val S.val R.val
    | _ => 0
  ⟨v % w4optSpec.m i, Nat.mod_lt _ (by fin_cases i <;> simp [w4optSpec, w4optM])⟩

def w4optSystem : System := ⟨w4optSpec, w4optTrans⟩

theorem w4opt_stateProduct : stateProduct w4optSpec = 24 := by
  simp [stateProduct, w4optSpec, w4optM, Fin.prod_univ_succ]

def w4optCfg (x0 : Fin 2) (x1 : Fin 2) (x2 : Fin 2) (x3 : Fin 3) : Config w4optSpec
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3

def w4optCfgCode (c : Config w4optSpec) : Nat :=
  (c ⟨0, by decide⟩).1 + 2 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 2 * ((c ⟨3, by decide⟩).1)))

def w4optCfgOfCode (k : Nat) : Config w4optSpec :=
  w4optCfg
    ⟨k % 2, by omega⟩
    ⟨(k / 2) % 2, by omega⟩
    ⟨(k / 4) % 2, by omega⟩
    ⟨(k / 8) % 3, by omega⟩

def w4optGoodCycleCodes : List Nat := [0, 1, 3, 7, 15, 11, 19, 18, 2, 6, 4, 5, 13, 12, 20, 16]

def w4optGoodCycleConfigs : List (Config w4optSpec) :=
  w4optGoodCycleCodes.map w4optCfgOfCode

theorem w4optGoodCycle_nonempty : w4optGoodCycleConfigs ≠ [] := by
  simp [w4optGoodCycleConfigs, w4optGoodCycleCodes]

theorem w4optGoodCycle_unique_privileged_aux :
    ∀ c ∈ w4optGoodCycleConfigs,
      ∃ i, privileged w4optSystem c i ∧
        ∀ j, privileged w4optSystem c j → j = i := by
  native_decide

theorem w4optGoodCycle_unique_privileged :
    ∀ c ∈ w4optGoodCycleConfigs, ∃! i, privileged w4optSystem c i := by
  intro c hc
  simpa [ExistsUnique] using w4optGoodCycle_unique_privileged_aux c hc

theorem w4optGoodCycle_closed :
    ∀ k : Fin w4optGoodCycleConfigs.length,
      ∃ i,
        privileged w4optSystem (w4optGoodCycleConfigs.get k) i ∧
          w4optGoodCycleConfigs.get (nextIndex w4optGoodCycleConfigs k) =
            move w4optSystem (w4optGoodCycleConfigs.get k) i := by
  native_decide

theorem w4optGoodCycle_distinct :
    ∀ j₁ j₂ : Fin w4optGoodCycleConfigs.length,
      w4optGoodCycleConfigs.get j₁ = w4optGoodCycleConfigs.get j₂ → j₁ = j₂ := by
  native_decide

theorem w4optGoodCycle_fair :
    ∀ i : Fin w4optSystem.rs.n,
      ∃ k : Fin w4optGoodCycleConfigs.length,
        ∃ j, privileged w4optSystem (w4optGoodCycleConfigs.get k) j ∧
          w4optGoodCycleConfigs.get (nextIndex w4optGoodCycleConfigs k) =
            move w4optSystem (w4optGoodCycleConfigs.get k) j ∧ j = i := by
  native_decide

def w4optGoodCycle : GoodCycle w4optSystem where
  configs := w4optGoodCycleConfigs
  nonempty := w4optGoodCycle_nonempty
  unique_privileged := w4optGoodCycle_unique_privileged
  closed := w4optGoodCycle_closed
  distinct := w4optGoodCycle_distinct
  fair := w4optGoodCycle_fair

def w4optBadRank (c : Config w4optSpec) : Nat :=
  match w4optCfgCode c with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 8 => 1 | 9 => 2 | 10 => 1 | 11 => 0 | 12 => 0 | 13 => 0 | 14 => 2 | 15 => 0
  | 16 => 0 | 17 => 1 | 18 => 0 | 19 => 0 | 20 => 0 | 21 => 2 | 22 => 1 | 23 => 2
  | _ => 0

theorem w4optBadRank_decreases (c c' : Config w4optSpec)
    (hbad : c ∉ w4optGoodCycleConfigs)
    (i : Fin w4optSpec.n)
    (hpriv : privileged w4optSystem c i)
    (hmove : c' = move w4optSystem c i)
    (hnext : move w4optSystem c i ∉ w4optGoodCycleConfigs) :
    w4optBadRank (move w4optSystem c i) < w4optBadRank c := by
  native_decide +revert

theorem w4optBadRank_step :
    ∀ {c' c : Config w4optSpec},
      badStep w4optSystem w4optGoodCycle c' c → w4optBadRank c' < w4optBadRank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact w4optBadRank_decreases c _ hbad i hpriv rfl hnext

theorem w4opt_converges : converges w4optSystem w4optGoodCycle := by
  let f : Config w4optSpec → Nat := w4optBadRank
  let r : Config w4optSpec → Config w4optSpec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := by
    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)
  refine Subrelation.wf (r := r) ?_ hwf
  intro c' c hstep
  exact w4optBadRank_step hstep

theorem w4opt_valid : valid w4optSystem := by
  exact ⟨w4optGoodCycle, w4opt_converges⟩

/-! ### Witness n=5, ms=(2, 2, 2, 3, 4), product=96 -/

def w5M (i : Fin 5) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 3
  | _ => 4

def w5Spec : RingSpec where
  n := 5
  n_ge_4 := by omega
  m := w5M
  m_pos := by intro i; fin_cases i <;> simp [w5M]

private def w5P0 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 1
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 0
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 0
  | 3, 0, 0 => 0
  | 3, 0, 1 => 0
  | 3, 1, 0 => 0
  | 3, 1, 1 => 0
  | _, _, _ => 0

private def w5P1 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | _, _, _ => 0

private def w5P2 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 1
  | 0, 1, 0 => 1
  | 0, 1, 1 => 0
  | 0, 1, 2 => 1
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 0
  | _, _, _ => 0

private def w5P3 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 0, 2 => 1
  | 0, 0, 3 => 0
  | 0, 1, 0 => 2
  | 0, 1, 1 => 2
  | 0, 1, 2 => 2
  | 0, 1, 3 => 0
  | 0, 2, 0 => 2
  | 0, 2, 1 => 2
  | 0, 2, 2 => 2
  | 0, 2, 3 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 2
  | 1, 0, 3 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 0
  | 1, 1, 3 => 1
  | 1, 2, 0 => 2
  | 1, 2, 1 => 0
  | 1, 2, 2 => 2
  | 1, 2, 3 => 1
  | _, _, _ => 0

private def w5P4 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 2
  | 0, 1, 1 => 2
  | 0, 2, 0 => 2
  | 0, 2, 1 => 2
  | 0, 3, 0 => 0
  | 0, 3, 1 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 0
  | 1, 2, 0 => 0
  | 1, 2, 1 => 0
  | 1, 3, 0 => 3
  | 1, 3, 1 => 0
  | 2, 0, 0 => 1
  | 2, 0, 1 => 1
  | 2, 1, 0 => 1
  | 2, 1, 1 => 1
  | 2, 2, 0 => 3
  | 2, 2, 1 => 2
  | 2, 3, 0 => 3
  | 2, 3, 1 => 0
  | _, _, _ => 0

def w5OutVal (i L S R : Nat) : Nat :=
  match i with
  | 0 => w5P0 L S R
  | 1 => w5P1 L S R
  | 2 => w5P2 L S R
  | 3 => w5P3 L S R
  | _ => w5P4 L S R

private lemma w5OutVal_lt (i : Fin 5)
    (L : Fin (w5Spec.m (left i)))
    (S : Fin (w5Spec.m i))
    (R : Fin (w5Spec.m (right i))) :
    w5OutVal i.val L.val S.val R.val < w5Spec.m i := by
  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp_all [w5OutVal, w5P0, w5P1, w5P2, w5P3, w5P4, w5Spec, w5M]

def w5Trans : TransFn w5Spec := by
  intro i L S R
  exact ⟨w5OutVal i.val L.val S.val R.val, w5OutVal_lt i L S R⟩

def w5System : System where
  rs := w5Spec
  f := w5Trans

theorem w5_stateProduct : stateProduct w5Spec = 96 := by
  simp [stateProduct, w5Spec, w5M, Fin.prod_univ_succ]

def w5Cfg (x0 : Fin 2) (x1 : Fin 2) (x2 : Fin 2) (x3 : Fin 3) (x4 : Fin 4) : Config w5Spec
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3
  | ⟨4, _⟩ => x4

def w5CfgCode (c : Config w5Spec) : Nat :=
  (c ⟨0, by decide⟩).1 + 2 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 2 * ((c ⟨3, by decide⟩).1 + 3 * ((c ⟨4, by decide⟩).1))))

def w5CfgOfCode (k : Nat) : Config w5Spec :=
  w5Cfg
    ⟨(k / 1) % 2, by omega⟩
    ⟨(k / 2) % 2, by omega⟩
    ⟨(k / 4) % 2, by omega⟩
    ⟨(k / 8) % 3, by omega⟩
    ⟨(k / 24) % 4, by omega⟩

def w5GoodCycleCodes : List Nat := [0, 1, 3, 7, 15, 11, 19, 43, 42, 40, 44, 28, 52, 68, 92, 84, 80, 72]

def w5GoodCycleConfigs : List (Config w5Spec) :=
  w5GoodCycleCodes.map w5CfgOfCode

def w5RankVals : List Nat := [0, 0, 12, 0, 10, 9, 11, 0, 8, 7, 9, 0, 9, 8, 10, 0, 7, 6, 8, 0, 6, 5, 23, 22, 11, 22, 20, 21, 0, 3, 19, 20, 9, 12, 10, 11, 10, 13, 20, 21, 0, 5, 0, 0, 0, 4, 20, 21, 10, 21, 19, 20, 0, 2, 18, 19, 9, 18, 16, 17, 10, 19, 19, 20, 2, 17, 15, 16, 0, 1, 17, 18, 0, 15, 13, 14, 11, 12, 12, 13, 0, 16, 14, 15, 0, 17, 15, 16, 1, 19, 14, 15, 0, 18, 16, 23]

def w5BadRank (c : Config w5Spec) : Nat :=
  w5RankVals.getD (w5CfgCode c) 0

theorem w5GoodCycle_nonempty : w5GoodCycleConfigs ≠ [] := by
  decide

theorem w5GoodCycle_unique_privileged_aux :
    ∀ c ∈ w5GoodCycleConfigs,
      ∃ i, privileged w5System c i ∧
        ∀ j, privileged w5System c j → j = i := by
  native_decide

theorem w5GoodCycle_unique_privileged :
    ∀ c ∈ w5GoodCycleConfigs, ∃! i, privileged w5System c i := by
  intro c hc
  simpa [ExistsUnique] using w5GoodCycle_unique_privileged_aux c hc

theorem w5GoodCycle_closed :
    ∀ k : Fin w5GoodCycleConfigs.length,
      ∃ i,
        privileged w5System (w5GoodCycleConfigs.get k) i ∧
          w5GoodCycleConfigs.get (nextIndex w5GoodCycleConfigs k) =
            move w5System (w5GoodCycleConfigs.get k) i := by
  native_decide

theorem w5GoodCycle_distinct :
    ∀ j₁ j₂ : Fin w5GoodCycleConfigs.length,
      w5GoodCycleConfigs.get j₁ = w5GoodCycleConfigs.get j₂ → j₁ = j₂ := by
  native_decide

theorem w5GoodCycle_fair :
    ∀ i : Fin w5System.rs.n,
      ∃ k : Fin w5GoodCycleConfigs.length,
        ∃ j, privileged w5System (w5GoodCycleConfigs.get k) j ∧
          w5GoodCycleConfigs.get (nextIndex w5GoodCycleConfigs k) =
            move w5System (w5GoodCycleConfigs.get k) j ∧ j = i := by
  native_decide

def w5GoodCycle : GoodCycle w5System where
  configs := w5GoodCycleConfigs
  nonempty := w5GoodCycle_nonempty
  unique_privileged := w5GoodCycle_unique_privileged
  closed := w5GoodCycle_closed
  distinct := w5GoodCycle_distinct
  fair := w5GoodCycle_fair

theorem w5BadRank_decreases_from
    (c : Config w5Spec)
    (hbad : c ∉ w5GoodCycleConfigs)
    (i : Fin 5)
    (hpriv : privileged w5System c i)
    (hnext : move w5System c i ∉ w5GoodCycleConfigs) :
    w5BadRank (move w5System c i) < w5BadRank c := by
  native_decide +revert

theorem w5BadRank_decreases :
    ∀ {c' c : Config w5Spec},
      badStep w5System w5GoodCycle c' c → w5BadRank c' < w5BadRank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact w5BadRank_decreases_from c hbad i hpriv hnext

theorem w5_converges : converges w5System w5GoodCycle := by
  let f : Config w5Spec → Nat := w5BadRank
  let r : Config w5Spec → Config w5Spec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := by
    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)
  refine Subrelation.wf (r := r) ?_ hwf
  intro c' c hstep
  exact w5BadRank_decreases hstep

theorem w5_valid : valid w5System := by
  exact ⟨w5GoodCycle, w5_converges⟩

/-! ### Witness n=6, ms=(2, 2, 2, 4, 3, 3), product=288 -/

def w6M (i : Fin 6) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 4
  | 4 => 3
  | _ => 3

def w6Spec : RingSpec where
  n := 6
  n_ge_4 := by omega
  m := w6M
  m_pos := by intro i; fin_cases i <;> simp [w6M]

private def w6P0 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 0
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 0
  | _, _, _ => 0

private def w6P1 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | _, _, _ => 0

private def w6P2 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 1
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 1
  | 1, 0, 3 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 1
  | 1, 1, 3 => 1
  | _, _, _ => 0

private def w6P3 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 3
  | 0, 1, 0 => 2
  | 0, 1, 1 => 3
  | 0, 1, 2 => 1
  | 0, 2, 0 => 2
  | 0, 2, 1 => 2
  | 0, 2, 2 => 1
  | 0, 3, 0 => 2
  | 0, 3, 1 => 0
  | 0, 3, 2 => 3
  | 1, 0, 0 => 1
  | 1, 0, 1 => 2
  | 1, 0, 2 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 0
  | 1, 2, 0 => 3
  | 1, 2, 1 => 2
  | 1, 2, 2 => 2
  | 1, 3, 0 => 3
  | 1, 3, 1 => 0
  | 1, 3, 2 => 0
  | _, _, _ => 0

private def w6P4 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 2
  | 0, 0, 2 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 2
  | 0, 1, 2 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 2
  | 0, 2, 2 => 2
  | 1, 0, 0 => 0
  | 1, 0, 1 => 2
  | 1, 0, 2 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 0
  | 1, 1, 2 => 0
  | 1, 2, 0 => 0
  | 1, 2, 1 => 2
  | 1, 2, 2 => 2
  | 2, 0, 0 => 0
  | 2, 0, 1 => 1
  | 2, 0, 2 => 1
  | 2, 1, 0 => 2
  | 2, 1, 1 => 1
  | 2, 1, 2 => 2
  | 2, 2, 0 => 2
  | 2, 2, 1 => 2
  | 2, 2, 2 => 2
  | 3, 0, 0 => 1
  | 3, 0, 1 => 0
  | 3, 0, 2 => 0
  | 3, 1, 0 => 1
  | 3, 1, 1 => 0
  | 3, 1, 2 => 1
  | 3, 2, 0 => 0
  | 3, 2, 1 => 0
  | 3, 2, 2 => 1
  | _, _, _ => 0

private def w6P5 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 2
  | 1, 1, 1 => 1
  | 1, 2, 0 => 2
  | 1, 2, 1 => 0
  | 2, 0, 0 => 1
  | 2, 0, 1 => 1
  | 2, 1, 0 => 1
  | 2, 1, 1 => 1
  | 2, 2, 0 => 2
  | 2, 2, 1 => 0
  | _, _, _ => 0

def w6OutVal (i L S R : Nat) : Nat :=
  match i with
  | 0 => w6P0 L S R
  | 1 => w6P1 L S R
  | 2 => w6P2 L S R
  | 3 => w6P3 L S R
  | 4 => w6P4 L S R
  | _ => w6P5 L S R

private lemma w6OutVal_lt (i : Fin 6)
    (L : Fin (w6Spec.m (left i)))
    (S : Fin (w6Spec.m i))
    (R : Fin (w6Spec.m (right i))) :
    w6OutVal i.val L.val S.val R.val < w6Spec.m i := by
  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp_all [w6OutVal, w6P0, w6P1, w6P2, w6P3, w6P4, w6P5, w6Spec, w6M]

def w6Trans : TransFn w6Spec := by
  intro i L S R
  exact ⟨w6OutVal i.val L.val S.val R.val, w6OutVal_lt i L S R⟩

def w6System : System where
  rs := w6Spec
  f := w6Trans

theorem w6_stateProduct : stateProduct w6Spec = 288 := by
  simp [stateProduct, w6Spec, w6M, Fin.prod_univ_succ]

def w6Cfg (x0 : Fin 2) (x1 : Fin 2) (x2 : Fin 2) (x3 : Fin 4) (x4 : Fin 3) (x5 : Fin 3) : Config w6Spec
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3
  | ⟨4, _⟩ => x4
  | ⟨5, _⟩ => x5

def w6CfgCode (c : Config w6Spec) : Nat :=
  (c ⟨0, by decide⟩).1 + 2 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 2 * ((c ⟨3, by decide⟩).1 + 4 * ((c ⟨4, by decide⟩).1 + 3 * ((c ⟨5, by decide⟩).1)))))

def w6CfgOfCode (k : Nat) : Config w6Spec :=
  w6Cfg
    ⟨(k / 1) % 2, by omega⟩
    ⟨(k / 2) % 2, by omega⟩
    ⟨(k / 4) % 2, by omega⟩
    ⟨(k / 8) % 4, by omega⟩
    ⟨(k / 32) % 3, by omega⟩
    ⟨(k / 96) % 3, by omega⟩

def w6GoodCycleCodes : List Nat := [0, 1, 3, 7, 15, 11, 19, 23, 31, 63, 39, 55, 87, 183, 182, 180, 176, 168, 172, 164, 160, 184, 120, 112, 144, 240, 272, 264, 268, 260, 256, 280, 248, 224, 192]

def w6GoodCycleConfigs : List (Config w6Spec) :=
  w6GoodCycleCodes.map w6CfgOfCode

def w6RankVals : List Nat := [0, 0, 29, 0, 3, 2, 28, 0, 3, 2, 26, 0, 2, 1, 27, 0, 2, 1, 25, 0, 23, 22, 24, 0, 5, 4, 26, 3, 22, 21, 23, 0, 3, 2, 22, 1, 20, 19, 21, 0, 7, 6, 27, 3, 6, 5, 28, 4, 18, 17, 29, 5, 19, 18, 20, 0, 4, 3, 23, 2, 21, 20, 22, 0, 13, 12, 30, 11, 14, 13, 29, 3, 16, 15, 27, 3, 15, 14, 30, 4, 17, 16, 28, 4, 18, 17, 19, 0, 12, 11, 27, 10, 25, 24, 30, 5, 1, 12, 10, 11, 2, 15, 9, 10, 2, 15, 7, 8, 1, 14, 8, 9, 0, 8, 6, 7, 4, 23, 5, 6, 0, 9, 7, 8, 1, 22, 2, 3, 1, 34, 32, 33, 6, 35, 31, 32, 6, 38, 34, 35, 5, 37, 35, 36, 0, 7, 5, 6, 3, 8, 4, 5, 2, 35, 33, 34, 7, 36, 32, 33, 0, 11, 9, 10, 0, 12, 1, 2, 0, 14, 1, 2, 0, 13, 2, 3, 0, 15, 2, 3, 0, 16, 0, 0, 0, 10, 8, 9, 2, 23, 3, 4, 0, 32, 30, 31, 4, 33, 29, 30, 4, 43, 27, 28, 3, 30, 28, 29, 3, 42, 26, 27, 24, 45, 25, 26, 6, 43, 27, 28, 23, 44, 24, 25, 0, 33, 31, 32, 5, 43, 30, 31, 5, 44, 33, 34, 4, 36, 34, 35, 0, 41, 4, 6, 2, 42, 3, 4, 0, 34, 32, 33, 6, 44, 31, 32, 0, 36, 34, 35, 0, 37, 1, 4, 0, 39, 1, 4, 0, 38, 2, 5, 0, 40, 3, 5, 1, 41, 2, 3, 0, 35, 33, 34, 7, 45, 32, 33]

def w6BadRank (c : Config w6Spec) : Nat :=
  w6RankVals.getD (w6CfgCode c) 0

theorem w6GoodCycle_nonempty : w6GoodCycleConfigs ≠ [] := by
  decide

theorem w6GoodCycle_unique_privileged_aux :
    ∀ c ∈ w6GoodCycleConfigs,
      ∃ i, privileged w6System c i ∧
        ∀ j, privileged w6System c j → j = i := by
  native_decide

theorem w6GoodCycle_unique_privileged :
    ∀ c ∈ w6GoodCycleConfigs, ∃! i, privileged w6System c i := by
  intro c hc
  simpa [ExistsUnique] using w6GoodCycle_unique_privileged_aux c hc

theorem w6GoodCycle_closed :
    ∀ k : Fin w6GoodCycleConfigs.length,
      ∃ i,
        privileged w6System (w6GoodCycleConfigs.get k) i ∧
          w6GoodCycleConfigs.get (nextIndex w6GoodCycleConfigs k) =
            move w6System (w6GoodCycleConfigs.get k) i := by
  native_decide

theorem w6GoodCycle_distinct :
    ∀ j₁ j₂ : Fin w6GoodCycleConfigs.length,
      w6GoodCycleConfigs.get j₁ = w6GoodCycleConfigs.get j₂ → j₁ = j₂ := by
  native_decide

theorem w6GoodCycle_fair :
    ∀ i : Fin w6System.rs.n,
      ∃ k : Fin w6GoodCycleConfigs.length,
        ∃ j, privileged w6System (w6GoodCycleConfigs.get k) j ∧
          w6GoodCycleConfigs.get (nextIndex w6GoodCycleConfigs k) =
            move w6System (w6GoodCycleConfigs.get k) j ∧ j = i := by
  native_decide

def w6GoodCycle : GoodCycle w6System where
  configs := w6GoodCycleConfigs
  nonempty := w6GoodCycle_nonempty
  unique_privileged := w6GoodCycle_unique_privileged
  closed := w6GoodCycle_closed
  distinct := w6GoodCycle_distinct
  fair := w6GoodCycle_fair

theorem w6BadRank_decreases_from
    (c : Config w6Spec)
    (hbad : c ∉ w6GoodCycleConfigs)
    (i : Fin 6)
    (hpriv : privileged w6System c i)
    (hnext : move w6System c i ∉ w6GoodCycleConfigs) :
    w6BadRank (move w6System c i) < w6BadRank c := by
  native_decide +revert

theorem w6BadRank_decreases :
    ∀ {c' c : Config w6Spec},
      badStep w6System w6GoodCycle c' c → w6BadRank c' < w6BadRank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact w6BadRank_decreases_from c hbad i hpriv hnext

theorem w6_converges : converges w6System w6GoodCycle := by
  let f : Config w6Spec → Nat := w6BadRank
  let r : Config w6Spec → Config w6Spec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := by
    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)
  refine Subrelation.wf (r := r) ?_ hwf
  intro c' c hstep
  exact w6BadRank_decreases hstep

theorem w6_valid : valid w6System := by
  exact ⟨w6GoodCycle, w6_converges⟩

/-! ### Witness n=7, ms=(3, 2, 2, 2, 3, 4, 3), product=864 -/

def w7M (i : Fin 7) : Nat :=
  match i.val with
  | 0 => 3
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 3

def w7Spec : RingSpec where
  n := 7
  n_ge_4 := by omega
  m := w7M
  m_pos := by intro i; fin_cases i <;> simp [w7M]

private def w7P0 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 0
  | 0, 1, 0 => 2
  | 0, 1, 1 => 0
  | 0, 2, 0 => 2
  | 0, 2, 1 => 2
  | 1, 0, 0 => 1
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 2, 0 => 2
  | 1, 2, 1 => 2
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 1
  | 2, 2, 0 => 2
  | 2, 2, 1 => 0
  | _, _, _ => 0

private def w7P1 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 0
  | 2, 0, 0 => 1
  | 2, 0, 1 => 0
  | 2, 1, 0 => 1
  | 2, 1, 1 => 1
  | _, _, _ => 0

private def w7P2 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | _, _, _ => 0

private def w7P3 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 0, 1, 2 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 1
  | _, _, _ => 0

private def w7P4 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 2
  | 0, 1, 1 => 1
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 0, 2, 0 => 2
  | 0, 2, 1 => 1
  | 0, 2, 2 => 2
  | 0, 2, 3 => 2
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 2
  | 1, 0, 3 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 1, 2, 0 => 2
  | 1, 2, 1 => 0
  | 1, 2, 2 => 2
  | 1, 2, 3 => 2
  | _, _, _ => 0

private def w7P5 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 3
  | 0, 1, 1 => 1
  | 0, 1, 2 => 1
  | 0, 2, 0 => 2
  | 0, 2, 1 => 0
  | 0, 2, 2 => 1
  | 0, 3, 0 => 3
  | 0, 3, 1 => 0
  | 0, 3, 2 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 2
  | 1, 1, 1 => 3
  | 1, 1, 2 => 0
  | 1, 2, 0 => 2
  | 1, 2, 1 => 0
  | 1, 2, 2 => 0
  | 1, 3, 0 => 0
  | 1, 3, 1 => 3
  | 1, 3, 2 => 1
  | 2, 0, 0 => 1
  | 2, 0, 1 => 2
  | 2, 0, 2 => 0
  | 2, 1, 0 => 1
  | 2, 1, 1 => 1
  | 2, 1, 2 => 2
  | 2, 2, 0 => 0
  | 2, 2, 1 => 2
  | 2, 2, 2 => 2
  | 2, 3, 0 => 0
  | 2, 3, 1 => 0
  | 2, 3, 2 => 1
  | _, _, _ => 0

private def w7P6 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 2
  | 0, 1, 2 => 1
  | 0, 2, 0 => 0
  | 0, 2, 1 => 2
  | 0, 2, 2 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 0
  | 1, 2, 0 => 1
  | 1, 2, 1 => 0
  | 1, 2, 2 => 0
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 0, 2 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 0
  | 2, 1, 2 => 2
  | 2, 2, 0 => 0
  | 2, 2, 1 => 0
  | 2, 2, 2 => 2
  | 3, 0, 0 => 2
  | 3, 0, 1 => 0
  | 3, 0, 2 => 1
  | 3, 1, 0 => 1
  | 3, 1, 1 => 1
  | 3, 1, 2 => 1
  | 3, 2, 0 => 2
  | 3, 2, 1 => 0
  | 3, 2, 2 => 0
  | _, _, _ => 0

def w7OutVal (i L S R : Nat) : Nat :=
  match i with
  | 0 => w7P0 L S R
  | 1 => w7P1 L S R
  | 2 => w7P2 L S R
  | 3 => w7P3 L S R
  | 4 => w7P4 L S R
  | 5 => w7P5 L S R
  | _ => w7P6 L S R

private lemma w7OutVal_lt (i : Fin 7)
    (L : Fin (w7Spec.m (left i)))
    (S : Fin (w7Spec.m i))
    (R : Fin (w7Spec.m (right i))) :
    w7OutVal i.val L.val S.val R.val < w7Spec.m i := by
  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp_all [w7OutVal, w7P0, w7P1, w7P2, w7P3, w7P4, w7P5, w7P6, w7Spec, w7M]

def w7Trans : TransFn w7Spec := by
  intro i L S R
  exact ⟨w7OutVal i.val L.val S.val R.val, w7OutVal_lt i L S R⟩

def w7System : System where
  rs := w7Spec
  f := w7Trans

theorem w7_stateProduct : stateProduct w7Spec = 864 := by
  simp [stateProduct, w7Spec, w7M, Fin.prod_univ_succ]

def w7Cfg (x0 : Fin 3) (x1 : Fin 2) (x2 : Fin 2) (x3 : Fin 2) (x4 : Fin 3) (x5 : Fin 4) (x6 : Fin 3) : Config w7Spec
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3
  | ⟨4, _⟩ => x4
  | ⟨5, _⟩ => x5
  | ⟨6, _⟩ => x6

def w7CfgCode (c : Config w7Spec) : Nat :=
  (c ⟨0, by decide⟩).1 + 3 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 2 * ((c ⟨3, by decide⟩).1 + 2 * ((c ⟨4, by decide⟩).1 + 3 * ((c ⟨5, by decide⟩).1 + 4 * ((c ⟨6, by decide⟩).1))))))

def w7CfgOfCode (k : Nat) : Config w7Spec :=
  w7Cfg
    ⟨(k / 1) % 3, by omega⟩
    ⟨(k / 3) % 2, by omega⟩
    ⟨(k / 6) % 2, by omega⟩
    ⟨(k / 12) % 2, by omega⟩
    ⟨(k / 24) % 3, by omega⟩
    ⟨(k / 72) % 4, by omega⟩
    ⟨(k / 288) % 3, by omega⟩

def w7GoodCycleCodes : List Nat := [0, 1, 2, 5, 11, 23, 47, 35, 59, 131, 107, 179, 155, 167, 215, 71, 143, 95, 239, 527, 311, 335, 323, 347, 491, 779, 777, 201, 57, 129, 105, 177, 153, 165, 213, 69, 141, 93, 237, 813, 669, 381, 382, 379, 373, 361, 385, 529, 505, 289, 577, 576]

def w7GoodCycleConfigs : List (Config w7Spec) :=
  w7GoodCycleCodes.map w7CfgOfCode

def w7RankVals : List Nat := [0, 0, 0, 5, 38, 0, 37, 36, 35, 4, 37, 0, 11, 10, 9, 12, 39, 8, 36, 35, 34, 3, 36, 0, 9, 8, 7, 10, 35, 6, 34, 33, 32, 1, 34, 0, 10, 9, 8, 11, 36, 7, 35, 34, 33, 2, 35, 0, 8, 7, 6, 9, 34, 5, 33, 32, 31, 0, 33, 0, 25, 24, 23, 54, 55, 22, 26, 25, 24, 0, 26, 0, 15, 7, 6, 51, 52, 5, 49, 31, 30, 50, 51, 4, 23, 22, 21, 52, 53, 20, 24, 23, 22, 0, 24, 0, 6, 5, 4, 7, 32, 3, 31, 30, 29, 0, 31, 0, 29, 28, 27, 58, 59, 26, 32, 31, 30, 2, 32, 2, 7, 6, 5, 8, 33, 4, 32, 31, 30, 0, 32, 0, 24, 23, 22, 53, 54, 21, 25, 24, 23, 0, 25, 0, 4, 3, 2, 5, 30, 1, 29, 28, 27, 0, 29, 0, 27, 26, 25, 56, 57, 24, 28, 27, 26, 0, 28, 0, 5, 4, 3, 6, 31, 2, 30, 29, 28, 0, 30, 0, 28, 27, 26, 57, 58, 25, 31, 30, 29, 1, 31, 1, 9, 8, 7, 10, 35, 6, 34, 33, 32, 0, 34, 1, 26, 25, 24, 55, 56, 23, 27, 26, 25, 0, 27, 0, 14, 6, 5, 50, 51, 4, 48, 23, 22, 49, 50, 3, 22, 21, 20, 51, 52, 19, 23, 22, 21, 0, 23, 0, 15, 9, 8, 51, 52, 7, 49, 34, 33, 50, 51, 4, 23, 22, 21, 52, 53, 20, 50, 35, 34, 51, 52, 5, 19, 18, 17, 50, 51, 16, 48, 33, 32, 49, 50, 2, 64, 63, 62, 65, 66, 61, 65, 64, 63, 8, 65, 6, 1, 0, 3, 43, 42, 2, 41, 40, 20, 42, 41, 1, 15, 14, 18, 44, 43, 17, 40, 39, 19, 41, 40, 0, 13, 12, 16, 40, 39, 15, 38, 37, 17, 39, 38, 0, 14, 13, 17, 41, 40, 16, 39, 38, 18, 40, 39, 0, 12, 11, 15, 39, 38, 14, 37, 36, 16, 38, 37, 0, 29, 28, 60, 59, 58, 59, 30, 29, 61, 31, 30, 4, 5, 0, 7, 47, 46, 6, 45, 44, 31, 46, 45, 5, 6, 0, 22, 48, 47, 21, 7, 0, 23, 0, 0, 1, 4, 0, 6, 46, 45, 5, 44, 43, 30, 45, 44, 4, 18, 17, 28, 49, 48, 27, 45, 44, 31, 46, 45, 5, 5, 1, 7, 47, 46, 6, 45, 44, 31, 46, 45, 5, 7, 2, 23, 49, 48, 22, 8, 3, 24, 5, 4, 2, 5, 4, 52, 44, 43, 51, 42, 41, 62, 43, 42, 50, 28, 27, 60, 59, 58, 59, 41, 40, 61, 42, 41, 4, 14, 13, 53, 45, 44, 52, 43, 42, 63, 44, 43, 51, 29, 28, 61, 60, 59, 60, 44, 43, 64, 45, 44, 52, 10, 9, 14, 37, 36, 13, 35, 34, 15, 36, 35, 0, 27, 26, 59, 58, 57, 58, 28, 27, 60, 29, 28, 3, 2, 0, 4, 44, 43, 3, 42, 41, 21, 43, 42, 2, 16, 15, 19, 45, 44, 18, 41, 40, 20, 42, 41, 0, 3, 0, 5, 45, 44, 4, 43, 42, 22, 44, 43, 3, 17, 16, 20, 46, 45, 19, 44, 43, 23, 45, 44, 4, 13, 12, 16, 40, 39, 15, 38, 37, 17, 39, 38, 1, 30, 29, 61, 60, 59, 60, 31, 30, 62, 32, 31, 5, 0, 0, 8, 6, 41, 7, 38, 39, 36, 5, 40, 6, 12, 13, 15, 13, 42, 14, 37, 38, 35, 4, 39, 5, 10, 11, 13, 11, 38, 12, 35, 36, 33, 2, 37, 3, 11, 12, 14, 12, 39, 13, 36, 37, 34, 3, 38, 4, 9, 10, 12, 10, 37, 11, 34, 35, 32, 1, 36, 2, 26, 27, 57, 55, 38, 56, 27, 28, 58, 1, 29, 2, 12, 13, 50, 48, 53, 49, 46, 47, 53, 47, 52, 48, 13, 23, 51, 49, 54, 50, 14, 24, 52, 0, 25, 1, 11, 12, 49, 47, 48, 48, 45, 46, 50, 46, 47, 47, 19, 29, 52, 50, 60, 51, 46, 47, 53, 47, 48, 48, 12, 13, 50, 48, 49, 49, 46, 47, 51, 47, 48, 48, 28, 29, 59, 57, 58, 58, 29, 30, 60, 6, 31, 7, 13, 14, 51, 49, 54, 50, 47, 48, 61, 48, 53, 49, 28, 29, 59, 57, 58, 58, 29, 30, 60, 2, 31, 3, 14, 15, 52, 50, 55, 51, 48, 49, 62, 49, 54, 50, 29, 30, 60, 58, 59, 59, 49, 50, 63, 50, 55, 51, 10, 11, 13, 11, 38, 12, 35, 36, 14, 0, 37, 0, 27, 28, 58, 56, 57, 57, 28, 29, 59, 1, 30, 2, 13, 14, 51, 49, 54, 50, 47, 48, 54, 48, 53, 49, 14, 24, 52, 50, 55, 51, 15, 25, 53, 0, 26, 2, 14, 15, 52, 50, 55, 51, 48, 49, 55, 49, 54, 50, 20, 30, 53, 51, 61, 52, 49, 50, 56, 50, 55, 51, 13, 19, 51, 49, 52, 50, 47, 48, 52, 48, 51, 49, 29, 64, 63, 58, 67, 62, 30, 65, 64, 7, 66, 8]

def w7BadRank (c : Config w7Spec) : Nat :=
  w7RankVals.getD (w7CfgCode c) 0

theorem w7GoodCycle_nonempty : w7GoodCycleConfigs ≠ [] := by
  decide

theorem w7GoodCycle_unique_privileged_aux :
    ∀ c ∈ w7GoodCycleConfigs,
      ∃ i, privileged w7System c i ∧
        ∀ j, privileged w7System c j → j = i := by
  native_decide

theorem w7GoodCycle_unique_privileged :
    ∀ c ∈ w7GoodCycleConfigs, ∃! i, privileged w7System c i := by
  intro c hc
  simpa [ExistsUnique] using w7GoodCycle_unique_privileged_aux c hc

theorem w7GoodCycle_closed :
    ∀ k : Fin w7GoodCycleConfigs.length,
      ∃ i,
        privileged w7System (w7GoodCycleConfigs.get k) i ∧
          w7GoodCycleConfigs.get (nextIndex w7GoodCycleConfigs k) =
            move w7System (w7GoodCycleConfigs.get k) i := by
  native_decide

theorem w7GoodCycle_distinct :
    ∀ j₁ j₂ : Fin w7GoodCycleConfigs.length,
      w7GoodCycleConfigs.get j₁ = w7GoodCycleConfigs.get j₂ → j₁ = j₂ := by
  native_decide

theorem w7GoodCycle_fair :
    ∀ i : Fin w7System.rs.n,
      ∃ k : Fin w7GoodCycleConfigs.length,
        ∃ j, privileged w7System (w7GoodCycleConfigs.get k) j ∧
          w7GoodCycleConfigs.get (nextIndex w7GoodCycleConfigs k) =
            move w7System (w7GoodCycleConfigs.get k) j ∧ j = i := by
  native_decide

def w7GoodCycle : GoodCycle w7System where
  configs := w7GoodCycleConfigs
  nonempty := w7GoodCycle_nonempty
  unique_privileged := w7GoodCycle_unique_privileged
  closed := w7GoodCycle_closed
  distinct := w7GoodCycle_distinct
  fair := w7GoodCycle_fair

theorem w7BadRank_decreases_from
    (c : Config w7Spec)
    (hbad : c ∉ w7GoodCycleConfigs)
    (i : Fin 7)
    (hpriv : privileged w7System c i)
    (hnext : move w7System c i ∉ w7GoodCycleConfigs) :
    w7BadRank (move w7System c i) < w7BadRank c := by
  native_decide +revert

theorem w7BadRank_decreases :
    ∀ {c' c : Config w7Spec},
      badStep w7System w7GoodCycle c' c → w7BadRank c' < w7BadRank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact w7BadRank_decreases_from c hbad i hpriv hnext

theorem w7_converges : converges w7System w7GoodCycle := by
  let f : Config w7Spec → Nat := w7BadRank
  let r : Config w7Spec → Config w7Spec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := by
    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)
  refine Subrelation.wf (r := r) ?_ hwf
  intro c' c hstep
  exact w7BadRank_decreases hstep

theorem w7_valid : valid w7System := by
  exact ⟨w7GoodCycle, w7_converges⟩

/-! ### Witness n=8, ms=(2, 2, 3, 4, 3, 3, 2, 3), product=2592 -/

def w8M (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | _ => 3

def w8Spec : RingSpec where
  n := 8
  n_ge_4 := by omega
  m := w8M
  m_pos := by intro i; fin_cases i <;> simp [w8M]

private def w8P0 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 0
  | _, _, _ => 0

private def w8P1 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 0, 1, 2 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 1
  | _, _, _ => 0

private def w8P2 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 2
  | 0, 1, 1 => 1
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 0, 2, 0 => 2
  | 0, 2, 1 => 1
  | 0, 2, 2 => 2
  | 0, 2, 3 => 1
  | 1, 0, 0 => 1
  | 1, 0, 1 => 0
  | 1, 0, 2 => 2
  | 1, 0, 3 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0
  | 1, 1, 2 => 2
  | 1, 1, 3 => 0
  | 1, 2, 0 => 2
  | 1, 2, 1 => 0
  | 1, 2, 2 => 2
  | 1, 2, 3 => 0
  | _, _, _ => 0

private def w8P3 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 3
  | 0, 1, 0 => 3
  | 0, 1, 1 => 1
  | 0, 1, 2 => 1
  | 0, 2, 0 => 2
  | 0, 2, 1 => 0
  | 0, 2, 2 => 0
  | 0, 3, 0 => 3
  | 0, 3, 1 => 0
  | 0, 3, 2 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 2
  | 1, 1, 1 => 3
  | 1, 1, 2 => 0
  | 1, 2, 0 => 2
  | 1, 2, 1 => 0
  | 1, 2, 2 => 0
  | 1, 3, 0 => 0
  | 1, 3, 1 => 3
  | 1, 3, 2 => 0
  | 2, 0, 0 => 1
  | 2, 0, 1 => 2
  | 2, 0, 2 => 0
  | 2, 1, 0 => 1
  | 2, 1, 1 => 0
  | 2, 1, 2 => 0
  | 2, 2, 0 => 0
  | 2, 2, 1 => 2
  | 2, 2, 2 => 2
  | 2, 3, 0 => 0
  | 2, 3, 1 => 0
  | 2, 3, 2 => 1
  | _, _, _ => 0

private def w8P4 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 0
  | 0, 1, 2 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 0
  | 0, 2, 2 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 1
  | 1, 1, 2 => 1
  | 1, 2, 0 => 0
  | 1, 2, 1 => 1
  | 1, 2, 2 => 1
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 0, 2 => 0
  | 2, 1, 0 => 2
  | 2, 1, 1 => 0
  | 2, 1, 2 => 0
  | 2, 2, 0 => 2
  | 2, 2, 1 => 0
  | 2, 2, 2 => 0
  | 3, 0, 0 => 1
  | 3, 0, 1 => 2
  | 3, 0, 2 => 0
  | 3, 1, 0 => 1
  | 3, 1, 1 => 1
  | 3, 1, 2 => 1
  | 3, 2, 0 => 0
  | 3, 2, 1 => 2
  | 3, 2, 2 => 0
  | _, _, _ => 0

private def w8P5 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 2
  | 1, 1, 1 => 0
  | 1, 2, 0 => 2
  | 1, 2, 1 => 2
  | 2, 0, 0 => 1
  | 2, 0, 1 => 0
  | 2, 1, 0 => 1
  | 2, 1, 1 => 1
  | 2, 2, 0 => 0
  | 2, 2, 1 => 0
  | _, _, _ => 0

private def w8P6 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 1
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 0, 1, 2 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 0, 2 => 1
  | 1, 1, 0 => 0
  | 1, 1, 1 => 1
  | 1, 1, 2 => 1
  | 2, 0, 0 => 1
  | 2, 0, 1 => 0
  | 2, 0, 2 => 0
  | 2, 1, 0 => 1
  | 2, 1, 1 => 0
  | 2, 1, 2 => 0
  | _, _, _ => 0

private def w8P7 (L S R : Nat) : Nat :=
  match L, S, R with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 2
  | 0, 2, 0 => 2
  | 0, 2, 1 => 2
  | 1, 0, 0 => 0
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 2, 0 => 1
  | 1, 2, 1 => 2
  | _, _, _ => 0

def w8OutVal (i L S R : Nat) : Nat :=
  match i with
  | 0 => w8P0 L S R
  | 1 => w8P1 L S R
  | 2 => w8P2 L S R
  | 3 => w8P3 L S R
  | 4 => w8P4 L S R
  | 5 => w8P5 L S R
  | 6 => w8P6 L S R
  | _ => w8P7 L S R

private lemma w8OutVal_lt (i : Fin 8)
    (L : Fin (w8Spec.m (left i)))
    (S : Fin (w8Spec.m i))
    (R : Fin (w8Spec.m (right i))) :
    w8OutVal i.val L.val S.val R.val < w8Spec.m i := by
  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp_all [w8OutVal, w8P0, w8P1, w8P2, w8P3, w8P4, w8P5, w8P6, w8P7, w8Spec, w8M]

def w8Trans : TransFn w8Spec := by
  intro i L S R
  exact ⟨w8OutVal i.val L.val S.val R.val, w8OutVal_lt i L S R⟩

def w8System : System where
  rs := w8Spec
  f := w8Trans

theorem w8_stateProduct : stateProduct w8Spec = 2592 := by
  simp [stateProduct, w8Spec, w8M, Fin.prod_univ_succ]

def w8Cfg (x0 : Fin 2) (x1 : Fin 2) (x2 : Fin 3) (x3 : Fin 4) (x4 : Fin 3) (x5 : Fin 3) (x6 : Fin 2) (x7 : Fin 3) : Config w8Spec
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3
  | ⟨4, _⟩ => x4
  | ⟨5, _⟩ => x5
  | ⟨6, _⟩ => x6
  | ⟨7, _⟩ => x7

def w8CfgCode (c : Config w8Spec) : Nat :=
  (c ⟨0, by decide⟩).1 + 2 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 3 * ((c ⟨3, by decide⟩).1 + 4 * ((c ⟨4, by decide⟩).1 + 3 * ((c ⟨5, by decide⟩).1 + 3 * ((c ⟨6, by decide⟩).1 + 2 * ((c ⟨7, by decide⟩).1)))))))

def w8CfgOfCode (k : Nat) : Config w8Spec :=
  w8Cfg
    ⟨(k / 1) % 2, by omega⟩
    ⟨(k / 2) % 2, by omega⟩
    ⟨(k / 4) % 3, by omega⟩
    ⟨(k / 12) % 4, by omega⟩
    ⟨(k / 48) % 3, by omega⟩
    ⟨(k / 144) % 3, by omega⟩
    ⟨(k / 432) % 2, by omega⟩
    ⟨(k / 864) % 3, by omega⟩

def w8GoodCycleCodes : List Nat := [0, 1, 3, 7, 5, 9, 21, 17, 29, 25, 27, 35, 11, 23, 15, 39, 87, 51, 55, 53, 57, 81, 129, 273, 177, 153, 165, 161, 173, 169, 171, 179, 155, 167, 159, 183, 279, 255, 207, 351, 783, 1647, 1215, 2079, 2078, 2076, 2080, 2104, 2100, 2064, 2016, 1728, 2160, 1296, 864]

def w8GoodCycleConfigs : List (Config w8Spec) :=
  w8GoodCycleCodes.map w8CfgOfCode

def w8RankVals : List Nat := [0, 0, 8, 0, 6, 0, 7, 0, 5, 0, 18, 0, 5, 4, 16, 0, 3, 0, 21, 2, 4, 0, 17, 0, 1, 0, 20, 0, 2, 0, 20, 1, 6, 1, 19, 0, 4, 3, 15, 0, 7, 4, 16, 5, 12, 5, 88, 6, 2, 1, 13, 0, 11, 0, 12, 0, 10, 0, 86, 4, 6, 5, 17, 1, 5, 4, 22, 5, 11, 5, 87, 5, 80, 79, 86, 7, 81, 80, 86, 81, 9, 0, 85, 3, 3, 2, 14, 0, 4, 3, 15, 4, 11, 4, 87, 5, 78, 77, 79, 5, 8, 3, 9, 4, 7, 2, 83, 2, 76, 75, 77, 1, 75, 74, 78, 75, 76, 75, 87, 61, 79, 78, 85, 6, 80, 79, 85, 80, 8, 0, 84, 2, 77, 76, 78, 2, 78, 77, 79, 78, 79, 78, 89, 62, 5, 4, 8, 3, 6, 1, 7, 2, 5, 0, 81, 0, 78, 77, 79, 0, 3, 0, 84, 2, 4, 0, 80, 0, 1, 0, 83, 0, 2, 0, 83, 1, 6, 0, 82, 0, 77, 76, 78, 0, 78, 77, 79, 78, 79, 78, 88, 62, 70, 69, 71, 68, 67, 66, 68, 67, 66, 65, 84, 58, 74, 73, 75, 0, 73, 72, 76, 73, 74, 73, 85, 59, 71, 70, 84, 69, 72, 71, 84, 72, 65, 64, 83, 57, 71, 70, 72, 69, 72, 71, 73, 72, 73, 72, 85, 70, 77, 76, 78, 4, 7, 2, 8, 3, 6, 1, 82, 1, 75, 74, 76, 0, 74, 73, 77, 74, 75, 74, 86, 60, 78, 77, 84, 5, 79, 78, 84, 79, 7, 0, 83, 1, 76, 75, 77, 0, 77, 76, 78, 77, 78, 77, 87, 61, 66, 65, 67, 64, 63, 62, 64, 63, 62, 61, 64, 54, 61, 60, 62, 52, 60, 59, 67, 60, 61, 60, 63, 53, 58, 57, 66, 56, 59, 58, 66, 59, 63, 62, 65, 55, 53, 52, 54, 51, 64, 63, 65, 64, 65, 64, 91, 98, 69, 68, 70, 67, 66, 65, 67, 66, 65, 64, 67, 57, 73, 72, 74, 0, 72, 71, 75, 72, 73, 72, 75, 58, 70, 69, 71, 68, 71, 70, 72, 71, 64, 63, 66, 56, 70, 69, 71, 68, 71, 70, 72, 71, 72, 71, 73, 69, 91, 90, 92, 89, 64, 63, 65, 64, 63, 62, 86, 93, 89, 88, 90, 87, 86, 85, 91, 88, 87, 86, 91, 100, 97, 96, 98, 95, 98, 97, 99, 98, 64, 63, 87, 94, 90, 89, 91, 88, 91, 90, 92, 91, 92, 91, 93, 101, 64, 63, 65, 62, 61, 60, 62, 61, 60, 59, 62, 52, 59, 58, 60, 50, 58, 57, 65, 58, 59, 58, 61, 51, 56, 55, 64, 54, 57, 56, 64, 57, 61, 60, 63, 53, 51, 50, 52, 49, 62, 61, 63, 62, 63, 62, 89, 96, 49, 48, 50, 47, 46, 45, 47, 46, 45, 44, 87, 94, 60, 59, 61, 51, 59, 58, 66, 59, 60, 59, 88, 95, 96, 95, 97, 94, 97, 96, 98, 97, 44, 43, 86, 93, 50, 49, 51, 48, 51, 50, 52, 51, 52, 51, 88, 95, 89, 88, 90, 87, 62, 61, 63, 62, 61, 60, 84, 91, 87, 86, 88, 85, 84, 83, 89, 86, 85, 84, 89, 98, 95, 94, 96, 93, 96, 95, 97, 96, 43, 42, 85, 92, 88, 87, 89, 86, 89, 88, 90, 89, 90, 89, 91, 99, 70, 69, 71, 68, 67, 66, 68, 67, 66, 65, 84, 58, 81, 80, 82, 56, 64, 63, 87, 64, 65, 64, 83, 57, 62, 61, 86, 60, 63, 62, 86, 63, 67, 66, 85, 59, 80, 79, 81, 55, 81, 80, 82, 81, 82, 81, 92, 99, 73, 72, 74, 71, 70, 69, 71, 70, 69, 68, 88, 95, 77, 76, 78, 52, 76, 75, 79, 76, 77, 76, 89, 96, 97, 96, 98, 95, 98, 97, 99, 98, 68, 67, 87, 94, 74, 73, 75, 72, 75, 74, 76, 75, 76, 75, 89, 96, 80, 79, 81, 69, 68, 67, 69, 68, 67, 66, 85, 59, 78, 77, 79, 53, 77, 76, 80, 77, 78, 77, 90, 97, 81, 80, 87, 70, 82, 81, 87, 82, 68, 67, 86, 60, 79, 78, 80, 54, 80, 79, 81, 80, 81, 80, 91, 98, 65, 64, 66, 63, 62, 61, 63, 62, 61, 60, 63, 53, 60, 59, 61, 51, 59, 58, 66, 59, 60, 59, 62, 52, 57, 56, 65, 55, 58, 57, 65, 58, 62, 61, 64, 54, 52, 51, 53, 50, 63, 62, 64, 63, 64, 63, 90, 97, 68, 67, 69, 66, 65, 64, 66, 65, 64, 63, 66, 56, 72, 71, 73, 0, 71, 70, 74, 71, 72, 71, 74, 57, 69, 68, 70, 67, 70, 69, 71, 70, 63, 62, 65, 55, 69, 68, 70, 67, 70, 69, 71, 70, 71, 70, 72, 68, 90, 89, 91, 88, 63, 62, 64, 63, 62, 61, 85, 92, 88, 87, 89, 86, 85, 84, 90, 87, 86, 85, 90, 99, 96, 95, 97, 94, 97, 96, 98, 97, 63, 62, 86, 93, 89, 88, 90, 87, 90, 89, 91, 90, 91, 90, 92, 100, 0, 61, 9, 60, 7, 58, 8, 59, 6, 57, 19, 50, 6, 56, 17, 48, 4, 55, 22, 56, 5, 56, 18, 49, 2, 53, 21, 52, 3, 54, 21, 55, 7, 58, 20, 51, 5, 48, 16, 47, 8, 59, 17, 60, 13, 60, 89, 94, 3, 46, 14, 45, 12, 43, 13, 44, 11, 42, 87, 92, 7, 57, 18, 49, 6, 56, 23, 57, 12, 57, 88, 93, 81, 93, 87, 92, 82, 94, 87, 95, 10, 41, 86, 91, 4, 47, 15, 46, 5, 48, 16, 49, 12, 49, 88, 93, 79, 86, 80, 85, 9, 59, 10, 60, 8, 58, 84, 89, 77, 84, 78, 83, 76, 81, 79, 84, 77, 82, 88, 96, 80, 92, 86, 91, 81, 93, 86, 94, 9, 40, 85, 90, 78, 85, 79, 84, 79, 86, 80, 87, 80, 87, 90, 97, 6, 41, 9, 40, 7, 38, 8, 39, 6, 37, 82, 30, 79, 74, 80, 28, 4, 35, 85, 36, 5, 36, 81, 29, 2, 33, 84, 32, 3, 34, 84, 35, 7, 38, 83, 31, 78, 73, 79, 27, 79, 74, 80, 75, 80, 75, 89, 97, 71, 66, 72, 65, 68, 63, 69, 64, 67, 62, 85, 93, 75, 70, 76, 24, 74, 69, 77, 70, 75, 70, 86, 94, 72, 94, 85, 93, 73, 95, 85, 96, 66, 61, 84, 92, 72, 67, 73, 66, 73, 68, 74, 69, 74, 69, 86, 94, 78, 73, 79, 41, 8, 39, 9, 40, 7, 38, 83, 31, 76, 71, 77, 25, 75, 70, 78, 71, 76, 71, 87, 95, 79, 74, 85, 42, 80, 75, 85, 76, 8, 39, 84, 32, 77, 72, 78, 26, 78, 73, 79, 74, 79, 74, 88, 96, 67, 62, 68, 61, 64, 59, 65, 60, 63, 58, 65, 51, 62, 57, 63, 49, 61, 56, 68, 57, 62, 57, 64, 50, 59, 54, 67, 53, 60, 55, 67, 56, 64, 59, 66, 52, 54, 49, 55, 48, 65, 60, 66, 61, 66, 61, 92, 95, 70, 65, 71, 64, 67, 62, 68, 63, 66, 61, 68, 54, 74, 69, 75, 0, 73, 68, 76, 69, 74, 69, 76, 55, 71, 66, 72, 65, 72, 67, 73, 68, 65, 60, 67, 53, 71, 66, 72, 65, 72, 67, 73, 68, 73, 68, 74, 66, 92, 87, 93, 86, 65, 60, 66, 61, 64, 59, 87, 90, 90, 85, 91, 84, 87, 82, 92, 85, 88, 83, 92, 97, 98, 93, 99, 92, 99, 94, 100, 95, 65, 60, 88, 91, 91, 86, 92, 85, 92, 87, 93, 88, 93, 88, 94, 98, 0, 62, 10, 61, 8, 59, 9, 60, 7, 58, 20, 51, 7, 57, 18, 49, 5, 56, 23, 57, 6, 57, 19, 50, 3, 54, 22, 53, 4, 55, 22, 56, 8, 59, 21, 52, 6, 49, 17, 48, 9, 60, 18, 61, 14, 61, 90, 95, 4, 47, 15, 46, 13, 44, 14, 45, 12, 43, 88, 93, 8, 58, 19, 50, 7, 57, 24, 58, 13, 58, 89, 94, 82, 94, 88, 93, 83, 95, 88, 96, 11, 42, 87, 92, 5, 48, 16, 47, 6, 49, 17, 50, 13, 50, 89, 94, 80, 87, 81, 86, 10, 60, 11, 61, 9, 59, 85, 90, 78, 85, 79, 84, 77, 82, 80, 85, 78, 83, 89, 97, 81, 93, 87, 92, 82, 94, 87, 95, 10, 41, 86, 91, 79, 86, 80, 85, 80, 87, 81, 88, 81, 88, 91, 98, 1, 68, 11, 67, 9, 65, 10, 66, 8, 64, 26, 57, 15, 79, 24, 55, 6, 62, 29, 63, 7, 63, 25, 56, 4, 60, 28, 59, 5, 61, 28, 62, 9, 65, 27, 58, 14, 78, 23, 54, 15, 79, 24, 80, 17, 80, 93, 98, 5, 71, 16, 70, 14, 68, 15, 69, 13, 67, 89, 94, 9, 75, 20, 51, 8, 74, 25, 75, 14, 75, 90, 95, 83, 95, 89, 94, 84, 96, 89, 97, 12, 66, 88, 93, 6, 72, 17, 71, 7, 73, 18, 74, 14, 74, 90, 95, 14, 78, 23, 68, 10, 66, 11, 67, 9, 65, 27, 58, 12, 76, 21, 52, 11, 75, 26, 76, 15, 76, 91, 96, 15, 79, 29, 69, 16, 80, 29, 81, 10, 66, 28, 59, 13, 77, 22, 53, 14, 78, 23, 79, 16, 79, 92, 97, 68, 63, 69, 62, 65, 60, 66, 61, 64, 59, 66, 52, 63, 58, 64, 50, 62, 57, 69, 58, 63, 58, 65, 51, 60, 55, 68, 54, 61, 56, 68, 57, 65, 60, 67, 53, 55, 50, 56, 49, 66, 61, 67, 62, 67, 62, 93, 96, 71, 66, 72, 65, 68, 63, 69, 64, 67, 62, 69, 55, 75, 70, 76, 0, 74, 69, 77, 70, 75, 70, 77, 56, 72, 67, 73, 66, 73, 68, 74, 69, 66, 61, 68, 54, 72, 67, 73, 66, 73, 68, 74, 69, 74, 69, 75, 67, 93, 88, 94, 87, 66, 61, 67, 62, 65, 60, 88, 91, 91, 86, 92, 85, 88, 83, 93, 86, 89, 84, 93, 98, 99, 94, 100, 93, 100, 95, 101, 96, 66, 61, 89, 92, 92, 87, 93, 86, 93, 88, 94, 89, 94, 89, 95, 99, 0, 60, 12, 59, 10, 57, 11, 58, 9, 56, 23, 49, 9, 55, 21, 47, 7, 54, 26, 55, 8, 55, 22, 48, 5, 52, 25, 51, 6, 53, 25, 54, 10, 57, 24, 50, 8, 47, 20, 46, 11, 58, 21, 59, 17, 59, 92, 93, 6, 45, 18, 44, 16, 42, 17, 43, 15, 41, 90, 91, 10, 56, 22, 48, 9, 55, 27, 56, 16, 56, 91, 92, 84, 92, 90, 91, 85, 93, 90, 94, 14, 40, 89, 90, 7, 46, 19, 45, 8, 47, 20, 48, 16, 48, 91, 92, 82, 85, 83, 84, 13, 58, 14, 59, 12, 57, 87, 88, 80, 83, 81, 82, 79, 80, 82, 83, 80, 81, 94, 95, 83, 91, 89, 90, 84, 92, 89, 93, 13, 39, 88, 89, 81, 84, 82, 83, 82, 85, 83, 86, 83, 86, 95, 96, 3, 40, 13, 39, 11, 37, 12, 38, 10, 36, 28, 29, 17, 73, 26, 27, 8, 34, 31, 35, 9, 35, 27, 28, 6, 32, 30, 31, 7, 33, 30, 34, 11, 37, 29, 30, 16, 72, 25, 26, 17, 73, 26, 74, 19, 74, 95, 96, 7, 65, 18, 64, 16, 62, 17, 63, 15, 61, 91, 92, 11, 69, 22, 23, 10, 68, 27, 69, 16, 69, 92, 93, 85, 93, 91, 92, 86, 94, 91, 95, 14, 60, 90, 91, 8, 66, 19, 65, 9, 67, 20, 68, 16, 68, 92, 93, 16, 72, 25, 40, 12, 38, 13, 39, 11, 37, 29, 30, 14, 70, 23, 24, 13, 69, 28, 70, 17, 70, 93, 94, 17, 73, 31, 41, 18, 74, 31, 75, 12, 38, 30, 31, 15, 71, 24, 25, 16, 72, 25, 73, 18, 73, 94, 95, 0, 61, 13, 60, 11, 58, 12, 59, 10, 57, 24, 50, 10, 56, 22, 48, 8, 55, 27, 56, 9, 56, 23, 49, 6, 53, 26, 52, 7, 54, 26, 55, 11, 58, 25, 51, 9, 48, 21, 47, 12, 59, 22, 60, 18, 60, 93, 94, 0, 64, 16, 63, 14, 61, 15, 62, 13, 60, 27, 53, 0, 68, 0, 0, 0, 67, 19, 68, 14, 68, 28, 54, 7, 65, 27, 64, 15, 66, 27, 67, 12, 59, 26, 52, 0, 65, 17, 64, 0, 66, 18, 67, 14, 67, 28, 65, 83, 86, 84, 85, 14, 59, 15, 60, 13, 58, 88, 89, 81, 84, 82, 83, 80, 81, 83, 84, 81, 82, 95, 96, 84, 92, 90, 91, 85, 93, 90, 94, 14, 59, 89, 90, 82, 85, 83, 84, 83, 86, 84, 87, 84, 87, 96, 97, 0, 33, 11, 32, 9, 30, 10, 31, 8, 29, 21, 22, 8, 28, 19, 20, 6, 27, 24, 28, 7, 28, 20, 21, 4, 25, 23, 24, 5, 26, 23, 27, 9, 30, 22, 23, 7, 20, 18, 19, 10, 31, 19, 32, 15, 32, 91, 92, 5, 18, 16, 17, 14, 15, 15, 16, 13, 14, 89, 90, 9, 29, 20, 21, 8, 28, 25, 29, 14, 29, 90, 91, 83, 91, 89, 90, 84, 92, 89, 93, 12, 13, 88, 89, 6, 19, 17, 18, 7, 20, 18, 21, 14, 21, 90, 91, 81, 84, 82, 83, 11, 31, 12, 32, 10, 30, 86, 87, 79, 82, 80, 81, 78, 79, 81, 82, 79, 80, 90, 91, 82, 90, 88, 89, 83, 91, 88, 92, 11, 12, 87, 88, 80, 83, 81, 82, 81, 84, 82, 85, 82, 85, 92, 93, 2, 39, 12, 38, 10, 36, 11, 37, 9, 35, 27, 28, 16, 50, 25, 26, 7, 33, 30, 34, 8, 34, 26, 27, 5, 31, 29, 30, 6, 32, 29, 33, 10, 36, 28, 29, 15, 49, 24, 25, 16, 50, 25, 51, 18, 51, 94, 95, 6, 42, 17, 41, 15, 39, 16, 40, 14, 38, 90, 91, 10, 46, 21, 22, 9, 45, 26, 46, 15, 46, 91, 92, 84, 92, 90, 91, 85, 93, 90, 94, 13, 37, 89, 90, 7, 43, 18, 42, 8, 44, 19, 45, 15, 45, 91, 92, 15, 49, 24, 39, 11, 37, 12, 38, 10, 36, 28, 29, 13, 47, 22, 23, 12, 46, 27, 47, 16, 47, 92, 93, 16, 50, 30, 40, 17, 51, 30, 52, 11, 37, 29, 30, 14, 48, 23, 24, 15, 49, 24, 50, 17, 50, 93, 94, 69, 79, 70, 78, 66, 76, 67, 77, 65, 75, 67, 68, 64, 74, 65, 66, 63, 73, 70, 74, 64, 74, 66, 67, 61, 71, 69, 70, 62, 72, 69, 73, 66, 76, 68, 69, 56, 59, 57, 58, 67, 77, 68, 78, 68, 78, 94, 95, 72, 82, 73, 81, 69, 79, 70, 80, 68, 78, 70, 71, 76, 86, 77, 78, 75, 85, 78, 86, 76, 86, 78, 79, 73, 83, 74, 82, 74, 84, 75, 85, 67, 77, 69, 70, 73, 83, 74, 82, 74, 84, 75, 85, 75, 85, 76, 83, 94, 97, 95, 96, 67, 77, 68, 78, 66, 76, 89, 90, 92, 95, 93, 94, 89, 90, 94, 95, 90, 91, 96, 97, 100, 103, 101, 102, 101, 104, 102, 105, 67, 77, 90, 91, 93, 96, 94, 95, 94, 97, 95, 98, 95, 98, 97, 98]

def w8BadRank (c : Config w8Spec) : Nat :=
  w8RankVals.getD (w8CfgCode c) 0

theorem w8GoodCycle_nonempty : w8GoodCycleConfigs ≠ [] := by
  decide

theorem w8GoodCycle_unique_privileged_aux :
    ∀ c ∈ w8GoodCycleConfigs,
      ∃ i, privileged w8System c i ∧
        ∀ j, privileged w8System c j → j = i := by
  native_decide

theorem w8GoodCycle_unique_privileged :
    ∀ c ∈ w8GoodCycleConfigs, ∃! i, privileged w8System c i := by
  intro c hc
  simpa [ExistsUnique] using w8GoodCycle_unique_privileged_aux c hc

theorem w8GoodCycle_closed :
    ∀ k : Fin w8GoodCycleConfigs.length,
      ∃ i,
        privileged w8System (w8GoodCycleConfigs.get k) i ∧
          w8GoodCycleConfigs.get (nextIndex w8GoodCycleConfigs k) =
            move w8System (w8GoodCycleConfigs.get k) i := by
  native_decide

theorem w8GoodCycle_distinct :
    ∀ j₁ j₂ : Fin w8GoodCycleConfigs.length,
      w8GoodCycleConfigs.get j₁ = w8GoodCycleConfigs.get j₂ → j₁ = j₂ := by
  native_decide

theorem w8GoodCycle_fair :
    ∀ i : Fin w8System.rs.n,
      ∃ k : Fin w8GoodCycleConfigs.length,
        ∃ j, privileged w8System (w8GoodCycleConfigs.get k) j ∧
          w8GoodCycleConfigs.get (nextIndex w8GoodCycleConfigs k) =
            move w8System (w8GoodCycleConfigs.get k) j ∧ j = i := by
  native_decide

def w8GoodCycle : GoodCycle w8System where
  configs := w8GoodCycleConfigs
  nonempty := w8GoodCycle_nonempty
  unique_privileged := w8GoodCycle_unique_privileged
  closed := w8GoodCycle_closed
  distinct := w8GoodCycle_distinct
  fair := w8GoodCycle_fair

theorem w8BadRank_decreases_from
    (c : Config w8Spec)
    (hbad : c ∉ w8GoodCycleConfigs)
    (i : Fin 8)
    (hpriv : privileged w8System c i)
    (hnext : move w8System c i ∉ w8GoodCycleConfigs) :
    w8BadRank (move w8System c i) < w8BadRank c := by
  native_decide +revert

theorem w8BadRank_decreases :
    ∀ {c' c : Config w8Spec},
      badStep w8System w8GoodCycle c' c → w8BadRank c' < w8BadRank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact w8BadRank_decreases_from c hbad i hpriv hnext

theorem w8_converges : converges w8System w8GoodCycle := by
  let f : Config w8Spec → Nat := w8BadRank
  let r : Config w8Spec → Config w8Spec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := by
    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)
  refine Subrelation.wf (r := r) ?_ hwf
  intro c' c hstep
  exact w8BadRank_decreases hstep

theorem w8_valid : valid w8System := by
  exact ⟨w8GoodCycle, w8_converges⟩

end LeanMn

