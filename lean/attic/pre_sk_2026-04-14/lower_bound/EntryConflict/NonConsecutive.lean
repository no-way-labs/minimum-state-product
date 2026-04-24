/-
  NonConsecutive.lean — Universal Entry Conflict for Non-Consecutive Binary (Phase 9)

  For ≥ 3 non-adjacent binary processors at sub-threshold product,
  every good cycle has an entry conflict. This is the §4.6 Layer 2-3 proof.

  Four mechanisms:
    1. Both-Even Return: M=1, J%2==K%2==0 → mover context = first non-mover
    2. Toggle-FR: any M, ≥3 one-sided → corner repetition
    3. Zero-Side EC: M=1, ≥2 one-sided
    4. Traversal Return: M=1, singleton first in (2,1)/(1,2) phase →
       after singleton fires, non-mover sees mover value

  Two ring-level lemmas:
    - Parity Obstruction: n=2k, k odd → all-fc=3 impossible
    - Ring Alternation: singleton side alternates at consecutive ternary

  The entry conflict chains into entryConflict_impossible → False.
-/
import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

/-! ### Singleton ring edge structure -/

/-- A ring edge e = {P_i, P_{i+1}} is a singleton if the mover walk
    traverses it exactly once. This is the edge-count notion used by the
    phase-9/10 mover-word layer. -/
def singletonEdge (gc : GoodCycle sys) (i : Fin sys.rs.n) : Prop :=
  ∃! k : Fin gc.configs.length,
    (gc.moverAt k = i ∧ gc.moverAt ⟨(k.val + 1) % gc.configs.length,
      Nat.mod_lt _ gc.configs_length_pos⟩ = right i) ∨
    (gc.moverAt k = right i ∧ gc.moverAt ⟨(k.val + 1) % gc.configs.length,
      Nat.mod_lt _ gc.configs_length_pos⟩ = i)

-- edgeCrossAt, edgeCrossSteps, edgeTraversalCount and related theorems
-- are now defined in CycleTypes.lean (imported above).

theorem GoodCycle.edgeTraversalCount_eq_edgeNetFlow_add_twice_ccw
    (gc : GoodCycle sys) (i : Fin sys.rs.n) :
    (gc.edgeTraversalCount i : Int) =
      gc.edgeNetFlow i + 2 * gc.ccwMoveCountAt (right i) := by
  rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right]
  unfold GoodCycle.edgeNetFlow
  omega

theorem GoodCycle.edgeTraversalCount_even_of_zeroWinding
    (gc : GoodCycle sys) (hzero : gc.zeroWinding) (i : Fin sys.rs.n) :
    Even (gc.edgeTraversalCount i) := by
  have hflow : gc.edgeNetFlow i = 0 := gc.edgeNetFlow_eq_zero_of_zeroWinding hzero i
  rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right]
  use gc.ccwMoveCountAt (right i)
  unfold GoodCycle.edgeNetFlow at hflow
  omega

theorem GoodCycle.edgeTraversalCount_odd_of_isOddWinding
    (gc : GoodCycle sys) (hodd : gc.isOddWinding) (i : Fin sys.rs.n) :
    Odd (gc.edgeTraversalCount i) := by
  have hflow : Int.natAbs (gc.edgeNetFlow i) = 1 :=
    gc.edgeNetFlow_natAbs_eq_one_of_isOddWinding hodd i
  rw [Int.natAbs_eq_iff, Nat.cast_one] at hflow
  rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right]
  rcases hflow with hflow | hflow
  · use gc.ccwMoveCountAt (right i)
    unfold GoodCycle.edgeNetFlow at hflow
    omega
  · use gc.cwMoveCountAt i
    unfold GoodCycle.edgeNetFlow at hflow
    omega

theorem GoodCycle.edgeTraversalCount_pos_of_isOddWinding
    (gc : GoodCycle sys) (hodd : gc.isOddWinding) (i : Fin sys.rs.n) :
    0 < gc.edgeTraversalCount i := by
  rcases gc.edgeTraversalCount_odd_of_isOddWinding hodd i with ⟨k, hk⟩
  omega

theorem GoodCycle.singletonEdge_or_edgeTraversalCount_ge_three_of_isOddWinding
    (gc : GoodCycle sys) (hodd : gc.isOddWinding) (i : Fin sys.rs.n) :
    gc.edgeTraversalCount i = 1 ∨ 3 ≤ gc.edgeTraversalCount i := by
  rcases gc.edgeTraversalCount_odd_of_isOddWinding hodd i with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · left
    omega
  · right
    omega

theorem singletonEdge_iff_edgeTraversalCount_eq_one (gc : GoodCycle sys)
    (i : Fin sys.rs.n) :
    singletonEdge gc i ↔ gc.edgeTraversalCount i = 1 := by
  constructor
  · intro hsingle
    rcases hsingle with ⟨k, hk, huniq⟩
    unfold GoodCycle.edgeTraversalCount
    have hset :
        gc.edgeCrossSteps i = {k} := by
      ext j
      rw [Finset.mem_singleton, mem_edgeCrossSteps_iff]
      constructor
      · intro hj
        exact huniq j hj
      · intro hj
        subst hj
        exact hk
    simp [hset]
  · intro hcount
    unfold GoodCycle.edgeTraversalCount at hcount
    have hcard : (gc.edgeCrossSteps i).card = 1 := hcount
    rcases Finset.card_eq_one.mp hcard with ⟨k, hkset⟩
    refine ⟨k, ?_, ?_⟩
    · exact (mem_edgeCrossSteps_iff gc i k).mp (by simpa [hkset])
    · intro j hj
      have hjset : j ∈ gc.edgeCrossSteps i := (mem_edgeCrossSteps_iff gc i j).mpr hj
      simpa [hkset] using hjset

theorem GoodCycle.not_singletonEdge_of_zeroWinding
    (gc : GoodCycle sys) (hzero : gc.zeroWinding) (i : Fin sys.rs.n) :
    ¬singletonEdge gc i := by
  intro hsingle
  have hcount : gc.edgeTraversalCount i = 1 :=
    (singletonEdge_iff_edgeTraversalCount_eq_one gc i).mp hsingle
  have heven : Even (gc.edgeTraversalCount i) :=
    gc.edgeTraversalCount_even_of_zeroWinding hzero i
  rw [hcount] at heven
  exact (by decide : ¬Even 1) heven

theorem GoodCycle.edgeTraversalCount_left_add_edgeTraversalCount
    (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.edgeTraversalCount (left p) + gc.edgeTraversalCount p =
      2 * (gc.cwMoveCountAt p + gc.ccwMoveCountAt p) := by
  rw [gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right (left p),
    gc.edgeTraversalCount_eq_cwMoveCountAt_add_ccwMoveCountAt_right p]
  have hright_left : right (left p) = p := by
    simpa using (right_left_eq_self p)
  rw [hright_left]
  have hbal := gc.outgoingMoveCount_eq_incomingMoveCount p
  omega

theorem GoodCycle.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay
    (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    gc.edgeTraversalCount (left p) + gc.edgeTraversalCount p =
      2 * (gc.fireCount p - gc.stayMoveCountAt p) := by
  rw [gc.edgeTraversalCount_left_add_edgeTraversalCount p]
  have hpart := gc.fireCount_eq_moveCount_partition p
  omega

/-- Under odd winding, any processor that fires exactly twice is adjacent to a
    singleton ring edge. This is the local singleton source used in the
    phase-10 odd-winding analysis. -/
theorem GoodCycle.singletonEdge_left_or_self_of_fireCount_two_of_isOddWinding
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (hodd : gc.isOddWinding) (hfire : gc.fireCount p = 2) :
    singletonEdge gc (left p) ∨ singletonEdge gc p := by
  by_cases hleft : gc.edgeTraversalCount (left p) = 1
  · left
    exact (singletonEdge_iff_edgeTraversalCount_eq_one gc (left p)).2 hleft
  · by_cases hself : gc.edgeTraversalCount p = 1
    · right
      exact (singletonEdge_iff_edgeTraversalCount_eq_one gc p).2 hself
    · have hleft_ge_three :
        3 ≤ gc.edgeTraversalCount (left p) := by
          rcases gc.singletonEdge_or_edgeTraversalCount_ge_three_of_isOddWinding hodd (left p) with
            hleft_one | hleft_ge_three
          · exact False.elim (hleft hleft_one)
          · exact hleft_ge_three
      have hself_ge_three : 3 ≤ gc.edgeTraversalCount p := by
        rcases gc.singletonEdge_or_edgeTraversalCount_ge_three_of_isOddWinding hodd p with
          hself_one | hself_ge_three
        · exact False.elim (hself hself_one)
        · exact hself_ge_three
      have hsum :
          gc.edgeTraversalCount (left p) + gc.edgeTraversalCount p =
            2 * (gc.fireCount p - gc.stayMoveCountAt p) :=
        gc.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay p
      have hpart := gc.fireCount_eq_moveCount_partition p
      rw [hfire] at hsum hpart
      have hstay_le : gc.stayMoveCountAt p ≤ 2 := by
        omega
      have hsum_le_four :
          gc.edgeTraversalCount (left p) + gc.edgeTraversalCount p ≤ 4 := by
        omega
      omega

/-! ### Return Cone Lemma -/

/-- If processor `p` does not fire at step `m`, then its state is unchanged after
    that step. This local form is convenient for interval arguments. -/
private theorem GoodCycle.stateAfter_succ_eq_self_of_fireIndicator_zero
    (gc : GoodCycle sys) (p : Fin sys.rs.n) {m : Nat}
    (hm : m < gc.configs.length) (hfire : gc.fireIndicator p m = 0) :
    gc.stateAfter p (m + 1) = gc.stateAfter p m := by
  have hmover_ne : gc.moverAt ⟨m, hm⟩ ≠ p := by
    intro hmover
    rw [gc.fireIndicator_of_lt p hm, hmover] at hfire
    simp at hfire
  have hnext :
      gc.stateAfter p (m + 1) =
        (gc.configs.get (nextIndex gc.configs ⟨m, hm⟩)) p := by
    by_cases hm1 : m + 1 < gc.configs.length
    · simp [GoodCycle.stateAfter, hm1, nextIndex, Nat.mod_eq_of_lt hm1]
    · have hm1_eq : m + 1 = gc.configs.length := by omega
      have hnext0 : nextIndex gc.configs ⟨m, hm⟩ = ⟨0, gc.configs_length_pos⟩ := by
        apply Fin.ext
        simp [nextIndex, hm1_eq]
      rw [hm1_eq, gc.stateAfter_of_ge p (le_rfl : gc.configs.length ≤ gc.configs.length), hnext0]
      rfl
  rw [hnext, gc.stateAfter_of_lt p hm]
  exact gc.state_eq_of_ne_moverAt ⟨m, hm⟩ p (fun h => hmover_ne h.symm)

/-- If processor `p` never fires on the linear interval of steps
    `{t, t+1, ..., t+d-1}`, then its state is unchanged between times `t` and
    `t+d`. -/
private theorem GoodCycle.stateAfter_eq_of_noMoves_from
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (t d : Nat)
    (htd : t + d ≤ gc.configs.length)
    (hfreeze : ∀ m : Nat, t ≤ m → m < t + d → gc.fireIndicator p m = 0) :
    gc.stateAfter p (t + d) = gc.stateAfter p t := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have htd' : t + d ≤ gc.configs.length := by omega
      have hm : t + d < gc.configs.length := by omega
      have hlast : gc.fireIndicator p (t + d) = 0 := hfreeze (t + d) (by omega) (by omega)
      calc
        gc.stateAfter p (t + (d + 1)) = gc.stateAfter p (t + d) := by
          simpa [Nat.add_assoc] using gc.stateAfter_succ_eq_self_of_fireIndicator_zero p hm hlast
        _ = gc.stateAfter p t := ih htd' (fun m hm1 hm2 => hfreeze m hm1 (by omega))

/-- A support interval packages the mover-word condition behind the return-cone
    lemma: exactly the processors in `procs` fire in the linear step interval
    `[startStep, endStep)`. -/
structure SupportInterval (gc : GoodCycle sys) where
  startStep : Fin gc.configs.length
  endStep : Fin gc.configs.length
  proper : startStep.val < endStep.val
  procs : Finset (Fin sys.rs.n)
  mover_mem_iff :
    ∀ k : Fin gc.configs.length,
      gc.moverAt k ∈ procs ↔ startStep.val ≤ k.val ∧ k.val < endStep.val

/-- A return cone [t, u) on the mover word: movers in this interval cover
    a contiguous arc S, with all firings of S-processors in [t, u). -/
structure ReturnCone (gc : GoodCycle sys) where
  startStep : Fin gc.configs.length
  endStep : Fin gc.configs.length
  nontrivial : startStep ≠ endStep
  /-- The config at the start equals the config at the end. -/
  config_repeat : gc.configs.get startStep = gc.configs.get endStep

/-- Return Cone Lemma (Lemma 4.6.1a): if [t,u) is a nontrivial return cone,
    g_t = g_u. Since good cycle configs are distinct, this is impossible. -/
theorem returnCone_false (gc : GoodCycle sys)
    (rc : ReturnCone gc)
    (hdistinct : ∀ j₁ j₂ : Fin gc.configs.length,
      gc.configs.get j₁ = gc.configs.get j₂ → j₁ = j₂) :
    False := by
  exact absurd (hdistinct _ _ rc.config_repeat) rc.nontrivial

/-- Any support interval yields a repeated good-cycle configuration at its
    endpoints: processors inside the support interval are frozen outside it, and
    processors outside the support interval are frozen inside it. -/
def SupportInterval.toReturnCone (si : SupportInterval gc) : ReturnCone gc := by
  classical
  refine
    { startStep := si.startStep
      endStep := si.endStep
      nontrivial := ?_
      config_repeat := ?_ }
  · intro hEq
    exact Nat.ne_of_lt si.proper (by simpa using congrArg Fin.val hEq)
  · funext p
    by_cases hp : p ∈ si.procs
    · have hend :
          gc.stateAfter p gc.configs.length = gc.stateAfter p si.endStep.val :=
          by
            simpa [Nat.add_sub_of_le (Nat.le_of_lt si.endStep.isLt)] using
              (gc.stateAfter_eq_of_noMoves_from p si.endStep.val
                (gc.configs.length - si.endStep.val)
                (by omega)
                (fun m hm1 hm2 => by
                  have hm_lt : m < gc.configs.length := by omega
                  have hk := si.mover_mem_iff ⟨m, hm_lt⟩
                  have hnot : gc.moverAt ⟨m, hm_lt⟩ ≠ p := by
                    intro hmover
                    have : gc.moverAt ⟨m, hm_lt⟩ ∈ si.procs := by simpa [hmover] using hp
                    have hlt : m < si.endStep.val := by simpa using (hk.mp this).2
                    exact (Nat.not_le_of_lt hlt) hm1
                  rw [gc.fireIndicator_of_lt p hm_lt]
                  simp [hnot]))
      have hstart :
          gc.stateAfter p si.startStep.val = gc.stateAfter p 0 :=
          by
            simpa using (gc.stateAfter_eq_of_noMoves_from p 0 si.startStep.val
              (by omega)
              (fun m hm1 hm2 => by
                have hm_lt : m < gc.configs.length := by omega
                have hk := si.mover_mem_iff ⟨m, hm_lt⟩
                have hnot : gc.moverAt ⟨m, hm_lt⟩ ≠ p := by
                  intro hmover
                  have : gc.moverAt ⟨m, hm_lt⟩ ∈ si.procs := by simpa [hmover] using hp
                  have hge : si.startStep.val ≤ m := by simpa using (hk.mp this).1
                  exact (Nat.not_le_of_lt hm2) (by simpa using hge)
                rw [gc.fireIndicator_of_lt p hm_lt]
                simp [hnot]))
      have hcycle : gc.stateAfter p gc.configs.length = gc.stateAfter p 0 := by
        simp [GoodCycle.stateAfter]
        intro h
        rfl
      calc
        (gc.configs.get si.startStep) p = gc.stateAfter p si.startStep.val := by
          simpa using (gc.stateAfter_of_lt p si.startStep.isLt).symm
        _ = gc.stateAfter p 0 := hstart
        _ = gc.stateAfter p gc.configs.length := hcycle.symm
        _ = gc.stateAfter p si.endStep.val := hend
        _ = (gc.configs.get si.endStep) p := by
          simpa using gc.stateAfter_of_lt p si.endStep.isLt
    · have hfreeze :
          ∀ m : Nat,
            si.startStep.val ≤ m →
              m < si.endStep.val →
                gc.fireIndicator p m = 0 := by
          intro m hm1 hm2
          have hm_lt : m < gc.configs.length := by omega
          have hk := si.mover_mem_iff ⟨m, hm_lt⟩
          have hnot : gc.moverAt ⟨m, hm_lt⟩ ≠ p := by
            intro hmover
            exact hp (by simpa [hmover] using hk.mpr ⟨hm1, hm2⟩)
          rw [gc.fireIndicator_of_lt p hm_lt]
          simp [hnot]
      have heq :
          gc.stateAfter p si.endStep.val = gc.stateAfter p si.startStep.val :=
        by
          simpa [Nat.add_sub_of_le (Nat.le_of_lt si.proper)] using
            gc.stateAfter_eq_of_noMoves_from p si.startStep.val
              (si.endStep.val - si.startStep.val)
              (by omega) (fun m hm1 hm2 => by
                apply hfreeze m hm1
                omega)
      calc
        (gc.configs.get si.startStep) p = gc.stateAfter p si.startStep.val := by
          simpa using (gc.stateAfter_of_lt p si.startStep.isLt).symm
        _ = gc.stateAfter p si.endStep.val := heq.symm
        _ = (gc.configs.get si.endStep) p := by
          simpa using gc.stateAfter_of_lt p si.endStep.isLt

/-- A support interval is already enough to contradict good-cycle distinctness. -/
theorem supportInterval_false (gc : GoodCycle sys) (si : SupportInterval gc) : False := by
  exact returnCone_false gc si.toReturnCone gc.distinct

/-- Package pointwise mover-membership facts into a support interval. This is
    the final shape needed by the two-singleton-edge / return-cone argument
    once the cut-arc combinatorics are discharged. -/
def supportIntervalOfPiecewise
    (gc : GoodCycle sys)
    (procs : Finset (Fin sys.rs.n))
    (startStep endStep : Fin gc.configs.length)
    (hproper : startStep.val < endStep.val)
    (hinside :
      ∀ k : Fin gc.configs.length,
        startStep.val ≤ k.val → k.val < endStep.val → gc.moverAt k ∈ procs)
    (hleft :
      ∀ k : Fin gc.configs.length,
        k.val < startStep.val → gc.moverAt k ∉ procs)
    (hright :
      ∀ k : Fin gc.configs.length,
        endStep.val ≤ k.val → gc.moverAt k ∉ procs) :
    SupportInterval gc where
  startStep := startStep
  endStep := endStep
  proper := hproper
  procs := procs
  mover_mem_iff := by
    intro k
    constructor
    · intro hk
      by_cases hks : k.val < startStep.val
      · exact False.elim ((hleft k hks) hk)
      · have hge : startStep.val ≤ k.val := by omega
        by_cases hke : k.val < endStep.val
        · exact ⟨hge, hke⟩
        · have hend : endStep.val ≤ k.val := by omega
          exact False.elim ((hright k hend) hk)
    · intro hk
      exact hinside k hk.1 hk.2

/-- The piecewise form above can be discharged immediately via the return-cone
    contradiction. -/
theorem supportInterval_false_of_piecewise
    (gc : GoodCycle sys)
    (procs : Finset (Fin sys.rs.n))
    (startStep endStep : Fin gc.configs.length)
    (hproper : startStep.val < endStep.val)
    (hinside :
      ∀ k : Fin gc.configs.length,
        startStep.val ≤ k.val → k.val < endStep.val → gc.moverAt k ∈ procs)
    (hleft :
      ∀ k : Fin gc.configs.length,
        k.val < startStep.val → gc.moverAt k ∉ procs)
    (hright :
      ∀ k : Fin gc.configs.length,
        endStep.val ≤ k.val → gc.moverAt k ∉ procs) :
    False := by
  exact supportInterval_false gc
    (supportIntervalOfPiecewise gc procs startStep endStep hproper hinside hleft hright)

private theorem singletonEdge_existsUnique_edgeCrossAt
    (gc : GoodCycle sys) (i : Fin sys.rs.n) (hsingle : singletonEdge gc i) :
    ∃! k : Fin gc.configs.length, edgeCrossAt gc i k := by
  rcases hsingle with ⟨k, hk, huniq⟩
  refine ⟨k, ?_, ?_⟩
  · simpa [edgeCrossAt, nextIndex] using hk
  · intro j hj
    apply huniq
    simpa [edgeCrossAt, nextIndex] using hj

private theorem edgeCrossAt_unique
    (gc : GoodCycle sys) (k : Fin gc.configs.length)
    {i j : Fin sys.rs.n} (hi : edgeCrossAt gc i k) (hj : edgeCrossAt gc j k) :
    i = j := by
  rcases gc.stepDir_cases k with hcw | hstay | hccw
  · have hi' := (edgeCrossAt_iff_stepDir gc i k).mp hi
    have hj' := (edgeCrossAt_iff_stepDir gc j k).mp hj
    rcases hi' with ⟨hmi, _⟩ | hbad
    · rcases hj' with ⟨hmj, _⟩ | hbad'
      · rw [← hmi, hmj]
      · rw [hcw] at hbad'
        cases hbad'.2
    · rw [hcw] at hbad
      cases hbad.2
  · have hi' := (edgeCrossAt_iff_stepDir gc i k).mp hi
    rcases hi' with hbad | hbad
    all_goals
      rw [hstay] at hbad
      cases hbad.2
  · have hi' := (edgeCrossAt_iff_stepDir gc i k).mp hi
    have hj' := (edgeCrossAt_iff_stepDir gc j k).mp hj
    rcases hi' with hbad | ⟨hmi, _⟩
    · rw [hccw] at hbad
      cases hbad.2
    · rcases hj' with hbad | ⟨hmj, _⟩
      · rw [hccw] at hbad
        cases hbad.2
      · have hright : right i = right j := by
          calc
            right i = gc.moverAt k := by rw [hmi]
            _ = right j := by rw [hmj]
        simpa using congrArg left hright

private theorem singletonEdge_crossing_ne_of_ne
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j) (hij : i ≠ j) :
    (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose ≠
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose := by
  intro hEq
  have hcross_i :
      edgeCrossAt gc i (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose :=
    (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose_spec.1
  have hcross_j :
      edgeCrossAt gc j (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose := by
    simpa [hEq] using
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose_spec.1
  exact hij (edgeCrossAt_unique gc _ hcross_i hcross_j)

private def cwDist (a b : Fin sys.rs.n) : Nat :=
  (b.val + sys.rs.n - a.val) % sys.rs.n

private theorem cwDist_lt_n (a b : Fin sys.rs.n) : cwDist a b < sys.rs.n := by
  unfold cwDist
  have hn : 0 < sys.rs.n := by
    exact lt_of_lt_of_le (by decide : 0 < 4) sys.rs.n_ge_4
  exact Nat.mod_lt _ hn

private def advance (p : Fin sys.rs.n) (d : Nat) : Fin sys.rs.n :=
  ⟨(p.val + d) % sys.rs.n, Nat.mod_lt _ (by
    exact lt_of_lt_of_le (by decide : 0 < 4) sys.rs.n_ge_4)⟩

@[simp] private theorem advance_zero (p : Fin sys.rs.n) :
    advance p 0 = p := by
  ext
  simp [advance, Nat.mod_eq_of_lt p.isLt]

@[simp] private theorem advance_succ (p : Fin sys.rs.n) (d : Nat) :
    advance p (d + 1) = right (advance p d) := by
  ext
  simp [advance, right_val]
  rw [show p.val + (d + 1) = (p.val + d) + 1 by omega]

private theorem advance_cwDist (a b : Fin sys.rs.n) :
    advance a (cwDist a b) = b := by
  ext
  unfold advance cwDist
  by_cases hab : a.val ≤ b.val
  · have hdist : (b.val + sys.rs.n - a.val) % sys.rs.n = b.val - a.val := by
      rw [show b.val + sys.rs.n - a.val = (b.val - a.val) + sys.rs.n by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hdist]
    change ((a.val + (b.val - a.val)) % sys.rs.n) = b.val
    rw [show a.val + (b.val - a.val) = b.val by omega, Nat.mod_eq_of_lt b.isLt]
  · have hdist : (b.val + sys.rs.n - a.val) % sys.rs.n = b.val + sys.rs.n - a.val := by
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hdist]
    change ((a.val + (b.val + sys.rs.n - a.val)) % sys.rs.n) = b.val
    rw [show a.val + (b.val + sys.rs.n - a.val) = b.val + sys.rs.n by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]

private theorem advance_injective (p : Fin sys.rs.n) {d e : Nat}
    (hd : d < sys.rs.n) (he : e < sys.rs.n)
    (h : advance p d = advance p e) : d = e := by
  have hval : ((p.val + d) % sys.rs.n) = ((p.val + e) % sys.rs.n) := by
    simpa [advance] using congrArg Fin.val h
  have hp := p.isLt
  by_cases hdw : p.val + d < sys.rs.n
  · rw [Nat.mod_eq_of_lt hdw] at hval
    by_cases hew : p.val + e < sys.rs.n
    · rw [Nat.mod_eq_of_lt hew] at hval
      omega
    · have he_ge : sys.rs.n ≤ p.val + e := Nat.le_of_not_lt hew
      rw [Nat.mod_eq_sub_mod he_ge] at hval
      have he_lt : p.val + e - sys.rs.n < sys.rs.n := by omega
      rw [Nat.mod_eq_of_lt he_lt] at hval
      omega
  · have hd_ge : sys.rs.n ≤ p.val + d := Nat.le_of_not_lt hdw
    rw [Nat.mod_eq_sub_mod hd_ge] at hval
    have hd_lt' : p.val + d - sys.rs.n < sys.rs.n := by omega
    rw [Nat.mod_eq_of_lt hd_lt'] at hval
    by_cases hew : p.val + e < sys.rs.n
    · rw [Nat.mod_eq_of_lt hew] at hval
      omega
    · have he_ge : sys.rs.n ≤ p.val + e := Nat.le_of_not_lt hew
      rw [Nat.mod_eq_sub_mod he_ge] at hval
      have he_lt : p.val + e - sys.rs.n < sys.rs.n := by omega
      rw [Nat.mod_eq_of_lt he_lt] at hval
      omega

private def cutArcPred (i j p : Fin sys.rs.n) : Prop :=
  ∃ d : Nat, d ≤ cwDist (right i) j ∧ advance (right i) d = p

private theorem cutArcPred_base (i j : Fin sys.rs.n) :
    cutArcPred i j (right i) := by
  refine ⟨0, Nat.zero_le _, ?_⟩
  simp

private theorem cutArcPred_end (i j : Fin sys.rs.n) :
    cutArcPred i j j := by
  exact ⟨cwDist (right i) j, le_rfl, advance_cwDist (right i) j⟩

private theorem cutArcPred_of_right {i j p : Fin sys.rs.n}
    (hp : cutArcPred i j p) (hpne : p ≠ j) :
    cutArcPred i j (right p) := by
  rcases hp with ⟨d, hd, rfl⟩
  have hdlt : d < cwDist (right i) j := by
    by_contra hnot
    have hEq : d = cwDist (right i) j := by omega
    apply hpne
    subst hEq
    simpa using advance_cwDist (right i) j
  refine ⟨d + 1, by omega, ?_⟩
  simpa [advance_succ]

private theorem cutArcPred_of_left {i j p : Fin sys.rs.n}
    (hp : cutArcPred i j p) (hpne : p ≠ right i) :
    cutArcPred i j (left p) := by
  rcases hp with ⟨d, hd, rfl⟩
  have hd0 : d ≠ 0 := by
    intro hd0
    apply hpne
    subst hd0
    simp
  have hdpos : 0 < d := by omega
  refine ⟨d - 1, by omega, ?_⟩
  have hsucc : advance (right i) d = right (advance (right i) (d - 1)) := by
    have hdeq : d = (d - 1) + 1 := by omega
    rw [hdeq]
    simpa using advance_succ (right i) (d - 1)
  simpa using (congrArg left hsucc).symm

private theorem eq_self_of_not_cutArcPred_of_right {i j p : Fin sys.rs.n}
    (hp : ¬cutArcPred i j p) (hnext : cutArcPred i j (right p)) :
    p = i := by
  rcases hnext with ⟨d, hd, hdEq⟩
  by_cases hd0 : d = 0
  · subst hd0
    have hEq : right i = right p := by simpa using hdEq
    simpa using (congrArg left hEq).symm
  · have hdpos : 0 < d := by omega
    have hpred : advance (right i) (d - 1) = p := by
      have hsucc : advance (right i) d = right (advance (right i) (d - 1)) := by
        have hdeq : d = (d - 1) + 1 := by omega
        rw [hdeq]
        simpa using advance_succ (right i) (d - 1)
      rw [hdEq] at hsucc
      simpa using (congrArg left hsucc).symm
    exact False.elim (hp ⟨d - 1, by omega, hpred⟩)

private theorem eq_right_of_not_cutArcPred_of_left {i j p : Fin sys.rs.n}
    (hp : ¬cutArcPred i j p) (hprev : cutArcPred i j (left p)) :
    p = right j := by
  rcases hprev with ⟨d, hd, hdEq⟩
  by_cases hlast : d = cwDist (right i) j
  · subst hlast
    have hleftpj : left p = j := by
      calc
        left p = advance (right i) (cwDist (right i) j) := hdEq.symm
        _ = j := advance_cwDist (right i) j
    simpa using congrArg right hleftpj
  · have hneqj : left p ≠ j := by
      intro hEq
      apply hlast
      apply advance_injective (right i) (lt_of_le_of_lt hd (cwDist_lt_n (right i) j))
        (cwDist_lt_n (right i) j)
      calc
        advance (right i) d = left p := hdEq
        _ = j := hEq
        _ = advance (right i) (cwDist (right i) j) := (advance_cwDist (right i) j).symm
    have hp' : cutArcPred i j p := by
      have hprev' : cutArcPred i j (left p) := ⟨d, hd, hdEq⟩
      simpa using (cutArcPred_of_right hprev' hneqj : cutArcPred i j (right (left p)))
    exact False.elim (hp hp')

private theorem cutArcPred_next_iff_of_not_crossing
    (gc : GoodCycle sys) (i j : Fin sys.rs.n) (k : Fin gc.configs.length)
    (hci : ¬edgeCrossAt gc i k) (hcj : ¬edgeCrossAt gc j k) :
    cutArcPred i j (gc.moverAt (nextIndex gc.configs k)) ↔
      cutArcPred i j (gc.moverAt k) := by
  rcases gc.next_mover_is_local k with hleft | hself | hright
  · constructor
    · intro hnext
      by_cases hcurr : cutArcPred i j (gc.moverAt k)
      · exact hcurr
      · have hcurr_eq : gc.moverAt k = right j :=
          eq_right_of_not_cutArcPred_of_left hcurr (by simpa [hleft] using hnext)
        have hnext_eq : gc.moverAt (nextIndex gc.configs k) = j := by
          rw [hleft, hcurr_eq]
          simpa using left_right_eq_self j
        exact False.elim (hcj (Or.inr ⟨hcurr_eq, hnext_eq⟩))
    · intro hcurr
      by_cases hcurr_eq : gc.moverAt k = right i
      · have hnext_eq : gc.moverAt (nextIndex gc.configs k) = i := by
          rw [hleft, hcurr_eq]
          simpa using left_right_eq_self i
        exact False.elim (hci (Or.inr ⟨hcurr_eq, hnext_eq⟩))
      · simpa [hleft] using cutArcPred_of_left hcurr hcurr_eq
  · simpa [hself]
  · constructor
    · intro hnext
      by_cases hcurr : cutArcPred i j (gc.moverAt k)
      · exact hcurr
      · have hcurr_eq : gc.moverAt k = i :=
          eq_self_of_not_cutArcPred_of_right hcurr (by simpa [hright] using hnext)
        have hnext_eq : gc.moverAt (nextIndex gc.configs k) = right i := by
          simpa [hright, hcurr_eq] using hright
        exact False.elim (hci (Or.inl ⟨hcurr_eq, hnext_eq⟩))
    · intro hcurr
      by_cases hcurr_eq : gc.moverAt k = j
      · have hnext_eq : gc.moverAt (nextIndex gc.configs k) = right j := by
          simpa [hright, hcurr_eq] using hright
        exact False.elim (hcj (Or.inl ⟨hcurr_eq, hnext_eq⟩))
      · simpa [hright] using cutArcPred_of_right hcurr hcurr_eq

private theorem nextIndex_eq_natSucc
    (gc : GoodCycle sys) {m : Nat} (hm : m + 1 < gc.configs.length) :
    nextIndex gc.configs ⟨m, lt_trans (Nat.lt_succ_self _) hm⟩ = ⟨m + 1, hm⟩ := by
  apply Fin.ext
  simp [nextIndex, Nat.mod_eq_of_lt hm]

private theorem cutArcPred_eq_of_no_cut_crossings_between
    (gc : GoodCycle sys) (i j : Fin sys.rs.n) (a b : Nat)
    (ha : a ≤ b) (hb : b < gc.configs.length)
    (havoid :
      ∀ k : Fin gc.configs.length,
        a ≤ k.val → k.val < b →
          ¬edgeCrossAt gc i k ∧ ¬edgeCrossAt gc j k) :
    cutArcPred i j (gc.moverAt ⟨a, lt_of_le_of_lt ha hb⟩) ↔
      cutArcPred i j (gc.moverAt ⟨b, hb⟩) := by
  induction b, ha using Nat.le_induction with
  | base =>
      simp
  | succ b hab ih =>
      have hb_lt : b < gc.configs.length := by omega
      have hkavoid :
          ¬edgeCrossAt gc i ⟨b, hb_lt⟩ ∧
            ¬edgeCrossAt gc j ⟨b, hb_lt⟩ :=
        havoid ⟨b, hb_lt⟩ hab (by simpa using Nat.lt_succ_self b)
      have hprev :
          cutArcPred i j (gc.moverAt ⟨a, lt_of_le_of_lt hab hb_lt⟩) ↔
            cutArcPred i j (gc.moverAt ⟨b, hb_lt⟩) := by
        simpa using ih hb_lt (fun k hk1 hk2 => havoid k hk1 (by omega))
      have hstep :
          cutArcPred i j (gc.moverAt ⟨b + 1, hb⟩) ↔
            cutArcPred i j (gc.moverAt ⟨b, hb_lt⟩) := by
        simpa [nextIndex_eq_natSucc gc hb] using
          cutArcPred_next_iff_of_not_crossing gc i j ⟨b, hb_lt⟩ hkavoid.1 hkavoid.2
      calc
        cutArcPred i j (gc.moverAt ⟨a, lt_of_le_of_lt (Nat.le_succ_of_le hab) hb⟩) ↔
            cutArcPred i j (gc.moverAt ⟨b, hb_lt⟩) := by
              simpa using hprev
        _ ↔ cutArcPred i j (gc.moverAt ⟨b + 1, hb⟩) := hstep.symm

private theorem cwDist_right_self (i : Fin sys.rs.n) :
    cwDist (right i) i = sys.rs.n - 1 := by
  unfold cwDist
  by_cases hi : i.val + 1 < sys.rs.n
  · rw [right_val, Nat.mod_eq_of_lt hi]
    rw [show i.val + sys.rs.n - (i.val + 1) = sys.rs.n - 1 by omega]
    rw [Nat.mod_eq_of_lt]
    have hnpos : 0 < sys.rs.n := by
      exact lt_of_lt_of_le (by decide : 0 < 4) sys.rs.n_ge_4
    omega
  · have hiEq : i.val + 1 = sys.rs.n := by omega
    rw [right_val, hiEq, Nat.mod_self]
    have hiVal : i.val = sys.rs.n - 1 := by omega
    rw [hiVal]
    rw [show sys.rs.n - 1 + sys.rs.n - 0 = (sys.rs.n - 1) + sys.rs.n by omega]
    rw [Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt]
    have hnpos : 0 < sys.rs.n := by
      exact lt_of_lt_of_le (by decide : 0 < 4) sys.rs.n_ge_4
    omega

private theorem advance_n_sub_one_from_right (i : Fin sys.rs.n) :
    advance (right i) (sys.rs.n - 1) = i := by
  simpa [cwDist_right_self i] using advance_cwDist (right i) i

private theorem cwDist_lt_n_sub_one_of_ne (i j : Fin sys.rs.n) (hij : j ≠ i) :
    cwDist (right i) j < sys.rs.n - 1 := by
  have hlt : cwDist (right i) j < sys.rs.n := cwDist_lt_n (right i) j
  by_contra hnot
  have hge : sys.rs.n - 1 ≤ cwDist (right i) j := by omega
  have hEq : cwDist (right i) j = sys.rs.n - 1 := by omega
  apply hij
  calc
    j = advance (right i) (cwDist (right i) j) := (advance_cwDist (right i) j).symm
    _ = advance (right i) (sys.rs.n - 1) := by rw [hEq]
    _ = i := advance_n_sub_one_from_right i

private theorem not_cutArcPred_at_left_cut
    (i j : Fin sys.rs.n) (hij : j ≠ i) :
    ¬cutArcPred i j i := by
  intro hiArc
  rcases hiArc with ⟨d, hd, hdEq⟩
  have hdlt : d < sys.rs.n := lt_of_le_of_lt hd (cwDist_lt_n (right i) j)
  have hEqd : d = sys.rs.n - 1 := by
    apply advance_injective (right i) hdlt (by omega)
    calc
      advance (right i) d = i := hdEq
      _ = advance (right i) (sys.rs.n - 1) := (advance_n_sub_one_from_right i).symm
  have hDlt : cwDist (right i) j < sys.rs.n - 1 := cwDist_lt_n_sub_one_of_ne i j hij
  omega

private theorem not_cutArcPred_at_right_cut
    (i j : Fin sys.rs.n) (hij : j ≠ i) :
    ¬cutArcPred i j (right j) := by
  intro hjArc
  rcases hjArc with ⟨d, hd, hdEq⟩
  have hDlt : cwDist (right i) j < sys.rs.n - 1 := cwDist_lt_n_sub_one_of_ne i j hij
  have hdlt : d < sys.rs.n := lt_of_le_of_lt hd (cwDist_lt_n (right i) j)
  have hsuccEq :
      advance (right i) (cwDist (right i) j + 1) = right j := by
    rw [advance_succ]
    simpa using congrArg right (advance_cwDist (right i) j)
  have hdEq' :
      advance (right i) d = advance (right i) (cwDist (right i) j + 1) := by
    calc
      advance (right i) d = right j := hdEq
      _ = advance (right i) (cwDist (right i) j + 1) := hsuccEq.symm
  have hEqd :
      d = cwDist (right i) j + 1 := by
    apply advance_injective (right i) hdlt (by omega) hdEq'
  omega

private noncomputable def cutArcFinset (i j : Fin sys.rs.n) : Finset (Fin sys.rs.n) := by
  classical
  exact Finset.univ.filter (fun p => cutArcPred i j p)

private theorem mem_cutArcFinset (i j p : Fin sys.rs.n) :
    p ∈ cutArcFinset i j ↔ cutArcPred i j p := by
  classical
  simp [cutArcFinset]

private noncomputable def cutArcComplFinset (i j : Fin sys.rs.n) : Finset (Fin sys.rs.n) := by
  classical
  exact Finset.univ.filter (fun p => ¬cutArcPred i j p)

private theorem mem_cutArcComplFinset (i j p : Fin sys.rs.n) :
    p ∈ cutArcComplFinset i j ↔ ¬cutArcPred i j p := by
  classical
  simp [cutArcComplFinset]

private theorem not_edgeCrossAt_of_ne_singletonCross
    (gc : GoodCycle sys) (i : Fin sys.rs.n) (hsingle : singletonEdge gc i)
    {k : Fin gc.configs.length}
    (hk : k ≠ (singletonEdge_existsUnique_edgeCrossAt gc i hsingle).choose) :
    ¬edgeCrossAt gc i k := by
  intro hcross
  exact hk ((singletonEdge_existsUnique_edgeCrossAt gc i hsingle).choose_spec.2 k hcross)

private theorem cutArcPred_next_iff_not_of_edgeCrossAt_left
    (gc : GoodCycle sys) {i j : Fin sys.rs.n} (hij : i ≠ j)
    {k : Fin gc.configs.length} (hcross : edgeCrossAt gc i k) :
    cutArcPred i j (gc.moverAt (nextIndex gc.configs k)) ↔
      ¬cutArcPred i j (gc.moverAt k) := by
  rcases hcross with hcw | hccw
  · have hcurr : ¬cutArcPred i j (gc.moverAt k) := by
      simpa [hcw.1] using not_cutArcPred_at_left_cut i j hij.symm
    have hnext : cutArcPred i j (gc.moverAt (nextIndex gc.configs k)) := by
      simpa [hcw.2] using cutArcPred_base i j
    constructor
    · intro _
      exact hcurr
    · intro _
      exact hnext
  · have hcurr : cutArcPred i j (gc.moverAt k) := by
      simpa [hccw.1] using cutArcPred_base i j
    have hnext : ¬cutArcPred i j (gc.moverAt (nextIndex gc.configs k)) := by
      simpa [hccw.2] using not_cutArcPred_at_left_cut i j hij.symm
    constructor
    · intro h
      exact False.elim (hnext h)
    · intro h
      exact False.elim (h hcurr)

private theorem cutArcPred_next_iff_not_of_edgeCrossAt_right
    (gc : GoodCycle sys) {i j : Fin sys.rs.n} (hij : i ≠ j)
    {k : Fin gc.configs.length} (hcross : edgeCrossAt gc j k) :
    cutArcPred i j (gc.moverAt (nextIndex gc.configs k)) ↔
      ¬cutArcPred i j (gc.moverAt k) := by
  rcases hcross with hcw | hccw
  · have hcurr : cutArcPred i j (gc.moverAt k) := by
      simpa [hcw.1] using cutArcPred_end i j
    have hnext : ¬cutArcPred i j (gc.moverAt (nextIndex gc.configs k)) := by
      simpa [hcw.2] using not_cutArcPred_at_right_cut i j hij.symm
    constructor
    · intro h
      exact False.elim (hnext h)
    · intro h
      exact False.elim (h hcurr)
  · have hcurr : ¬cutArcPred i j (gc.moverAt k) := by
      simpa [hccw.1] using not_cutArcPred_at_right_cut i j hij.symm
    have hnext : cutArcPred i j (gc.moverAt (nextIndex gc.configs k)) := by
      simpa [hccw.2] using cutArcPred_end i j
    constructor
    · intro _
      exact hcurr
    · intro _
      exact hnext

private theorem cutArcPred_eq_after_first_between_ordered_singletonCrossings
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j)
    (hord :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val <
        (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val)
    {k : Fin gc.configs.length}
    (hk1 :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val + 1 ≤ k.val)
    (hk2 :
      k.val ≤ (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val) :
    cutArcPred i j (gc.moverAt k) ↔
      cutArcPred i j
        (gc.moverAt (nextIndex gc.configs (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose)) := by
  let ki : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose
  let kj : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose
  have hki_succ : ki.val + 1 < gc.configs.length := by omega
  have hnext_ki : nextIndex gc.configs ki = ⟨ki.val + 1, hki_succ⟩ := by
    simpa [ki] using (nextIndex_eq_natSucc gc (m := ki.val) hki_succ)
  have hconst :
      cutArcPred i j (gc.moverAt ⟨ki.val + 1, hki_succ⟩) ↔
        cutArcPred i j (gc.moverAt k) := by
    refine cutArcPred_eq_of_no_cut_crossings_between gc i j (ki.val + 1) k.val hk1 k.isLt ?_
    intro x hx1 hx2
    have hx_ne_i : x ≠ ki := by
      intro hEq
      have : ki.val + 1 ≤ ki.val := by simpa [ki, hEq] using hx1
      omega
    have hx_ne_j : x ≠ kj := by
      intro hEq
      have : kj.val < kj.val := by
        have hxkj : x.val < kj.val := by omega
        simpa [kj, hEq] using hxkj
      omega
    exact ⟨by
      simpa [ki] using not_edgeCrossAt_of_ne_singletonCross gc i hi hx_ne_i,
      by simpa [kj] using not_edgeCrossAt_of_ne_singletonCross gc j hj hx_ne_j⟩
  simpa [ki, hnext_ki] using hconst.symm

private theorem cutArcPred_eq_before_first_ordered_singletonCrossing
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j)
    (hord :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val <
        (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val)
    {k : Fin gc.configs.length}
    (hk : k.val ≤ (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val) :
    cutArcPred i j (gc.moverAt k) ↔
      cutArcPred i j (gc.moverAt (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose) := by
  let ki : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose
  let kj : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose
  refine cutArcPred_eq_of_no_cut_crossings_between gc i j k.val ki.val hk ki.isLt ?_
  intro x hx1 hx2
  have hx_ne_i : x ≠ ki := by
    intro hEq
    have : x.val < x.val := by simpa [ki, hEq] using hx2
    omega
  have hx_ne_j : x ≠ kj := by
    intro hEq
    have : x.val < kj.val := by
      have hxki : x.val < ki.val := by simpa [ki] using hx2
      omega
    simpa [kj, hEq] using this
  exact ⟨by
    simpa [ki] using not_edgeCrossAt_of_ne_singletonCross gc i hi hx_ne_i,
    by simpa [kj] using not_edgeCrossAt_of_ne_singletonCross gc j hj hx_ne_j⟩

private theorem cutArcPred_eq_after_second_ordered_singletonCrossing
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j)
    (hij : i ≠ j)
    (hord :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val <
        (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val)
    (hkj_succ :
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 <
        gc.configs.length)
    {k : Fin gc.configs.length}
    (hk :
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 ≤ k.val) :
    cutArcPred i j (gc.moverAt k) ↔
      cutArcPred i j
        (gc.moverAt (nextIndex gc.configs (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose)) := by
  let ki : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose
  let kj : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose
  have hnext_kj : nextIndex gc.configs kj = ⟨kj.val + 1, hkj_succ⟩ := by
    simpa [kj] using (nextIndex_eq_natSucc gc (m := kj.val) hkj_succ)
  have hconst :
      cutArcPred i j (gc.moverAt ⟨kj.val + 1, hkj_succ⟩) ↔
        cutArcPred i j (gc.moverAt k) := by
    refine cutArcPred_eq_of_no_cut_crossings_between gc i j (kj.val + 1) k.val hk k.isLt ?_
    intro x hx1 hx2
    have hx_ne_i : x ≠ ki := by
      intro hEq
      have : ki.val < ki.val + 1 := by
        have hxi : ki.val < x.val := by
          have hxgt : kj.val + 1 ≤ x.val := by simpa [kj] using hx1
          omega
        simpa [hEq] using hxi
      omega
    have hx_ne_j : x ≠ kj := by
      intro hEq
      have : kj.val + 1 ≤ kj.val := by simpa [kj, hEq] using hx1
      omega
    exact ⟨by
      simpa [ki] using not_edgeCrossAt_of_ne_singletonCross gc i hi hx_ne_i,
      by simpa [kj] using not_edgeCrossAt_of_ne_singletonCross gc j hj hx_ne_j⟩
  simpa [kj, hnext_kj] using hconst.symm

private theorem cutArcPred_after_second_iff_not_after_first_of_ordered_internal
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j) (hij : i ≠ j)
    (hord :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val <
        (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val)
    (hkj_succ :
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 <
        gc.configs.length) :
    cutArcPred i j
        (gc.moverAt (nextIndex gc.configs (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose)) ↔
      ¬cutArcPred i j
        (gc.moverAt (nextIndex gc.configs (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose)) := by
  let ki : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose
  let kj : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose
  have hcross_j : edgeCrossAt gc j kj :=
    (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose_spec.1
  have hki_succ : ki.val + 1 < gc.configs.length := by omega
  have hnext_ki : nextIndex gc.configs ki = ⟨ki.val + 1, hki_succ⟩ := by
    simpa [ki] using (nextIndex_eq_natSucc gc (m := ki.val) hki_succ)
  have hnext_kj : nextIndex gc.configs kj = ⟨kj.val + 1, hkj_succ⟩ := by
    simpa [kj] using (nextIndex_eq_natSucc gc (m := kj.val) hkj_succ)
  have hmid :
      cutArcPred i j (gc.moverAt kj) ↔
        cutArcPred i j (gc.moverAt (nextIndex gc.configs ki)) := by
    have hki_lt_kj : ki.val + 1 ≤ kj.val := by
      simpa [ki, kj] using Nat.succ_le_of_lt hord
    have hkj_le : kj.val ≤ (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val := by
      simp [kj]
    have :=
      cutArcPred_eq_after_first_between_ordered_singletonCrossings gc hi hj hord
        (k := kj) hki_lt_kj hkj_le
    simpa [ki, kj, hnext_ki] using this
  have htoggle :
      cutArcPred i j (gc.moverAt (nextIndex gc.configs kj)) ↔
        ¬cutArcPred i j (gc.moverAt kj) := by
    simpa [hnext_kj] using cutArcPred_next_iff_not_of_edgeCrossAt_right gc hij hcross_j
  constructor
  · intro hafter
    have hnot_kj : ¬cutArcPred i j (gc.moverAt kj) := htoggle.mp hafter
    intro hafter_first
    exact hnot_kj (hmid.mpr hafter_first)
  · intro hnot_after_first
    have hnot_kj : ¬cutArcPred i j (gc.moverAt kj) := by
      intro hkj
      exact hnot_after_first (hmid.mp hkj)
    exact htoggle.mpr hnot_kj

private theorem two_ordered_singletonEdges_internal_false
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j) (hij : i ≠ j)
    (hord :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val <
        (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val)
    (hkj_succ :
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 <
        gc.configs.length) :
    False := by
  let ki : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose
  let kj : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose
  have hcross_i : edgeCrossAt gc i ki :=
    (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose_spec.1
  have hki_succ : ki.val + 1 < gc.configs.length := by
    omega
  have hnext_ki : nextIndex gc.configs ki = ⟨ki.val + 1, hki_succ⟩ := by
    simpa [ki] using (nextIndex_eq_natSucc gc (m := ki.val) hki_succ)
  have hnext_kj : nextIndex gc.configs kj = ⟨kj.val + 1, hkj_succ⟩ := by
    simpa [kj] using (nextIndex_eq_natSucc gc (m := kj.val) hkj_succ)
  have hproper :
      (nextIndex gc.configs ki).val < (nextIndex gc.configs kj).val := by
    simpa [hnext_ki, hnext_kj] using Nat.succ_lt_succ hord
  have htoggle_i :
      cutArcPred i j (gc.moverAt (nextIndex gc.configs ki)) ↔
        ¬cutArcPred i j (gc.moverAt ki) := by
    simpa [hnext_ki] using cutArcPred_next_iff_not_of_edgeCrossAt_left gc hij hcross_i
  have htoggle_after :
      cutArcPred i j (gc.moverAt (nextIndex gc.configs kj)) ↔
        ¬cutArcPred i j (gc.moverAt (nextIndex gc.configs ki)) :=
    cutArcPred_after_second_iff_not_after_first_of_ordered_internal
      gc hi hj hij hord hkj_succ
  by_cases hafter :
      cutArcPred i j (gc.moverAt (nextIndex gc.configs ki))
  · exact supportInterval_false_of_piecewise
        gc (cutArcFinset i j) (nextIndex gc.configs ki) (nextIndex gc.configs kj) hproper
        (fun k hk1 hk2 => by
          have hk1' : ki.val + 1 ≤ k.val := by
            simpa [hnext_ki] using hk1
          have hk2' : k.val ≤ kj.val := by
            have : k.val < kj.val + 1 := by
              simpa [hnext_kj] using hk2
            omega
          have hconst :=
            cutArcPred_eq_after_first_between_ordered_singletonCrossings
              gc hi hj hord (k := k) hk1' hk2'
          exact (mem_cutArcFinset i j (gc.moverAt k)).2 (hconst.mpr hafter))
        (fun k hk => by
          have hk' : k.val ≤ ki.val := by
            have : k.val < ki.val + 1 := by
              simpa [hnext_ki] using hk
            omega
          have hbefore :=
            cutArcPred_eq_before_first_ordered_singletonCrossing
              gc hi hj hord (k := k) hk'
          have hki_false : ¬cutArcPred i j (gc.moverAt ki) := htoggle_i.mp hafter
          have hk_false : ¬cutArcPred i j (gc.moverAt k) := by
            intro hkcut
            exact hki_false (hbefore.mp hkcut)
          simpa [mem_cutArcFinset] using hk_false)
        (fun k hk => by
          have hk' : kj.val + 1 ≤ k.val := by
            simpa [hnext_kj] using hk
          have hafter_const :=
            cutArcPred_eq_after_second_ordered_singletonCrossing
              gc hi hj hij hord hkj_succ (k := k) hk'
          have hend_false :
              ¬cutArcPred i j (gc.moverAt (nextIndex gc.configs kj)) := by
            intro hend
            exact (htoggle_after.mp hend) hafter
          have hk_false : ¬cutArcPred i j (gc.moverAt k) := by
            intro hkcut
            exact hend_false (hafter_const.mp hkcut)
          simpa [mem_cutArcFinset] using hk_false)
  · exact supportInterval_false_of_piecewise
        gc (cutArcComplFinset i j) (nextIndex gc.configs ki) (nextIndex gc.configs kj) hproper
        (fun k hk1 hk2 => by
          have hk1' : ki.val + 1 ≤ k.val := by
            simpa [hnext_ki] using hk1
          have hk2' : k.val ≤ kj.val := by
            have : k.val < kj.val + 1 := by
              simpa [hnext_kj] using hk2
            omega
          have hconst :=
            cutArcPred_eq_after_first_between_ordered_singletonCrossings
              gc hi hj hord (k := k) hk1' hk2'
          have hk_false : ¬cutArcPred i j (gc.moverAt k) := by
            intro hkcut
            exact hafter (hconst.mp hkcut)
          exact (mem_cutArcComplFinset i j (gc.moverAt k)).2 hk_false)
        (fun k hk => by
          have hk' : k.val ≤ ki.val := by
            have : k.val < ki.val + 1 := by
              simpa [hnext_ki] using hk
            omega
          have hbefore :=
            cutArcPred_eq_before_first_ordered_singletonCrossing
              gc hi hj hord (k := k) hk'
          have hki_true : cutArcPred i j (gc.moverAt ki) := by
            by_contra hki_false
            exact hafter (htoggle_i.mpr hki_false)
          have hk_true : cutArcPred i j (gc.moverAt k) := hbefore.mpr hki_true
          simpa [mem_cutArcComplFinset] using hk_true)
        (fun k hk => by
          have hk' : kj.val + 1 ≤ k.val := by
            simpa [hnext_kj] using hk
          have hafter_const :=
            cutArcPred_eq_after_second_ordered_singletonCrossing
              gc hi hj hij hord hkj_succ (k := k) hk'
          have hend_true :
              cutArcPred i j (gc.moverAt (nextIndex gc.configs kj)) :=
            htoggle_after.mpr hafter
          have hk_true : cutArcPred i j (gc.moverAt k) := hafter_const.mpr hend_true
          simpa [mem_cutArcComplFinset] using hk_true)

private theorem two_singletonEdges_internal_crossings_false
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j) (hij : i ≠ j)
    (hki_succ :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val + 1 <
        gc.configs.length)
    (hkj_succ :
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 <
        gc.configs.length) :
    False := by
  let ki : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose
  let kj : Fin gc.configs.length := (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose
  have hcross_ne : ki ≠ kj := singletonEdge_crossing_ne_of_ne gc hi hj hij
  have hvals_ne : ki.val ≠ kj.val := by
    intro hEq
    apply hcross_ne
    exact Fin.ext hEq
  rcases lt_or_gt_of_ne hvals_ne with hord | hord
  · simpa [ki, kj] using
      two_ordered_singletonEdges_internal_false gc hi hj hij hord hkj_succ
  · simpa [ki, kj] using
      two_ordered_singletonEdges_internal_false gc hj hi hij.symm hord hki_succ

private theorem two_singletonEdges_force_final_crossing
    (gc : GoodCycle sys) {i j : Fin sys.rs.n}
    (hi : singletonEdge gc i) (hj : singletonEdge gc j) (hij : i ≠ j) :
    (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val + 1 =
        gc.configs.length ∨
      (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 =
        gc.configs.length := by
  by_cases hki :
      (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val + 1 <
        gc.configs.length
  · by_cases hkj :
        (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 <
          gc.configs.length
    · exact False.elim
        (two_singletonEdges_internal_crossings_false gc hi hj hij hki hkj)
    · right
      omega
  · left
    omega

/-! ### Binary Bounce Context Lemma (Claim 4.6.3, No Binary 2-Cycle) -/

-- Helper: move at position q ≠ p leaves value unchanged.
private lemma move_at_ne (sys : System) (c : Config sys.rs) (p q : Fin sys.rs.n)
    (hne : q ≠ p) : move sys c p q = c q := by
  simp [move, hne]

-- Helper: left p ≠ p for n ≥ 4.
private lemma left_ne_self' {n : Nat} (hn : 4 ≤ n) (p : Fin n) : left p ≠ p := by
  intro h
  have := congrArg Fin.val h
  simp only [left_val] at this
  have hp := p.isLt
  by_cases hp0 : p.val = 0
  · rw [hp0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at this; omega
  · rw [show p.val + n - 1 = (p.val - 1) + n from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at this; omega

-- Helper: right p ≠ p for n ≥ 4.
private lemma right_ne_self' {n : Nat} (hn : 4 ≤ n) (p : Fin n) : right p ≠ p := by
  intro h
  have := congrArg Fin.val h
  simp only [right_val] at this
  have hp := p.isLt
  by_cases hp1 : p.val + 1 < n
  · rw [Nat.mod_eq_of_lt hp1] at this; omega
  · rw [show p.val + 1 = n from by omega, Nat.mod_self] at this; omega

-- Helper: nextIndex k ≠ k when list length ≥ 2.
private lemma nextIndex_ne_self {α : Type} {xs : List α} (k : Fin xs.length)
    (hlen : xs.length ≥ 2) : nextIndex xs k ≠ k := by
  intro h
  have := congrArg Fin.val h
  simp only [nextIndex] at this
  have hk := k.isLt
  by_cases hk1 : k.val + 1 < xs.length
  · rw [Nat.mod_eq_of_lt hk1] at this; omega
  · rw [show k.val + 1 = xs.length from by omega, Nat.mod_self] at this; omega

-- Helper: if nextIndex k₁ = k₂ and nextIndex k₂ = k₁ then length ≤ 2.
private lemma cycle_length_le_two {α : Type} {xs : List α}
    {k₁ k₂ : Fin xs.length} (hne : k₁ ≠ k₂)
    (h₁ : nextIndex xs k₁ = k₂) (h₂ : nextIndex xs k₂ = k₁) :
    xs.length ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have hk₁v := congrArg Fin.val h₁
  have hk₂v := congrArg Fin.val h₂
  simp only [nextIndex] at hk₁v hk₂v
  have hk₁lt := k₁.isLt
  have hk₂lt := k₂.isLt
  have hne_val : k₁.val ≠ k₂.val := fun h => hne (Fin.ext h)
  -- Eliminate the mod in hk₁v: (k₁.val + 1) % xs.length = k₂.val
  have hmod₁ : (k₁.val + 1) % xs.length = k₂.val := hk₁v
  have hmod₂ : (k₂.val + 1) % xs.length = k₁.val := hk₂v
  -- Case split on whether k₁.val + 1 < xs.length
  by_cases hc₁ : k₁.val + 1 < xs.length
  · rw [Nat.mod_eq_of_lt hc₁] at hmod₁
    -- k₂.val = k₁.val + 1
    by_cases hc₂ : k₂.val + 1 < xs.length
    · rw [Nat.mod_eq_of_lt hc₂] at hmod₂
      -- k₁.val = k₂.val + 1 = k₁.val + 2, contradiction
      omega
    · -- k₂.val + 1 = xs.length, so (k₂.val + 1) % xs.length = 0
      have : k₂.val + 1 = xs.length := by omega
      rw [this, Nat.mod_self] at hmod₂
      -- k₁.val = 0, k₂.val = 1, length = 2, contradicts hgt
      omega
  · -- k₁.val + 1 = xs.length (since k₁.val < xs.length, k₁.val + 1 ≤ xs.length)
    have : k₁.val + 1 = xs.length := by omega
    rw [this, Nat.mod_self] at hmod₁
    -- k₂.val = 0
    by_cases hc₂ : k₂.val + 1 < xs.length
    · rw [Nat.mod_eq_of_lt hc₂] at hmod₂
      -- k₁.val = k₂.val + 1 = 1, length = 2, contradicts hgt
      omega
    · have : k₂.val + 1 = xs.length := by omega
      -- k₂.val = 0 and k₂.val + 1 = xs.length means length = 1
      -- But hgt says length ≥ 3, contradiction
      omega

/-- No Binary 2-Cycle Lemma: for a binary processor with exactly 2 firings
    in a cycle of length ≥ 3, the two (L,R) contexts must differ.
    Otherwise f(L,0,R)=1 and f(L,1,R)=0, which creates a 2-cycle at p:
    p is privileged at the config after each firing, forcing p to fire
    at consecutive steps. With only 2 firings total, this means the cycle
    has length 2, contradicting hlen ≥ 3. -/
theorem no_binary_2_cycle (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    -- Two steps where p fires
    (k₁ k₂ : Fin gc.configs.length) (hne : k₁ ≠ k₂)
    (hmov₁ : gc.moverAt k₁ = p) (hmov₂ : gc.moverAt k₂ = p)
    -- p fires exactly twice: only at k₁ and k₂
    (hexact : ∀ k : Fin gc.configs.length, gc.moverAt k = p → k = k₁ ∨ k = k₂)
    -- Cycle has length ≥ 3 (other processors fire between p's two firings)
    (hlen : gc.configs.length ≥ 3)
    -- Same (L, R) context at both steps
    (hL : (gc.configs.get k₁) (left p) = (gc.configs.get k₂) (left p))
    (hR : (gc.configs.get k₁) (right p) = (gc.configs.get k₂) (right p)) :
    -- Then S values must also be equal (same full triple → entry conflict)
    (gc.configs.get k₁) p = (gc.configs.get k₂) p := by
  -- Binary: sys.rs.m p = 2
  have hm2 : sys.rs.m p = 2 := hbin
  -- By contradiction: assume S₁ ≠ S₂
  by_contra hneS
  -- p is privileged at both steps
  have hpriv₁ : privileged sys (gc.configs.get k₁) p := by
    rw [← hmov₁]; exact gc.moverAt_privileged k₁
  have hpriv₂ : privileged sys (gc.configs.get k₂) p := by
    rw [← hmov₂]; exact gc.moverAt_privileged k₂
  -- Unfold privileged to get f ≠ S
  unfold privileged at hpriv₁ hpriv₂
  -- Abbreviate
  set S₁ := (gc.configs.get k₁) p with hS₁_def
  set S₂ := (gc.configs.get k₂) p with hS₂_def
  set L₀ := (gc.configs.get k₁) (left p) with hL₀_def
  set R₀ := (gc.configs.get k₁) (right p) with hR₀_def
  -- Rewrite hpriv₂ to use L₀, R₀ via hL, hR
  have hpriv₂' : sys.f p L₀ S₂ R₀ ≠ S₂ := by
    have : L₀ = (gc.configs.get k₂) (left p) := hL
    have : R₀ = (gc.configs.get k₂) (right p) := hR
    rw [this, ‹L₀ = _›]; exact hpriv₂
  -- In Fin 2: f(L₀, S₁, R₀) ≠ S₁ and S₁ ≠ S₂ → f(L₀, S₁, R₀).val = S₂.val
  set f₁ := sys.f p L₀ S₁ R₀ with hf₁_def
  have hf₁_eq : f₁ = S₂ := by
    ext
    have hf₁lt : f₁.val < 2 := hm2 ▸ f₁.isLt
    have hS₁lt : S₁.val < 2 := hm2 ▸ S₁.isLt
    have hS₂lt : S₂.val < 2 := hm2 ▸ S₂.isLt
    have hfne : f₁.val ≠ S₁.val := fun h => hpriv₁ (Fin.ext h)
    have hSne : S₁.val ≠ S₂.val := fun h => hneS (Fin.ext h)
    omega
  -- left p ≠ p and right p ≠ p (since n ≥ 4)
  have hlp_ne : (left p : Fin sys.rs.n) ≠ p := left_ne_self' sys.rs.n_ge_4 p
  have hrp_ne : (right p : Fin sys.rs.n) ≠ p := right_ne_self' sys.rs.n_ge_4 p
  -- Use closed property at k₁: configs.get(nextIndex k₁) = move(configs.get k₁, i₁)
  -- where i₁ is privileged. By uniqueness, i₁ = p.
  obtain ⟨i₁, hpriv_i₁, hclosed₁⟩ := gc.closed k₁
  have hi₁_eq : i₁ = p :=
    (gc.moverAt_unique k₁ i₁ hpriv_i₁).symm ▸ hmov₁
  rw [hi₁_eq] at hclosed₁
  -- Show p is privileged at nextIndex k₁:
  -- The next config = move(configs.get k₁, p), which at:
  --   left p: unchanged (= L₀), right p: unchanged (= R₀), p: f₁ = S₂
  -- So f(L₀, S₂, R₀) ≠ S₂ holds by hpriv₂'.
  have hnext_priv : privileged sys (gc.configs.get (nextIndex gc.configs k₁)) p := by
    unfold privileged
    rw [hclosed₁]
    rw [move_at_ne sys (gc.configs.get k₁) p (left p) hlp_ne]
    rw [move_at_ne sys (gc.configs.get k₁) p (right p) hrp_ne]
    -- For move at p itself: move sys c p p = Fin.cast ... (f p (c (left p)) (c p) (c (right p)))
    show sys.f p L₀ (move sys (gc.configs.get k₁) p p) R₀ ≠
         move sys (gc.configs.get k₁) p p
    have hmP : move sys (gc.configs.get k₁) p p =
        Fin.cast (by rfl) (sys.f p (gc.configs.get k₁ (left p)) (gc.configs.get k₁ p)
          (gc.configs.get k₁ (right p))) := by
      simp [move]
    rw [hmP, Fin.cast_eq_self]
    -- Now goal is: f p L₀ f₁ R₀ ≠ f₁
    change sys.f p L₀ f₁ R₀ ≠ f₁
    rw [hf₁_eq]
    exact hpriv₂'
  -- By unique_privileged, moverAt(nextIndex k₁) = p
  have hmov_next₁ : gc.moverAt (nextIndex gc.configs k₁) = p :=
    (gc.moverAt_unique (nextIndex gc.configs k₁) p hnext_priv).symm
  -- By hexact, nextIndex k₁ ∈ {k₁, k₂}
  rcases hexact (nextIndex gc.configs k₁) hmov_next₁ with h_eq_k₁ | h_eq_k₂
  · -- nextIndex k₁ = k₁: impossible since length ≥ 3 ≥ 2
    exact absurd h_eq_k₁ (nextIndex_ne_self k₁ (by omega))
  · -- nextIndex k₁ = k₂. Now repeat for k₂.
    obtain ⟨i₂, hpriv_i₂, hclosed₂⟩ := gc.closed k₂
    have hi₂_eq : i₂ = p :=
      (gc.moverAt_unique k₂ i₂ hpriv_i₂).symm ▸ hmov₂
    rw [hi₂_eq] at hclosed₂
    -- f(L₀, S₂, R₀) = S₁ (in Fin 2, ≠ S₂ and only 2 values)
    set f₂ := sys.f p L₀ S₂ R₀ with hf₂_def
    have hf₂_eq : f₂ = S₁ := by
      ext
      have hf₂lt : f₂.val < 2 := hm2 ▸ f₂.isLt
      have hS₁lt : S₁.val < 2 := hm2 ▸ S₁.isLt
      have hS₂lt : S₂.val < 2 := hm2 ▸ S₂.isLt
      have hfne : f₂.val ≠ S₂.val := fun h => hpriv₂' (Fin.ext h)
      have hSne : S₁.val ≠ S₂.val := fun h => hneS (Fin.ext h)
      omega
    -- p is privileged at nextIndex k₂
    have hnext_priv₂ : privileged sys (gc.configs.get (nextIndex gc.configs k₂)) p := by
      unfold privileged
      rw [hclosed₂]
      rw [move_at_ne sys (gc.configs.get k₂) p (left p) hlp_ne]
      rw [move_at_ne sys (gc.configs.get k₂) p (right p) hrp_ne]
      show sys.f p ((gc.configs.get k₂) (left p)) (move sys (gc.configs.get k₂) p p)
           ((gc.configs.get k₂) (right p)) ≠
           move sys (gc.configs.get k₂) p p
      have hmP₂ : move sys (gc.configs.get k₂) p p =
          Fin.cast (by rfl) (sys.f p (gc.configs.get k₂ (left p)) (gc.configs.get k₂ p)
            (gc.configs.get k₂ (right p))) := by
        simp [move]
      rw [hmP₂, Fin.cast_eq_self]
      -- Goal: f p (c₂(left p)) (f p (c₂(left p)) S₂ (c₂(right p))) (c₂(right p)) ≠
      --       f p (c₂(left p)) S₂ (c₂(right p))
      -- c₂(left p) = L₀ by hL, c₂(right p) = R₀ by hR
      rw [← hL, ← hR]
      -- f p L₀ (f p L₀ S₂ R₀) R₀ ≠ f p L₀ S₂ R₀
      -- i.e., f p L₀ f₂ R₀ ≠ f₂
      change sys.f p L₀ f₂ R₀ ≠ f₂
      rw [hf₂_eq]
      exact hpriv₁
    have hmov_next₂ : gc.moverAt (nextIndex gc.configs k₂) = p :=
      (gc.moverAt_unique (nextIndex gc.configs k₂) p hnext_priv₂).symm
    rcases hexact (nextIndex gc.configs k₂) hmov_next₂ with h_eq_k₁' | h_eq_k₂'
    · -- nextIndex k₁ = k₂ and nextIndex k₂ = k₁ → length ≤ 2
      exact absurd (cycle_length_le_two hne h_eq_k₂ h_eq_k₁') (by omega)
    · -- nextIndex k₂ = k₂: impossible since length ≥ 3 ≥ 2
      exact absurd h_eq_k₂' (nextIndex_ne_self k₂ (by omega))

/-- In a cycle of length at least 3, a binary processor that fires exactly twice
    cannot keep the mover token on itself at either firing. Otherwise its two
    firings are consecutive with identical neighbor contexts, contradicting the
    binary 2-cycle obstruction. -/
theorem GoodCycle.stayMoveCountAt_eq_zero_of_binary_fireCount_two
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (hlen : gc.configs.length ≥ 3)
    (hfire : gc.fireCount p = 2) :
    gc.stayMoveCountAt p = 0 := by
  by_contra hstay
  have hstay_pos : 0 < gc.stayMoveCountAt p := by
    omega
  unfold GoodCycle.stayMoveCountAt at hstay_pos
  have hstay_ne :
      (∑ k : Fin gc.configs.length,
        if gc.moverAt k = p ∧ gc.stepDir k = .stay then 1 else 0) ≠ 0 := by
    omega
  rcases Finset.exists_ne_zero_of_sum_ne_zero hstay_ne with ⟨k, _, hk_ne_zero⟩
  have hk : gc.moverAt k = p ∧ gc.stepDir k = .stay := by
    by_cases hk' : gc.moverAt k = p ∧ gc.stepDir k = .stay
    · exact hk'
    · simp [hk'] at hk_ne_zero
  have hmov_next : gc.moverAt (nextIndex gc.configs k) = p := by
    calc
      gc.moverAt (nextIndex gc.configs k) = gc.moverAt k :=
        gc.eq_self_of_stepDir_eq_stay hk.2
      _ = p := hk.1
  have hk_ne_next : k ≠ nextIndex gc.configs k := by
    intro h
    exact nextIndex_ne_self k (by omega) h.symm
  have hexact : ∀ j : Fin gc.configs.length, gc.moverAt j = p →
      j = k ∨ j = nextIndex gc.configs k := by
    intro j hj
    by_cases hjk : j = k
    · exact Or.inl hjk
    · by_cases hjnext : j = nextIndex gc.configs k
      · exact Or.inr hjnext
      · have hthree :
          3 ≤ ∑ t : Fin gc.configs.length, if gc.moverAt t = p then (1 : Nat) else 0 := by
          have hsubset :
              ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length)) ⊆ Finset.univ := by
            intro t _
            simp
          have hsubset_sum_eq :
              Finset.sum ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length))
                (fun t => if gc.moverAt t = p then (1 : Nat) else 0) = 3 := by
            have hfilter :
                {x ∈ ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length)) |
                    gc.moverAt x = p} =
                  ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length)) := by
              apply Finset.ext
              intro t
              constructor
              · intro ht
                exact (Finset.mem_filter.mp ht).1
              · intro ht
                refine Finset.mem_filter.mpr ?_
                refine ⟨ht, ?_⟩
                simp at ht
                rcases ht with rfl | ht
                · exact hk.1
                · rcases ht with rfl | rfl
                  · exact hmov_next
                  · exact hj
            calc
              Finset.sum ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length))
                  (fun t => if gc.moverAt t = p then (1 : Nat) else 0)
                = ({x ∈ ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length)) |
                    gc.moverAt x = p}).card := by
                    simp
              _ = (({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length)).card) := by
                    rw [hfilter]
              _ = 3 := by
                    have hpair_insert :
                        ({k, nextIndex gc.configs k} : Finset (Fin gc.configs.length)) =
                          insert (nextIndex gc.configs k) ({k} : Finset (Fin gc.configs.length)) := by
                      ext t
                      simp [or_comm]
                    have hcard_pair :
                        ({k, nextIndex gc.configs k} : Finset (Fin gc.configs.length)).card = 2 := by
                      rw [hpair_insert, Finset.card_insert_of_notMem]
                      · simp
                      · simpa [eq_comm] using hk_ne_next
                    have hj_not_mem_pair :
                        j ∉ ({k, nextIndex gc.configs k} : Finset (Fin gc.configs.length)) := by
                      simp [hjk, hjnext]
                    have htriple_insert :
                        ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length)) =
                          insert j ({k, nextIndex gc.configs k} : Finset (Fin gc.configs.length)) := by
                      ext t
                      simp [or_assoc, or_comm, or_left_comm]
                    rw [htriple_insert, Finset.card_insert_of_notMem hj_not_mem_pair, hcard_pair]
          have hsubset_sum :
              3 ≤ Finset.sum ({k, nextIndex gc.configs k, j} : Finset (Fin gc.configs.length))
                (fun t => if gc.moverAt t = p then (1 : Nat) else 0) := by
            omega
          exact le_trans hsubset_sum
            (Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
              intro t _ _
              split_ifs <;> omega))
        have : False := by
          rw [← gc.fireCount_eq_sum_moverAt p, hfire] at hthree
          omega
        exact False.elim this
  have hL :
      (gc.configs.get k) (left p) =
        (gc.configs.get (nextIndex gc.configs k)) (left p) := by
    symm
    exact gc.state_eq_of_ne_moverAt k (left p) (by
      rw [hk.1]
      exact left_ne_self' sys.rs.n_ge_4 p)
  have hR :
      (gc.configs.get k) (right p) =
        (gc.configs.get (nextIndex gc.configs k)) (right p) := by
    symm
    exact gc.state_eq_of_ne_moverAt k (right p) (by
      rw [hk.1]
      exact right_ne_self' sys.rs.n_ge_4 p)
  have hself_eq :
      (gc.configs.get k) p =
        (gc.configs.get (nextIndex gc.configs k)) p :=
    no_binary_2_cycle gc p hbin k (nextIndex gc.configs k) hk_ne_next hk.1 hmov_next
      hexact hlen hL hR
  have hself_ne :
      (gc.configs.get k) p ≠
        (gc.configs.get (nextIndex gc.configs k)) p := by
    have hne := gc.state_ne_at_moverAt k
    rw [hk.1] at hne
    intro hEq
    exact hne hEq.symm
  exact hself_ne hself_eq

/-- For a binary processor that fires exactly twice in an odd-winding cycle of
    length at least 3, the two incident edge traversal counts are exactly
    `(1,3)` or `(3,1)`. This is the precise local counting statement behind the
    phase-10 singleton-edge argument. -/
theorem GoodCycle.adjacentEdgeTraversalCounts_of_binary_fireCount_two_of_isOddWinding
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (hlen : gc.configs.length ≥ 3)
    (hodd : gc.isOddWinding)
    (hfire : gc.fireCount p = 2) :
    (gc.edgeTraversalCount (left p) = 1 ∧ gc.edgeTraversalCount p = 3) ∨
      (gc.edgeTraversalCount (left p) = 3 ∧ gc.edgeTraversalCount p = 1) := by
  have hstay0 : gc.stayMoveCountAt p = 0 :=
    gc.stayMoveCountAt_eq_zero_of_binary_fireCount_two p hbin hlen hfire
  have hsum :
      gc.edgeTraversalCount (left p) + gc.edgeTraversalCount p = 4 := by
    rw [gc.edgeTraversalCount_left_add_edgeTraversalCount_eq_twice_fireCount_sub_stay p,
      hfire, hstay0]
  rcases gc.singletonEdge_or_edgeTraversalCount_ge_three_of_isOddWinding hodd (left p) with
    hleft1 | hleft3
  · rcases gc.singletonEdge_or_edgeTraversalCount_ge_three_of_isOddWinding hodd p with
      hself1 | hself3
    · exfalso
      omega
    · left
      omega
  · rcases gc.singletonEdge_or_edgeTraversalCount_ge_three_of_isOddWinding hodd p with
      hself1 | hself3
    · right
      omega
    · exfalso
      omega

/-- A binary processor with exactly two firings contributes exactly one
    singleton incident edge in the odd-winding regime. -/
theorem GoodCycle.exactlyOneAdjacentSingletonEdge_of_binary_fireCount_two_of_isOddWinding
    (gc : GoodCycle sys)
    (p : Fin sys.rs.n)
    (hbin : isBinary sys.rs p)
    (hlen : gc.configs.length ≥ 3)
    (hodd : gc.isOddWinding)
    (hfire : gc.fireCount p = 2) :
    (singletonEdge gc (left p) ∧ ¬singletonEdge gc p) ∨
      (¬singletonEdge gc (left p) ∧ singletonEdge gc p) := by
  rcases gc.adjacentEdgeTraversalCounts_of_binary_fireCount_two_of_isOddWinding
      p hbin hlen hodd hfire with h | h
  · left
    refine ⟨(singletonEdge_iff_edgeTraversalCount_eq_one gc (left p)).2 h.1, ?_⟩
    intro hsingle
    have hcount : gc.edgeTraversalCount p = 1 :=
      (singletonEdge_iff_edgeTraversalCount_eq_one gc p).1 hsingle
    omega
  · right
    refine ⟨?_, (singletonEdge_iff_edgeTraversalCount_eq_one gc p).2 h.2⟩
    intro hsingle
    have hcount : gc.edgeTraversalCount (left p) = 1 :=
      (singletonEdge_iff_edgeTraversalCount_eq_one gc (left p)).1 hsingle
    omega

/-- On a ring with at least three binary processors but no run of three
    consecutive binaries, one can extract two binary processors that are not
    adjacent to each other. This is the combinatorial input needed for the
    phase-10 singleton-edge counting argument. -/
theorem exists_binary_nonadjacent_pair_of_hasGe3Binary_noThreeConsecutive
    (rs : RingSpec)
    (h3bin : hasGe3Binary rs)
    (hnoncons : ¬∃ i : Fin rs.n, threeConsecutiveBinary rs i) :
    ∃ p q : Fin rs.n,
      isBinary rs p ∧ isBinary rs q ∧ q ≠ p ∧ q ≠ left p ∧ q ≠ right p := by
  classical
  let binSet : Finset (Fin rs.n) := Finset.univ.filter (fun i : Fin rs.n => rs.m i = 2)
  have hcard : 2 < binSet.card := by
    unfold hasGe3Binary binaryCount at h3bin
    dsimp [binSet]
    omega
  rcases Finset.two_lt_card.mp hcard with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have habin : isBinary rs a := by
    simpa [binSet, isBinary] using ha
  have hbbin : isBinary rs b := by
    simpa [binSet, isBinary] using hb
  have hcbin : isBinary rs c := by
    simpa [binSet, isBinary] using hc
  by_cases hb_adj : b = left a ∨ b = right a
  · by_cases hc_adj : c = left a ∨ c = right a
    · have hleftbin : isBinary rs (left a) := by
        rcases hb_adj with hbleft | hbright
        · rw [← hbleft]
          exact hbbin
        · rcases hc_adj with hcleft | hcright
          · rw [← hcleft]
            exact hcbin
          · exfalso
            exact hbc (by simpa [hbright, hcright])
      have hrightbin : isBinary rs (right a) := by
        rcases hb_adj with hbleft | hbright
        · rcases hc_adj with hcleft | hcright
          · exfalso
            exact hbc (by simpa [hbleft, hcleft])
          · rw [← hcright]
            exact hcbin
        · rw [← hbright]
          exact hbbin
      have hthree : threeConsecutiveBinary rs (left a) := by
        refine ⟨hleftbin, ?_, ?_⟩
        · simpa using habin
        · simpa using hrightbin
      exact False.elim (hnoncons ⟨left a, hthree⟩)
    · refine ⟨a, c, habin, hcbin, ?_, ?_, ?_⟩
      · simpa [eq_comm] using hac
      · intro h
        exact hc_adj (Or.inl h)
      · intro h
        exact hc_adj (Or.inr h)
  · refine ⟨a, b, habin, hbbin, ?_, ?_, ?_⟩
    · simpa [eq_comm] using hab
    · intro h
      exact hb_adj (Or.inl h)
    · intro h
      exact hb_adj (Or.inr h)

/-- Two nonadjacent binary processors that each fire exactly twice contribute
    two distinct singleton edges in the odd-winding regime. -/
theorem GoodCycle.exists_two_distinct_singletonEdges_of_two_nonadjacent_binary_fireCount_two_of_isOddWinding
    (gc : GoodCycle sys)
    (p q : Fin sys.rs.n)
    (hpbin : isBinary sys.rs p)
    (hqbin : isBinary sys.rs q)
    (hlen : gc.configs.length ≥ 3)
    (hodd : gc.isOddWinding)
    (hpfire : gc.fireCount p = 2)
    (hqfire : gc.fireCount q = 2)
    (hqp : q ≠ p)
    (hqleft : q ≠ left p)
    (hqright : q ≠ right p) :
    ∃ i j : Fin sys.rs.n, i ≠ j ∧ singletonEdge gc i ∧ singletonEdge gc j := by
  rcases gc.exactlyOneAdjacentSingletonEdge_of_binary_fireCount_two_of_isOddWinding
      p hpbin hlen hodd hpfire with hp | hp
  · rcases gc.exactlyOneAdjacentSingletonEdge_of_binary_fireCount_two_of_isOddWinding
        q hqbin hlen hodd hqfire with hq | hq
    · refine ⟨left p, left q, ?_, hp.1, hq.1⟩
      intro hEq
      have : p = q := by
        calc
          p = right (left p) := by simpa using (right_left_eq_self p).symm
          _ = right (left q) := by rw [hEq]
          _ = q := by simpa using (right_left_eq_self q)
      exact hqp this.symm
    · refine ⟨left p, q, ?_, hp.1, hq.2⟩
      intro hEq
      exact hqleft (by simpa [eq_comm] using hEq)
  · rcases gc.exactlyOneAdjacentSingletonEdge_of_binary_fireCount_two_of_isOddWinding
        q hqbin hlen hodd hqfire with hq | hq
    · refine ⟨p, left q, ?_, hp.2, hq.1⟩
      intro hEq
      have : q = right p := by
        calc
          q = right (left q) := by simpa using (right_left_eq_self q).symm
          _ = right p := by rw [← hEq]
      exact hqright this
    · refine ⟨p, q, ?_, hp.2, hq.2⟩
      intro hEq
      exact hqp (by simpa [eq_comm] using hEq)

/-- In the fully minimal odd-winding regime where every binary processor fires
    exactly twice, having at least three binaries but no three consecutive
    binaries already forces two distinct singleton edges. -/
theorem GoodCycle.exists_two_distinct_singletonEdges_of_all_binary_fireCount_two_of_hasGe3Binary_noThreeConsecutive
    (gc : GoodCycle sys)
    (h3bin : hasGe3Binary sys.rs)
    (hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (hlen : gc.configs.length ≥ 3)
    (hodd : gc.isOddWinding)
    (hfire2 : ∀ p : Fin sys.rs.n, isBinary sys.rs p → gc.fireCount p = 2) :
    ∃ i j : Fin sys.rs.n, i ≠ j ∧ singletonEdge gc i ∧ singletonEdge gc j := by
  rcases exists_binary_nonadjacent_pair_of_hasGe3Binary_noThreeConsecutive sys.rs h3bin hnoncons with
    ⟨p, q, hpbin, hqbin, hqp, hqleft, hqright⟩
  exact gc.exists_two_distinct_singletonEdges_of_two_nonadjacent_binary_fireCount_two_of_isOddWinding
    p q hpbin hqbin hlen hodd (hfire2 p hpbin) (hfire2 q hqbin) hqp hqleft hqright

/-- In the same minimal odd-winding regime, the two forced singleton edges
    cannot both cross strictly before the terminal mover step. -/
theorem GoodCycle.exists_two_distinct_singletonEdges_with_final_crossing_of_all_binary_fireCount_two_of_hasGe3Binary_noThreeConsecutive
    (gc : GoodCycle sys)
    (h3bin : hasGe3Binary sys.rs)
    (hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (hlen : gc.configs.length ≥ 3)
    (hodd : gc.isOddWinding)
    (hfire2 : ∀ p : Fin sys.rs.n, isBinary sys.rs p → gc.fireCount p = 2) :
    ∃ i j : Fin sys.rs.n,
      ∃ hij : i ≠ j,
      ∃ hi : singletonEdge gc i,
      ∃ hj : singletonEdge gc j,
        (singletonEdge_existsUnique_edgeCrossAt gc i hi).choose.val + 1 =
            gc.configs.length ∨
          (singletonEdge_existsUnique_edgeCrossAt gc j hj).choose.val + 1 =
            gc.configs.length := by
  rcases gc.exists_two_distinct_singletonEdges_of_all_binary_fireCount_two_of_hasGe3Binary_noThreeConsecutive
      h3bin hnoncons hlen hodd hfire2 with
    ⟨i, j, hij, hi, hj⟩
  refine ⟨i, j, hij, hi, hj, ?_⟩
  exact two_singletonEdges_force_final_crossing gc hi hj hij

/-! ### Universal Entry Conflict for Non-Consecutive Binary -/

/-- Good cycle configs are pairwise distinct.
    This follows directly from the `distinct` field of `GoodCycle`. -/
private theorem good_cycle_configs_distinct (gc : GoodCycle sys) :
    ∀ j₁ j₂ : Fin gc.configs.length,
      gc.configs.get j₁ = gc.configs.get j₂ → j₁ = j₂ :=
  gc.distinct

-- NOTE: universal_entry_conflict_nonconsec was removed to break a circular
-- dependency (NonConsecutive.lean imported CaseObstructions.lean which imported
-- GlobalMinGap.lean, creating a cycle through the sorry). The non-consecutive
-- zero-winding case is now handled directly via nonConsecutive_zeroWinding_false
-- in GlobalMinGap.lean.

end LeanMn
