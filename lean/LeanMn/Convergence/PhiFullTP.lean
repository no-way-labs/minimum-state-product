/-
  Convergence/PhiFullTP.lean — Φ_full (TP-reachable max fc) + TP layer

  Defines the intermediate layers between FutureFc (PhiFull.lean) and
  the 617-edge DAG (ConstLayerDAG.lean).

  Key quantities:
  - cup2TpInvariant = (Exp2Count, Int21Count, Exp2Weight) from TP.lean
  - cup2PhiFull = max fc over TP-preserving bad-reachable configs
  - cup2CPhiStep = bad step preserving FutureFc AND TP AND Φ_full

  Architecture:
  - Every CF step either preserves (TP, Φ_full) → CΦ step, or
    strictly decreases (TP, Φ_full) in lex → handled by TP/Φ_full descent.
  - cup2BadConstFutureStep_wf follows from WF(CΦ) ∧ WF(TP/Φ_full descent)
    via wf_of_inner_segment.
-/
import LeanMn.Convergence.PhiFull
import LeanMn.Convergence.TP
import LeanMn.Convergence.Reachable

namespace LeanMn

/-! ### TP-preserving bad steps and reachability -/

/-- Forward TP-preserving bad step: bad step from c to c' that preserves
    all three TP quantities (Exp2Count, Int21Count, Exp2Weight). -/
def cup2TpBadStepFwd (n : Nat) (hn : 4 ≤ n)
    (c c' : Config (cup2Spec n hn)) : Prop :=
  cup2BadStepFwd n hn c c' ∧
    cup2TpInvariant n hn c' = cup2TpInvariant n hn c

/-- TP-bad-reachable: reflexive transitive closure of TP-preserving bad steps. -/
def cup2TpReachable (n : Nat) (hn : 4 ≤ n)
    (c d : Config (cup2Spec n hn)) : Prop :=
  Relation.ReflTransGen (cup2TpBadStepFwd n hn) c d

instance (n : Nat) (hn : 4 ≤ n) (c c' : Config (cup2Spec n hn)) :
    Decidable (cup2TpBadStepFwd n hn c c') := by
  unfold cup2TpBadStepFwd
  infer_instance

instance cup2TpBadStepFwd_decidableRel (n : Nat) (hn : 4 ≤ n) :
    DecidableRel (cup2TpBadStepFwd n hn) :=
  fun c c' => inferInstance

instance (n : Nat) (hn : 4 ≤ n) (c d : Config (cup2Spec n hn)) :
    Decidable (cup2TpReachable n hn c d) := by
  unfold cup2TpReachable
  exact instDecidableReflTransGen _ c d

lemma cup2TpReachable_refl (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2TpReachable n hn c c :=
  Relation.ReflTransGen.refl

lemma cup2TpReachable_trans (n : Nat) (hn : 4 ≤ n)
    {a b c : Config (cup2Spec n hn)}
    (hab : cup2TpReachable n hn a b)
    (hbc : cup2TpReachable n hn b c) :
    cup2TpReachable n hn a c :=
  Relation.ReflTransGen.trans hab hbc

lemma cup2TpReachable_step (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hstep : cup2TpBadStepFwd n hn c c') :
    cup2TpReachable n hn c c' :=
  Relation.ReflTransGen.single hstep

/-- TP-reachable is a sub-relation of bad-reachable. -/
lemma cup2TpReachable_implies_badReachable (n : Nat) (hn : 4 ≤ n)
    {c d : Config (cup2Spec n hn)}
    (h : cup2TpReachable n hn c d) :
    cup2BadReachable n hn c d := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih hstep.1

/-- TP invariant is preserved along TP-reachable paths. -/
lemma cup2TpInvariant_eq_of_tpReachable (n : Nat) (hn : 4 ≤ n)
    {c d : Config (cup2Spec n hn)}
    (h : cup2TpReachable n hn c d) :
    cup2TpInvariant n hn d = cup2TpInvariant n hn c := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.2.trans ih

/-! ### Φ_full definition -/

/-- The set of configs TP-bad-reachable from c, as a Finset.
    Computable via BFS (Reachable.lean provides Decidable ReflTransGen). -/
def cup2TpReachableSet (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) : Finset (Config (cup2Spec n hn)) :=
  Finset.univ.filter fun d => cup2TpReachable n hn c d

/-- Φ_full: max fc over all TP-bad-reachable configs (including self). -/
def cup2PhiFull (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) : Nat :=
  (cup2TpReachableSet n hn c).sup (fun d => cup2Fc n hn d)

/-! ### Basic properties -/

lemma mem_cup2TpReachableSet_iff (n : Nat) (hn : 4 ≤ n)
    (c d : Config (cup2Spec n hn)) :
    d ∈ cup2TpReachableSet n hn c ↔ cup2TpReachable n hn c d := by
  simp only [cup2TpReachableSet, Finset.mem_filter, Finset.mem_univ, true_and]

lemma self_mem_cup2TpReachableSet (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    c ∈ cup2TpReachableSet n hn c := by
  rw [mem_cup2TpReachableSet_iff]
  exact cup2TpReachable_refl n hn c

lemma cup2Fc_le_cup2PhiFull (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2Fc n hn c ≤ cup2PhiFull n hn c := by
  unfold cup2PhiFull
  exact Finset.le_sup (f := fun d => cup2Fc n hn d) (self_mem_cup2TpReachableSet n hn c)

lemma cup2PhiFull_attained (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    ∃ d : Config (cup2Spec n hn),
      cup2TpReachable n hn c d ∧
        cup2Fc n hn d = cup2PhiFull n hn c := by
  rcases Finset.exists_mem_eq_sup (cup2TpReachableSet n hn c)
      ⟨c, self_mem_cup2TpReachableSet n hn c⟩ (fun d => cup2Fc n hn d) with
    ⟨d, hd, hsup⟩
  exact ⟨d, (mem_cup2TpReachableSet_iff n hn c d).mp hd, hsup.symm⟩

lemma cup2PhiFull_eq_fc_of_tpReachable_fc_le (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn))
    (hfc_le : ∀ d : Config (cup2Spec n hn),
      cup2TpReachable n hn c d → cup2Fc n hn d ≤ cup2Fc n hn c) :
    cup2PhiFull n hn c = cup2Fc n hn c := by
  apply le_antisymm
  · unfold cup2PhiFull
    apply Finset.sup_le
    intro d hd
    exact hfc_le d ((mem_cup2TpReachableSet_iff n hn c d).mp hd)
  · exact cup2Fc_le_cup2PhiFull n hn c

/-- Φ_full ≤ FutureFc, since TP-reachable ⊆ bad-reachable. -/
lemma cup2PhiFull_le_cup2FutureFc (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) :
    cup2PhiFull n hn c ≤ cup2FutureFc n hn c := by
  unfold cup2PhiFull cup2FutureFc
  apply Finset.sup_le
  intro d hd
  rw [mem_cup2TpReachableSet_iff] at hd
  exact Finset.le_sup (f := fun d => cup2Fc n hn d)
    ((mem_cup2ReachableSet_iff n hn c d).mpr
      (cup2TpReachable_implies_badReachable n hn hd))

/-! ### Monotonicity -/

/-- TP-reachable set inclusion: if c TP-reaches d, then TpReachable(d) ⊆ TpReachable(c). -/
lemma cup2TpReachableSet_subset_of_tpReachable (n : Nat) (hn : 4 ≤ n)
    {c d : Config (cup2Spec n hn)}
    (hcd : cup2TpReachable n hn c d) :
    cup2TpReachableSet n hn d ⊆ cup2TpReachableSet n hn c := by
  intro e he
  rw [mem_cup2TpReachableSet_iff] at he ⊢
  exact cup2TpReachable_trans n hn hcd he

/-- Φ_full is non-increasing on TP-preserving bad steps.
    Proof: TP-reachable from c' ⊆ TP-reachable from c (via the step c→c'). -/
theorem cup2PhiFull_tp_step_mono (n : Nat) (hn : 4 ≤ n)
    {c c' : Config (cup2Spec n hn)}
    (hstep : cup2TpBadStepFwd n hn c c') :
    cup2PhiFull n hn c' ≤ cup2PhiFull n hn c := by
  unfold cup2PhiFull
  apply Finset.sup_le
  intro e he
  exact Finset.le_sup (f := fun d => cup2Fc n hn d)
    (cup2TpReachableSet_subset_of_tpReachable n hn
      (cup2TpReachable_step n hn hstep) he)

/-- Φ_full is non-increasing along TP-reachable paths. -/
theorem cup2PhiFull_mono (n : Nat) (hn : 4 ≤ n)
    {c d : Config (cup2Spec n hn)}
    (hcd : cup2TpReachable n hn c d) :
    cup2PhiFull n hn d ≤ cup2PhiFull n hn c := by
  unfold cup2PhiFull
  apply Finset.sup_le
  intro e he
  exact Finset.le_sup (f := fun d => cup2Fc n hn d)
    (cup2TpReachableSet_subset_of_tpReachable n hn hcd he)

/-! ### CΦ step definition -/

/-- CΦ step: bad step preserving FutureFc AND TpInvariant AND Φ_full.
    This is the innermost layer, handled by the 617-edge DAG + interior. -/
def cup2CPhiStep (n : Nat) (hn : 4 ≤ n)
    (c' c : Config (cup2Spec n hn)) : Prop :=
  cup2BadConstFutureStep n hn c' c ∧
    cup2TpInvariant n hn c' = cup2TpInvariant n hn c ∧
    cup2PhiFull n hn c' = cup2PhiFull n hn c

/-! ### TP non-increasing on bad steps (n ≥ 9) -/

/-! ### Local TP component ≤ lemmas (position case split) -/

/-- Local Exp2 after ≤ before for any move at any position. -/
private lemma localExp2_move_le (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) :
    localExp2After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) ≤
      localExp2Before n i (c (left i)).1 (c i).1 (c (right i)).1 := by
  have hin : i.1 < n := i.2
  by_cases h0 : i.1 = 0
  · -- TBot: both bit positions out of range
    unfold localExp2After localExp2Before
    rw [cup2Exp2BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega),
        cup2Exp2BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega)]
    have hleft_val : (left i).1 = n - 1 := by
      rw [left_val, h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [cup2Exp2BitVal_eq_zero_of_ge_top n _ _ _ (by omega),
        cup2Exp2BitVal_eq_zero_of_ge_top n _ _ _ (by omega)]
  · by_cases h1 : i.1 = 1
    · -- TLow: both bit positions out of range
      unfold localExp2After localExp2Before
      have hleft_lt : (left i).1 < 2 := by rw [left_val_of_ne_zero (by omega)]; omega
      rw [cup2Exp2BitVal_eq_zero_of_lt_two n _ _ _ hleft_lt,
          cup2Exp2BitVal_eq_zero_of_lt_two n _ _ _ hleft_lt,
          cup2Exp2BitVal_eq_zero_of_lt_two n _ _ _ (by omega),
          cup2Exp2BitVal_eq_zero_of_lt_two n _ _ _ (by omega)]
    · by_cases htop : i.1 + 1 = n
      · -- TTop: both bit positions out of range
        unfold localExp2After localExp2Before
        have hleft_ge : n ≤ (left i).1 + 2 := by
          rw [left_val_of_ne_zero (by omega)]; omega
        rw [cup2Exp2BitVal_eq_zero_of_ge_top n _ _ _ hleft_ge,
            cup2Exp2BitVal_eq_zero_of_ge_top n _ _ _ hleft_ge,
            cup2Exp2BitVal_eq_zero_of_ge_top n _ _ _ (by omega),
            cup2Exp2BitVal_eq_zero_of_ge_top n _ _ _ (by omega)]
      · by_cases hhigh : i.1 + 2 = n
        · -- THigh: right bit (i.1) out of range; left bit ((left i).1 = n-3) in range
          unfold localExp2After localExp2Before
          have hi_ge : n ≤ i.1 + 2 := by omega
          rw [cup2Exp2BitVal_eq_zero_of_ge_top n i.1 _ _ hi_ge,
              cup2Exp2BitVal_eq_zero_of_ge_top n i.1 _ _ hi_ge]
          simp only [Nat.add_zero]
          have hleft_lo : 2 ≤ (left i).1 := by
            rw [left_val_of_ne_zero (by omega)]; omega
          have hleft_hi : (left i).1 + 2 < n := by
            rw [left_val_of_ne_zero (by omega)]; omega
          rw [cup2Exp2BitVal_eq_inner n _ _ _ hleft_lo hleft_hi,
              cup2Exp2BitVal_eq_inner n _ _ _ hleft_lo hleft_hi]
          have hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
              THighVal (c (left i)).1 (c i).1 (c (right i)).1 := by
            unfold cup2OutVal; simp [h0, h1, htop, hhigh]
          rw [hout]
          exact localExp2High_le
            ⟨_, by simpa [cup2Spec, cup2M_left_high hn4 hhigh] using (c (left i)).2⟩
            ⟨_, by simpa [cup2Spec, cup2M_self_high hn4 hhigh] using (c i).2⟩
            ⟨_, by simpa [cup2Spec, cup2M_right_high hn4 hhigh] using (c (right i)).2⟩
        · -- TMid: 2 ≤ i, i + 2 < n
          have hi2 : 2 ≤ i.1 := by omega
          have hitop : i.1 + 2 < n := by omega
          unfold localExp2After localExp2Before
          have hleft_val : (left i).1 = i.1 - 1 := left_val_of_ne_zero (by omega)
          have hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
              TMidVal (c (left i)).1 (c i).1 (c (right i)).1 := by
            unfold cup2OutVal; simp [h0, h1, htop, hhigh]
          rw [hout]
          have hL : (c (left i)).1 < 3 := by
            simpa [cup2Spec, cup2M_left_mid hn4 (by omega) (by omega) htop]
              using (c (left i)).2
          have hS : (c i).1 < 3 := by
            simpa [cup2Spec, cup2M_self_mid hn4 (by omega) htop] using (c i).2
          have hR : (c (right i)).1 < 3 := by
            simpa [cup2Spec, cup2M_right_mid hn4 (by omega) htop hhigh]
              using (c (right i)).2
          by_cases h2 : i.1 = 2
          · -- i = 2: left bit (j=1) out of range, right bit (j=2) in range
            rw [cup2Exp2BitVal_eq_zero_of_lt_two n (left i).1 _ _
                  (by rw [hleft_val]; omega),
                cup2Exp2BitVal_eq_zero_of_lt_two n (left i).1 _ _
                  (by rw [hleft_val]; omega)]
            simp only [Nat.zero_add]
            rw [cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop,
                cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop]
            exact localExp2Mid_right_only_le ⟨_, hL⟩ ⟨_, hS⟩ ⟨_, hR⟩
          · -- i ≥ 3: both bits in range
            rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _
                  (by rw [hleft_val]; omega) (by rw [hleft_val]; omega),
                cup2Exp2BitVal_eq_inner n (left i).1 _ _
                  (by rw [hleft_val]; omega) (by rw [hleft_val]; omega),
                cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop,
                cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop]
            exact localExp2Mid_inner_le ⟨_, hL⟩ ⟨_, hS⟩ ⟨_, hR⟩

/-- Local Int21 after ≤ before for any move at any position. -/
private lemma localInt21_move_le (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) :
    localInt21After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) ≤
      localInt21Before n i (c (left i)).1 (c i).1 (c (right i)).1 := by
  have hin : i.1 < n := i.2
  by_cases h0 : i.1 = 0
  · unfold localInt21After localInt21Before
    rw [cup2Int21BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega),
        cup2Int21BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega)]
    have hleft_val : (left i).1 = n - 1 := by
      rw [left_val, h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [cup2Int21BitVal_eq_zero_of_ge_top n _ _ _ (by omega),
        cup2Int21BitVal_eq_zero_of_ge_top n _ _ _ (by omega)]
  · by_cases h1 : i.1 = 1
    · unfold localInt21After localInt21Before
      have hleft_lt : (left i).1 < 2 := by rw [left_val_of_ne_zero (by omega)]; omega
      rw [cup2Int21BitVal_eq_zero_of_lt_two n _ _ _ hleft_lt,
          cup2Int21BitVal_eq_zero_of_lt_two n _ _ _ hleft_lt,
          cup2Int21BitVal_eq_zero_of_lt_two n _ _ _ (by omega),
          cup2Int21BitVal_eq_zero_of_lt_two n _ _ _ (by omega)]
    · by_cases htop : i.1 + 1 = n
      · unfold localInt21After localInt21Before
        have hleft_ge : n ≤ (left i).1 + 2 := by
          rw [left_val_of_ne_zero (by omega)]; omega
        rw [cup2Int21BitVal_eq_zero_of_ge_top n _ _ _ hleft_ge,
            cup2Int21BitVal_eq_zero_of_ge_top n _ _ _ hleft_ge,
            cup2Int21BitVal_eq_zero_of_ge_top n _ _ _ (by omega),
            cup2Int21BitVal_eq_zero_of_ge_top n _ _ _ (by omega)]
      · by_cases hhigh : i.1 + 2 = n
        · unfold localInt21After localInt21Before
          have hi_ge : n ≤ i.1 + 2 := by omega
          rw [cup2Int21BitVal_eq_zero_of_ge_top n i.1 _ _ hi_ge,
              cup2Int21BitVal_eq_zero_of_ge_top n i.1 _ _ hi_ge]
          simp only [Nat.add_zero]
          have hleft_lo : 2 ≤ (left i).1 := by
            rw [left_val_of_ne_zero (by omega)]; omega
          have hleft_hi : (left i).1 + 2 < n := by
            rw [left_val_of_ne_zero (by omega)]; omega
          rw [cup2Int21BitVal_eq_inner n _ _ _ hleft_lo hleft_hi,
              cup2Int21BitVal_eq_inner n _ _ _ hleft_lo hleft_hi]
          have hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
              THighVal (c (left i)).1 (c i).1 (c (right i)).1 := by
            unfold cup2OutVal; simp [h0, h1, htop, hhigh]
          rw [hout]
          exact localInt21High_le
            ⟨_, by simpa [cup2Spec, cup2M_left_high hn4 hhigh] using (c (left i)).2⟩
            ⟨_, by simpa [cup2Spec, cup2M_self_high hn4 hhigh] using (c i).2⟩
            ⟨_, by simpa [cup2Spec, cup2M_right_high hn4 hhigh] using (c (right i)).2⟩
        · have hi2 : 2 ≤ i.1 := by omega
          have hitop : i.1 + 2 < n := by omega
          unfold localInt21After localInt21Before
          have hleft_val : (left i).1 = i.1 - 1 := left_val_of_ne_zero (by omega)
          have hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
              TMidVal (c (left i)).1 (c i).1 (c (right i)).1 := by
            unfold cup2OutVal; simp [h0, h1, htop, hhigh]
          rw [hout]
          have hL : (c (left i)).1 < 3 := by
            simpa [cup2Spec, cup2M_left_mid hn4 (by omega) (by omega) htop]
              using (c (left i)).2
          have hS : (c i).1 < 3 := by
            simpa [cup2Spec, cup2M_self_mid hn4 (by omega) htop] using (c i).2
          have hR : (c (right i)).1 < 3 := by
            simpa [cup2Spec, cup2M_right_mid hn4 (by omega) htop hhigh]
              using (c (right i)).2
          by_cases h2 : i.1 = 2
          · rw [cup2Int21BitVal_eq_zero_of_lt_two n (left i).1 _ _
                  (by rw [hleft_val]; omega),
                cup2Int21BitVal_eq_zero_of_lt_two n (left i).1 _ _
                  (by rw [hleft_val]; omega)]
            simp only [Nat.zero_add]
            rw [cup2Int21BitVal_eq_inner n i.1 _ _ hi2 hitop,
                cup2Int21BitVal_eq_inner n i.1 _ _ hi2 hitop]
            exact localInt21Mid_right_only_le ⟨_, hL⟩ ⟨_, hS⟩ ⟨_, hR⟩
          · rw [cup2Int21BitVal_eq_inner n (left i).1 _ _
                  (by rw [hleft_val]; omega) (by rw [hleft_val]; omega),
                cup2Int21BitVal_eq_inner n (left i).1 _ _
                  (by rw [hleft_val]; omega) (by rw [hleft_val]; omega),
                cup2Int21BitVal_eq_inner n i.1 _ _ hi2 hitop,
                cup2Int21BitVal_eq_inner n i.1 _ _ hi2 hitop]
            exact localInt21Mid_inner_le ⟨_, hL⟩ ⟨_, hS⟩ ⟨_, hR⟩

/-- Local Exp2Weight after ≤ before for any move at any position. -/
private lemma localExp2Weight_move_le (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n) :
    localExp2WeightAfter n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) ≤
      localExp2WeightBefore n i (c (left i)).1 (c i).1 (c (right i)).1 := by
  have hin : i.1 < n := i.2
  by_cases h0 : i.1 = 0
  · unfold localExp2WeightAfter localExp2WeightBefore
    rw [cup2Exp2BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega),
        cup2Exp2BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega)]
    have hleft_val : (left i).1 = n - 1 := by
      rw [left_val, h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [cup2Exp2BitVal_eq_zero_of_ge_top n (left i).1 _ _ (by rw [hleft_val]; omega),
        cup2Exp2BitVal_eq_zero_of_ge_top n (left i).1 _ _ (by rw [hleft_val]; omega)]
  · by_cases h1 : i.1 = 1
    · unfold localExp2WeightAfter localExp2WeightBefore
      have hleft_lt : (left i).1 < 2 := by rw [left_val_of_ne_zero (by omega)]; omega
      rw [cup2Exp2BitVal_eq_zero_of_lt_two n (left i).1 _ _ hleft_lt,
          cup2Exp2BitVal_eq_zero_of_lt_two n (left i).1 _ _ hleft_lt,
          cup2Exp2BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega),
          cup2Exp2BitVal_eq_zero_of_lt_two n i.1 _ _ (by omega)]
    · by_cases htop : i.1 + 1 = n
      · unfold localExp2WeightAfter localExp2WeightBefore
        have hleft_ge : n ≤ (left i).1 + 2 := by
          rw [left_val_of_ne_zero (by omega)]; omega
        rw [cup2Exp2BitVal_eq_zero_of_ge_top n (left i).1 _ _ hleft_ge,
            cup2Exp2BitVal_eq_zero_of_ge_top n (left i).1 _ _ hleft_ge,
            cup2Exp2BitVal_eq_zero_of_ge_top n i.1 _ _ (by omega),
            cup2Exp2BitVal_eq_zero_of_ge_top n i.1 _ _ (by omega)]
      · by_cases hhigh : i.1 + 2 = n
        · unfold localExp2WeightAfter localExp2WeightBefore
          have hi_ge : n ≤ i.1 + 2 := by omega
          rw [cup2Exp2BitVal_eq_zero_of_ge_top n i.1 _ _ hi_ge,
              cup2Exp2BitVal_eq_zero_of_ge_top n i.1 _ _ hi_ge]
          simp only [Nat.mul_zero, Nat.add_zero]
          have hleft_lo : 2 ≤ (left i).1 := by
            rw [left_val_of_ne_zero (by omega)]; omega
          have hleft_hi : (left i).1 + 2 < n := by
            rw [left_val_of_ne_zero (by omega)]; omega
          rw [cup2Exp2BitVal_eq_inner n _ _ _ hleft_lo hleft_hi,
              cup2Exp2BitVal_eq_inner n _ _ _ hleft_lo hleft_hi]
          have hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
              THighVal (c (left i)).1 (c i).1 (c (right i)).1 := by
            unfold cup2OutVal; simp [h0, h1, htop, hhigh]
          rw [hout]
          exact localExp2WeightHigh_le (left i).1
            ⟨_, by simpa [cup2Spec, cup2M_left_high hn4 hhigh] using (c (left i)).2⟩
            ⟨_, by simpa [cup2Spec, cup2M_self_high hn4 hhigh] using (c i).2⟩
            ⟨_, by simpa [cup2Spec, cup2M_right_high hn4 hhigh] using (c (right i)).2⟩
        · have hi2 : 2 ≤ i.1 := by omega
          have hitop : i.1 + 2 < n := by omega
          unfold localExp2WeightAfter localExp2WeightBefore
          have hleft_val : (left i).1 = i.1 - 1 := left_val_of_ne_zero (by omega)
          have hout : cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
              TMidVal (c (left i)).1 (c i).1 (c (right i)).1 := by
            unfold cup2OutVal; simp [h0, h1, htop, hhigh]
          rw [hout]
          have hL : (c (left i)).1 < 3 := by
            simpa [cup2Spec, cup2M_left_mid hn4 (by omega) (by omega) htop]
              using (c (left i)).2
          have hS : (c i).1 < 3 := by
            simpa [cup2Spec, cup2M_self_mid hn4 (by omega) htop] using (c i).2
          have hR : (c (right i)).1 < 3 := by
            simpa [cup2Spec, cup2M_right_mid hn4 (by omega) htop hhigh]
              using (c (right i)).2
          by_cases h2 : i.1 = 2
          · rw [cup2Exp2BitVal_eq_zero_of_lt_two n (left i).1 _ _
                  (by rw [hleft_val]; omega),
                cup2Exp2BitVal_eq_zero_of_lt_two n (left i).1 _ _
                  (by rw [hleft_val]; omega)]
            simp only [Nat.mul_zero, Nat.zero_add]
            rw [cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop,
                cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop]
            exact localExp2WeightMid_right_only_le i.1 ⟨_, hL⟩ ⟨_, hS⟩ ⟨_, hR⟩
          · rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _
                  (by rw [hleft_val]; omega) (by rw [hleft_val]; omega),
                cup2Exp2BitVal_eq_inner n (left i).1 _ _
                  (by rw [hleft_val]; omega) (by rw [hleft_val]; omega),
                cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop,
                cup2Exp2BitVal_eq_inner n i.1 _ _ hi2 hitop]
            have hweight_rel : i.1 = (left i).1 + 1 := by rw [hleft_val]; omega
            rw [hweight_rel]
            exact localExp2WeightMid_inner_le_param (left i).1 ⟨_, hL⟩ ⟨_, hS⟩ ⟨_, hR⟩

/-- Componentwise ≤ for three Nat pairs → lex nonincreasing (equal or strict decrease). -/
private lemma componentwise_le_to_lex {a1 b1 a2 b2 a3 b3 : Nat}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) :
    (a1, a2, a3) = (b1, b2, b3) ∨
    a1 < b1 ∨ (a1 = b1 ∧ a2 < b2) ∨ (a1 = b1 ∧ a2 = b2 ∧ a3 < b3) := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | hlt1
  · rcases Nat.eq_or_lt_of_le h2 with rfl | hlt2
    · rcases Nat.eq_or_lt_of_le h3 with rfl | hlt3
      · left; rfl
      · right; right; right; exact ⟨rfl, rfl, hlt3⟩
    · right; right; left; exact ⟨rfl, hlt2⟩
  · right; left; exact hlt1

private theorem cup2TpInvariant_badStep_nonincreasing (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hbad : badStep (cup2System n hn4) (cup2GoodCycle n hn4) c' c) :
    cup2TpInvariant n hn4 c' = cup2TpInvariant n hn4 c ∨
    (cup2Exp2Count n hn4 c' < cup2Exp2Count n hn4 c) ∨
    (cup2Exp2Count n hn4 c' = cup2Exp2Count n hn4 c ∧
      cup2Int21Count n hn4 c' < cup2Int21Count n hn4 c) ∨
    (cup2Exp2Count n hn4 c' = cup2Exp2Count n hn4 c ∧
      cup2Int21Count n hn4 c' = cup2Int21Count n hn4 c ∧
      cup2Exp2Weight n hn4 c' < cup2Exp2Weight n hn4 c) := by
  -- Extract mover from badStep
  have ⟨_, _, hstep⟩ := hbad
  rcases hstep with ⟨i, _hpriv, rfl⟩
  have hin : i.1 < n := i.2
  -- Decompose each component into local + rest (rest cancels)
  have he2 : cup2Exp2Count n hn4 (move (cup2System n hn4) c i) ≤ cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c i, cup2Exp2_split n hn4 c i, cup2Exp2_rest_move_eq n hn4 c i]
    suffices localExp2After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) ≤
      localExp2Before n i (c (left i)).1 (c i).1 (c (right i)).1 by omega
    exact localExp2_move_le n hn4 hn9 c i
  have hi21 : cup2Int21Count n hn4 (move (cup2System n hn4) c i) ≤ cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c i, cup2Int21_split n hn4 c i, cup2Int21_rest_move_eq n hn4 c i]
    suffices localInt21After n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) ≤
      localInt21Before n i (c (left i)).1 (c i).1 (c (right i)).1 by omega
    exact localInt21_move_le n hn4 hn9 c i
  have hew : cup2Exp2Weight n hn4 (move (cup2System n hn4) c i) ≤ cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c i, cup2Exp2Weight_split n hn4 c i,
        cup2Exp2Weight_rest_move_eq n hn4 c i]
    suffices localExp2WeightAfter n i (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) ≤
      localExp2WeightBefore n i (c (left i)).1 (c i).1 (c (right i)).1 by omega
    exact localExp2Weight_move_le n hn4 hn9 c i
  -- Convert componentwise ≤ to the lex disjunction
  have hlex := componentwise_le_to_lex he2 hi21 hew
  rcases hlex with heq | hlt
  · left; simp [cup2TpInvariant] at heq ⊢; exact heq
  · rcases hlt with h | h | h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; exact h

/-! ### Split CF into CΦ vs (TP,Φ_full)-dropping -/

/-- Measure for intermediate layers: TP code combined with Φ_full. -/
noncomputable def cup2CfLayerMeasure (n : Nat) (hn : 4 ≤ n)
    (c : Config (cup2Spec n hn)) : Nat × Nat × Nat × Nat :=
  (cup2Exp2Count n hn c, cup2Int21Count n hn c, cup2Exp2Weight n hn c, cup2PhiFull n hn c)

/-- Every CF step either preserves (TP, Φ_full) [CΦ] or strictly decreases
    the 4-component lex measure. -/
private theorem cf_step_cphi_or_measure_drop (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hcf : cup2BadConstFutureStep n hn4 c' c) :
    cup2CPhiStep n hn4 c' c ∨
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))
      (cup2CfLayerMeasure n hn4 c') (cup2CfLayerMeasure n hn4 c) := by
  have hbad := hcf.1
  rcases cup2TpInvariant_badStep_nonincreasing n hn4 hn9 hbad with
    htp_eq | hexp2_lt | ⟨hexp2_eq, hi21_lt⟩ | ⟨hexp2_eq, hi21_eq, hweight_lt⟩
  · -- TP preserved
    have hphi_le := cup2PhiFull_tp_step_mono n hn4 ⟨hbad, htp_eq⟩
    rcases Nat.eq_or_lt_of_le hphi_le with hphi_eq | hphi_lt
    · -- Φ_full preserved → CΦ step
      left
      exact ⟨hcf, htp_eq, hphi_eq⟩
    · -- Φ_full drops → measure drops in component 4
      right
      -- Extract TP component equalities from htp_eq
      have htp := htp_eq
      unfold cup2TpInvariant at htp
      have h1 : cup2Exp2Count n hn4 c' = cup2Exp2Count n hn4 c := congrArg Prod.fst htp
      have h23 : (cup2Int21Count n hn4 c', cup2Exp2Weight n hn4 c') =
          (cup2Int21Count n hn4 c, cup2Exp2Weight n hn4 c) := congrArg Prod.snd htp
      have h2 : cup2Int21Count n hn4 c' = cup2Int21Count n hn4 c := congrArg Prod.fst h23
      have h3 : cup2Exp2Weight n hn4 c' = cup2Exp2Weight n hn4 c := congrArg Prod.snd h23
      show Prod.Lex _ _ (cup2CfLayerMeasure n hn4 c') (cup2CfLayerMeasure n hn4 c)
      simp only [cup2CfLayerMeasure, h1, h2, h3]
      exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ hphi_lt))
  · -- Exp2Count drops → measure drops in component 1
    right; show Prod.Lex _ _ (cup2CfLayerMeasure n hn4 c') (cup2CfLayerMeasure n hn4 c)
    exact Prod.Lex.left _ _ hexp2_lt
  · -- Exp2Count eq, Int21Count drops → component 2
    right; show Prod.Lex _ _ (cup2CfLayerMeasure n hn4 c') (cup2CfLayerMeasure n hn4 c)
    simp only [cup2CfLayerMeasure, hexp2_eq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hi21_lt)
  · -- Exp2Count eq, Int21Count eq, Exp2Weight drops → component 3
    right; show Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))
        (cup2CfLayerMeasure n hn4 c') (cup2CfLayerMeasure n hn4 c)
    unfold cup2CfLayerMeasure; rw [hexp2_eq, hi21_eq]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ hweight_lt))

/-! ### Well-foundedness combinator (duplicated from Main.lean to avoid circular import) -/

private theorem wf_of_inner_segment {α : Type*}
    {inner segment : α → α → Prop}
    (h_inner : WellFounded inner)
    (h_segment : WellFounded segment)
    (h_compose : ∀ {a b c : α}, inner b a → segment c b → segment c a) :
    WellFounded (fun x y => inner x y ∨ segment x y) := by
  apply WellFounded.intro
  intro a₀
  have h_seg_acc := h_segment.apply a₀
  induction h_seg_acc with
  | intro a₀ _ ih_seg =>
    suffices ∀ a₁, Acc inner a₁ →
        (∀ x, segment x a₁ → segment x a₀) →
        Acc (fun x y => inner x y ∨ segment x y) a₁ from
      this a₀ (h_inner.apply a₀) (fun x h => h)
    intro a₁ h_acc h_lift
    induction h_acc with
    | intro a₁ _ ih_inner =>
      constructor
      intro x hx
      cases hx with
      | inl h_i => exact ih_inner x h_i (fun y hy => h_lift y (h_compose h_i hy))
      | inr h_s => exact ih_seg x (h_lift x h_s)

/-! ### Segment relation for TP/Φ_full drops -/

/-- Segment: chain of CΦ steps followed by a measure-dropping CF step. -/
noncomputable def cup2CfLayerDropSegment (n : Nat) (hn4 : 4 ≤ n)
    (c' c : Config (cup2Spec n hn4)) : Prop :=
  ∃ d, Relation.ReflTransGen (cup2CPhiStep n hn4) d c ∧
    cup2BadConstFutureStep n hn4 c' d ∧
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))
      (cup2CfLayerMeasure n hn4 c') (cup2CfLayerMeasure n hn4 d)

/-- CΦ chains preserve the measure. -/
private lemma cfLayerMeasure_eq_of_cphiChain (n : Nat) (hn4 : 4 ≤ n)
    {d c : Config (cup2Spec n hn4)}
    (hchain : Relation.ReflTransGen (cup2CPhiStep n hn4) d c) :
    cup2CfLayerMeasure n hn4 d = cup2CfLayerMeasure n hn4 c := by
  induction hchain with
  | refl => rfl
  | tail _ hstep ih =>
    unfold cup2CfLayerMeasure at ih ⊢
    rw [ih]
    have ⟨_, htp, hphi⟩ := hstep
    unfold cup2TpInvariant at htp
    have h1 : cup2Exp2Count n hn4 _ = cup2Exp2Count n hn4 _ := congrArg Prod.fst htp
    have h23 := congrArg Prod.snd htp
    have h2 : cup2Int21Count n hn4 _ = cup2Int21Count n hn4 _ := congrArg Prod.fst h23
    have h3 : cup2Exp2Weight n hn4 _ = cup2Exp2Weight n hn4 _ := congrArg Prod.snd h23
    simp only [h1, h2, h3, hphi]

/-- The 4-component lex well-founded relation. -/
private def lexWf4 : WellFounded
    (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))) :
      Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Prop) :=
  WellFounded.prod_lex Nat.lt_wfRel.wf
    (WellFounded.prod_lex Nat.lt_wfRel.wf
      (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf))

/-- The segment relation is well-founded: measure strictly drops. -/
noncomputable def cup2CfLayerDropSegment_wf (n : Nat) (hn4 : 4 ≤ n) :
    WellFounded (cup2CfLayerDropSegment n hn4) := by
  apply WellFounded.mono (InvImage.wf (cup2CfLayerMeasure n hn4) lexWf4)
  intro c' c ⟨d, hchain, _, hdrop⟩
  show Prod.Lex _ _ (cup2CfLayerMeasure n hn4 c') (cup2CfLayerMeasure n hn4 c)
  have heq := cfLayerMeasure_eq_of_cphiChain n hn4 hchain
  rw [← heq]; exact hdrop

/-- CΦ step extends a segment. -/
private theorem cphi_extends_cfLayerSegment (n : Nat) (hn4 : 4 ≤ n)
    {a b c : Config (cup2Spec n hn4)}
    (h_cphi : cup2CPhiStep n hn4 b a)
    (h_seg : cup2CfLayerDropSegment n hn4 c b) :
    cup2CfLayerDropSegment n hn4 c a := by
  rcases h_seg with ⟨d, hchain, hcf_drop, hmeasure⟩
  exact ⟨d, Relation.ReflTransGen.tail hchain h_cphi, hcf_drop, hmeasure⟩

/-! ### Main result: WF of CF steps via CΦ + measure drop -/

/-- Every CF step is either CΦ or a measure-dropping segment.
    (Uses the TP non-increasing lemma, now fully proved.) -/
private theorem cf_step_cphi_or_segment (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hcf : cup2BadConstFutureStep n hn4 c' c) :
    cup2CPhiStep n hn4 c' c ∨ cup2CfLayerDropSegment n hn4 c' c := by
  rcases cf_step_cphi_or_measure_drop n hn4 hn9 hcf with hcphi | hdrop
  · left; exact hcphi
  · right; exact ⟨c, Relation.ReflTransGen.refl, hcf, hdrop⟩

/-- WF of CF steps, given WF of CΦ steps.
    Uses wf_of_inner_segment with inner = CΦ, segment = measure-drop. -/
theorem cup2BadConstFutureStep_wf_of_cphi (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (h_cphi_wf : WellFounded (cup2CPhiStep n hn4)) :
    WellFounded (cup2BadConstFutureStep n hn4) := by
  -- CF ⊆ CΦ ∪ CfLayerDropSegment
  -- CΦ is WF (given)
  -- CfLayerDropSegment is WF (measure drops)
  -- CΦ step extends CfLayerDropSegment (chain extension)
  have hwf_union := wf_of_inner_segment h_cphi_wf
    (cup2CfLayerDropSegment_wf n hn4)
    (cphi_extends_cfLayerSegment n hn4)
  exact WellFounded.mono hwf_union (fun {c' c} hcf =>
    cf_step_cphi_or_segment n hn4 hn9 hcf)

end LeanMn
